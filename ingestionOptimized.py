#!/usr/bin/env python3
"""
openEHR → CatSalut CDR ingestor  (v12.1  2025-05-01)

• atomic global _codes (with safety re-insert of _id:"ar_code")
• full key/value shortcut pass (deep)
• replication factor, safe inserts
• detailed per-EHR logging
"""

import os, json, logging, threading, certifi, traceback, time
from datetime import datetime, timezone
from dateutil import parser 
from typing import Any, Dict, List, Tuple, Set
from bson     import ObjectId
from pymongo  import MongoClient
from pymongo.database import Database
from pymongo.errors import BulkWriteError
from pymongo.collection import Collection
from multiprocessing import freeze_support
import re


# ───────── logging ─────────
logging.basicConfig(
    level=getattr(logging, os.getenv("LOG_LEVEL","INFO").upper()),
    format="[%(processName)s %(asctime)s] %(levelname)s %(message)s",
    datefmt="%H:%M:%S",
)
logging.getLogger("pymongo").setLevel(logging.WARNING)

# ───────── globals shared by workers ─────────
CACHE_LOCK = threading.Lock()

LOCATABLE = {                   # quick membership test
    "COMPOSITION","SECTION","ADMIN_ENTRY","OBSERVATION","EVALUATION",
    "INSTRUCTION","ACTION","CLUSTER","ITEM_TREE","ITEM_LIST","ITEM_SINGLE",
    "ITEM_TABLE","ELEMENT","HISTORY","EVENT","POINT_EVENT","INTERVAL_EVENT",
    "ACTIVITY","ISM_TRANSITION","INSTRUCTION_DETAILS","CARE_ENTRY",
    "PARTY_PROXY","EVENT_CONTEXT"
}

NON_ARCHETYPED_RM = {             
    "HISTORY","ISM_TRANSITION", "EVENT_CONTEXT"
}

LOC_HINT = {"archetype_node_id", "archetype_details"}
#SKIP_ATTRS = {"archetype_details", "uid"}
SKIP_ATTRS = {}


def load_jsonc(path: str) -> dict:
    txt = open(path, encoding="utf-8").read()
    txt = re.sub(r"//.*?$|/\*.*?\*/", "", txt, flags=re.M | re.S)
    return json.loads(txt)

RAW_RULES = load_jsonc("mappings.jsonc").get("templates", {})

# ACTIVE_RULES will be built lazily during the first encounter
ACTIVE_RULES: dict[int, list[dict]] = {}

SEARCH = None          

SHORTCUT_KEYS : Dict[str,str] = {}
SHORTCUT_VALS : Dict[str,str] = {}
alloc_code = None

cfg_global: dict = {}         
_local = threading.local()

CODE_BOOK   : dict[str, dict[str, int]] = {}   # e.g. CODE_BOOK["ar_code"][sid] = n
SEQ         : dict[str, int]            = {"ar_code": 0}
_INDEX_RE = re.compile(r'^(a|pc|pch)(-?\d+)$') 

# ═════════ config ═════════
def cfg(path="config.json"):
    with open(path,encoding="utf-8") as f:
        return json.load(f)

# ═════════ _codes allocator ═════════
def load_codes_from_db(codes_col: Collection):
    """Rebuild CODE_BOOK and SEQ from the persisted _codes document."""
    doc = codes_col.find_one({"_id": "ar_code"}) or {}

    # ── 1.  archetype-ID codes ────────────────────────────────────
    ar_book: dict[str, int] = {}
    for rm, subtree in doc.items():
        if rm in ("_id", "_max", "_min", "unknown", "at"):
            continue
        if not isinstance(subtree, dict):
            continue
        for name, vers in subtree.items():
            if not isinstance(vers, dict):
                continue
            for ver, code in vers.items():
                ar_book[f"{rm}.{name}.{ver}"] = code

    # ── 2.  at-codes (negative) ───────────────────────────────────
    at_book = {k: int(v) for k, v in (doc.get("at") or {}).items()
               if isinstance(v, int)}

    with CACHE_LOCK:
        CODE_BOOK["ar_code"] = ar_book
        CODE_BOOK["at"]      = at_book
        SEQ["ar_code"]       = doc.get("_max", SEQ["ar_code"])
        SEQ["at"]            = doc.get("_min", SEQ["at"])

def _primary_flush_loop(tgt_coll: Collection, cfg: dict):
    interval = cfg["codes_refresh_interval"]
    while True:
        time.sleep(interval)
        try:
            # pass in the Database, not the Collection or MongoClient
            flush_globals_into_db(tgt_coll.database, cfg)
            logging.info("✅ Primary: flushed _codes to %r", cfg["target"]["codes_collection"])
        except Exception:
            logging.exception("❌ Primary: failed to flush _codes")

def _secondary_reload_loop(tgt_coll: Collection, cfg: dict):
    interval = cfg["codes_refresh_interval"]
    while True:
        time.sleep(interval)
        try:
            load_codes_from_db(tgt_coll.database[cfg["target"]["codes_collection"]])
            logging.info("🔄 Secondary: reloaded _codes from server")
        except Exception:
            logging.exception("❌ Secondary: failed to reload _codes")

def make_allocator(_: str):
    """
    In-memory allocator.
    • primary: allocates any new non-at… codes into CODE_BOOK/SEQ
    • secondary: if sees a non-at… sid not in CODE_BOOK, marks the doc as bad
                 and returns None, so that composition is skipped.
    """
    def alloc(key: str, sid: str) -> int|None:
            sid_lower = sid.lower()
            if key == "ar_code" and sid_lower.startswith("at"):
                n = at_code_to_int(sid)
                if n is not None:
                    return n

            book = CODE_BOOK.setdefault(key,{})
            if sid in book:
                return book[sid]

            if cfg_global.get("role") != "primary":
                _local.bad_code = True
                return None

            SEQ.setdefault(key,0)
            SEQ[key] += 1
            code = SEQ[key]
            book[sid] = code
            return code

    return alloc

def bootstrap_codes(db, coll_name):
    col = db[coll_name]
    col.update_one({"_id":"ar_code"},
                   {"$setOnInsert": {"_id":"ar_code"}},
                   upsert=True)
    col.update_one({"_id":"sequence"},
                   {"$setOnInsert": {"_id":"sequence","seq": {"ar_code":0}}},
                   upsert=True)


# ═════════ shortcut expansion ═══════════
def apply_sc(o):
    if isinstance(o,dict):
        return {SHORTCUT_KEYS.get(k,k):apply_sc(v) for k,v in o.items()}
    if isinstance(o,list):
        return [apply_sc(x) for x in o]
    if isinstance(o,str):
        if o in SHORTCUT_VALS:
            return SHORTCUT_VALS[o]
    return o


# ───────── claim & lock a patient ─────────
def claim_patient_id(coll) -> str|None:
    doc = coll.find_one_and_update(
        {"used": {"$ne": True}},
        {"$set": {"used": True}},
        sort=[("_id", 1)],
        projection={"ehr_id": 1},
    )
    if not doc:
        return None
    eid = doc["ehr_id"]

    # retry loop for update_many:
    retries = 3
    while retries:
        try:
            coll.update_many(
                {"ehr_id": eid, "used": False},
                {"$set": {"used": True}}
            )
            return eid
        except BulkWriteError as bwe:
            # if there are duplicate‐key errors, you can handle them here
            raise
        except WriteError as we:
            if we.code == 6:    # “operation was interrupted”
                retries -= 1
                time.sleep(0.5)
                continue
            else:
                raise
    # if we ran out of retries, give up on this eid and mark it back to unused
    coll.update_many({"ehr_id": eid}, {"$set": {"used": False}})
    return None

def next_patient_id(src_coll, *, stop_after:int):
    """Generator that hands out up to `stop_after` patient IDs."""
    issued = 0
    while issued < stop_after:
        eid = claim_patient_id(src_coll)
        if eid is None:
            break
        issued += 1
        yield eid

# ═════════ at‑code → int ════════════════════════════════════════

_AT_RE = re.compile(r"""
    ^at0*([0-9]{1,5})           # major: 1-5 digits   (→ 0 … 99 999)
    (?:\.([0-9]{1,4}))?         # optional .fraction: 1-4 digits
$""", re.IGNORECASE | re.VERBOSE)

_START_DOTTED = -10_000           # first id for dotted at-codes
_AT_ROOT      = re.compile(r"^at0*([1-9][0-9]*)$", re.I)
_AT_DOTTED    = re.compile(r"^at[0-9]+(?:\.[0-9]{1,4})+$", re.I)

CODE_BOOK: dict[str, dict[str, int]] = {
    "ar_code": {},   # positive codes for archetype-IDs
    "at":      {},   # negative codes for at-codes
}
SEQ: dict[str, int] = {
    "ar_code": 0,    # highest positive so far
    "at":      -1,   # most-negative so far (≥ –1)
}

def at_code_to_int(at: str) -> int | None:
    """
    • plain  at0005      → –5
    • plain  at0150      → –150
    • dotted at0005.02   → –10000, –10001, …  (sequential, stable)
    All values are **negative**.  The mapping is persisted in
    CODE_BOOK["at"] and flushed to Mongo so it is repeatable across runs.
    """
    s = at.lower()

    # ① already known
    if s in CODE_BOOK["at"]:
        return CODE_BOOK["at"][s]

    # ② secondaries never allocate new codes
    if cfg_global.get("role") != "primary":
        _local.bad_code = True
        return None

    # ③ plain root (any length)  →  −numericPart
    m_root = _AT_ROOT.match(s)
    if m_root:
        code = -int(m_root.group(1))          # at0132 → –132
        CODE_BOOK["at"][s] = code
        SEQ["at"] = min(SEQ["at"], code)
        return code

    # ④ dotted variant  →  sequential from –10 000 downwards
    if _AT_DOTTED.match(s):
        SEQ["at"] = SEQ["at"] - 1 if SEQ["at"] <= _START_DOTTED else _START_DOTTED
        code = SEQ["at"]
        CODE_BOOK["at"][s] = code
        return code

    logging.warning("at_code_to_int: could not parse %r", at)
    return None

def archetype_id(obj: dict) -> str | None:
    # 1️⃣ look in archetype_details.archetype_id.value
    ad = obj.get("archetype_details") or {}
    ai = ad.get("archetype_id")
    if isinstance(ai, dict) and ai.get("value"):
        return ai["value"].strip()
    if isinstance(ai, str) and ai.strip():
        return ai.strip()

    # 2️⃣ fallback to the direct archetype_node_id property if present
    ani = obj.get("archetype_node_id")
    if isinstance(ani, str) and ani.strip():
        return ani.strip()

    return None

# ───────── decide if a locatable must get its own node ──────────
def split_me_as_a_new_node(obj: dict) -> bool:
    """
    Emit a separate node for ANY dict that has both
    an '_type' and an 'archetype_node_id' field.
    """
    if not isinstance(obj, dict):
        return False
    """Emit a separate node for ANY dict that carries an archetype_node_id."""
    return isinstance(obj, dict) and "archetype_node_id" in obj

def strip_locatables(d: dict) -> dict:
    """
    Return a shallow copy of *d* with every key whose value is
    - a locatable dict, or
    - a list containing at least one locatable
    removed.
    """
    out = {}
    for k, v in d.items():
        if isinstance(v, dict) and is_locatable(v):
            continue
        if isinstance(v, list) and any(is_locatable(x) for x in v):
            continue
        out[k] = v
    return out

def is_locatable(obj: dict) -> bool:
    if not isinstance(obj, dict):
        return False

    # only test membership if _type is actually a str
    t = obj.get("_type")
    if isinstance(t, str) and t in LOCATABLE:
        return True

    # fallback: any of our “hints” in the dict keys
    return any(k in obj for k in LOC_HINT)

def dpath_get(obj: Any, path: str) -> Any | None:
    """
    Follow a dotted JSON-path.  
    • dict  – follow the key  
    • list  – three cases  
        1. next part is a numeric index → that element  
        2. list len == 1 → dive into its only element  
        3. otherwise     → collect that field from *all* elements  
           and return a list (filtered for None); if the final list
           has just one item, unwrap it to the single value.
    """
    parts = path.split(".")

    def walk(cur, idx):
        if idx == len(parts):
            return cur

        part = parts[idx]

        # ---------- dictionaries ----------
        if isinstance(cur, dict):
            return walk(cur.get(part), idx + 1)

        # ---------- lists ----------
        if isinstance(cur, list):
            # numeric index (“0”, “1” …)
            if part.isdigit():
                n = int(part)
                if 0 <= n < len(cur):
                    return walk(cur[n], idx + 1)
                return None

            # single-item list – just dive into it
            if len(cur) == 1:
                return walk(cur[0], idx)

            # several items – collect from all of them
            coll = [walk(item, idx) for item in cur]
            coll = [v for v in coll if v is not None]
            if not coll:
                return None
            if len(coll) == 1:
                return coll[0]
            return coll

        # ---------- anything else ----------
        return None

    return walk(obj, 0)

def seg_to_int(seg: str|int) -> int:
    """
    Convert a mapping-segment into its numeric form.

    • int – already numeric, return as is
    • str starting with 'at' – at-code ➜ at_code_to_int()
    • archetype id  (openEHR-EHR-…) – allocator gives the current code
    """
    if isinstance(seg, int):
        return seg
    if isinstance(seg, str):
        seg_l = seg.lower()
        if seg_l.startswith("at"):
            n = at_code_to_int(seg)
            if n is None:
                raise ValueError(f"bad at-code {seg}")
            return n
        # archetype id → numeric code (creates it on first encounter)
        n = alloc_code("ar_code", seg)
        if n is None:
            raise ValueError(f"unknown archetype id {seg}")
        return n
    raise TypeError("segment must be str or int")

def to_bson_dates(obj):
    """
    Recursively convert both:
      • openEHR style:   {"_type":"DV_DATE_TIME"|"DV_DATE","value":"ISO-string"}
      • legacy style:    {"T":"ddt"|"dt",   "v":"ISO-string"}
    into Python datetimes (naïve UTC) so PyMongo stores BSON dates.
    """
    # 1) openEHR style containers
    if isinstance(obj, dict):
        t0 = obj.get("_type")
        if t0 in ("DV_DATE_TIME", "DV_DATE") and isinstance(obj.get("value"), str):
            try:
                dt = parser.isoparse(obj["value"])
                if dt.tzinfo is not None:
                    dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
                new = obj.copy()
                new["value"] = dt
                return new
            except Exception as e:
                logging.warning(f"to_bson_dates: failed parsing {obj['value']!r}: {e}")
                return obj

        # 2) legacy style containers
        t1 = obj.get("T", "").lower()
        if t1 in ("ddt", "dt") and isinstance(obj.get("v"), str):
            try:
                dt = parser.isoparse(obj["v"])
                if dt.tzinfo is not None:
                    dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
                new = obj.copy()
                new["v"] = dt
                return new
            except Exception as e:
                logging.warning(f"to_bson_dates: failed parsing {obj['v']!r}: {e}")
                return obj

        # 3) recurse into all other dict keys
        return {k: to_bson_dates(v) for k, v in obj.items()}

    # 4) recurse lists
    if isinstance(obj, list):
        return [to_bson_dates(item) for item in obj]

    # 5) leave everything else unchanged
    return obj

def build_pc(ani: int, ancestors: list[int]) -> list[str]:
    """
     Return the cumulative path-chain (`pc`).

     *ancestors* are expected in **root-first** order.
       • If the node is the root (no parent) an empty list is returned.
       • Otherwise the first element is  "<ani>.<parent>",
         the last element is the full   "<ani>.<…>.11".
    """
    segs = [str(ani)] + [str(x) for x in reversed(ancestors)]
    # always include the single-node chain
    pc = [segs[0]]
    if len(segs) < 2:
        return pc
    acc = f"{segs[0]}.{segs[1]}"
    pc.append(acc)
    for s in segs[2:]:
        acc = f"{acc}.{s}"
        pc.append(acc)
    return pc

def get_rules_for(template: int, original_num: str) -> list[dict]:
    """
    Build (and cache) the compiled rule list.

    * pathChain : author writes LEAF → ROOT               → we keep it as-is
    * contains  : author writes LEAF → ROOT               → **reverse** here
                   so inside transform() it is ROOT → LEAF
    * _cont is always **one** tuple (not a list of tuples) because
      transform() expects a single subsequence to match.
    """
    if template in ACTIVE_RULES:
        return ACTIVE_RULES[template]

    raw_block = RAW_RULES.get(original_num, {})
    compiled: list[dict] = []

    for r in raw_block.get("rules", []):
        w = r["when"]

        # 1.  contiguous chain (leaf-first)
        p_raw      = w.get("pathChain", [])
        path_codes = tuple(seg_to_int(x) for x in p_raw)

        # 2.  contains / ancestors
        c_raw  = w.get("contains", [])
        cont   = tuple(seg_to_int(x) for x in reversed(c_raw))   # root-first

        # 3.  any dotted predicates
        extra: list[tuple[str, Any]] = [
            (k, v) for k, v in w.items()
            if k not in ("pathChain", "contains")
        ]

        compiled.append({
            "_path"  : path_codes,   # leaf-first
            "_cont"  : cont,         # root-first tuple  (may be empty)
            "_extra" : extra,
            "copy"   : r["copy"],
        })

    ACTIVE_RULES[template] = compiled
    return compiled
# ────────────────────────────────────────────────────────────────────
#  Flatten a composition
# ────────────────────────────────────────────────────────────────────
def walk(node: dict,
         ancestors: Tuple[int, ...],
         cn: List[dict],
         *,
         inside_list: bool,
         attr_key: str | None = None) -> None:
    """
    Flatten every locatable into cn.
    We collect scalars → convert dates → apply shortcuts → append once.
    The list `_anc` (root-first codes) is kept for transform().
    """
    aid   = archetype_id(node)
    code  = None
    if aid and aid.startswith("at"):
        code = at_code_to_int(aid)
    elif aid:
        code = alloc_code("ar_code", aid)

    is_root = not ancestors
    emit    = (inside_list or is_root or split_me_as_a_new_node(node)) \
               and code is not None

    if emit:
        # 1) collect all simple fields
        scalars: Dict[str,Any] = {}
        for k, v in node.items():
            # drop nested locatables
            if isinstance(v, dict) and is_locatable(v):
                if v.get("_type") in NON_ARCHETYPED_RM:
                    scalars[k] = strip_locatables(v)
                continue
            if k in SKIP_ATTRS:
                continue
            if isinstance(v, dict) and split_me_as_a_new_node(v):
                continue
            if isinstance(v, list) and any(split_me_as_a_new_node(x) for x in v):
                continue
            scalars[k] = v

        # 2) convert DV_DATE_TIME/legacy → real datetime
        scalars = to_bson_dates(scalars)

        # 3) apply shortcuts + meta
        d = apply_sc(scalars)
        d["ani"] = code
        if attr_key:
            d["ak"] = SHORTCUT_KEYS.get(attr_key, attr_key)
        rt = node.get("_type")
        if rt and rt in SHORTCUT_VALS:
            d["T"] = SHORTCUT_VALS[rt]

        # 4) append exactly once, carrying root-first ancestors
        cn.append({
            "d":   d,
            "_anc": list(ancestors),
        })

    # recurse on child locatables
    new_anc = ancestors + ((code,) if emit else ())
    for k, v in node.items():
        if isinstance(v, dict) and is_locatable(v):
            walk(v, new_anc, cn, inside_list=False, attr_key=k)
        elif isinstance(v, list):
            for it in v:
                if is_locatable(it):
                    walk(it, new_anc, cn, inside_list=True, attr_key=k)



def transform(raw: dict) -> tuple[dict, dict] | None:
    comp        = raw["canonicalJSON"]
    root_aid    = archetype_id(comp) or "unknown"
    template_id = alloc_code("ar_code", root_aid)

    # 1) flatten into cn[]
    cn: List[dict] = []
    walk(comp, (), cn, inside_list=False)
    if _local.bad_code and cfg_global.get("role") != "primary":
        return None

    rules = get_rules_for(template_id, root_aid)

    # 2) decorate each cn node with its leaf-first p
    for node in cn:
        anc = node["_anc"]                           # still root-first
        pc  = build_pc(node["d"]["ani"], anc)        # returns leaf-first segments
        if pc:
            node["p"] = pc[-1]                       # full path, leaf-first

    # 3) build sn exactly as before, just drop hx
    sn: List[dict] = []
    for node in cn:
        dblock = node["d"]
        anc    = node["_anc"]
        pc_set = set(build_pc(dblock["ani"], anc))

        for rule in rules:
            # 3a) contiguous match
            rc = rule["_path"]
            if rc:
                key = ".".join(str(x) for x in rc)
                if key not in pc_set:
                    continue

            # 3b) contains/subsequence match
            rc2 = rule["_cont"]
            if rc2:
                j = 0
                for code in anc:
                    if code == rc2[j]:
                        j += 1
                        if j == len(rc2):
                            break
                if j != len(rc2):
                    continue

            # 3c) extra predicates
            if any(dpath_get({"d": dblock}, path) != val_req
                   for path, val_req in rule["_extra"]):
                continue

            # 4) rule matched → slim
            slim: Dict[str,Any] = {}
            for expr in rule["copy"]:
                if expr.startswith("d."):
                    sub = expr[2:]
                    val = dpath_get(dblock, sub)
                    if val is None:
                        continue
                    cur = slim.setdefault("d", {})
                    for part in sub.split(".")[:-1]:
                        cur = cur.setdefault(part, {})
                    cur[sub.split(".")[-1]] = val
                elif expr == "p":
                    slim["p"] = node["p"]

            if slim:
                sn.append(slim)

    # 4) now it’s safe to drop the internal _anc from cn
    for node in cn:
        node.pop("_anc", None)

    # 5) assemble the two output docs
    base_doc = {
        "_id":     raw["_id"],
        "ehr_id":  raw["ehr_id"],
        "comp_id": raw["_id"],
        "v":       raw.get("composition_version"),
        "tid":     template_id,
        "cn":      cn,
    }
    search_doc = {
        "_id":    raw["_id"],
        "ehr_id": raw["ehr_id"],
        "tid":    template_id,
        "sn":     sn,
    }
    return base_doc, search_doc

    
    # ═════════ safe insert ═══════════════════
def safe_insert(col,docs):
    if not docs: return 0
    try: return len(col.insert_many(docs,ordered=False).inserted_ids)
    except BulkWriteError as bwe:
        dup=sum(1 for e in bwe.details.get("writeErrors",[]) if e["code"]==11000)
        other=[e for e in bwe.details.get("writeErrors",[]) if e["code"]!=11000]
        if other: raise
        return len(docs)-dup

# ═════════ batch flag reset ═══════════════
def reset_used(coll,batch):
    while True:
        ids=[d["_id"] for d in coll.find({"used":True},{"_id":1}).limit(batch)]
        if not ids: break
        coll.update_many({"_id":{"$in":ids}},{"$unset":{"used":""}})

# ═════════ worker init ════════════════════
def init_worker(cfg: dict, ca: str) -> None:
    """
    Connects to Mongo, primes the shortcut tables and installs the
    in‑memory *alloc_code* function.  
    """
    global SRC, TGT, SEARCH, alloc_code

    src_cli = MongoClient(cfg["source"]["connection_string"], tlsCAFile=ca)
    tgt_cli = MongoClient(cfg["target"]["connection_string"], tlsCAFile=ca)

    SRC = src_cli[cfg["source"]["database_name"]][
        cfg["source"]["collection_name"]
    ]
    TGT = tgt_cli[cfg["target"]["database_name"]][
        cfg["target"]["compositions_collection"]
    ]
    SEARCH = tgt_cli[cfg["target"]["database_name"]][     
        cfg["target"]["search_collection"]
    ]

    alloc_code = make_allocator("")      # now purely in‑memory

    # ── populate the shortcut tables (keys / values) ───────────────────
    sc = tgt_cli[cfg["target"]["database_name"]][
        cfg["target"]["shortcuts_collection"]
    ].find_one({"_id": "shortcuts"}) or {}

    SHORTCUT_KEYS.update(sc.get("keys",   {}))
    SHORTCUT_VALS.update(sc.get("values", {}))

# ═════════ per-patient job ════════════════
def proc(eid, cfg):
    try:
        raws = list(SRC.find({"ehr_id": eid},
                             {"_id":1, "ehr_id":1, "canonicalJSON":1, "comp_id":1, "composition_version":1}))
        if not raws:
            return eid, 0, 0, []

        rf            = cfg.get("replication_factor", 1)
        docs_full     = []
        docs_search   = []

        for r in raws:
            _local.bad_code = False
            result = transform(r)
            if result is None:
                continue
            base, slim = result
            
            if not slim["sn"]:            # ← nothing matched the mapping rules
                slim = None 

            for i in range(rf):
                new_id = ObjectId()
                # full doc
                d = base.copy()
                d["_id"]   = new_id
                d["ehr_id"] = f"{eid}~r{i+1}"
                docs_full.append(d)
                # search doc (only if we have one)
                if slim is not None:
                    s = slim.copy()
                    s["_id"]   = new_id
                    s["ehr_id"] = d["ehr_id"]
                    docs_search.append(s)

        ins_full   = safe_insert(TGT,    docs_full)
        ins_search = safe_insert(SEARCH, docs_search)

        return eid, len(raws), ins_full, []

    except Exception:
        return eid, 0, 0, [traceback.format_exc()]

# ────────────────────────────────────────────────────────────────
#  Correct flush_globals_into_db
# ────────────────────────────────────────────────────────────────
def flush_globals_into_db(db: Database, cfg: dict) -> None:
    """
    Persist all content of CODE_BOOK and SEQ into the target
    <codes_collection>.  Works with any archetype-ID string—whether it
    contains 1, 2, 3, or many dots.

    Document layout:

        _id  = "ar_code"
        at   = { "at0005": -5, … }
        _min = most-negative at-code
        <rm> = { <name>: { <version>: code, … }, … }
        _max = highest positive archetype code
    """
    codes_col = db[cfg["target"]["codes_collection"]]

    # ── 1.  AT-codes (negative) ──────────────────────────────────
    nested: Dict[str, Any] = {
        "at":   CODE_BOOK.get("at", {}),
        "_min": SEQ.get("at", -1),
    }

    # ── 2.  positive archetype codes  ────────────────────────────
    book      = CODE_BOOK.get("ar_code", {})
    max_code  = 0

    for sid, code in book.items():
        if isinstance(code, int) and code > max_code:
            max_code = code

        # split robustly:   rm . name . version-with-dots-if-any
        parts = sid.split(".")
        rm    = parts[0]                       # always present
        name  = parts[1] if len(parts) > 1 else ""
        ver   = ".".join(parts[2:]) if len(parts) > 2 else ""

        nested.setdefault(rm, {}) \
              .setdefault(name, {})[ver] = code

    nested["_max"] = max_code

    # ── 3.  write back to Mongo  ─────────────────────────────────
    codes_col.replace_one(
        {"_id": "ar_code"},
        {"_id": "ar_code", **nested},
        upsert=True,
    )
    codes_col.replace_one(
        {"_id": "sequence"},
        {"_id": "sequence", "seq": SEQ},
        upsert=True,
    )

# ═════════ main ═══════════════════════════
def main():
    global alloc_code, cfg_global
    c  = cfg()
    ca = certifi.where()
    cfg_global = c
    alloc_code = make_allocator("") 

    # ───── optional clean / reset steps (unchanged) ─────
    if c.get("clean_collections", False):
        tgt = MongoClient(c["target"]["connection_string"], tlsCAFile=ca)
        db  = tgt[c["target"]["database_name"]]
        logging.info("🧹 dropping target collections")
        for n in ("compositions_collection",
                  "search_collection",
                  "codes_collection"):
            db[c["target"][n]].drop()
        tgt.close()

    if c.get("reset_used_flags", False):
        src = MongoClient(c["source"]["connection_string"], tlsCAFile=ca)
        logging.info("🧹 resetting source.used flags")
        reset_used(
            src[c["source"]["database_name"]][c["source"]["collection_name"]],
            c.get("batch_size_reset", 2500),
        )
        src.close()

    # ───── bootstrap the three seed documents once ─────
    tgt = MongoClient(c["target"]["connection_string"], tlsCAFile=ca)
    bootstrap_codes(
        tgt[c["target"]["database_name"]], c["target"]["codes_collection"]
    )
    tgt.close()

    # ───── ‹S E Q U E N T I A L› ingestion – no workers ─────
    init_worker(c, ca)                       # we still reuse the worker‑init

    load_codes_from_db(TGT.database[c["target"]["codes_collection"]])
    logging.info("Loaded %d existing ar_codes before restart",
             len(CODE_BOOK.get("ar_code", {})))
    role = c.get("role", "primary").lower()
    cfg_global["role"] = role         
    if role == "primary":
        threading.Thread(
            target=_primary_flush_loop,
            args=(TGT, c),
            daemon=True
        ).start()
    else:
        # load once immediately, then refresh
        load_codes_from_db(TGT.database[c["target"]["codes_collection"]])
        threading.Thread(
            target=_secondary_reload_loop,
            args=(TGT, c),
            daemon=True
        ).start()
    logging.info("🔖 Started in %s role; codes will refresh every %d seconds",
                 role, c["codes_refresh_interval"])
                 
    src_coll = SRC                           # set by init_worker
    plimit   = c.get("patient_limit", 500)

    logging.info("🏃 single‑worker run, up to %d patients", plimit)

    done = fail = total_read = total_ins = 0
    for count, eid in enumerate(next_patient_id(SRC, stop_after=plimit), start=1):
        eid, read, ins, errs = proc(eid, c)
        total_read += read
        total_ins  += ins
        if errs:
            fail += 1
            logging.error("✖ %s failed\n%s", eid, errs[0])
        else:
            done += 1

        if count % 10 == 0:
            logging.info("… processed %d / %d", count, plimit)

    logging.info("✓ done %d  ✖ failed %d   source %d  inserted %d",
                 done, fail, total_read, total_ins)

    tgt_cli = MongoClient(c["target"]["connection_string"], tlsCAFile=ca)
    db      = tgt_cli[c["target"]["database_name"]]
    flush_globals_into_db(db, c)
    logging.info("ar_code next value will be %d", SEQ["ar_code"] + 1)
    tgt_cli.close()
    
if __name__=="__main__":
    freeze_support(); main()
