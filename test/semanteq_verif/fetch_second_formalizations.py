#!/usr/bin/env python3
"""Complete SemantEq-Verif with the 38 candidates that are not redistributed here.

    python3 test/semanteq_verif/fetch_second_formalizations.py

Thirty-eight Erdős candidates are a second formalization of the problem, taken from the
repository plby/lean-proofs. That repository carries no licence, so `pairs.jsonl` holds these
rows with `candidate: null`. This script downloads the 38 source files at the pinned commit,
cuts each one down to the candidate used in the paper (the kept spans and the few characters we
added are in `second_formalizations.json`), checks every result against its SHA-256, and writes
the complete benchmark, 226 rows, to test/data/semanteq_verif.jsonl.

It needs only the Python standard library. With --from-dir <checkout> it reads the files from a
local checkout of the repository at that commit instead of downloading them.
"""
import argparse, hashlib, json, sys, urllib.request
from pathlib import Path
HERE = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--from-dir", type=Path, default=None, help="local checkout of the repository at the pinned commit")
    ap.add_argument("--out", type=Path, default=HERE.parent / "data" / "semanteq_verif.jsonl")
    a = ap.parse_args()
    spec = json.loads((HERE / "second_formalizations.json").read_text(encoding="utf-8"))
    repo, commit, recipes = spec["repository"], spec["commit"], spec["candidates"]
    rows = [json.loads(l) for l in (HERE / "pairs.jsonl").read_text(encoding="utf-8").splitlines() if l.strip()]
    done = 0
    for r in rows:
        if r["candidate"] is not None: continue
        rec = recipes[r["id"]]
        if a.from_dir: src = (a.from_dir / rec["path"]).read_text(encoding="utf-8")
        else:
            url = f"https://raw.githubusercontent.com/{repo}/{commit}/{rec['path']}"
            with urllib.request.urlopen(url, timeout=60) as fh: src = fh.read().decode("utf-8")
        cand = "".join(src[o[1]:o[2]] if o[0] == "keep" else o[1] for o in rec["ops"])
        if hashlib.sha256(cand.encode("utf-8")).hexdigest() != rec["sha256"]:
            sys.exit(f"{r['id']}: the rebuilt candidate does not match its checksum; is {rec['path']} the file at commit {commit[:8]}?")
        r["candidate"] = cand; done += 1
    a.out.parent.mkdir(parents=True, exist_ok=True)
    with a.out.open("w", encoding="utf-8") as fh:
        for r in rows: fh.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"rebuilt {done} candidates from {repo}@{commit[:8]}; wrote {len(rows)} pairs to {a.out}")

if __name__ == "__main__":
    main()
