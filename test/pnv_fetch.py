#!/usr/bin/env python3
"""Fetch ProofNetVerif (Hugging Face: PAug/ProofNetVerif) and write the pair files
the from-scratch reproduction needs, in the id scheme used throughout this repository
(`pnv:<split>:<row>:<Book>|<exercise>`).

    python3 test/pnv_fetch.py                 # test split -> test/data/pnv_test.jsonl (+ labels)
    python3 test/pnv_fetch.py --split valid   # the validation split as well
    python3 test/pnv_fetch.py --limit 20      # first 20 rows only (smoke test)

Also derived from the test split, when present:
    test/data/ablation_pnv.jsonl     the 50 ProofNetVerif pairs of the ablation set (ids from test/results)
    test/data/equivalent_set.jsonl   the 407 pairs of the equivalent set: 369 test pairs + the 38 recall pairs

Requires the `datasets` package (pip install datasets). Downloads are cached by Hugging Face
under $HF_HOME (default ~/.cache/huggingface).
"""
import argparse, json, os, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
DATASET = "PAug/ProofNetVerif"

def complete_source(header: str, decls: str) -> str:
    header = header.rstrip("\n"); decls = decls.rstrip()
    if decls.endswith(":="): decls += " sorry"
    elif not decls.endswith("sorry"): decls += " := sorry"
    return f"{header}\n\n{decls}\n"

def jl(p):
    with open(p) as fh:
        for l in fh:
            l = l.strip()
            if l: yield json.loads(l)

def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--split", default="test", choices=("test", "valid"))
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--outdir", type=Path, default=HERE / "data")
    a = ap.parse_args()
    from datasets import load_dataset
    ds = load_dataset(DATASET, split=a.split)
    rows = list(enumerate(ds))
    if a.limit: rows = rows[: a.limit]
    a.outdir.mkdir(parents=True, exist_ok=True)
    pairs = a.outdir / f"pnv_{a.split}.jsonl"; labels = a.outdir / f"pnv_{a.split}_labels.jsonl"
    by_id = {}
    with pairs.open("w") as fp, labels.open("w") as fl:
        for idx, r in rows:
            pid = f"pnv:{a.split}:{idx:04d}:{r['id']}"
            pair = {"id": pid, "reference": complete_source(r["lean4_src_header"], r["lean4_formalization"]),
                    "candidate": complete_source(r["lean4_src_header"], r["lean4_prediction"])}
            by_id[pid] = pair
            fp.write(json.dumps(pair, ensure_ascii=False) + "\n")
            fl.write(json.dumps({"id": pid, "correct": bool(r["correct"]), "row": idx}, ensure_ascii=False) + "\n")
    print(f"wrote {len(rows)} pairs to {pairs} and labels to {labels}", file=sys.stderr)
    if a.split != "test" or a.limit: return
    # the ProofNetVerif half of the ablation set
    abl = [r["id"] for r in jl(HERE / "results" / "ablation_verdicts.jsonl") if r["class"] == "pnv"]
    with (a.outdir / "ablation_pnv.jsonl").open("w") as f:
        n = 0
        for i in abl:
            if i in by_id: f.write(json.dumps(by_id[i], ensure_ascii=False) + "\n"); n += 1
    print(f"wrote {n} of {len(abl)} ablation-set ProofNetVerif pairs", file=sys.stderr)
    # the equivalent set: the 369 adjudicated-equivalent test pairs + the recall suite's 38 equivalent pairs
    cap = [r["id"] for r in jl(HERE / "results" / "capability_verdicts.jsonl")]
    rec = {r["id"]: r for r in jl(HERE / "eval" / "recall" / "suite.jsonl")}
    with (a.outdir / "equivalent_set.jsonl").open("w") as f:
        n = 0
        for i in cap:
            src = by_id.get(i) or rec.get(i)
            if src: f.write(json.dumps({"id": i, "reference": src["reference"], "candidate": src["candidate"]}, ensure_ascii=False) + "\n"); n += 1
    print(f"wrote {n} of {len(cap)} equivalent-set pairs", file=sys.stderr)

if __name__ == "__main__":
    main()
