# SemantEq public test suites

Self-contained, runnable evaluation data for the SemantEq evaluator and its
ProofChecker. Everything here is a copy — the canonical development data lives
outside this directory.

## eval/ — statement-pair suites for the evaluator
- `recall/` — 40 pairs of curated transformations and blind
  autoformalizations; 38 are equivalent (`expected: equivalent`), each with a
  hand-proved equivalence witness backing its label, and 2 were ruled
  non-equivalent on review (`expected: not_equivalent`). The default search
  accepts 24 of the 38 (the others are the recall misses of the paper's
  capability study) and rejects the 2; `default_search_accepts` records that
  verdict per pair and is what the runner scores against.
- `ablation/` — the 50 constructed pairs of the paper's ablation set (Table 2,
  right half), all non-equivalent (must be REJECTED), in four classes named
  after the failure modes of Section 3; see its README.

Each suite: `suite.jsonl` ({id, reference, candidate}), `manifest.jsonl`
(per-pair `expected` + provenance), `pairs/<id>/ref.lean|cand.lean` (raw
statements). Run + score everything:

    ./eval/run_eval.sh          # or: run_eval.sh recall|ablation

## Reproducing the paper's tables from scratch
- `reproduce.sh` — re-runs the programs stage by stage (corpus, suites,
  ablation, campaign, pnv, tiers); `reproduce.sh tables` then prints Tables 1
  to 5 from the fresh records via `reproduce_tables.py`. `pnv_fetch.py`
  downloads ProofNetVerif and rebuilds its pair files under the ids used here.
  Runtimes and knobs are in the script header and in the top-level README.
- `results/` — the per-pair record behind the paper's tables (one line per
  pair and run). The reproduction reads it only for the BEq+ rows, whose
  port is not part of this repository.

## proofaudit/ — labeled implication-proof fixtures (SemantEq-ProofAudit)
The audit corpus: 12 statement pairs, 25 proof fixtures (faithful proofs the
checker must PASS; unfaithful/look-alike proofs it must FAIL, each built
around a named deception). `corpus.jsonl`, `manifest.jsonl` (per-fixture
expected verdict), `pairs/<dir>/ref.lean|cand.lean|<proof>.lean`. Four
directions of non-equivalent pairs are expected to PASS: they are the honest
direction of a one-directional pair (the `note` field of the manifest
explains each); their pairs stay non-equivalent because the other direction
fails.

    ./proofaudit/run_proofaudit.sh
