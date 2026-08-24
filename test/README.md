# StaticEval public test suites

Self-contained, runnable evaluation data for the StaticEval evaluator and its
ProofChecker. Everything here is a copy — the canonical development data lives
outside this directory.

## eval/ — statement-pair suites for the evaluator
- `recall/` — 40 equivalent-pair alternates (all must be ACCEPTED); curated
  transformations + blind autoformalizations, each with a hand-proved
  equivalence witness backing its label.
- `pollution/` — 35 pairs: 29 "true statement + junk" laundering attacks (must
  be REJECTED) + 6 `ctl:*` faithful twins (must be ACCEPTED — the
  over-rejection meter).
- `traps/` — 29 adversarial pairs, both sides independently provable but not
  equivalent (must be REJECTED).

Each suite: `suite.jsonl` ({id, reference, candidate}), `manifest.jsonl`
(per-pair `expected` + provenance), `pairs/<id>/ref.lean|cand.lean` (raw
statements). Run + score everything:

    ./eval/run_eval.sh          # or: run_eval.sh recall|pollution|traps

## proofchecker/ — labeled implication-proof fixtures
The AuditCorpus: 10 statement pairs, 19 proof fixtures (faithful proofs the
checker must PASS; unfaithful/look-alike proofs it must FAIL, each built
around a named deception). `corpus.jsonl`, `manifest.jsonl` (per-fixture
expected verdict), `pairs/<dir>/ref.lean|cand.lean|<proof>.lean`.

    ./proofchecker/run_proofchecker.sh
