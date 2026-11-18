# SemantEq public test suites

Self-contained, runnable evaluation data for the SemantEq evaluator and its
ProofChecker.

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
  after the failure modes of Section 2; see its README.

Each suite: `suite.jsonl` ({id, reference, candidate}), `manifest.jsonl`
(per-pair `expected` + provenance), `pairs/<id>/ref.lean|cand.lean` (raw
statements). Run + score everything:

    ./eval/run_eval.sh          # or: run_eval.sh recall|ablation

## Reproducing the paper's tables from scratch
- `reproduce.sh` — re-runs the programs stage by stage (corpus, suites,
  ablation, campaign, neg832, verif, pnv, tiers); `reproduce.sh tables` then
  prints the paper's Tables 1 to 3, 8 to 11, 15 and 17 to 19 from the fresh
  records via `reproduce_tables.py`, and `reproduce_tables.py released` prints
  them from the released records without running anything. `pnv_fetch.py`
  downloads ProofNetVerif and rebuilds its pair files under the ids used here.
  Runtimes and knobs are in the script header and in the top-level README.
  The suites and the reproduction run the evaluator with `--timeout 0`, as
  the paper's runs did.
- `results/` — the per-pair record behind the paper's tables (one line per
  pair and run). The reproduction reads it only for the BEq+ rows, whose
  port is not part of this repository.

## proofaudit/ — labeled implication-proof fixtures (SemantEq-ProofAudit)
The audit corpus: 14 statement pairs, 31 proof fixtures (faithful proofs the
checker must PASS; unfaithful/look-alike proofs it must FAIL, each built
around a named deception). `corpus.jsonl`, `manifest.jsonl` (per-fixture
expected verdict), `pairs/<dir>/ref.lean|cand.lean|<proof>.lean`. Six
directions of non-equivalent pairs are expected to PASS: they are the honest
direction of a one-directional pair (the `note` field of the manifest
explains each); their pairs stay non-equivalent because the other direction
fails. The Munkres 18.8b pair here is validation row 0402; the false
acceptance of the paper's Appendix G is a different pair with the same
exercise name, validation row 0006, which is not released. The expected verdicts hold in both modes (`STRICT=1` runs the
strict reading).

    ./proofaudit/run_proofaudit.sh
    STRICT=1 ./proofaudit/run_proofaudit.sh

## campaign/, campaign_neg832/ — model-written proofs on ProofNetVerif
`campaign/` holds the proofs for the 511 pairs of the certification set (the
471 test pairs that ProofNetVerif labels equivalent and the 40 recall pairs),
`campaign_neg832/` those for the other 832 test pairs, so the two cover the
full test split. Each has the statements, the proofs of both directions under
four prompt styles, and a manifest with the checker's verdict on every proof.
See their READMEs.

## semanteq_verif/ — the SemantEq-Verif benchmark
226 labelled pairs on IMO, Putnam and Erdős problems, with the model-written
proofs and the checker's verdicts. Thirty-eight candidates are rebuilt by
`semanteq_verif/fetch_second_formalizations.py`. See its README.
