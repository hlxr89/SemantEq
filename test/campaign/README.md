# Model-written proof campaign (SemantEq-ProofAudit at scale)

Every implication proof written by a frontier model for the 511 pairs of the
paper's campaign, in both directions and under four prompt styles, together
with the checker's verdict on each, and a runner that re-checks a style and
prints the paper's table.

**Provenance.** Proofs were written by OpenAI Codex CLI 0.151.0 with model
`gpt-5.6-sol` at reasoning effort `medium`, one session per pair, on
30 August 2026, against Lean v4.28.1 with Mathlib `1f9fffd5` (the current
release at the time). They were then checked by SemantEq-ProofAudit under this
repository's toolchain; a proof that no longer elaborates here is recorded as
`error`. The prompts are verbatim in `prompts/`.

## Layout

```
pairs/<pair>/ref.lean, cand.lean        the two statements (once per pair)
proofs/<style>/<pair>/ref_imp_cand.lean  the model's proof of ref ⇒ cand
proofs/<style>/<pair>/cand_imp_ref.lean  the model's proof of cand ⇒ ref
prompts/<style>.txt                      the four prompts (unrestricted, faithful, rewrite, expedient)
manifest.jsonl                           one row per pair: label, source, and per style and
                                         direction the checker's verdict and marks
run_campaign.sh                          re-check a style (or all) and print the scoring
```

Each proof file is a self-contained checker fixture: the assumed statement
proved by `sorry`, then the goal statement with the model's proof. A direction
the model declined is left with the goal as `sorry` and a `-- not proved`
comment (status `skipped`).

## Manifest

```json
{"pair": "pnv_test_0003_Rudin_exercise_5_5", "label": "equivalent",
 "source": "ProofNetVerif test split",
 "faithful": {"ref_imp_cand": {"status": "accepted", "library_true": false,
                               "ante_arg_warn": false, "severe": false},
              "cand_imp_ref": {"status": "accepted", "library_true": false,
                               "ante_arg_warn": true,  "severe": true}},
 ...}
```

- `label`: `equivalent` (410 pairs) or `non_equivalent` (101), after the
  adjudication described in the paper.
- `status`: `accepted` (checker PASS), `rejected` (FAIL), `skipped` (the model
  left the goal as `sorry`), `error` (does not elaborate on this toolchain).
- On an accepted direction: `library_true` (the goal's conclusion is provable
  from the library alone; recorded, never failed), `ante_arg_warn` (a library
  fact or an antecedent-free local fact met a hypothesis of the antecedent;
  tolerated), `severe` (that fact drew on no local hypothesis; the paper's
  strict reading counts these as failures).

## Running

```bash
./test/campaign/run_campaign.sh faithful     # one style, ~10–15 min, ~8 GB RAM
./test/campaign/run_campaign.sh              # all four styles
LIMIT=20 ./test/campaign/run_campaign.sh rewrite   # first 20 pairs, for a smoke test
```

The runner audits every proof of the style in one process, writes the raw
records to `results/<style>.jsonl`, and prints, per population, the number of
pairs certified in both directions, in one, and in neither, under the
tolerant reading (every PASS counts) and the strict reading (a PASS with a
severe mark counts as a failure), followed by how many directions agree with
the verdicts recorded in the manifest.

Expected, over all 511 pairs (the paper's Table 4 and Appendix Table 5):

| style | equivalent, tolerant | equivalent, strict | non-equivalent, tolerant | non-equivalent, strict |
|---|---|---|---|---|
| unrestricted | 322/52/36 | 317/57/36 | 0/58/43 | 0/51/50 |
| faithful     | 332/49/29 | 326/55/29 | 0/66/35 | 0/58/43 |
| rewrite      | 331/50/29 | 325/56/29 | 0/68/33 | 0/64/37 |
| expedient    | 309/41/60 | 305/45/60 | 0/48/53 | 0/45/56 |
