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
 "faithful": {"ref_imp_cand": {"status": "accepted",
                               "ante_arg_warn": false, "severe": false},
              "cand_imp_ref": {"status": "accepted",
                               "ante_arg_warn": true,  "severe": true}},
 ...}
```

- `label`: `equivalent` (407 pairs) or `non_equivalent` (104), after the
  adjudication described in the paper.
- `status`: `accepted` (checker PASS), `rejected` (FAIL), `skipped` (the model
  left the goal as `sorry`), `error` (does not elaborate on this toolchain).
- On an accepted direction: `ante_arg_warn` (a library fact or an
  antecedent-free local fact met a hypothesis of the antecedent; tolerated),
  `severe` (that fact drew on no local hypothesis). The paper's strict
  reading is the checker's `--strict` mode: every severe use fails, and the
  proofs of local lemmas admitted on the shape of their statement are read as
  well, so a severe use inside such a proof fails too. Re-scoring the default
  records with `severe` as a failure reproduces the strict columns below up to
  the three equivalent-pair rows where a severe use sits inside such a proof
  (unrestricted 317/58/32, faithful 323/57/27, expedient 304/45/58 from the
  records; 317/56/34, 323/56/28, 303/45/59 from the mode).

## Running

```bash
./test/campaign/run_campaign.sh faithful     # one style, ~10–15 min, ~8 GB RAM
./test/campaign/run_campaign.sh              # all four styles
LIMIT=20 ./test/campaign/run_campaign.sh rewrite   # first 20 pairs, for a smoke test
STRICT=1 ./test/campaign/run_campaign.sh faithful  # the strict reading as a mode (--strict)
```

The runner audits every proof of the style in one process, writes the raw
records to `results/<style>.jsonl`, and prints, per population, the number of
pairs certified in both directions, in one, and in neither, under the
tolerant reading (every PASS counts) and the strict reading (a PASS with a
severe mark counts as a failure), followed by how many directions agree with
the verdicts recorded in the manifest. Under `STRICT=1` the checker runs in
`--strict` mode, the records go to `results/<style>.strict.jsonl`, and the two
readings coincide because a severe use is already a failure; the agreement
line then compares against the manifest's default-mode verdicts, so the
directions the strict mode fails show up as disagreements.

Expected, over all 511 pairs (the paper's Table 4 and Appendix Table 5):

| style | equivalent, tolerant | equivalent, strict | non-equivalent, tolerant | non-equivalent, strict |
|---|---|---|---|---|
| unrestricted | 322/53/32 | 317/56/34 | 0/57/47 | 0/50/54 |
| faithful     | 330/50/27 | 323/56/28 | 0/67/37 | 0/59/45 |
| rewrite      | 329/51/27 | 323/57/27 | 0/70/34 | 0/64/40 |
| expedient    | 309/40/58 | 303/45/59 | 0/49/55 | 0/46/58 |
