# SemantEq-Verif

A second benchmark in the format of ProofNetVerif, built from problems that
occur nowhere else in the paper: 226 pairs of a reference and a candidate
formalization on 122 problems, each with an informal statement and a label.
No equivalence tool was run on a pair before its label was final.

| Part | Problems | Pairs | Equivalent | Non-equivalent |
|---|---|---|---|---|
| IMO and Putnam | 40 | 141 | 70 | 71 |
| Erdős | 82 | 85 | 22 | 63 |
| Total | 122 | 226 | 92 | 134 |

## Files

```
pairs.jsonl                        the benchmark, one row per pair
second_formalizations.json         how to rebuild the 38 candidates that are not redistributed
fetch_second_formalizations.py     rebuilds them and writes the complete benchmark
proofs/<style>/<pair>/*.lean       the model-written proofs of both directions, four prompt styles
manifest.jsonl                     SemantEq-ProofAudit's verdict on every proof, as in ../campaign/
../results/semanteq_verif_verdicts.jsonl   SemantEq-Eval and BEq+ on every pair
```

A row of `pairs.jsonl`:

| Field | Meaning |
|---|---|
| `id` | Pair id, `<problem>-<k>` |
| `part` | `IMO`, `Putnam` or `Erdős` |
| `candidate_from` | Where the candidate comes from (below) |
| `nl_statement` | The informal statement |
| `reference` | The reference as one complete Lean file with one theorem whose proof is `sorry` |
| `candidate` | The candidate in the same form, or `null` for the 38 rows below |
| `correct` | The label: `true` when the candidate is faithful to the informal statement |

Every Lean file is for Lean `v4.30.0-rc1` with Mathlib `0c154d67`. The file
is an input of SemantEq-Eval as it is, which reads `id`, `reference` and
`candidate`.

## Construction

**IMO and Putnam.** The references are the official statements of
[Compfiles](https://github.com/dwrensha/compfiles) for 20 IMO problems and of
[PutnamBench](https://github.com/trishullab/PutnamBench) for 20 Putnam
problems, drawn with a fixed seed. Qwen3.5-9B wrote the candidates from the
informal statement alone, without the reference. A small model was chosen on
purpose, so that many candidates are wrong in natural ways, and at most four
distinct candidates per problem are kept. For a problem that asks to find
something, the official answer is part of the informal statement and of the
reference.

**Erdős.** The reference is the statement of the problem in the
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project at commit `f50ff7be`. The candidate is an earlier statement of the
same problem in that project, from before a commit that corrected it (47
pairs), or the formalization of the same problem in the public collection
[plby/lean-proofs](https://github.com/plby/lean-proofs) at commit `8822f7dd`
(38 pairs).

**Labels.** As in ProofNetVerif, a label says whether the candidate is
faithful to the informal statement, and it is not set by comparing the
candidate with the reference. A pair labelled equivalent therefore holds two
valid formalizations of the same informal statement, which a tool may or may
not certify as equivalent. Language models proposed the labels in independent
readings, and an author read and verified every label. Ten pairs whose label
could not be decided, or whose reference changes the claim of the text, were
left out. The IMO and Putnam pairs on which the model screen was unsure were
selected first, so that part is enriched for hard cases. Seven of the 63
non-equivalent Erdős labels rest on a strict reading of the rule, because the
candidate differs from the text only in a degenerate case or a redundant
condition.

**Sources and licences.** Compfiles, PutnamBench (its Lean 4 statements) and
Formal Conjectures are released under Apache 2.0. Each reference names its
source file and commit in a header comment and lists what was changed to make
it a standalone file.

## The 38 candidates that are not redistributed

plby/lean-proofs carries no licence, so the 38 candidates taken from it are
not in this repository, and neither are the model's proofs for those pairs,
which restate the candidate. One command rebuilds them:

```bash
python3 test/semanteq_verif/fetch_second_formalizations.py
```

It downloads the 38 source files at the pinned commit, cuts each one down to
the candidate used in the paper, checks the result against its SHA-256, and
writes all 226 rows to `test/data/semanteq_verif.jsonl`. It needs only the
Python standard library. The verdicts on these 38 pairs are in the manifest
and in the results file like all others, marked `proofs_released: false` in
the manifest.

## Results

`python3 test/reproduce_tables.py released` prints the paper's tables for this
benchmark (the second section of Table 1, the bottom panel of Table 3, and
Tables 17 to 19) from the released records. Over all 226 pairs, as pairs
certified in both directions, in one, and in neither:

| | Equivalent | Non-equivalent | Precision | Recall |
|---|---|---|---|---|
| BEq+ | 21 | 0 | 100.0 | 22.8 |
| SemantEq-Eval | 23 / 6 / 63 | 0 / 18 / 116 | 100.0 | 25.0 |
| SemantEq-ProofAudit, expedient | 50 / 21 / 21 | 4 / 27 / 103 | 92.6 | 54.3 |
| SemantEq-ProofAudit, unrestricted | 44 / 18 / 30 | 5 / 34 / 95 | 89.8 | 47.8 |
| SemantEq-ProofAudit, faithful | 48 / 21 / 23 | 8 / 29 / 97 | 85.7 | 52.2 |
| SemantEq-ProofAudit, rewrite | 52 / 22 / 18 | 4 / 34 / 96 | 92.9 | 56.5 |

BEq+ does not attempt the second direction when the first fails, so its row
gives only acceptances. Its numbers come from our port to this toolchain,
which is not part of this repository.

**SemantEq-Eval** ran with the settings of the paper's Table 1: the default
search with no time limit. The runner set seven pairs aside after 15 minutes
without progress (verdict `Stalled`), and they count as not accepted.

**The proofs** were written by the prover of the paper's Section 4, OpenAI
Codex with model `gpt-5.6-sol`, under the four prompts of
`../campaign/prompts/`, in one session per pair and prompt style with a limit
of 40 minutes, in November 2026. They were checked by SemantEq-ProofAudit
v1.4.1 under this repository's toolchain.

## Running

```bash
test/reproduce.sh verif                                        # SemantEq-Eval and the checker, then: test/reproduce.sh tables
SET=semanteq_verif ./test/campaign/run_campaign.sh rewrite     # the checker on one prompt style
```
