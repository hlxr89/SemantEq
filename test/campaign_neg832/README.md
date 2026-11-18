# Model-written proofs for the rest of the ProofNetVerif test split

The campaign of `../campaign/` covers the 471 test pairs that ProofNetVerif
labels equivalent. This folder adds the other 832 scored test pairs, which
ProofNetVerif labels not equivalent, so that the two together cover the full
test split of 1,303 pairs (the paper's Table 15, the bottom panel of Table 8,
and Table 9). Every pair here is non-equivalent under both label sets, so a
pair certified in both directions is a false acceptance.

**Provenance.** Proofs were written by OpenAI Codex CLI 0.162.1 with model
`gpt-5.6-sol` at reasoning effort `medium`, one new session per pair and
prompt style with a limit of 40 minutes, with web search disabled, on 14 and
15 November 2026, against Lean v4.28.1 with Mathlib `1f9fffd5`. The prompts
are the four of `../campaign/prompts/`, unchanged. The proofs were then
checked by SemantEq-ProofAudit v1.4.1 under this repository's toolchain. The
checker was fixed before any of these proofs was checked.

## Layout

```
pairs/<pair>/ref.lean, cand.lean         the two statements
proofs/<style>/<pair>/ref_imp_cand.lean  the model's proof of ref ⇒ cand
proofs/<style>/<pair>/cand_imp_ref.lean  the model's proof of cand ⇒ ref
manifest.jsonl                           one row per pair, as in ../campaign/
```

The manifest has the fields of `../campaign/manifest.jsonl` and one more per
direction, `compiled_when_written`: the proof compiled on the toolchain it
was written against and the model did not mark it as unproved. A file that
compiled then and does not elaborate here has status `error`.

## Running

```bash
SET=campaign_neg832 ./test/campaign/run_campaign.sh faithful   # one style
SET=campaign_neg832 ./test/campaign/run_campaign.sh            # all four styles
```

Expected, over the 832 pairs, as pairs certified in both directions, in one,
and in neither:

| style | tolerant | strict | both proofs compiled when written |
|---|---|---|---|
| unrestricted | 17/185/630 | 17/165/650 | 356 |
| faithful     | 33/260/539 | 20/230/582 | 185 |
| rewrite      | 35/253/544 | 22/224/586 | 163 |
| expedient    | 11/151/670 | 7/137/688  | 355 |

`python3 test/reproduce_tables.py released` prints the paper's tables for the
full test split from this manifest and the one of `../campaign/`.
