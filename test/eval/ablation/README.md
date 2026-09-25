# test/eval/ablation — the constructed half of the ablation set (Table 2, right half)

Fifty non-equivalent pairs, all of which SemantEq must REJECT, in four classes named after
the failure modes of Section 3 of the paper. Every pair is a single edit of a real statement
or a pairing of two library facts, and every added claim or partner statement is provable
from the library alone, so an unrestricted prover proves both directions and a rejection is
the work of the restriction and the audits, not of proving power.

| class (`manifest.jsonl`) | n | shape |
|---|---|---|
| `added_claim` | 18 | the candidate adds a claim the reference does not make (a conjunct, a hypothesis, a tighter bound, a stronger conclusion) |
| `neighbouring_theorem` | 14 | a different true theorem about the same objects, phrased to collide with the reference |
| `unrelated_true_fact` | 14 | a fact provable on its own: a decidable identity, a restatement of a library theorem, a decoy instance |
| `vacuous_hypotheses` | 4 | contradictory hypotheses, or two unrelated contradictions |

The other half of the ablation set is fifty ProofNetVerif test-split pairs labelled
non-equivalent after adjudication, every pair BEq+ accepts on that split among them; they are
listed by id (class `pnv`) with their per-arm verdicts in `../../results/ablation_verdicts.jsonl`,
and the ids name the rows of the public ProofNetVerif dataset (`pnv:test:<row>:<Book>|<exercise>`),
whose statements are not redistributed here. `suite.jsonl` is the driver input for this half;
`pairs/<id>/` holds the two statements as files.
