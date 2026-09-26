# F1 — no proof ex falso (Appendix F)

Two unrelated contradictions. Each side implies the other only by deriving
`False` from the antecedent and exploding it into the goal, which the ex falso
audit refuses; the pair is rejected in both directions. (A self-contradictory
statement paired with its own rearrangement is still accepted, since that proof
rearranges components and never derives `False`.)

Reproduce:

    lake exe semanteq case_studies/F1_ex_falso_pair/ref.lean case_studies/F1_ex_falso_pair/cand.lean

Expected: `Inconclusive` (neither direction accepted).
