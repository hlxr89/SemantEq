# D2 — a pair settled by two bridges (Appendix D)

USAMO 1996 Problem 1. `ref.lean` is the Compfiles reference; `cand.lean` is
the candidate printed in Appendix D, the same `Finset.range 90` sum with the
division by 90 moved inside the sum. Indexing the statements surfaces
`one_div_mul_eq_div` and `Finset.sum_div`, both equations; applied in
sequence they turn one statement into the other, and the trigonometric sum
is carried across unchanged.

`cand_compfiles_autoformalized.lean` is the blind autoformalized candidate
from the recall suite (`auto:Compfiles:Usa1996P1`). It sums over
`Finset.Icc 1 90` instead of `Finset.range 90`, so relating it to the
reference needs a reindexing of the sum in addition to the division lemmas,
which is beyond the static search (the campaign model proved it with
`Finset.sum_image` and a locally proved set identity, and the checker
certified both directions).

Reproduce:

    lake exe semanteq --depth 2 case_studies/D2_usamo_1996_p1_two_bridges/ref.lean case_studies/D2_usamo_1996_p1_two_bridges/cand.lean
    lake exe semanteq           case_studies/D2_usamo_1996_p1_two_bridges/ref.lean case_studies/D2_usamo_1996_p1_two_bridges/cand.lean
    lake exe semanteq --depth 2 case_studies/D2_usamo_1996_p1_two_bridges/ref.lean case_studies/D2_usamo_1996_p1_two_bridges/cand_compfiles_autoformalized.lean

Observed: the first gives `EquivalentRestricted`, both directions closed by
the two-step search with exactly the two lemmas; the second, at the default
depth one, gives `Inconclusive`; the third gives `Inconclusive` (the recall
miss described above).

Note on headers: the candidate imports all of Mathlib. With the reference's
own three-module header `Finset.sum_div` is not in scope and the chain cannot
be found, which is the relativity to the library that §5 discusses.
