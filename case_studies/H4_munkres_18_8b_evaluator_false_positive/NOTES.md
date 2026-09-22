# H4 — the one pair SemantEq-Eval accepts wrongly (Appendix H)

Munkres 18.8b, ProofNetVerif validation pair 0006. The candidate adds
`[Preorder X]` on the domain, which the conclusion never uses. The direction
from the reference is honest; in the direction from the candidate the search
fills the missing preorder by itself with `specializationPreorder X`, the
order every topological space induces on its own points, which is a structure
the goal does not carry. The checker refuses the same term at its
instantiation check; the evaluator's search has no check at that point.

`semanteq_record.json` is the evaluator's recorded output for the pair
(verdict `EquivalentRestricted`, both proof terms, used constants).

Reproduce:

    lake exe semanteq case_studies/H4_munkres_18_8b_evaluator_false_positive/ref.lean case_studies/H4_munkres_18_8b_evaluator_false_positive/cand.lean

Expected: `EquivalentRestricted` (the false positive), with
`specializationPreorder` among the constants of the candidate ⇒ reference term.
