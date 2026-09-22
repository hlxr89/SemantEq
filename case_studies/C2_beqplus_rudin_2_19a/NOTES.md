# C2 — A textual usage check is loose (Appendix C, second pair)

ProofNetVerif test pair `pnv:test:0479`, human label non-equivalent,
accepted in both directions by BEq+ (released implementation in its own
environment, and our port on the current toolchain).

BEq+ accepted scripts:

    -- reference ⇒ candidate
    have this := base_theorem A B hA hB (Set.disjoint_iff_inter_eq_empty.mpr h)
    exact SeparatedNhds.disjoint this

    -- candidate ⇒ reference
    have this : Disjoint A B := by apply_rules [base_theorem]
    exact NormalSpace.normal A B hA hB this

On the right the antecedent is never used: `apply_rules` proves the `have`
from the goal's own hypothesis (it elaborates to `have this := hAB`) and the
library lemma `NormalSpace.normal` supplies the whole content, although
`base_theorem` appears in the script.

Reproduce with SemantEq-Eval (the pair must be rejected):

    lake exe semanteq case_studies/C2_beqplus_rudin_2_19a/ref.lean case_studies/C2_beqplus_rudin_2_19a/cand.lean
