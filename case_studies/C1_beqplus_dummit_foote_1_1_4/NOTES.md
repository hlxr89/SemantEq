# C1 — Closing tactics prove the goal without the antecedent (Appendix C, first pair)

ProofNetVerif test pair `pnv:test:0836`, human label non-equivalent,
accepted in both directions by BEq+ (released implementation in its own
environment, and our port on the current toolchain).

BEq+ accepted scripts (from its released implementation; reproduced by our port):

    -- reference ⇒ candidate
    convert base_theorem using 0
    simp_all_arith!
    exact fun n a b c => base_theorem n a b c

    -- candidate ⇒ reference
    convert base_theorem using 0
    simp_all_arith!
    noncomm_ring

The candidate is a `%`-arithmetic identity over `Nat`, an instance of
`Nat.mul_mod`; re-running the accepted scripts with the antecedent replaced by
`2 + 2 = 4` still accepts both directions.

Reproduce with SemantEq-Eval (the pair must be rejected):

    lake exe semanteq case_studies/C1_beqplus_dummit_foote_1_1_4/ref.lean case_studies/C1_beqplus_dummit_foote_1_1_4/cand.lean
