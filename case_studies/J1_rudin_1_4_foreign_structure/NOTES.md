# J1 — instantiating the antecedent at a foreign structure (Appendix J)

The candidate is a theorem about an arbitrary linearly ordered set; the model
proves the reference (a partial order) from it by instantiating that set at
`Prop`, with the order's elements standing in for propositions. Nothing in the
goal speaks of `Prop`, so the instantiation check (the change-of-variables
clause) refuses the proof.

Source: campaign, faithful style, pair `pnv_test_0022_Rudin_exercise_1_4`,
direction candidate ⇒ reference.

Reproduce with SemantEq-ProofAudit (the proof must be rejected):

    lake exe semanteq --proof case_studies/J1_rudin_1_4_foreign_structure/cand_imp_ref.lean

Expected: `FAIL`, with the reasons naming the violated clause.
