# D1 — a pair settled by rearrangement alone (Appendix D)

Munkres 29.10. The candidate keeps the reference's context and permutes the
conjuncts of the conclusion. No library lemma is needed: both directions close
by logical rearrangement (the structural closer), the chain of Definition 1
being a single rearrangement step each way.

Source: recall suite, pair `equiv:ProofNetSharp:exercise_29_10`.

Reproduce:

    lake exe semanteq case_studies/D1_munkres_29_10_rearrangement/ref.lean case_studies/D1_munkres_29_10_rearrangement/cand.lean

Expected: `EquivalentRestricted`, both directions closed by
`structural solve_by_elim [...]`.
