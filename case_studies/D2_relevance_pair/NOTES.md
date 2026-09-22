# D2 — relevance (Appendix D)

`Irrational (Real.sqrt 2)` against `Irrational (Real.sqrt 2) ∧ (2 + 2 = 4)`.
The candidate's second conjunct is provable by reflexivity without the
antecedent, so the relevance audit refuses the direction reference ⇒ candidate
before any search. The other direction (drop a conjunct) is an honest
structural weakening, so the verdict is one-directional.

Source: pollution suite, pair `pol:and_arith`.

Reproduce:

    lake exe semanteq case_studies/D2_relevance_pair/ref.lean case_studies/D2_relevance_pair/cand.lean

Expected: `LikelyTooStrong` (only candidate ⇒ reference closes).
