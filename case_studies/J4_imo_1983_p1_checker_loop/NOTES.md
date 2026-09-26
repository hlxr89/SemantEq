# J4 — the checker in the loop overturns a label (Appendix J)

IMO 1983 Problem 1, a candidate autoformalized blind from the natural-language
statement; it entered the recall suite labelled equivalent (a hand-written proof
shows logical equivalence). The checker in the loop showed the label wrong and
the pair is now non-equivalent (2026-09-24). The reference carries positivity in the type `ℝ+`; the
candidate works over `ℝ` and restores positivity as a conjunct on the
condition side of its biconditional. Every campaign style is rejected in both
directions.

- `ref_imp_cand_loop_final.lean`: the proof after four rounds of revision
  driven only by the checker's reasons. Every fault about the proof itself is
  gone and one residual remains: the positivity conjunct is provable without
  the antecedent, because the reference asserts nothing about positivity. The
  rejection is about the pair. (The revisions in this experiment were written
  by an assistant language model, not by the campaign model.)
- `hypvariant_*.lean`: the candidate with positivity moved into a hypothesis
  and nothing else changed. Both directions pass under the checker's
  tolerance, and each carries one use that the strict reading marks severe:
  reference ⇒ candidate meets a hypothesis of the antecedent with the closed
  fact `zero_le_one` (while building the subtype element), and candidate ⇒
  reference feeds it a local positivity fact proved without any local
  hypothesis. This is the residue of a change of domain, positivity carried
  in a type on one side and stated on the other, which the library states
  one way only.

Reproduce:

    lake exe semanteq --proof case_studies/J4_imo_1983_p1_checker_loop/ref_imp_cand_loop_final.lean
    lake exe semanteq --proof case_studies/J4_imo_1983_p1_checker_loop/hypvariant_ref_imp_cand.lean case_studies/J4_imo_1983_p1_checker_loop/hypvariant_cand_imp_ref.lean
    lake exe semanteq case_studies/J4_imo_1983_p1_checker_loop/ref.lean case_studies/J4_imo_1983_p1_checker_loop/cand.lean

Observed: loop final `FAIL` with `goal part closes ante-free`; both
hypothesis-variant directions `PASS`, each with one `severe:` warning (see
above; every recorded flag is visible under `--raw`); the evaluator does not
decide the original pair.
