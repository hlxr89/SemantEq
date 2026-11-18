import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set (ℤ × ℤ × ℤ) := {(2, 4, 8), (3, 5, 15)}

-- ===== assumed statement (antecedent) =====
theorem imo1992_p1_assumed (a b c : ℤ) (ha : 1 < a) (hb : a < b) (hc : b < c) :
    ⟨a, b, c⟩ ∈ solution_set ↔
    (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
  ∀ a b c : ℤ, (1 < a ∧ a < b ∧ b < c ∧ (a - 1) * (b - 1) * (c - 1) ∣ a * b * c - 1) ↔
  ((a = 2 ∧ b = 4 ∧ c = 8) ∨ (a = 3 ∧ b = 5 ∧ c = 15)) := by
  intro a b c
  constructor
  · rintro ⟨ha, hb, hc, hdiv⟩
    have hmem : ⟨a, b, c⟩ ∈ solution_set :=
      (imo1992_p1_assumed a b c ha hb hc).mpr hdiv
    simpa only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] using hmem
  · intro heq
    have hmem : ⟨a, b, c⟩ ∈ solution_set := by
      simpa only [solution_set, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq] using heq
    rcases heq with hfirst | hsecond
    · rcases hfirst with ⟨rfl, rfl, rfl⟩
      have ha : (1 : ℤ) < 2 := by norm_num -- non-rewrite step
      have hb : (2 : ℤ) < 4 := by norm_num -- non-rewrite step
      have hc : (4 : ℤ) < 8 := by norm_num -- non-rewrite step
      exact ⟨ha, hb, hc, (imo1992_p1_assumed 2 4 8 ha hb hc).mp hmem⟩
    · rcases hsecond with ⟨rfl, rfl, rfl⟩
      have ha : (1 : ℤ) < 3 := by norm_num -- non-rewrite step
      have hb : (3 : ℤ) < 5 := by norm_num -- non-rewrite step
      have hc : (5 : ℤ) < 15 := by norm_num -- non-rewrite step
      exact ⟨ha, hb, hc, (imo1992_p1_assumed 3 5 15 ha hb hc).mp hmem⟩
