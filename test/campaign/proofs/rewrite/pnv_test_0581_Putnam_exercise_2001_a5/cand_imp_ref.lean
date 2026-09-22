import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ (a n : ℕ), 0 < a ∧ 0 < n ∧ a ^ (n + 1) - (a + 1) ^ n = 2001 ∧ ∀ b m : ℕ, 0 < b → 0 < m → a ^ (n + 1) - (a + 1) ^ n = b ^ (m + 1) - (b + 1) ^ m → a = b ∧ n = m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  obtain ⟨a, n, ha, hn, hvalue, h_unique⟩ := dummy_assumed
  refine ⟨(a, n), ⟨ha, hn, hvalue⟩, ?_⟩
  intro p hp
  obtain ⟨b, m⟩ := p
  obtain ⟨hab, hnm⟩ := h_unique b m hp.1 hp.2.1 (hvalue.trans hp.2.2.symm)
  exact Prod.ext hab.symm hnm.symm
