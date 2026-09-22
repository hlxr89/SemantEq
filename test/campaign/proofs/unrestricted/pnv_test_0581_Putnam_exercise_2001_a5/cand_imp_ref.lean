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
  obtain ⟨a, n, ha, hn, heq, hunique⟩ := dummy_assumed
  refine ⟨(a, n), ⟨ha, hn, heq⟩, ?_⟩
  rintro ⟨b, m⟩ ⟨hb, hm, hbm⟩
  obtain ⟨hab, hnm⟩ := hunique b m hb hm (heq.trans hbm.symm)
  simp [hab, hnm]
