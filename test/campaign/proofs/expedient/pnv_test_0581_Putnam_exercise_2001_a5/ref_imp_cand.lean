import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2001_a5_assumed :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : ∃ (a n : ℕ), 0 < a ∧ 0 < n ∧ a ^ (n + 1) - (a + 1) ^ n = 2001 ∧ ∀ b m : ℕ, 0 < b → 0 < m → a ^ (n + 1) - (a + 1) ^ n = b ^ (m + 1) - (b + 1) ^ m → a = b ∧ n = m := by
  obtain ⟨p, hp, hu⟩ := exercise_2001_a5_assumed
  refine ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, ?_⟩
  intro b m hb hm heq
  have h := hu (b, m) ⟨hb, hm, heq.symm.trans hp.2.2⟩
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
