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
  rcases dummy_assumed with ⟨a, n, ha, hn, hval, huniq⟩
  refine ⟨(a, n), ⟨ha, hn, hval⟩, ?_⟩
  rintro ⟨b, m⟩ ⟨hb, hm, hbval⟩
  have heq : a ^ (n + 1) - (a + 1) ^ n = b ^ (m + 1) - (b + 1) ^ m :=
    hval.trans hbval.symm
  rcases huniq b m hb hm heq with ⟨hab, hnm⟩
  exact Prod.ext hab.symm hnm.symm
