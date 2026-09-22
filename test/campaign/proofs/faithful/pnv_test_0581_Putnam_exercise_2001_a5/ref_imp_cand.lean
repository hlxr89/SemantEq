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
  rcases exercise_2001_a5_assumed with ⟨⟨a, n⟩, hval, huniq⟩
  refine ⟨a, n, hval.1, hval.2.1, hval.2.2, ?_⟩
  intro b m hb hm heq
  have hbm : b ^ (m + 1) - (b + 1) ^ m = 2001 := heq ▸ hval.2.2
  have hp : (b, m).1 > 0 ∧ (b, m).2 > 0 ∧
      (b, m).1 ^ ((b, m).2 + 1) - ((b, m).1 + 1) ^ (b, m).2 = 2001 :=
    ⟨hb, hm, hbm⟩
  have hpair : (b, m) = (a, n) := huniq (b, m) hp
  exact ⟨congrArg Prod.fst hpair |>.symm, congrArg Prod.snd hpair |>.symm⟩
