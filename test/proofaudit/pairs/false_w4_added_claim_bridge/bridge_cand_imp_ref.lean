import Mathlib

-- ===== assumed statement (antecedent) =====
theorem c_assumed : (0 : ℕ) ∈ Set.univ ∧ Nat.Prime 5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
-- The honest direction: dropping the extra conjunct through the same local
-- iff. PASSES; the pair stays non-equivalent because the other direction fails.
theorem r : Nat.Prime 5 := by
  have h : (0 : ℕ) ∈ Set.univ ∧ Nat.Prime 5 ↔ Nat.Prime 5 := ⟨fun hp => hp.2, fun hp => ⟨Set.mem_univ 0, hp⟩⟩
  exact h.mp c_assumed
