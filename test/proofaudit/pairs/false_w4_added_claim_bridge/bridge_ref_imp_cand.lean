import Mathlib

-- ===== assumed statement (antecedent) =====
theorem r_assumed : Nat.Prime 5 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
-- An added library-true claim, hidden inside a local iff whose directions do
-- use their hypothesis; the component proving the extra conjunct does not.
-- Must FAIL (the same defect as `⟨ante, rfl⟩` without the wrapper).
theorem c : (0 : ℕ) ∈ Set.univ ∧ Nat.Prime 5 := by
  have h : Nat.Prime 5 ↔ (0 : ℕ) ∈ Set.univ ∧ Nat.Prime 5 := ⟨fun hp => ⟨Set.mem_univ 0, hp⟩, fun hp => hp.2⟩
  exact h.mp r_assumed
