import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos204

-- ===== assumed statement (antecedent) =====
theorem erdos_204_assumed :
    ¬ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] ∧ x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_204_goal :
    ¬ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, ∀ x : ℤ, x ≡ a d [ZMOD d] → x ≡ a d' [ZMOD d'] → Nat.gcd d d' = 1) := by
  rintro ⟨n, a, hcover, hcompat⟩
  apply erdos_204_assumed
  refine ⟨n, a, hcover, ?_⟩
  intro d hd d' hd' _ hcommon
  obtain ⟨x, hxd, hxd'⟩ := hcommon
  exact hcompat d hd d' hd' x hxd hxd'

end Erdos204
