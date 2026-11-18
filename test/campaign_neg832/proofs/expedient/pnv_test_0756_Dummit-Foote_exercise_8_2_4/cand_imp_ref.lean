import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (H : IsDomain R) (H1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d x y, d ∣ a ∧ d ∣ b ∧ x * a + y * b = d) (H2 : ∀ a : R, a ≠ 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsUnit (a * a^n)) : IsPrincipalIdealRing R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  letI : IsBezout R := IsBezout.iff_span_pair_isPrincipal.mpr fun a b => by
    use gcd a b
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact Ideal.mem_span_singleton.mpr (gcd_dvd_left a b)
      · rw [hx]
        exact Ideal.mem_span_singleton.mpr (gcd_dvd_right a b)
    · apply Ideal.span_le.mpr
      intro x hx
      change x = gcd a b at hx
      subst x
      rcases eq_or_ne a 0 with rfl | ha
      · obtain ⟨u, hu⟩ := (gcd_zero_left' b).symm
        exact Ideal.mem_span_pair.mpr ⟨0, u, by simpa [mul_comm] using hu⟩
      rcases eq_or_ne b 0 with rfl | hb
      · obtain ⟨u, hu⟩ := (gcd_zero_right' a).symm
        exact Ideal.mem_span_pair.mpr ⟨u, 0, by simpa [mul_comm] using hu⟩
      obtain ⟨r, s, hrs⟩ := h1 a b ha hb
      exact Ideal.mem_span_pair.mpr ⟨r, s, hrs.symm⟩
  letI : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun f => by
    let a : ℕ → R := fun n => f.1 (n + 1)
    have ha : ∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i := fun i => by
      constructor
      · exact (f.2 i).1
      · obtain ⟨_, x, _, hx⟩ := f.2 (i + 1)
        exact ⟨x, hx⟩
    obtain ⟨N, hN⟩ := h2 a ha
    obtain ⟨u, hu, heq⟩ := hN (N + 1) (Nat.le_succ N)
    apply (f.2 (N + 1)).not_associated
    obtain ⟨v, rfl⟩ := hu
    symm
    exact ⟨v, by simpa [a, mul_comm] using heq.symm⟩⟩⟩
  exact ((IsBezout.TFAE (R := R)).out 3 1).mp (inferInstance : WfDvdMonoid R)
