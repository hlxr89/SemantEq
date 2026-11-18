import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (R : Type*) [CommRing R] [IsDomain R] (h : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d r s, d ∣ a ∧ d ∣ b ∧ d = r * a + s * b) (h2 : ∀ (a₁ a₂ a₃ : R), a₁ ≠ 0 → a₂ ≠ 0 → a₃ ≠ 0 → (∃ N : ℕ, ∀ n : ℕ, n ≥ N → a₁ * a₂ ^ n * a₃ ^ n = 1)) : IsPrincipalIdealRing R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  have hwf : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨by
    rintro ⟨f, hf⟩
    let a : ℕ → R := fun n ↦ f (n + 1)
    obtain ⟨N, hN⟩ := h2 a (fun i ↦ ⟨(hf i).1, (dvd_and_not_dvd_iff.mpr (hf (i + 1))).1⟩)
    obtain ⟨u, hu, heq⟩ := hN (N + 1) (Nat.le_succ N)
    exact (dvd_and_not_dvd_iff.mpr (hf (N + 1))).2 ⟨u, by simpa [a, mul_comm] using heq⟩
  ⟩⟩
  letI : WfDvdMonoid R := hwf
  have hbez : IsBezout R := IsBezout.iff_span_pair_isPrincipal.mpr (by
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simpa using (inferInstance : (Ideal.span ({y} : Set R)).IsPrincipal)
    rcases eq_or_ne y 0 with rfl | hy
    · rw [show ({x, 0} : Set R) = insert 0 {x} by ext; simp [or_comm], Ideal.span_insert_zero]
      infer_instance
    obtain ⟨r, s, hrs⟩ := h1 x y hx hy
    refine ⟨⟨gcd x y, ?_⟩⟩
    apply le_antisymm
    · apply Ideal.span_le.2
      rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.mem_span_singleton.mpr (gcd_dvd_left x y),
        Ideal.mem_span_singleton.mpr (gcd_dvd_right x y)⟩
    · apply Ideal.span_le.2
      rw [Set.singleton_subset_iff]
      rw [hrs]
      exact add_mem (mul_mem_left _ r (subset_span (Set.mem_insert x {y})))
        (mul_mem_left _ s (subset_span (Set.mem_insert_of_mem x (Set.mem_singleton y)))) )
  letI : IsBezout R := hbez
  exact ((IsBezout.TFAE (R := R)).out 3 1).mp hwf
