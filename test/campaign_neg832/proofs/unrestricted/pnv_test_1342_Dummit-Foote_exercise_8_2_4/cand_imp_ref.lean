import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (R : Type*) [CommRing R] [IsDomain R] (h1 : ∀ (a b : R) (ha : a ≠ 0) (hb : b ≠ 0), ∃ (d : R) (r s : R), d ∣ a ∧ d ∣ b ∧ d = r * a + s * b) (h2 : ∀ (a : ℕ → R) (h : ∀ i, a (i + 1) ∣ a i) (n : ℕ), ∃ N, ∀ m ≥ N, IsUnit (a m) ↔ IsUnit (a n)) : IsPrincipalIdealRing R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  have hbezout : IsBezout R := IsBezout.iff_span_pair_isPrincipal.mpr (by
    intro x y
    by_cases hx : x = 0
    · subst x
      simpa using (inferInstance : (Ideal.span ({y} : Set R)).IsPrincipal)
    by_cases hy : y = 0
    · subst y
      refine ⟨⟨x, ?_⟩⟩
      simp
    obtain ⟨r, s, hrs⟩ := h1 x y hx hy
    refine ⟨⟨gcd x y, ?_⟩⟩
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      have hz' : z = x ∨ z = y := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
      have hxg := GCDMonoid.gcd_dvd_left x y
      have hyg := GCDMonoid.gcd_dvd_right x y
      rcases hz' with hz' | hz'
      · subst z
        exact Ideal.mem_span_singleton.mpr hxg
      · subst z
        exact Ideal.mem_span_singleton.mpr hyg
    · apply Ideal.span_le.mpr
      intro z hz
      have hz' : z = gcd x y := by simpa only [Set.mem_singleton_iff] using hz
      subst z
      rw [hrs]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
  letI : IsBezout R := hbezout
  have hwf : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨by
    rintro ⟨f, hf⟩
    let a : ℕ → R := fun n ↦ f (n + 1)
    have ha : ∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i := by
      intro i
      constructor
      · exact (hf i).1
      · obtain ⟨_, c, _, hc⟩ := hf (i + 1)
        exact ⟨c, by simpa [a, Nat.add_assoc] using hc⟩
    obtain ⟨N, hN⟩ := h2 a ha
    obtain ⟨u, hu, heu⟩ := hN (N + 1) (by omega)
    have hassoc : Associated (a (N + 1)) (a N) := by
      obtain ⟨v, rfl⟩ := hu
      refine ⟨v⁻¹, ?_⟩
      rw [heu]
      simp [mul_comm, mul_left_comm, mul_assoc]
    exact (hf (N + 1)).not_associated hassoc⟩⟩
  exact ((IsBezout.TFAE (R := R)).out 3 1).mp hwf
