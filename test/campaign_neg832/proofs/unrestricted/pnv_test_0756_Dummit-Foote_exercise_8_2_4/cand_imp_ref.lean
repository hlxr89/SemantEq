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
  have hbezout : IsBezout R := by
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro x y
    rw [Submodule.isPrincipal_iff]
    by_cases hx : x = 0
    · use y
      subst x
      rw [Ideal.submodule_span_eq]
      simp
    by_cases hy : y = 0
    · use x
      subst y
      rw [Ideal.submodule_span_eq]
      simp
    obtain ⟨r, s, hrs⟩ := h1 x y hx hy
    use gcd x y
    rw [Ideal.submodule_span_eq]
    apply Eq.symm
    apply le_antisymm
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hrs]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      have hdx := GCDMonoid.gcd_dvd_left x y
      have hdy := GCDMonoid.gcd_dvd_right x y
      rcases hz with rfl | rfl
      · exact Ideal.mem_span_singleton.mpr hdx
      · exact Ideal.mem_span_singleton.mpr hdy
  letI : IsBezout R := hbezout
  have hwf : WfDvdMonoid R := by
    constructor
    rw [wellFounded_iff_isEmpty_descending_chain]
    constructor
    rintro ⟨f, hf⟩
    let a : ℕ → R := fun n => f (n + 1)
    have ha : ∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i := by
      intro i
      exact ⟨(hf i).1, ⟨Classical.choose (hf (i + 1)).2,
        (Classical.choose_spec (hf (i + 1)).2).2⟩⟩
    obtain ⟨N, hN⟩ := h2 a ha
    obtain ⟨u, hu, hau⟩ := hN (N + 1) (Nat.le_succ N)
    have hassoc : Associated (a (N + 1)) (a N) := by
      apply Associated.symm
      use hu.unit
      simpa only [hu.unit_spec, mul_comm] using hau.symm
    exact (hf (N + 1)).not_associated hassoc
  exact ((IsBezout.TFAE (R := R)).out 3 1).mp hwf
