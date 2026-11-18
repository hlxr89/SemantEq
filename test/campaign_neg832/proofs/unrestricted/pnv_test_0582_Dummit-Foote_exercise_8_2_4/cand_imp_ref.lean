import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (hR : IsDomain R) (hgcd : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ d, ∃ r s : R, d = r * a + s * b ∧ ∀ t : R, t ∣ a → t ∣ b → t ∣ d) (hnoetherian : ∀ a : ℕ → R, (∀ n : ℕ, a (n + 1) ∣ a n) → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → IsUnit (a n)): IsPrincipalIdealRing R := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_8_2_4 {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
  (h1 : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r*a + s*b)
  (h2 : ∀ a : ℕ → R, (∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i) →
  ∃ N : ℕ, ∀ n ≥ N, ∃ u : R, IsUnit u ∧ a n = u * a N) :
  IsPrincipalIdealRing R := by
  have hbezout : IsBezout R := IsBezout.iff_span_pair_isPrincipal.mpr (by
    intro x y
    refine ⟨⟨gcd x y, ?_⟩⟩
    apply le_antisymm
    · apply Ideal.span_le.2
      intro z hz
      change z = x ∨ z = y at hz
      rcases hz with hz | hz
      · subst z
        show x ∈ Ideal.span ({gcd x y} : Set R)
        exact Ideal.mem_span_singleton.mpr (gcd_dvd_left x y)
      · subst z
        show y ∈ Ideal.span ({gcd x y} : Set R)
        exact Ideal.mem_span_singleton.mpr (gcd_dvd_right x y)
    · apply Ideal.span_le.2
      rintro z rfl
      by_cases hx : x = 0
      · subst x
        have hm : gcd 0 y ∈ Ideal.span ({y} : Set R) :=
          Ideal.mem_span_singleton.mpr (gcd_zero_left' y).symm.dvd
        exact Ideal.span_mono (by intro z hz; simp only [Set.mem_singleton_iff] at hz; subst z; simp) hm
      by_cases hy : y = 0
      · subst y
        have hm : gcd x 0 ∈ Ideal.span ({x} : Set R) :=
          Ideal.mem_span_singleton.mpr (gcd_zero_right' x).symm.dvd
        exact Ideal.span_mono (by intro z hz; simp only [Set.mem_singleton_iff] at hz; subst z; simp) hm
      obtain ⟨r, s, hrs⟩ := h1 x y hx hy
      rw [hrs]
      exact (Ideal.span {x, y}).add_mem
        (mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert x {y})))
        (mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem x (Set.mem_singleton y))))
    )
  letI : IsBezout R := hbezout
  have hwf : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨by
    rintro ⟨f, hf⟩
    let a : ℕ → R := fun n ↦ f (n + 1)
    have ha : ∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i := by
      intro i
      constructor
      · exact (hf i).1
      · obtain ⟨_, q, _, hq⟩ := hf (i + 1)
        exact ⟨q, hq⟩
    obtain ⟨N, hN⟩ := h2 a ha
    obtain ⟨u, hu, heq⟩ := hN (N + 1) (Nat.le_succ N)
    have hassoc : Associated (a (N + 1)) (a N) := by
      rw [heq]
      exact associated_unit_mul_left (a N) u hu
    exact (hf (N + 1)).not_associated hassoc
  ⟩⟩
  letI : WfDvdMonoid R := hwf
  exact ((IsBezout.TFAE (R := R)).out 3 1).mp hwf
