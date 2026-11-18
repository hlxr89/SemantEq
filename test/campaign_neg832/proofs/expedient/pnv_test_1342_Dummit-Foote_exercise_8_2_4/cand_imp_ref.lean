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
  letI : IsBezout R := by
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro a b
    by_cases ha : a = 0
    · subst a
      exact ⟨⟨b, by simp⟩⟩
    by_cases hb : b = 0
    · subst b
      exact ⟨⟨a, by simp⟩⟩
    obtain ⟨r, s, hrs⟩ := h1 a b ha hb
    have heq : (Ideal.span {gcd a b} : Ideal R) = Ideal.span {a, b} := le_antisymm (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Ideal.mem_span_pair.mpr ⟨r, s, hrs.symm⟩) (by
      rw [Ideal.span_le]
      intro x hx
      rcases hx with (rfl | hx)
      · exact Ideal.mem_span_singleton.mpr (gcd_dvd_left x b)
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact Ideal.mem_span_singleton.mpr (gcd_dvd_right a b))
    exact ⟨⟨gcd a b, (congrArg (fun I : Ideal R ↦ (I : Submodule R R)) heq).symm⟩⟩
  letI : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨by
    rintro ⟨a, ha⟩
    obtain ⟨N, hN⟩ := h2 (fun n ↦ a (n + 1)) (by
      intro i
      obtain ⟨x, hx, heq⟩ := (ha (i + 1)).2
      exact ⟨(ha i).1, ⟨x, heq⟩⟩)
    obtain ⟨u, hu, heu⟩ := hN (N + 1) (Nat.le_succ N)
    apply (ha (N + 1)).not_associated
    rw [heu]
    exact associated_unit_mul_left _ _ hu
  ⟩⟩
  exact (IsBezout.TFAE.out 3 1).mp (by infer_instance)
