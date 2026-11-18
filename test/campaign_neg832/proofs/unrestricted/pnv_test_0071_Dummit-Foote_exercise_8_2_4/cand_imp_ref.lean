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
  have hbezout : IsBezout R := by
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro a b
    by_cases ha : a = 0
    · refine ⟨⟨b, ?_⟩⟩
      change Ideal.span {a, b} = Ideal.span {b}
      rw [ha, Ideal.span_insert_zero]
    by_cases hb : b = 0
    · refine ⟨⟨a, ?_⟩⟩
      change Ideal.span {a, b} = Ideal.span {a}
      rw [hb, Ideal.span_pair_comm, Ideal.span_insert_zero]
    obtain ⟨r, s, hrs⟩ := h1 a b ha hb
    refine ⟨⟨gcd a b, ?_⟩⟩
    change Ideal.span {a, b} = Ideal.span {gcd a b}
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · subst x
        obtain ⟨c, hc⟩ := GCDMonoid.gcd_dvd_left a b
        exact Ideal.mem_span_singleton'.mpr ⟨c, by simpa [mul_comm] using hc.symm⟩
      · subst x
        obtain ⟨c, hc⟩ := GCDMonoid.gcd_dvd_right a b
        exact Ideal.mem_span_singleton'.mpr ⟨c, by simpa [mul_comm] using hc.symm⟩
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [hrs]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  letI : IsBezout R := hbezout
  have hwf : WellFounded (DvdNotUnit (α := R)) :=
    wellFounded_iff_isEmpty_descending_chain.mpr ⟨by
      rintro ⟨f, hf⟩
      let a : ℕ → R := fun n ↦ f (n + 1)
      have ha : ∀ i : ℕ, a i ≠ 0 ∧ a (i + 1) ∣ a i := by
        intro i
        constructor
        · exact (hf i).1
        · obtain ⟨_, x, _, hx⟩ := hf (i + 1)
          exact ⟨x, by simpa [a, Nat.add_assoc] using hx⟩
      obtain ⟨N, hN⟩ := h2 a ha
      obtain ⟨u, hu, heq⟩ := hN (N + 1) (Nat.le_add_right N 1)
      have hassoc : Associated (a (N + 1)) (a N) := by
        rw [heq]
        exact associated_unit_mul_left (a N) u hu
      exact (hf (N + 1)).not_associated (by simpa [a, Nat.add_assoc] using hassoc)⟩
  letI : WfDvdMonoid R := ⟨hwf⟩
  exact ((IsBezout.TFAE (R := R)).out 3 1 :
    WfDvdMonoid R ↔ IsPrincipalIdealRing R).mp (by infer_instance)
