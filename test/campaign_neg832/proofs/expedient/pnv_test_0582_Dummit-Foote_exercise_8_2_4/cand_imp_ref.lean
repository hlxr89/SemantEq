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
  letI : IsBezout R := IsBezout.iff_span_pair_isPrincipal.mpr fun a b => by
    rcases eq_or_ne a 0 with ha | ha
    · refine ⟨⟨b, le_antisymm ?_ ?_⟩⟩
      · apply Ideal.span_le.mpr
        intro x hx
        have hx' : x = a ∨ x = b := by simpa using hx
        rcases hx' with hxa | hxb
        · subst x; simp [ha]
        · subst x; exact Submodule.mem_span_singleton_self b
      · apply Submodule.span_le.mpr
        rintro x rfl
        exact Ideal.subset_span (by simp)
    rcases eq_or_ne b 0 with hb | hb
    · refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
      · apply Ideal.span_le.mpr
        intro x hx
        have hx' : x = a ∨ x = b := by simpa using hx
        rcases hx' with hxa | hxb
        · subst x; exact Submodule.mem_span_singleton_self a
        · subst x; simp [hb]
      · apply Submodule.span_le.mpr
        rintro x rfl
        exact Ideal.subset_span (by simp)
    obtain ⟨r, s, hrs⟩ := h1 a b ha hb
    refine ⟨⟨gcd a b, le_antisymm ?_ ?_⟩⟩
    · apply Ideal.span_le.mpr
      intro x hx
      have hx' : x = a ∨ x = b := by simpa using hx
      rcases hx' with hxa | hxb
      · subst x; exact Ideal.mem_span_singleton.mpr (gcd_dvd_left a b)
      · subst x; exact Ideal.mem_span_singleton.mpr (gcd_dvd_right a b)
    · apply Submodule.span_le.mpr
      rintro x rfl
      exact Ideal.mem_span_pair.mpr ⟨r, s, hrs.symm⟩
  letI : WfDvdMonoid R := ⟨wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun f => by
    obtain ⟨N, hN⟩ := h2 (fun n => f.1 (n + 1)) fun i =>
      ⟨(f.2 i).1, by
        obtain ⟨x, -, hx⟩ := (f.2 (i + 1)).2
        exact ⟨x, hx⟩⟩
    obtain ⟨u, hu, heq⟩ := hN (N + 1) (Nat.le_succ N)
    apply (f.2 (N + 1)).not_associated
    apply associated_of_dvd_dvd
    · obtain ⟨x, -, hx⟩ := (f.2 (N + 1)).2
      exact ⟨x, hx⟩
    · exact ⟨u, by simpa [mul_comm] using heq⟩
  ⟩⟩
  haveI : IsNoetherianRing R :=
    ((IsBezout.TFAE (R := R)).out 3 0).mp (inferInstance : WfDvdMonoid R)
  infer_instance
