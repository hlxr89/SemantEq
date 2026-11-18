import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_10_6_7_assumed {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {I : Ideal ℤ} (hI : I ≠ ⊥) : ∃ (n : ℤ), n ≠ 0 ∧ n ∈ I := by
  let f : ℤ →+* GaussianInt := algebraMap ℤ GaussianInt
  have hmap : Ideal.map f I ≠ ⊥ := by
    intro hmapbot
    apply hI
    apply (Ideal.map_eq_bot_iff_of_injective (f := f) ?_).mp hmapbot
    intro a b hab
    exact Int.cast_injective hab
  obtain ⟨z, hz0, hzim⟩ := exercise_10_6_7_assumed hmap
  refine ⟨z.1.re, ?_, ?_⟩
  · intro hzre
    apply hz0
    apply Subtype.ext
    apply Zsqrtd.ext <;> simpa only [Zsqrtd.re_zero, Zsqrtd.im_zero]
  · change z.1.re ∈ I
    -- non-rewrite step
    refine (Submodule.span_induction (p := fun x _ => x.re ∈ I ∧ x.im ∈ I) ?_ ?_ ?_ ?_ z.2).1
    · intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      change (a : GaussianInt).re ∈ I ∧ (a : GaussianInt).im ∈ I
      simpa only [Zsqrtd.re_intCast, Zsqrtd.im_intCast] using And.intro ha I.zero_mem
    · exact And.intro I.zero_mem I.zero_mem
    · intro x y _ _ hx hy
      exact And.intro (by simpa only [Zsqrtd.re_add] using I.add_mem hx.1 hy.1)
        (by simpa only [Zsqrtd.im_add] using I.add_mem hx.2 hy.2)
    · intro a x _ hx
      constructor
      · rw [smul_eq_mul, Zsqrtd.re_mul]
        exact I.add_mem (I.mul_mem_left a.re hx.1)
          (I.mul_mem_left ((-1 : ℤ) * a.im) hx.2)
      · rw [smul_eq_mul, Zsqrtd.im_mul]
        exact I.add_mem (I.mul_mem_left a.re hx.2) (I.mul_mem_left a.im hx.1)
