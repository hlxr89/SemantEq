import Mathlib

open Set

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1971_a1_refs_assumed
(S : Set (ℤ × ℤ × ℤ))
(hS : S.ncard = 9)
(L : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Set (ℝ × ℝ × ℝ))
(hL : L = fun ((a, b, c), (d, e, f)) =>
{(t*a + (1-t)*d, t*b + (1-t)*e, t*c + (1-t)*f) | t ∈ Ioo (0 : ℝ) 1})
: ∃ x y z : ℤ, ∃ P Q : ℤ × ℤ × ℤ, P ∈ S ∧ Q ∈ S ∧ P ≠ Q ∧ ((x : ℝ), (y : ℝ), (z : ℝ)) ∈ L (P, Q) :=
  by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a1 (S : Finset (Fin 3 → ℤ)) (hS : S.card = 9) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : Fin 3 → ℤ,
      (fun i => (z i : ℝ)) ∈
        openSegment ℝ (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) := by
  let f : (Fin 3 → ℤ) → ℤ × ℤ × ℤ := fun p => (p 0, p 1, p 2)
  let g : (ℤ × ℤ × ℤ) → (Fin 3 → ℤ) := fun P => ![P.1, P.2.1, P.2.2]
  have hgf : Function.LeftInverse g f := by
    intro p
    funext i
    fin_cases i <;> rfl
  have hf : Function.Injective f := hgf.injective
  let T : Set (ℤ × ℤ × ℤ) := f '' (↑S : Set (Fin 3 → ℤ))
  have hT : T.ncard = 9 := by
    rw [show T = f '' (↑S : Set (Fin 3 → ℤ)) from rfl,
      Set.ncard_image_of_injective _ hf, Set.ncard_coe_finset, hS]
  let L : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Set (ℝ × ℝ × ℝ) :=
    fun ((a, b, c), (d, e, f)) =>
      {(t*a + (1-t)*d, t*b + (1-t)*e, t*c + (1-t)*f) | t ∈ Ioo (0 : ℝ) 1}
  obtain ⟨x, y, z, P, Q, hP, hQ, hPQ, hz⟩ :=
    putnam_1971_a1_refs_assumed T hT L rfl
  rcases hP with ⟨p, hp, rfl⟩
  rcases hQ with ⟨q, hq, rfl⟩
  refine ⟨p, hp, q, hq, ?_, fun i => ![x, y, z] i, ?_⟩
  · intro hpq
    apply hPQ
    exact congrArg f hpq
  · rcases hz with ⟨t, ht, hpoint⟩
    refine ⟨t, 1 - t, ht.1, sub_pos.mpr ht.2, ?_, ?_⟩
    · simpa only [add_comm] using sub_add_cancel 1 t
    · apply funext
      intro i
      fin_cases i
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_zero, Fin.isValue] using
          congrArg (fun R => R.1) hpoint
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_one, Fin.isValue] using
          congrArg (fun R => R.2.1) hpoint
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_two, Fin.isValue] using
          congrArg (fun R => R.2.2) hpoint
