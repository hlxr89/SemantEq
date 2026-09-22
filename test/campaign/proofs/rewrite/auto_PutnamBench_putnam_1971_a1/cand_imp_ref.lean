import Mathlib

open Set

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1971_a1_assumed (S : Finset (Fin 3 → ℤ)) (hS : S.card = 9) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : Fin 3 → ℤ,
      (fun i => (z i : ℝ)) ∈
        openSegment ℝ (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a1_refs
(S : Set (ℤ × ℤ × ℤ))
(hS : S.ncard = 9)
(L : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Set (ℝ × ℝ × ℝ))
(hL : L = fun ((a, b, c), (d, e, f)) =>
{(t*a + (1-t)*d, t*b + (1-t)*e, t*c + (1-t)*f) | t ∈ Ioo (0 : ℝ) 1})
: ∃ x y z : ℤ, ∃ P Q : ℤ × ℤ × ℤ, P ∈ S ∧ Q ∈ S ∧ P ≠ Q ∧ ((x : ℝ), (y : ℝ), (z : ℝ)) ∈ L (P, Q) := by
  let f : (Fin 3 → ℤ) → ℤ × ℤ × ℤ := fun p => (p 0, p 1, p 2)
  let g : (ℤ × ℤ × ℤ) → (Fin 3 → ℤ) := fun P => ![P.1, P.2.1, P.2.2]
  have hfg : Function.LeftInverse f g := by
    intro P
    rcases P with ⟨a, b, c⟩
    rfl
  have hg : Function.Injective g := hfg.injective
  have hSfinite : S.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [hS]
    exact Nat.succ_ne_zero 8
  let T : Set (Fin 3 → ℤ) := g '' S
  have hTfinite : T.Finite := hSfinite.image g
  let F : Finset (Fin 3 → ℤ) := hTfinite.toFinset
  have hFcoe : (↑F : Set (Fin 3 → ℤ)) = T := hTfinite.coe_toFinset
  have hF : F.card = 9 := by
    rw [← Set.ncard_coe_finset, hFcoe,
      show T = g '' S from rfl, Set.ncard_image_of_injective _ hg, hS]
  obtain ⟨p, hp, q, hq, hpq, z, hz⟩ := putnam_1971_a1_assumed F hF
  have hpT : p ∈ T := by
    rw [← hFcoe]
    exact hp
  have hqT : q ∈ T := by
    rw [← hFcoe]
    exact hq
  rcases hpT with ⟨P, hP, rfl⟩
  rcases hqT with ⟨Q, hQ, rfl⟩
  rcases hz with ⟨a, b, ha, hb, hab, hpoint⟩
  have hb_eq : b = 1 - a := by
    rw [← hab]
    exact (add_sub_cancel_left a b).symm
  subst b
  refine ⟨z 0, z 1, z 2, P, Q, hP, hQ, ?_, ?_⟩
  · intro hPQ
    apply hpq
    exact congrArg g hPQ
  · rw [hL]
    refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · rw [← hab]
      exact lt_add_of_pos_right a hb
    · apply Prod.ext
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          congrArg (fun v => v 0) hpoint
      · apply Prod.ext
        · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
            congrArg (fun v => v 1) hpoint
        · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
            congrArg (fun v => v 2) hpoint
