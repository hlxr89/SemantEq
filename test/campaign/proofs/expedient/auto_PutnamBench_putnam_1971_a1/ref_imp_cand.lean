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
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a1 (S : Finset (Fin 3 → ℤ)) (hS : S.card = 9) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : Fin 3 → ℤ,
      (fun i => (z i : ℝ)) ∈
        openSegment ℝ (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) := by
  classical
  obtain ⟨p, hp, q, hq, hpq, hpmod⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S) (t := Finset.univ)
      (f := fun p i => (p i : ZMod 2)) (by simp [hS])
      (by intro p hp; simpa using Finset.mem_univ (fun i => (p i : ZMod 2)))
  have hdvd (i : Fin 3) : (2 : ℤ) ∣ q i - p i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (p i) (q i) 2).mp (congr_fun hpmod i)
  choose k hk using hdvd
  refine ⟨p, hp, q, hq, hpq, fun i => p i + k i, ?_⟩
  convert lineMap_mem_openSegment ℝ
    (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) using 1
  ext i
  have hki : (q i : ℝ) - p i = 2 * k i := by exact_mod_cast hk i
  simp [AffineMap.lineMap_apply]
  linarith
