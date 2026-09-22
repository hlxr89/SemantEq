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
  classical
  obtain ⟨P, hP, Q, hQ, hPQ, hmod⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to
      (s := S) (t := Set.univ)
      (f := fun (a, b, c) => ((a : ZMod 2), (b : ZMod 2), (c : ZMod 2)))
      (by simp [hS]) (by simp)
  rcases P with ⟨a, b, c⟩
  rcases Q with ⟨d, e, f⟩
  simp only [Prod.mk.injEq] at hmod
  have hda : (2 : ℤ) ∣ d - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a d 2).mp hmod.1
  have heb : (2 : ℤ) ∣ e - b :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub b e 2).mp hmod.2.1
  have hfc : (2 : ℤ) ∣ f - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c f 2).mp hmod.2.2
  obtain ⟨u, hu⟩ := hda
  obtain ⟨v, hv⟩ := heb
  obtain ⟨w, hw⟩ := hfc
  have hu' : (d : ℝ) - a = 2 * u := by exact_mod_cast hu
  have hv' : (e : ℝ) - b = 2 * v := by exact_mod_cast hv
  have hw' : (f : ℝ) - c = 2 * w := by exact_mod_cast hw
  refine ⟨a + u, b + v, c + w, (a, b, c), (d, e, f), hP, hQ, hPQ, ?_⟩
  rw [hL]
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
  norm_num at ⊢
  constructor
  · linarith
  constructor <;> linarith
