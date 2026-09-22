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
: ∃ x y z : ℤ, ∃ P Q : ℤ × ℤ × ℤ, P ∈ S ∧ Q ∈ S ∧ P ≠ Q ∧ ((x : ℝ), (y : ℝ), (z : ℝ)) ∈ L (P, Q) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1971_a1 (S : Finset (Fin 3 → ℤ)) (hS : S.card = 9) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ∃ z : Fin 3 → ℤ,
      (fun i => (z i : ℝ)) ∈
        openSegment ℝ (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) := by
  let enc : (Fin 3 → ℤ) → (ℤ × ℤ × ℤ) := fun p => (p 0, p 1, p 2)
  have henc : Function.Injective enc := by
    intro p q hpq
    funext i
    fin_cases i <;> simp [enc] at hpq ⊢ <;> simp_all
  let T : Set (ℤ × ℤ × ℤ) := ↑(S.image enc)
  have hT : T.ncard = 9 := by
    rw [show T = ↑(S.image enc) from rfl, Set.ncard_coe_finset,
      Finset.card_image_of_injective S henc, hS]
  let L : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → Set (ℝ × ℝ × ℝ) :=
    fun ((a, b, c), (d, e, f)) =>
      {(t*a + (1-t)*d, t*b + (1-t)*e, t*c + (1-t)*f) | t ∈ Ioo (0 : ℝ) 1}
  obtain ⟨x, y, z, P, Q, hPT, hQT, hPQ, hz⟩ :=
    putnam_1971_a1_refs_assumed T hT L rfl
  change P ∈ S.image enc at hPT
  change Q ∈ S.image enc at hQT
  rw [Finset.mem_image] at hPT hQT
  rcases hPT with ⟨p, hpS, rfl⟩
  rcases hQT with ⟨q, hqS, rfl⟩
  refine ⟨p, hpS, q, hqS, ?_, fun i => ![x, y, z] i, ?_⟩
  · intro hpq
    apply hPQ
    exact congrArg enc hpq
  · change (fun i => ((![x, y, z] i : ℤ) : ℝ)) ∈ _
    change ((x : ℝ), (y : ℝ), (z : ℝ)) ∈ L (enc p, enc q) at hz
    rcases hz with ⟨t, ht, heq⟩
    refine ⟨t, 1 - t, ht.1, sub_pos.mpr ht.2, by ring, ?_⟩
    funext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg (fun u => u.2.1) heq
    · exact congrArg (fun u => u.2.2) heq
