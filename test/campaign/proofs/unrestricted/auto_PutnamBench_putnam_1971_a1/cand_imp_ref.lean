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
  have hSfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  let dec : (ℤ × ℤ × ℤ) → (Fin 3 → ℤ) := fun p => ![p.1, p.2.1, p.2.2]
  have hdec : Function.Injective dec := by
    intro p q hpq
    apply Prod.ext
    · exact congrFun hpq 0
    · apply Prod.ext
      · exact congrFun hpq 1
      · exact congrFun hpq 2
  let F : Finset (Fin 3 → ℤ) := hSfin.toFinset.image dec
  have hF : F.card = 9 := by
    rw [Finset.card_image_of_injective _ hdec]
    simpa [Set.ncard_eq_toFinset_card S hSfin] using hS
  obtain ⟨p, hpF, q, hqF, hpq, z, hz⟩ := putnam_1971_a1_assumed F hF
  change p ∈ hSfin.toFinset.image dec at hpF
  change q ∈ hSfin.toFinset.image dec at hqF
  rw [Finset.mem_image] at hpF hqF
  rcases hpF with ⟨P, hPS, rfl⟩
  rcases hqF with ⟨Q, hQS, rfl⟩
  have hPS' : P ∈ S := by simpa using hPS
  have hQS' : Q ∈ S := by simpa using hQS
  refine ⟨z 0, z 1, z 2, P, Q, hPS', hQS', ?_, ?_⟩
  · intro hPQ
    apply hpq
    exact congrArg dec hPQ
  · rw [hL]
    rcases hz with ⟨a, b, ha, hb, hab, heq⟩
    refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · linarith
    · have hb' : b = 1 - a := by linarith
      subst b
      apply Prod.ext
      · exact congrFun heq 0
      · apply Prod.ext
        · exact congrFun heq 1
        · exact congrFun heq 2
