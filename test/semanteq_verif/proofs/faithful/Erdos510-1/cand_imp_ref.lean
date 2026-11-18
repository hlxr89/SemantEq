import Mathlib

open Real Filter

open scoped Finset

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos510

-- ===== assumed statement (antecedent) =====
theorem erdos_510_assumed :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ (N : ℕ), ∀ (A : Finset ℤ), # A = N →
      (∃ (θ : ℝ), (∑ n ∈ A, (n * θ).cos) < -c * (N : ℝ).sqrt) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_510 :
    ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N := by
  obtain ⟨c, hc, h⟩ := erdos_510_assumed
  refine ⟨c, hc, Filter.Eventually.of_forall ?_⟩
  intro N A _ hA
  have himage : #(A.image Int.ofNat) = #A :=
    Finset.card_image_iff.mpr (fun _ _ _ _ hxy => Int.ofNat.inj hxy)
  obtain ⟨θ, hθ⟩ := h N (A.image Int.ofNat) (himage.trans hA)
  refine ⟨θ, ?_⟩
  simpa [Finset.sum_image] using hθ

end Erdos510
