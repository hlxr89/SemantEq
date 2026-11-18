import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

namespace Erdos288

-- ===== assumed statement (antecedent) =====
theorem erdos_288_assumed :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_288_goal :
    Set.Finite { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
  let f : ℕ → (Fin 2 → ℕ+ × ℕ+) := fun k =>
    ![(⟨k + 2, by omega⟩, 1), (1, 1)]
  have hf_mem : ∀ k, f k ∈ { I : Fin 2 → ℕ+ × ℕ+ |
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n } := by
    intro k
    have hempty : Finset.Icc (⟨k + 2, by omega⟩ : ℕ+) 1 = ∅ := by
      ext x
      constructor
      · intro hx
        exfalso
        simp only [Finset.mem_Icc] at hx
        change k + 2 ≤ x.val ∧ x.val ≤ 1 at hx
        omega
      · intro hx
        simpa using hx
    refine ⟨1, ?_⟩
    simp [f, hempty]
  have hf_injective : Function.Injective f := by
    intro a b hab
    have h : a + 2 = b + 2 := by
      simpa [f] using congrArg (fun I => ((I 0).1 : ℕ)) hab
    omega
  have hrange : (Set.range f).Finite := erdos_288_assumed.subset (by
    intro I hI
    obtain ⟨k, rfl⟩ := hI
    exact hf_mem k)
  exact False.elim (Set.infinite_range_of_injective hf_injective hrange)

end Erdos288
