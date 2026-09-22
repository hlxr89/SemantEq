import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V] : ¬ ∃ (s : Finset (Submodule F V)) (hs : ∀ (p : Submodule F V), p ∈ s → p ≠ ⊤), (⊤ : Submodule F V) = s.sup id := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_7_2 {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] {ι : Type*} [Fintype ι] (γ : ι → Submodule K V)
  (h : ∀ i : ι, γ i ≠ ⊤) :
  (⋃ (i : ι), (γ i : Set V)) ≠ ⊤ := by
  classical
  exfalso
  apply dummy_assumed (F := K) (V := K × K)
  let p : Submodule K (K × K) := Submodule.prod (⊤ : Submodule K K) ⊥
  let q : Submodule K (K × K) := Submodule.prod (⊥ : Submodule K K) ⊤
  refine ⟨{p, q}, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · intro htop
      have hm : (0, 1) ∈ p :=
        htop ▸ Submodule.mem_top
      have hm2 : (1 : K) ∈ (⊥ : Submodule K K) :=
        (Submodule.mem_prod.mp hm).2
      change (1 : K) = 0 at hm2
      exact one_ne_zero hm2
    · intro htop
      have hm : (1, 0) ∈ q :=
        htop ▸ Submodule.mem_top
      have hm1 : (1 : K) ∈ (⊥ : Submodule K K) :=
        (Submodule.mem_prod.mp hm).1
      change (1 : K) = 0 at hm1
      exact one_ne_zero hm1
  · rw [Finset.sup_insert, Finset.sup_singleton]
    dsimp [id, p, q]
    rw [Submodule.prod_sup_prod]
    simp only [sup_bot_eq, bot_sup_eq]
    ext x
    constructor
    · intro _
      exact Submodule.mem_prod.mpr ⟨Submodule.mem_top, Submodule.mem_top⟩
    · intro _
      exact Submodule.mem_top
