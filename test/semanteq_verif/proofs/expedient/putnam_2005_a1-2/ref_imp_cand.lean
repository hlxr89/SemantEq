import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def IsPow23 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

-- ===== assumed statement (antecedent) =====
theorem putnam_2005_a1_assumed
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, IsPow23 x) ∧
    (∀ x y : ℕ, x ∈ S → y ∈ S → x ≠ y → ¬(x ∣ y)) ∧
    S.sum id = n :=
by
  obtain ⟨k, a, hsum, hanti⟩ := putnam_2005_a1_assumed n (by exact_mod_cast hn)
  let f : Fin k → ℕ := fun i => 2^(a i 0) * 3^(a i 1)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hanti i j hne (by simp [f, hij])
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy hdiv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hanti i j (fun hij => hxy (congrArg f hij)) hdiv
  · rw [Finset.sum_image (fun _ _ _ _ hij => hinj hij)]
    have hsum' : (∑ i : Fin k, f i) = n := by
      exact_mod_cast hsum.symm
    simpa using hsum'
