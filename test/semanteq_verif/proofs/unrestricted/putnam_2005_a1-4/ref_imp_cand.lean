import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def is_power_of_2_and_3 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

def no_divides (s : List ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ s → b ∈ s → a ≠ b → ¬(a ∣ b)

-- ===== assumed statement (antecedent) =====
theorem putnam_2005_a1_assumed
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
  by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  ∃ s : List ℕ, (∀ x ∈ s, is_power_of_2_and_3 x) ∧ no_divides s ∧ s.sum = n := by
  obtain ⟨k, a, hsum, hanti⟩ := putnam_2005_a1_assumed (n : ℤ) (by omega)
  let f : Fin k → ℕ := fun i => 2 ^ (a i 0) * 3 ^ (a i 1)
  refine ⟨List.ofFn f, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy hdiv
    rw [List.mem_ofFn] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    apply hanti i j hij
    exact_mod_cast hdiv
  · rw [List.sum_ofFn]
    exact_mod_cast hsum.symm
