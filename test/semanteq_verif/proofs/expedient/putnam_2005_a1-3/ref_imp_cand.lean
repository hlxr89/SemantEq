import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def is_power_of_2_3 (n : ℕ) : Prop := ∃ r s : ℕ, n = 2^r * 3^s

def no_divides_in_list (l : List ℕ) : Prop :=
  ∀ a₁ a₂, a₁ ∈ l → a₂ ∈ l → a₁ ≠ a₂ → ¬(a₁ ∣ a₂)

-- ===== assumed statement (antecedent) =====
theorem putnam_2005_a1_assumed
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  ∃ l : List ℕ, 
    (∀ x ∈ l, is_power_of_2_3 x) ∧
    (l.sum = n) ∧
    (no_divides_in_list l) := by
  obtain ⟨k, a, hsum, hdiv⟩ := putnam_2005_a1_assumed n (by exact_mod_cast hn)
  let f : Fin k → ℕ := fun i => 2 ^ (a i 0) * 3 ^ (a i 1)
  refine ⟨List.ofFn f, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i 0, a i 1, rfl⟩
  · rw [List.sum_ofFn]
    exact_mod_cast hsum.symm
  · intro x y hx hy hxy hxydiv
    simp only [List.mem_ofFn] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    apply hdiv i j hij
    exact_mod_cast hxydiv
