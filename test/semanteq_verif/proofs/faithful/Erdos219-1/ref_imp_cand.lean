import Mathlib

-- No `open` or `open scoped` lines occur in either input.

-- ===== unified context (both sides' local defs, merged) =====
section AP

variable {α : Type*} [AddCommMonoid α]

def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

end AP

namespace Erdos219

def primeArithmeticProgressions : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > 0, s.IsAPOfLength l}

-- ===== assumed statement (antecedent) =====
theorem erdos_219_assumed :
    ∀ N : ℕ, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_219_goal :
    ∀ N, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l := by
  -- not proved: the candidate quantifies over ℕ∞ and its N = ⊤ case requires an infinite prime arithmetic progression, which the reference's ℕ-indexed statement does not provide
  sorry

end Erdos219
