import Mathlib

open Filter

open Submonoid

open scoped Pointwise

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos123

def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧
    s.sum id = n

def PairwiseCoprime (a b c : ℕ) : Prop := Pairwise (Nat.Coprime.onFun ![a, b, c])

-- ===== assumed statement (antecedent) =====
theorem erdos_123_assumed :
    ∀ a > 1, ∀ b > 1, ∀ c > 1, PairwiseCoprime a b c →
    IsDComplete (↑(powers a) * ↑(powers b) * ↑(powers c)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_123 (a b c : ℕ) (ha : a > 1) (hb : b > 1) (hc : c > 1)
    (h_coprime : PairwiseCoprime a b c) :
    IsDComplete (↑(powers a) * ↑(powers b) * ↑(powers c)) := by
  exact erdos_123_assumed a ha b hb c hc h_coprime

end Erdos123
