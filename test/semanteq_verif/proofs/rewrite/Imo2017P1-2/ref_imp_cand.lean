import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Prop := ∃ k : ℕ, k * k = n

def seq (a₀ : ℕ) : ℕ → ℕ
| 0 => a₀
| n + 1 =>
  let a := seq a₀ n
  if Nat.sqrt a * Nat.sqrt a = a then
    Nat.sqrt a
  else
    a + 3

-- ===== assumed statement (antecedent) =====
theorem imo2017_p1_assumed
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a₀ : ℕ) (h : a₀ > 1) :
  (∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A) ↔ 3 ∣ a₀ := by
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨k, rfl⟩
      rw [Nat.sqrt_eq]
    · intro hn
      exact ⟨Nat.sqrt n, hn.symm⟩
  have hstep : ∀ x i, 1 < x → if IsSquare (seq x i)
      then seq x (i + 1) = Nat.sqrt (seq x i)
      else seq x (i + 1) = seq x i + 3 := by
    intro x i hx
    simp only [hsquare]
    by_cases hs : Nat.sqrt (seq x i) * Nat.sqrt (seq x i) = seq x i
    · simp only [if_pos hs, seq]
    · simp only [if_neg hs, seq]
  have hinf (A : ℕ) :
      (∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A) ↔ {n | seq a₀ n = A}.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    constructor
    · intro hu N
      obtain ⟨n, hn, heq⟩ := hu (N + 1)
      exact ⟨n, heq, lt_of_lt_of_le (Nat.lt_succ_self N) hn⟩
    · intro hu N
      obtain ⟨n, hn, heq⟩ := hu N
      exact ⟨n, Nat.le_of_lt heq, hn⟩
  have hexists :
      (∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A) ↔
        (∃ A, {n | seq a₀ n = A}.Infinite) := by
    exact exists_congr hinf
  have hmem : a₀ ∈ solution_set ↔ 3 ∣ a₀ := by
    exact and_iff_right (lt_trans Nat.zero_lt_one h)
  exact hexists.trans
    ((imo2017_p1_assumed (fun x => seq x) (fun x => rfl) hstep a₀ h).trans hmem)
