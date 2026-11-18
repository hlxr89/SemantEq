import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Prop :=
  ∃ k : ℕ, k * k = n

def dec_is_perfect_square (n : ℕ) : Bool :=
  Nat.sqrt n * Nat.sqrt n = n

def infinitely_many_eq (f : ℕ → ℕ) (A : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, f n = A

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a₀ : ℕ) (ha₀ : a₀ > 1) :
  let sequence : ℕ → ℕ := Nat.rec a₀ (fun n aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  (∃ A : ℕ, infinitely_many_eq sequence A) ↔ (3 ∣ a₀) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  classical
  intro x hx
  let sequence : ℕ → ℕ := Nat.rec x (fun _ aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have hsquare (n : ℕ) : IsSquare n ↔ dec_is_perfect_square n = true := by
    change (∃ r, n = r * r) ↔ decide (Nat.sqrt n * Nat.sqrt n = n) = true
    rw [decide_eq_true_eq, ← Nat.exists_mul_self]
    simp only [eq_comm]
  have haeq : ∀ n, a x n = sequence n := by
    intro n
    induction n with
    | zero => exact ha₀ x
    | succ n ih =>
        have hstep := ha₁ x n hx
        by_cases hp : IsSquare (a x n)
        · rw [if_pos hp] at hstep
          rw [hstep, ih]
          change Nat.sqrt (sequence n) =
            if dec_is_perfect_square (sequence n) then Nat.sqrt (sequence n)
            else sequence n + 3
          rw [(hsquare (sequence n)).mp (ih ▸ hp)]
          rfl
        · rw [if_neg hp] at hstep
          rw [hstep, ih]
          change sequence n + 3 =
            if dec_is_perfect_square (sequence n) then Nat.sqrt (sequence n)
            else sequence n + 3
          have hd : dec_is_perfect_square (sequence n) = false :=
            Bool.eq_false_of_not_eq_true (fun htrue => hp (ih.symm ▸ (hsquare _).mpr htrue))
          rw [hd]
          rfl
  have hcand := problem_statement_assumed x hx
  change (∃ A : ℕ, infinitely_many_eq sequence A) ↔ 3 ∣ x at hcand
  constructor
  · rintro ⟨A, hA⟩
    have hmany : infinitely_many_eq sequence A := by
      intro N
      obtain ⟨n, hnmem, hn⟩ := Set.infinite_iff_exists_gt.mp hA N
      have heq : sequence n = A := by
        rw [← haeq n]
        exact hnmem
      exact ⟨n, Nat.le_of_lt hn, heq⟩
    exact ⟨Nat.zero_lt_of_lt hx, hcand.mp ⟨A, hmany⟩⟩
  · rintro ⟨hpos, hdiv⟩
    obtain ⟨A, hmany⟩ := hcand.mpr hdiv
    refine ⟨A, Set.infinite_iff_exists_gt.mpr ?_⟩
    intro N
    obtain ⟨n, hn, hseq⟩ := hmany (N + 1)
    have heq : a x n = A := by
      rw [haeq n]
      exact hseq
    exact ⟨n, heq, lt_of_lt_of_le (Nat.lt_succ_self N) hn⟩
