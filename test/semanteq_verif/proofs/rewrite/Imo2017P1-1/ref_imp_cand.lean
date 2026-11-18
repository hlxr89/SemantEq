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
theorem imo2017_p1_assumed
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a₀ : ℕ) (ha₀ : a₀ > 1) :
  let sequence : ℕ → ℕ := Nat.rec a₀ (fun n aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  (∃ A : ℕ, infinitely_many_eq sequence A) ↔ (3 ∣ a₀) := by
  classical
  let a : ℕ → ℕ → ℕ := fun x => Nat.rec x (fun _ aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have ha_init : ∀ x, a x 0 = x := by
    intro x
    rfl
  have h := imo2017_p1_assumed a ha_init (by
    intro x i hx
    have hs : IsSquare (a x i) ↔ dec_is_perfect_square (a x i) = true := by
      change (∃ r, a x i = r * r) ↔
        decide (Nat.sqrt (a x i) * Nat.sqrt (a x i) = a x i) = true
      rw [decide_eq_true_eq, ← Nat.exists_mul_self]
      simp only [eq_comm]
    by_cases hp : IsSquare (a x i)
    · rw [if_pos hp]
      change (if dec_is_perfect_square (a x i) then _ else _) = _
      rw [hs.mp hp]
      rfl
    · rw [if_neg hp]
      change (if dec_is_perfect_square (a x i) then _ else _) = _
      rw [Bool.eq_false_of_not_eq_true (fun hd => hp (hs.mpr hd))]
      rfl) a₀ ha₀
  change (∃ A : ℕ, infinitely_many_eq (a a₀) A) ↔ 3 ∣ a₀
  have hset : a₀ ∈ solution_set ↔ 3 ∣ a₀ := by
    simp only [solution_set, Set.mem_setOf_eq, and_iff_right (Nat.zero_lt_of_lt ha₀)]
  rw [← hset, ← h]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, Set.infinite_iff_exists_gt.mpr ?_⟩
    intro N
    obtain ⟨n, hn, heq⟩ := hA (N + 1)
    exact ⟨n, heq, lt_of_lt_of_le (Nat.lt_succ_self N) hn⟩
  · rintro ⟨A, hA⟩
    refine ⟨A, fun N => ?_⟩
    obtain ⟨n, heq, hn⟩ := Set.infinite_iff_exists_gt.mp hA N
    exact ⟨n, Nat.le_of_lt hn, heq⟩
