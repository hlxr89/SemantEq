import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
def S_seq (S₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => S₀
  | n + 1 => {a : ℕ | a > 0 ∧ (a - 1 ∈ S_seq S₀ n ∧ a ∉ S_seq S₀ n) ∨ (a - 1 ∉ S_seq S₀ n ∧ a ∈ S_seq S₀ n)}

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S₀ : Set ℕ) (hS₀ : S₀.Finite) (hS₀_pos : ∀ x ∈ S₀, x > 0) :
  Set.Infinite {N : ℕ | S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2000_b5
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  classical
  let S₀ : Set ℕ := {a | (a : ℤ) ∈ S 0}
  have hS₀fin : S₀.Finite := by
    apply ((hSfin 0).image Int.natAbs).subset
    intro a ha
    exact ⟨(a : ℤ), ha, by simp⟩
  have hS₀pos : ∀ a ∈ S₀, a > 0 := by
    intro a ha
    have := hSpos 0 (a : ℤ) ha
    omega
  have hcorr : ∀ k a, a ∈ S_seq S₀ k ↔ (a : ℤ) ∈ S k := by
    intro k
    induction k with
    | zero =>
        intro a
        rfl
    | succ k ih =>
        intro a
        cases a with
        | zero =>
            have hk : (0 : ℤ) ∉ S k := by
              intro h
              have := hSpos k 0 h
              omega
            have hk' : (0 : ℤ) ∉ S (k + 1) := by
              intro h
              have := hSpos (k + 1) 0 h
              omega
            simp [S_seq, hk, hk']
        | succ a =>
            rw [S_seq, hSdef]
            simp only [Set.mem_setOf_eq, Nat.succ_pos, true_and,
              Nat.succ_sub_one]
            simp only [ih]
            simp [Xor']
            tauto
  have hinf := problem_statement_assumed S₀ hS₀fin hS₀pos
  intro n
  obtain ⟨N, hNmem, hN⟩ := hinf.exists_gt n
  refine ⟨N, by omega, ?_⟩
  have hreturn : S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀} := hNmem
  ext z
  by_cases hz : 0 ≤ z
  · lift z to ℕ using hz with a
    rw [← hcorr]
    rw [hreturn]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h with h | ⟨b, hb, hab⟩
      · exact Or.inl h
      · right
        subst a
        change ((N + b : ℕ) : ℤ) - (N : ℤ) ∈ S 0
        have heq : ((N + b : ℕ) : ℤ) - (N : ℤ) = (b : ℤ) := by
          push_cast
          ring
        rw [heq]
        exact hb
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · by_cases hle : N ≤ a
        · right
          refine ⟨a - N, ?_, by omega⟩
          change ((a - N : ℕ) : ℤ) ∈ S 0
          have heq : ((a - N : ℕ) : ℤ) = (a : ℤ) - N := by omega
          rwa [heq]
        · have hnot : (a : ℤ) - N ≤ 0 := by omega
          have hpos := hSpos 0 ((a : ℤ) - N) h
          omega
  · have hzneg : z < 0 := by omega
    have hleft : z ∉ S N := by
      intro h
      have := hSpos N z h
      omega
    have hzero : z ∉ S 0 := by
      intro h
      have := hSpos 0 z h
      omega
    have hshift : z - (N : ℤ) ∉ S 0 := by
      intro h
      have := hSpos 0 (z - (N : ℤ)) h
      omega
    simp [hleft, hzero, hshift]
