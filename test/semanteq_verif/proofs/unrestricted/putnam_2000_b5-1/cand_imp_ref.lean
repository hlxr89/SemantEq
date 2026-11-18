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
  let S₀ : Set ℕ := {x : ℕ | (x : ℤ) ∈ S 0}
  have hS₀fin : S₀.Finite := by
    apply ((hSfin 0).image Int.toNat).subset
    intro x hx
    refine ⟨(x : ℤ), hx, ?_⟩
    simp
  have hS₀pos : ∀ x ∈ S₀, x > 0 := by
    intro x hx
    have := hSpos 0 (x : ℤ) hx
    omega
  have hseqpos : ∀ n x, x ∈ S_seq S₀ n → x > 0 := by
    intro n
    induction n with
    | zero => exact hS₀pos
    | succ n ih =>
        intro x hx
        simp only [S_seq, Set.mem_setOf_eq] at hx
        rcases hx with hx | hx
        · exact hx.1
        · exact ih x hx.2
  let T : ℕ → Set ℤ := fun n => {z : ℤ | 0 < z ∧ z.toNat ∈ S_seq S₀ n}
  have hTdef : ∀ n, ∀ z, z ∈ T (n + 1) ↔ Xor' (z - 1 ∈ T n) (z ∈ T n) := by
    intro n z
    change (0 < z ∧ z.toNat ∈ S_seq S₀ (n + 1)) ↔
      Xor' (0 < z - 1 ∧ (z - 1).toNat ∈ S_seq S₀ n)
        (0 < z ∧ z.toNat ∈ S_seq S₀ n)
    by_cases hz : 0 < z
    · have hsub : (z - 1).toNat = z.toNat - 1 := by omega
      simp only [S_seq, Set.mem_setOf_eq, hsub]
      constructor
      · intro h
        rcases h with ⟨_, h⟩
        rcases h with h | h
        · have hmpos := hseqpos n (z.toNat - 1) h.2.1
          exact Or.inl ⟨⟨by omega, h.2.1⟩, fun hp => h.2.2 hp.2⟩
        · exact Or.inr ⟨⟨hz, h.2⟩, fun hp => h.1 hp.2⟩
      · intro h
        refine ⟨hz, ?_⟩
        rcases h with h | h
        · exact Or.inl ⟨by omega, h.1.2, fun hp => h.2 ⟨hz, hp⟩⟩
        · exact Or.inr ⟨(fun hp => h.2 ⟨by have := hseqpos n _ hp; omega, hp⟩), h.1.2⟩
    · have hone : ¬ 1 < z := by omega
      simp [hz, hone]
  have hST : ∀ n, S n = T n := by
    intro n
    induction n with
    | zero =>
        ext z
        change (z ∈ S 0) ↔ (0 < z ∧ z.toNat ∈ S₀)
        constructor
        · intro hz
          refine ⟨hSpos 0 z hz, ?_⟩
          change ((z.toNat : ℕ) : ℤ) ∈ S 0
          simpa only [Int.toNat_of_nonneg (le_of_lt (hSpos 0 z hz))]
        · intro hz
          have hm := hz.2
          change ((z.toNat : ℕ) : ℤ) ∈ S 0 at hm
          simpa only [Int.toNat_of_nonneg (le_of_lt hz.1)] using hm
    | succ n ih =>
        ext z
        rw [hSdef, hTdef]
        simp only [ih]
  have hgood := problem_statement_assumed S₀ hS₀fin hS₀pos
  intro n
  obtain ⟨N, hNgood, hNgt⟩ := hgood.exists_gt n
  refine ⟨N, le_of_lt hNgt, ?_⟩
  rw [hST N, hST 0]
  ext z
  change (0 < z ∧ z.toNat ∈ S_seq S₀ N) ↔
    (0 < z ∧ z.toNat ∈ S₀) ∨
      (0 < z - (N : ℤ) ∧ (z - (N : ℤ)).toNat ∈ S₀)
  by_cases hz : 0 < z
  · have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hz)
    have hmem := Set.ext_iff.mp hNgood z.toNat
    change (z.toNat ∈ S_seq S₀ N) ↔
      z.toNat ∈ S₀ ∨ ∃ a ∈ S₀, N + a = z.toNat at hmem
    constructor
    · intro h
      rcases h with ⟨_, hs⟩
      rcases hmem.mp hs with h0 | ⟨a, ha, hea⟩
      · exact Or.inl ⟨hz, h0⟩
      · right
        constructor
        · have hapos := hS₀pos a ha
          omega
        · have hdiff : (z - (N : ℤ)).toNat = a := by omega
          simpa only [hdiff] using ha
    · intro h
      refine ⟨hz, hmem.mpr ?_⟩
      rcases h with h | h
      · exact Or.inl h.2
      · right
        refine ⟨(z - (N : ℤ)).toNat, h.2, ?_⟩
        omega
  · have hdiff : ¬ 0 < z - (N : ℤ) := by omega
    constructor
    · intro h
      exact (hz h.1).elim
    · intro h
      rcases h with h | h
      · exact (hz h.1).elim
      · exact (hdiff h.1).elim
