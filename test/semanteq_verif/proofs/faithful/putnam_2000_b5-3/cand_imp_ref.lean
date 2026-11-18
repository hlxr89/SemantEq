import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S₀ : Set ℕ) (hS₀ : ∀ x ∈ S₀, x > 0) :
  ∃ S : ℕ → Set ℕ,
    S 0 = S₀ ∧
    (∀ n, S (n + 1) = {a : ℕ | a > 0 ∧ ((a - 1) ∈ S n ∧ ¬(a ∈ S n)) ∨ (a ∈ S n ∧ ¬((a - 1) ∈ S n))}) ∧
    Set.Finite (S 0) ∧
    (∀ n, Set.Finite (S n)) ∧
    Set.Infinite {N : ℕ | S N = S₀ ∪ {x + N | x ∈ S₀}} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2000_b5
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  let S₀ : Set ℕ := {x | (x : ℤ) ∈ S 0}
  have hS₀ : ∀ x ∈ S₀, x > 0 := by
    intro x hx
    exact_mod_cast hSpos 0 (x : ℤ) hx
  obtain ⟨T, hT0, hTrec, hTfin0, hTfin, hTinf⟩ :=
    problem_statement_assumed S₀ hS₀
  have hTS : ∀ k, T k = {x : ℕ | (x : ℤ) ∈ S k} := by
    intro k
    induction k with
    | zero => simpa [S₀] using hT0
    | succ k ih =>
      rw [hTrec k]
      ext a
      simp only [Set.mem_setOf_eq]
      rw [hSdef k (a : ℤ)]
      simp only [Xor', ih, Set.mem_setOf_eq]
      by_cases ha : a = 0
      · subst a
        simp only [CharP.cast_eq_zero, gt_iff_lt, lt_self_iff_false, false_and,
          zero_sub]
        have hz : (0 : ℤ) ∉ S k := by
          intro hz
          exact (hSpos k 0 hz).false
        have hneg : (-1 : ℤ) ∉ S k := by
          intro hneg
          have := hSpos k (-1) hneg
          omega
        simp [hz, hneg]
      · have hapos : a > 0 := Nat.pos_of_ne_zero ha
        have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
        rw [hcast]
        simp only [hapos, true_and]
  intro n
  obtain ⟨N, hNmem, hnN⟩ := hTinf.exists_gt n
  refine ⟨N, Nat.le_of_lt hnN, ?_⟩
  have hTN : T N = S₀ ∪ {x + N | x ∈ S₀} := hNmem
  rw [hTS N] at hTN
  ext M
  constructor
  · intro hM
    have hMpos : M > 0 := hSpos N M hM
    have hcast : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg (le_of_lt hMpos)
    have hmnat : M.toNat ∈ S₀ ∪ {x + N | x ∈ S₀} := by
      rw [← hTN]
      exact hcast ▸ hM
    rcases hmnat with hm0 | hmshift
    · exact Or.inl (by simpa [S₀, hcast] using hm0)
    · rcases hmshift with ⟨x, hx, hxeq⟩
      right
      change M - (N : ℤ) ∈ S 0
      have hMx : M - (N : ℤ) = (x : ℤ) := by
        omega
      rw [hMx]
      exact hx
  · intro hM
    have hmnat : M.toNat ∈ S₀ ∪ {x + N | x ∈ S₀} := by
      rcases hM with hm0 | hmshift
      · left
        change (M.toNat : ℤ) ∈ S 0
        have hMpos : M > 0 := hSpos 0 M hm0
        simpa [Int.toNat_of_nonneg (le_of_lt hMpos)] using hm0
      · right
        change M - (N : ℤ) ∈ S 0 at hmshift
        have hdiffpos : M - (N : ℤ) > 0 := hSpos 0 (M - (N : ℤ)) hmshift
        let x := (M - (N : ℤ)).toNat
        refine ⟨x, ?_, ?_⟩
        · have hxcast : (x : ℤ) = M - (N : ℤ) := by
            dsimp [x]
            exact Int.toNat_of_nonneg (le_of_lt hdiffpos)
          change (x : ℤ) ∈ S 0
          rw [hxcast]
          exact hmshift
        · dsimp [x]
          omega
    have hmLift : (M.toNat : ℤ) ∈ S N := by
      have : M.toNat ∈ {x : ℕ | (x : ℤ) ∈ S N} := by
        rw [hTN]
        exact hmnat
      exact this
    have hMpos : M > 0 := by
      rcases hM with hm0 | hmshift
      · exact hSpos 0 M hm0
      · have := hSpos 0 (M - (N : ℤ)) hmshift
        omega
    simpa [Int.toNat_of_nonneg (le_of_lt hMpos)] using hmLift
