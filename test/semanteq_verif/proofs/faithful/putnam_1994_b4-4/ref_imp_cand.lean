import Mathlib

open Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
def A : Matrix (Fin 2) (Fin 2) ℤ := !![3, 2; 4, 3]

def d_n (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin 2 × Fin 2)).gcd (fun p : Fin 2 × Fin 2 => Int.natAbs ((A ^ n - 1) p.1 p.2))

-- ===== assumed statement (antecedent) =====
theorem putnam_1994_b4_assumed
(matgcd : Matrix (Fin 2) (Fin 2) ℤ → ℤ)
(A : Matrix (Fin 2) (Fin 2) ℤ)
(d : ℕ → ℤ)
(hmatgcd : ∀ M, matgcd M = Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1))
(hA : A 0 0 = 3 ∧ A 0 1 = 2 ∧ A 1 0 = 4 ∧ A 1 1 = 3)
(hd : ∀ n ≥ 1, d n = matgcd (A ^ n - 1))
: Tendsto d atTop atTop :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : ∀ M : ℕ, ∃ n : ℕ, n ≥ 1 ∧ d_n n ≥ M := by
  let matgcd : Matrix (Fin 2) (Fin 2) ℤ → ℤ := fun M =>
    Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1)
  let d : ℕ → ℤ := fun n => d_n n
  have hgcd (M : Matrix (Fin 2) (Fin 2) ℤ) :
      (Finset.univ : Finset (Fin 2 × Fin 2)).gcd
          (fun p : Fin 2 × Fin 2 => Int.natAbs (M p.1 p.2)) =
        Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1) := by
    rw [show (Finset.univ : Finset (Fin 2 × Fin 2)) =
      {(0, 0), (0, 1), (1, 0), (1, 1)} by decide]
    simp only [Finset.gcd_insert, Finset.gcd_singleton]
    change Nat.gcd _ (Nat.gcd _ (Nat.gcd _ _)) = _
    simp [Int.gcd, Nat.gcd_assoc]
  have hd : ∀ n ≥ 1, d n = matgcd (A ^ n - 1) := by
    intro n hn
    change (d_n n : ℤ) = _
    rw [d_n]
    dsimp [matgcd]
    exact_mod_cast hgcd (A ^ n - 1)
  have ht : Tendsto d atTop atTop :=
    putnam_1994_b4_assumed matgcd A d (by intro M; rfl) (by simp [A]) hd
  intro M
  have hev : ∀ᶠ n : ℕ in atTop, (M : ℤ) ≤ d n :=
    (Filter.tendsto_atTop.1 ht) M
  rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
  let n := max N 1
  refine ⟨n, le_max_right _ _, ?_⟩
  have h := hN n (le_max_left _ _)
  change (M : ℤ) ≤ (d_n n : ℤ) at h
  exact_mod_cast h
