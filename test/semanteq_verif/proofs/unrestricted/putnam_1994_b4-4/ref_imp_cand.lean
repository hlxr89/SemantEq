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
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : ∀ M : ℕ, ∃ n : ℕ, n ≥ 1 ∧ d_n n ≥ M := by
  have univ_gcd (M : Matrix (Fin 2) (Fin 2) ℤ) :
      (Finset.univ : Finset (Fin 2 × Fin 2)).gcd
          (fun p => Int.natAbs (M p.1 p.2)) =
        Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1) := by
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · apply Nat.dvd_gcd
        · apply Nat.dvd_gcd
          · exact Finset.gcd_dvd (Finset.mem_univ (0, 0))
          · exact Finset.gcd_dvd (Finset.mem_univ (0, 1))
        · exact Finset.gcd_dvd (Finset.mem_univ (1, 0))
      · exact Finset.gcd_dvd (Finset.mem_univ (1, 1))
    · apply Finset.dvd_gcd
      intro p hp
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j
      · exact (Nat.gcd_dvd_left _ _).trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      · exact (Nat.gcd_dvd_left _ _).trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      · exact Nat.gcd_dvd_right _ _
  let matgcd : Matrix (Fin 2) (Fin 2) ℤ → ℤ := fun M =>
    Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1)
  have hlim : Tendsto (fun n => (d_n n : ℤ)) atTop atTop := by
    apply putnam_1994_b4_assumed matgcd A (fun n => (d_n n : ℤ))
    · intro X
      rfl
    · native_decide
    · intro n hn
      simp only [d_n, matgcd]
      exact_mod_cast univ_gcd (A ^ n - 1)
  intro M
  have hev := (tendsto_atTop.1 hlim) (M : ℤ)
  rcases (hev.and (eventually_ge_atTop (1 : ℕ))).exists with ⟨n, hn, hn1⟩
  exact ⟨n, hn1, by exact_mod_cast hn⟩
