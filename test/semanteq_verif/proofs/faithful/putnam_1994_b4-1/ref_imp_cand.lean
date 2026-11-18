import Mathlib

open Filter Topology

-- ===== unified context (both sides' local defs, merged) =====

noncomputable section

-- Define the matrix A
def A : Matrix (Fin 2) (Fin 2) ℤ := !![3, 2; 4, 3]

-- Define d_n as the GCD of all entries of A^n - I
def d_n (n : ℕ) : ℕ := 
  let M := A ^ n - 1
  let entries := (Finset.univ : Finset (Fin 2 × Fin 2)).image (fun p => M p.1 p.2)
  let abs_entries := List.map (fun x => Int.natAbs x) (Finset.toList entries)
  List.foldl (fun acc x => Int.gcd acc x) 0 abs_entries

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
theorem problem_statement : 
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → d_n n ≥ M := by
  have hbridge (M : Matrix (Fin 2) (Fin 2) ℤ) :
      (let entries := (Finset.univ : Finset (Fin 2 × Fin 2)).image (fun p => M p.1 p.2)
       let abs_entries := List.map (fun x => Int.natAbs x) (Finset.toList entries)
       List.foldl (fun acc x => Int.gcd acc x) 0 abs_entries) =
        Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1) := by
    classical
    let entries := (Finset.univ : Finset (Fin 2 × Fin 2)).image (fun p => M p.1 p.2)
    have hfold (l : List ℕ) : List.foldl Nat.gcd 0 l = (l : Multiset ℕ).gcd := by
      rw [List.foldl_eq_foldr]
      induction l with
      | nil => simp
      | cons a l ih =>
        change Nat.gcd a (List.foldr Nat.gcd 0 l) = Nat.gcd a (l : Multiset ℕ).gcd
        rw [ih]
    have hcoerce (l : List ℕ) :
        List.foldl (fun (acc : ℕ) (x : ℤ) => Int.gcd acc x) 0 (l : List ℤ) =
          (l : Multiset ℕ).gcd := by
      have haux (a : ℕ) :
          List.foldl (fun (acc : ℕ) (x : ℤ) => Int.gcd acc x) a (l : List ℤ) =
            List.foldl Nat.gcd a l := by
        induction l generalizing a with
        | nil => simp
        | cons x l ih =>
          change List.foldl (fun (acc : ℕ) (y : ℤ) => Int.gcd acc y)
            (Nat.gcd a x) (l : List ℤ) = List.foldl Nat.gcd (Nat.gcd a x) l
          exact ih _
      rw [haux, hfold]
    rw [show (let abs_entries := List.map (fun x => Int.natAbs x) (Finset.toList entries)
              List.foldl (fun acc x => Int.gcd acc x) 0 abs_entries) =
            entries.gcd Int.natAbs by
      dsimp only [entries]
      rw [hcoerce]
      rw [Finset.gcd_def, ← Finset.coe_toList]
      rfl]
    subst entries
    rw [Finset.gcd_image]
    have huniv : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
    rw [huniv]
    simp only [Finset.gcd_insert, Finset.gcd_singleton, Function.comp_apply]
    simp only [Int.gcd_eq_natAbs]
    simp only [Int.natAbs_natCast, normalize_apply]
    ac_rfl
  have ht : Tendsto (fun n => (d_n n : ℤ)) atTop atTop := by
    apply putnam_1994_b4_assumed
        (fun M => Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1))
        A (fun n => d_n n)
    · intro M
      rfl
    · norm_num [A]
    · intro n hn
      exact_mod_cast hbridge (A ^ n - 1)
  intro M
  rw [← eventually_atTop]
  exact (Filter.tendsto_atTop.1 ht (M : ℤ)).mono (by
    intro n hn
    exact_mod_cast hn)
