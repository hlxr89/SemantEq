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

lemma dvd_foldl_gcd (k a : ℕ) (l : List ℕ) :
    k ∣ l.foldl Nat.gcd a ↔ k ∣ a ∧ ∀ x ∈ l, k ∣ x := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
      rw [List.foldl_cons, ih]
      simp only [Nat.dvd_gcd_iff, List.mem_cons, forall_eq_or_imp]
      aesop

lemma fold_int_gcd_eq (a : ℕ) (l : List ℕ) :
    l.foldl (fun acc x => Int.gcd acc x) a = l.foldl Nat.gcd a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
      simp only [List.foldl_cons]
      exact ih _

lemma foldl_gcd_dvd (a : ℕ) (l : List ℕ) :
    l.foldl Nat.gcd a ∣ a ∧ ∀ x ∈ l, l.foldl Nat.gcd a ∣ x := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
      rw [List.foldl_cons]
      have h := ih (Nat.gcd a x)
      constructor
      · exact dvd_trans h.1 (Nat.gcd_dvd_left _ _)
      · intro y hy
        by_cases hxy : y = x
        · subst y
          exact dvd_trans h.1 (Nat.gcd_dvd_right _ _)
        · exact h.2 y ((List.mem_cons.mp hy).resolve_left hxy)

lemma candidate_gcd_eq (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (let entries := (Finset.univ : Finset (Fin 2 × Fin 2)).image (fun p => M p.1 p.2)
     let abs_entries := List.map (fun x => Int.natAbs x) (Finset.toList entries)
     List.foldl (fun acc x => Int.gcd acc x) 0 abs_entries) =
    Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1) := by
  rw [fold_int_gcd_eq]
  simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · apply Nat.dvd_gcd
      · apply Nat.dvd_gcd
        · apply (foldl_gcd_dvd _ _).2
          simp only [List.mem_map]
          refine ⟨M 0 0, ?_, rfl⟩
          simp
        · apply (foldl_gcd_dvd _ _).2
          simp only [List.mem_map]
          refine ⟨M 0 1, ?_, rfl⟩
          simp
      · apply (foldl_gcd_dvd _ _).2
        simp only [List.mem_map]
        refine ⟨M 1 0, ?_, rfl⟩
        simp
    · apply (foldl_gcd_dvd _ _).2
      simp only [List.mem_map]
      refine ⟨M 1 1, ?_, rfl⟩
      simp
  · rw [dvd_foldl_gcd]
    constructor
    · simp
    · intro x hx
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_image, Finset.mem_univ,
        true_and] at hx
      obtain ⟨y, ⟨p, rfl⟩, rfl⟩ := hx
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j
      · exact dvd_trans (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      · exact dvd_trans (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
      · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      · exact Nat.gcd_dvd_right _ _

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → d_n n ≥ M := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1994_b4
(matgcd : Matrix (Fin 2) (Fin 2) ℤ → ℤ)
(A : Matrix (Fin 2) (Fin 2) ℤ)
(d : ℕ → ℤ)
(hmatgcd : ∀ M, matgcd M = Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1))
(hA : A 0 0 = 3 ∧ A 0 1 = 2 ∧ A 1 0 = 4 ∧ A 1 1 = 3)
(hd : ∀ n ≥ 1, d n = matgcd (A ^ n - 1))
: Tendsto d atTop atTop := by
  have hAA : A = _root_.A := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hA.1
    · exact hA.2.1
    · exact hA.2.2.1
    · exact hA.2.2.2
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := problem_statement_assumed b.natAbs
  apply Filter.eventually_atTop.mpr
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : n ≥ N := le_trans (le_max_left _ _) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right _ _) hn
  have hdn : d n = (d_n n : ℤ) := by
    rw [hd n hn1, hmatgcd, hAA]
    exact_mod_cast (candidate_gcd_eq (_root_.A ^ n - 1)).symm
  rw [hdn]
  have hb : b ≤ (b.natAbs : ℤ) := Int.le_natAbs
  exact le_trans hb (by exact_mod_cast hN n hnN)
