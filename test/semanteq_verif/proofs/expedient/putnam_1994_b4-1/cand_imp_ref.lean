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
  have hfold (s : Finset ℤ) :
      List.foldl (fun acc x => Int.gcd acc x) 0
          (List.map (fun x => (Int.natAbs x : ℤ)) s.toList) =
        s.gcd Int.natAbs := by
    rw [Finset.gcd_def]
    calc
      _ = (Multiset.map Int.natAbs (↑s.toList : Multiset ℤ)).gcd := by
        rw [Multiset.gcd, Multiset.fold_eq_foldl, Multiset.map_coe,
          Multiset.coe_foldl, List.foldl_map, List.foldl_map]
        congr 1
      _ = (Multiset.map Int.natAbs s.val).gcd := by
        change (Multiset.map Int.natAbs (↑s.val.toList : Multiset ℤ)).gcd = _
        rw [Multiset.coe_toList]
  have hentries (M : Matrix (Fin 2) (Fin 2) ℤ) :
      ((Finset.univ : Finset (Fin 2 × Fin 2)).image
          (fun p => M p.1 p.2)).gcd Int.natAbs =
        Int.gcd (Int.gcd (Int.gcd (M 0 0) (M 0 1)) (M 1 0)) (M 1 1) := by
    rw [Finset.gcd_image]
    have hu : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0, 0), (0, 1), (1, 0), (1, 1)} := by native_decide
    rw [hu]
    simp [gcd_eq_nat_gcd, Int.gcd_eq_natAbs, Nat.gcd_comm, Nat.gcd_left_comm]
  have hdngcd (n : ℕ) :
      d_n n = Int.gcd (Int.gcd (Int.gcd ((_root_.A ^ n - 1) 0 0) ((_root_.A ^ n - 1) 0 1))
        ((_root_.A ^ n - 1) 1 0)) ((_root_.A ^ n - 1) 1 1) := by
    rw [d_n]
    change List.foldl (fun acc x => Int.gcd acc x) 0
      (List.flatMap (fun a : ℕ => [(a : ℤ)])
        (List.map (fun x => Int.natAbs x)
          ((Finset.univ : Finset (Fin 2 × Fin 2)).image
            (fun p => (_root_.A ^ n - 1) p.1 p.2)).toList)) = _
    rw [List.flatMap_map]
    change List.foldl (fun acc x => Int.gcd acc x) 0
      (List.flatMap (pure ∘ (fun a : ℤ => (a.natAbs : ℤ)))
        ((Finset.univ : Finset (Fin 2 × Fin 2)).image
          (fun p => (_root_.A ^ n - 1) p.1 p.2)).toList) = _
    rw [List.flatMap_pure_eq_map]
    rw [hfold]
    exact hentries _
  have hAeq : A = _root_.A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [_root_.A, hA]
  have hdeq (n : ℕ) (hn : n ≥ 1) : d n = (d_n n : ℤ) := by
    rw [hd n hn, hmatgcd, hAeq]
    exact_mod_cast (hdngcd n).symm
  apply Filter.tendsto_atTop.2
  intro b
  rcases problem_statement_assumed b.natAbs with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : n ≥ N := le_trans (le_max_left _ _) hn
  have hn1 : n ≥ 1 := le_trans (le_max_right _ _) hn
  calc
    b ≤ (b.natAbs : ℤ) := Int.le_natAbs
    _ ≤ (d_n n : ℕ) := by exact_mod_cast hN n hnN
    _ = d n := (hdeq n hn1).symm
