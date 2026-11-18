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
  have gcd_bridge (n : ℕ) :
      d_n n = Int.gcd (Int.gcd (Int.gcd ((_root_.A ^ n - 1) 0 0)
        ((_root_.A ^ n - 1) 0 1)) ((_root_.A ^ n - 1) 1 0))
        ((_root_.A ^ n - 1) 1 1) := by
    have intfold (l : List ℤ) (acc : ℕ) :
        List.foldl (fun acc x => Int.gcd acc x) acc l =
          (l.map Int.natAbs).foldl Nat.gcd acc := by
      induction l generalizing acc with -- non-rewrite step
      | nil => rfl
      | cons a l ih =>
          simp only [List.foldl_cons, List.map_cons]
          rw [ih]
          simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    have natfold (l : List ℕ) : l.foldl Nat.gcd 0 = l.toFinset.gcd id := by
      rw [List.foldl_eq_foldr]
      induction l with -- non-rewrite step
      | nil => simp only [List.foldr_nil, List.toFinset_nil, Finset.gcd_empty]
      | cons a l ih =>
          simp only [List.foldr_cons, List.toFinset_cons, Finset.gcd_insert, id_eq, ih]
          change a.gcd (l.toFinset.gcd id) = a.gcd (l.toFinset.gcd id)
          rfl
    simp only [d_n]
    rw [intfold, natfold]
    have fin_bridge (s : Finset ℤ) :
        (List.map Int.natAbs
          (List.flatMap (fun a : ℕ => [(a : ℤ)])
            (List.map Int.natAbs s.toList))).toFinset = s.image Int.natAbs := by
      ext x
      simp only [List.mem_toFinset, List.mem_map, List.mem_flatMap,
        List.mem_singleton, Finset.mem_toList, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨a, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(z.natAbs : ℤ), ⟨z.natAbs, ⟨z, hz, rfl⟩, rfl⟩,
          Int.natAbs_natCast z.natAbs⟩
    simp only [List.bind_eq_flatMap, List.pure_def]
    rw [fin_bridge, Finset.gcd_image, Finset.gcd_image]
    have huniv : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0, 0), (0, 1), (1, 0), (1, 1)} := by
      rw [← Finset.univ_product_univ, Finset.univ_fin2]
      rfl
    rw [huniv]
    simp only [Finset.gcd_insert, Finset.gcd_singleton, Function.comp_apply,
      _root_.A, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, sub_zero, Int.gcd_eq_natAbs,
      Int.natAbs_natCast, id_eq, normalize_eq]
    change Nat.gcd _ (Nat.gcd _ (Nat.gcd _ _)) =
      (Nat.gcd (Nat.gcd _ _) _).gcd _
    rw [Nat.gcd_assoc, Nat.gcd_assoc]
  have hAeq : A = _root_.A := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa only [_root_.A] using hA.1
    · simpa only [_root_.A] using hA.2.1
    · simpa only [_root_.A] using hA.2.2.1
    · simpa only [_root_.A] using hA.2.2.2
  have d_eq (n : ℕ) (hn : n ≥ 1) : d n = (d_n n : ℤ) := by
    rw [hd n hn, hmatgcd, hAeq]
    exact congrArg (fun x : ℕ => (x : ℤ)) (gcd_bridge n).symm
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := problem_statement_assumed b.natAbs
  rw [Filter.eventually_atTop]
  refine ⟨max N 1, ?_⟩
  intro n hn
  rw [d_eq n (le_trans (le_max_right N 1) hn)]
  exact le_trans Int.le_natAbs (by exact_mod_cast hN n (le_trans (le_max_left N 1) hn))
