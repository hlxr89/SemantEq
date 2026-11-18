import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- ===== assumed statement (antecedent) =====
variable (G : Type*) [Group G] (A B : G)
(hA : A^4 = 1) (hB : B^7 = 1) (hAB : A * B * A⁻¹ * B = 1) (hA2 : A^2 ≠ 1) (hB_ne_1 : B ≠ 1)

theorem problem_statement_assumed : 
  {x : G | ∃ C : G, x = C^2} = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1976_b2
(G : Type*) [Group G]
(A B : G)
(word : List (ℤ × ℤ) → G)
(hword : word = fun w : List (ℤ × ℤ) => (List.map (fun t : ℤ × ℤ => A^(t.1)*B^(t.2)) w).prod)
(hG : ∀ g : G, ∃ w : List (ℤ × ℤ), g = word w)
(hA : A^4 = 1 ∧ A^2 ≠ 1)
(hB : B^7 = 1 ∧ B ≠ 1)
(h1 : A*B*A^(-(1 : ℤ))*B = 1)
(S : Set G)
(hS : S = {g : G | ∃ C : G, C^2 = g})
: S.ncard = putnam_1976_b2_solution.1 ∧ S = {word w | w ∈ putnam_1976_b2_solution.2} := by
  have hsquares := problem_statement_assumed G A B
  have hSB : S = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    rw [hS]
    simpa [eq_comm] using hsquares
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hBo : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hBpow (i j : ℕ) (hi : i < 7) (hj : j < 7) (hij : i ≠ j) : B^i ≠ B^j := by
    intro he
    have hm := (pow_eq_pow_iff_modEq).mp he
    rw [hBo] at hm
    exact hij (Nat.ModEq.eq_of_lt_of_lt hm hi hj)
  have hABpow (i : ℕ) (hi : i < 7) : A^2 ≠ B^i := by
    by_cases hi0 : i = 0
    · subst i
      simpa using hA.2
    intro he
    have he2 : (B^i)^2 = 1 := by
      rw [← he, ← pow_mul]
      norm_num
      exact hA.1
    have hd : orderOf B ∣ i * 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_mul] using he2)
    rw [hBo] at hd
    interval_cases i
    all_goals first | exact hi0 rfl | norm_num at hd
  constructor
  · rw [hSB]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hA.2.symm,
        by simpa using hBpow 0 1 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 0 2 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 0 3 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 0 4 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 0 5 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 0 6 (by norm_num) (by norm_num) (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by simpa using hABpow 1 (by norm_num),
        hABpow 2 (by norm_num), hABpow 3 (by norm_num),
        hABpow 4 (by norm_num), hABpow 5 (by norm_num), hABpow 6 (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by simpa using hBpow 1 2 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 1 3 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 1 4 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 1 5 (by norm_num) (by norm_num) (by norm_num),
        by simpa using hBpow 1 6 (by norm_num) (by norm_num) (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hBpow 2 3 (by norm_num) (by norm_num) (by norm_num),
        hBpow 2 4 (by norm_num) (by norm_num) (by norm_num),
        hBpow 2 5 (by norm_num) (by norm_num) (by norm_num),
        hBpow 2 6 (by norm_num) (by norm_num) (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hBpow 3 4 (by norm_num) (by norm_num) (by norm_num),
        hBpow 3 5 (by norm_num) (by norm_num) (by norm_num),
        hBpow 3 6 (by norm_num) (by norm_num) (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hBpow 4 5 (by norm_num) (by norm_num) (by norm_num),
        hBpow 4 6 (by norm_num) (by norm_num) (by norm_num)⟩)]
    rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hBpow 5 6 (by norm_num) (by norm_num) (by norm_num))]
    simp [putnam_1976_b2_solution]
  · rw [hSB, hword]
    ext x
    simp [putnam_1976_b2_solution]
    simp only [eq_comm]
    simp only [zpow_ofNat]
