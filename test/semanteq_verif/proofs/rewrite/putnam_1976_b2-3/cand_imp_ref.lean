import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed 
  (G : Type*) [Group G] (A B : G)
  (hA : A^4 = 1) (hB : B^7 = 1) (hAB : A * B * A⁻¹ * B = 1) (hA2 : A^2 ≠ 1) (hB_ne_1 : B ≠ 1) : 
  {x : G | ∃ C : G, x = C^2} = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
  sorry

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
  have hsquares := problem_statement_assumed G A B hA.1 hB.1 (by simpa only [zpow_neg, zpow_one] using h1) hA.2 hB.2
  have hS' : S = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    rw [hS]
    ext x
    simp only [Set.mem_setOf_eq]
    rw [show (∃ C : G, C ^ 2 = x) ↔ (∃ C : G, x = C ^ 2) by
      simp only [eq_comm]]
    exact Set.ext_iff.mp hsquares x
  -- non-rewrite step: certify that the eight displayed group elements are distinct
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have horderB : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hA2sq : (A ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, hA.1]
  have horderA2 : orderOf (A ^ 2) = 2 := orderOf_eq_prime hA2sq hA.2
  have hpowB (i j : ℕ) (hi : i < 7) (hj : j < 7) (hij : B ^ i = B ^ j) : i = j := by
    rw [pow_eq_pow_iff_modEq, horderB] at hij
    exact Nat.ModEq.eq_of_lt_of_lt hij hi hj
  have hA2B (i : ℕ) (hi : 0 < i) (hi7 : i < 7) : A ^ 2 ≠ B ^ i := by
    intro heq
    have hBi7 : (B ^ i) ^ 7 = 1 := by
      rw [← pow_mul, mul_comm i 7, pow_mul, hB.1, one_pow]
    have hBi1 : B ^ i ≠ 1 := by
      intro hi1
      have := hpowB i 0 hi7 (by omega) (by simpa only [pow_zero] using hi1)
      omega
    have horderBi : orderOf (B ^ i) = 7 := orderOf_eq_prime hBi7 hBi1
    have hord := congrArg orderOf heq
    rw [horderA2, horderBi] at hord
    norm_num at hord
  have hBne (i j : ℕ) (hi : i < 7) (hj : j < 7) (hij : i ≠ j) : B ^ i ≠ B ^ j := by
    intro heq
    exact hij (hpowB i j hi hj heq)
  have hA2B1 : A ^ 2 ≠ B := by simpa only [pow_one] using hA2B 1 (by decide) (by decide)
  have h1B (i : ℕ) (hi : 0 < i) (hi7 : i < 7) : 1 ≠ B ^ i := by
    simpa only [pow_zero] using hBne 0 i (by decide) hi7 (by omega)
  have hBpow (i : ℕ) (hi : 1 < i) (hi7 : i < 7) : B ≠ B ^ i := by
    simpa only [pow_one] using hBne 1 i (by decide) hi7 (by omega)
  have hncard : ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G).ncard = 8 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_singleton]
    all_goals
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    all_goals
      try simp only [pow_one, Ne.symm hA.2, Ne.symm hB.2, hA2B1,
        h1B 2 (by decide) (by decide), h1B 3 (by decide) (by decide),
        h1B 4 (by decide) (by decide), h1B 5 (by decide) (by decide),
        h1B 6 (by decide) (by decide),
        hBpow 2 (by decide) (by decide), hBpow 3 (by decide) (by decide),
        hBpow 4 (by decide) (by decide), hBpow 5 (by decide) (by decide),
        hBpow 6 (by decide) (by decide),
        hA2B 1 (by decide) (by decide), hA2B 2 (by decide) (by decide),
        hA2B 3 (by decide) (by decide), hA2B 4 (by decide) (by decide),
        hA2B 5 (by decide) (by decide), hA2B 6 (by decide) (by decide),
        hBne 0 2 (by decide) (by decide) (by decide),
        hBne 0 3 (by decide) (by decide) (by decide),
        hBne 0 4 (by decide) (by decide) (by decide),
        hBne 0 5 (by decide) (by decide) (by decide),
        hBne 0 6 (by decide) (by decide) (by decide),
        hBne 1 2 (by decide) (by decide) (by decide),
        hBne 1 3 (by decide) (by decide) (by decide),
        hBne 1 4 (by decide) (by decide) (by decide),
        hBne 1 5 (by decide) (by decide) (by decide),
        hBne 1 6 (by decide) (by decide) (by decide),
        hBne 2 3 (by decide) (by decide) (by decide),
        hBne 2 4 (by decide) (by decide) (by decide),
        hBne 2 5 (by decide) (by decide) (by decide),
        hBne 2 6 (by decide) (by decide) (by decide),
        hBne 3 4 (by decide) (by decide) (by decide),
        hBne 3 5 (by decide) (by decide) (by decide),
        hBne 3 6 (by decide) (by decide) (by decide),
        hBne 4 5 (by decide) (by decide) (by decide),
        hBne 4 6 (by decide) (by decide) (by decide),
        hBne 5 6 (by decide) (by decide) (by decide), pow_zero,
        not_false_eq_true, true_and]
  constructor
  · rw [hS', hncard]
  · rw [hS', hword]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨[(0, 0)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(2, 0)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one]⟩
      · exact ⟨[(0, 1)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_one, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(0, 2)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(0, 3)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(0, 4)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(0, 5)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one, one_mul]⟩
      · exact ⟨[(0, 6)], by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero, zpow_ofNat, pow_zero, mul_one, one_mul]⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, zpow_zero,
          zpow_one, zpow_ofNat, pow_zero, pow_one, mul_one, one_mul, true_or, or_true]
