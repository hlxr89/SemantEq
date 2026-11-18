import Mathlib
open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (G : Type*) [Group G] (A B : G) 
  (h1 : A^4 = 1)
  (h2 : B^7 = 1)
  (h3 : A * B * A⁻¹ * B = 1)
  (h4 : A^2 ≠ 1)
  (h5 : B ≠ 1) :
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
: S.ncard = putnam_1976_b2_solution.1 ∧ S = {word w | w ∈ putnam_1976_b2_solution.2} :=
by
  have h1' : A * B * A⁻¹ * B = 1 := by
    simpa only [zpow_neg, zpow_one] using h1
  have hsquares := problem_statement_assumed G A B hA.1 hB.1 h1' hA.2 hB.2
  have hset : S = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    rw [hS]
    simpa only [Set.ext_iff, Set.mem_setOf_eq, eq_comm] using hsquares
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have horderB : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hBpow : ∀ {i j : ℕ}, i < 7 → j < 7 → B^i = B^j → i = j := by
    intro i j hi hj hij
    have hm := (pow_inj_mod.mp hij)
    rw [horderB, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
    exact hm
  have horderA2 : orderOf (A^2) = 2 := by
    apply orderOf_eq_prime
    · simpa only [← pow_mul] using hA.1
    · exact hA.2
  have hA2Bpow : ∀ i : ℕ, A^2 ≠ B^i := by
    intro i heq
    have hdvd : 2 ∣ 7 := by
      rw [← horderB, ← horderA2, heq]
      exact orderOf_pow_dvd i
    have hnot : ¬ 2 ∣ 7 := by omega -- non-rewrite step
    exact hnot hdvd
  have hBne : ∀ i j : ℕ, i < j → j < 7 → B^i ≠ B^j := by
    intro i j hij hj heq
    have := hBpow (Nat.lt_trans hij hj) hj heq
    omega -- non-rewrite step
  have hBne1 : ∀ j : ℕ, 1 < j → j < 7 → B ≠ B^j := by
    intro j h1j hj heq
    apply hBne 1 j h1j hj
    simpa only [pow_one] using heq
  have hBne0 : ∀ j : ℕ, 0 < j → j < 7 → 1 ≠ B^j := by
    intro j h0j hj heq
    apply hBne 0 j h0j hj
    simpa only [pow_zero] using heq
  have hnB5 : B^5 ∉ ({B^6} : Set G) := by
    simpa only [Set.mem_singleton_iff] using hBne 5 6 (by omega) (by omega)
  have hnB4 : B^4 ∉ ({B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hBne 4 5 (by omega) (by omega), hBne 4 6 (by omega) (by omega)⟩
  have hnB3 : B^3 ∉ ({B^4, B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hBne 3 4 (by omega) (by omega), hBne 3 5 (by omega) (by omega),
      hBne 3 6 (by omega) (by omega)⟩
  have hnB2 : B^2 ∉ ({B^3, B^4, B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hBne 2 3 (by omega) (by omega), hBne 2 4 (by omega) (by omega),
      hBne 2 5 (by omega) (by omega), hBne 2 6 (by omega) (by omega)⟩
  have hnB1 : B ∉ ({B^2, B^3, B^4, B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact And.intro (hBne1 2 (by omega) (by omega))
      ⟨hBne1 3 (by omega) (by omega), hBne1 4 (by omega) (by omega),
       hBne1 5 (by omega) (by omega), hBne1 6 (by omega) (by omega)⟩
  have hnA2 : A^2 ∉ ({B, B^2, B^3, B^4, B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    simpa only [pow_one] using And.intro (hA2Bpow 1)
      ⟨hA2Bpow 2, hA2Bpow 3, hA2Bpow 4, hA2Bpow 5, hA2Bpow 6⟩
  have hn1 : 1 ∉ ({A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact And.intro hA.2.symm
      ⟨hB.2.symm, hBne0 2 (by omega) (by omega), hBne0 3 (by omega) (by omega),
       hBne0 4 (by omega) (by omega), hBne0 5 (by omega) (by omega),
       hBne0 6 (by omega) (by omega)⟩
  constructor
  · rw [hset]
    rw [Set.ncard_insert_of_notMem hn1, Set.ncard_insert_of_notMem hnA2,
      Set.ncard_insert_of_notMem hnB1, Set.ncard_insert_of_notMem hnB2,
      Set.ncard_insert_of_notMem hnB3, Set.ncard_insert_of_notMem hnB4,
      Set.ncard_insert_of_notMem hnB5, Set.ncard_singleton]
  · rw [hset]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨[(0, 0)], Or.inl rfl, by simp only [hword, List.map_cons, zpow_zero,
          pow_zero, mul_one, List.map_nil, List.prod_cons, List.prod_nil]⟩
      · exact ⟨[(2, 0)], Or.inr (Or.inl rfl), by simp only [hword, List.map_cons,
          zpow_ofNat, zpow_zero, pow_zero, mul_one, List.map_nil, List.prod_cons, List.prod_nil]⟩
      · exact ⟨[(0, 1)], Or.inr (Or.inr (Or.inl rfl)), by simp only [hword,
          List.map_cons, zpow_zero, zpow_one, pow_zero, pow_one, one_mul, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]⟩
      · exact ⟨[(0, 2)], Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp only [hword,
          List.map_cons, zpow_zero, zpow_ofNat, pow_zero, one_mul, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one]⟩
      · exact ⟨[(0, 3)], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by
          simp only [hword, List.map_cons, zpow_zero, zpow_ofNat, pow_zero, one_mul, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]⟩
      · exact ⟨[(0, 4)], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by
          simp only [hword, List.map_cons, zpow_zero, zpow_ofNat, pow_zero, one_mul, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]⟩
      · exact ⟨[(0, 5)], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by
          simp only [hword, List.map_cons, zpow_zero, zpow_ofNat, pow_zero, one_mul, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]⟩
      · exact ⟨[(0, 6)], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by
          simp only [hword, List.map_cons, zpow_zero, zpow_ofNat, pow_zero, one_mul, List.map_nil,
            List.prod_cons, List.prod_nil, mul_one]⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        zpow_zero, zpow_one, zpow_ofNat, pow_zero, pow_one, mul_one, one_mul, true_or, or_true]
