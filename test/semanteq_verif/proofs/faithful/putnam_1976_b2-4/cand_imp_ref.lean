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
: S.ncard = putnam_1976_b2_solution.1 ∧ S = {word w | w ∈ putnam_1976_b2_solution.2} := by
  classical
  have h3 : A * B * A⁻¹ * B = 1 := by
    simpa using h1
  have hcand := problem_statement_assumed G A B hA.1 hB.1 h3 hA.2 hB.2
  have hsq : {g : G | ∃ C : G, C^2 = g} =
      {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    simpa [eq_comm] using hcand
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hBorder : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hBpow_ne {i j : ℕ} (hi : i < 7) (hj : j < 7) (hij : i ≠ j) :
      B ^ i ≠ B ^ j := by
    intro heq
    apply hij
    have hm := (pow_eq_pow_iff_modEq).mp heq
    rw [hBorder] at hm
    exact Nat.ModEq.eq_of_lt_of_lt hm hi hj
  have hA2order : orderOf (A^2) = 2 := by
    apply orderOf_eq_prime
    · simpa [← pow_mul] using hA.1
    · exact hA.2
  have hA2_ne_Bpow {k : ℕ} : A^2 ≠ B^k := by
    intro heq
    have hp : (A^2)^7 = 1 := by
      rw [heq, ← pow_mul, Nat.mul_comm, pow_mul, hB.1, one_pow]
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hA2order] at hd
    norm_num at hd
  have hcard : ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G).ncard = 8 := by
    let f : Fin 8 → G := fun i => if (i : ℕ) = 7 then A^2 else B^(i : ℕ)
    refine Set.ncard_eq_of_bijective (fun i hi => f ⟨i, hi⟩) ?_ ?_ ?_
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h | h | h | h | h | h | h | h
      · exact ⟨0,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨7,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨1,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨2,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨3,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨4,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨5,  by omega, by simpa [f] using h.symm⟩
      · exact ⟨6,  by omega, by simpa [f] using h.symm⟩
    · intro i hi
      interval_cases i <;> simp [f]
    · intro i j hi hj heq
      by_cases hi7 : i = 7
      · subst i
        by_cases hj7 : j = 7
        · exact hj7.symm
        · simp [f, hj7] at heq
          exact False.elim (hA2_ne_Bpow heq)
      · by_cases hj7 : j = 7
        · subst j
          simp [f, hi7] at heq
          exact False.elim (hA2_ne_Bpow heq.symm)
        · simp [f, hi7, hj7] at heq
          by_contra hij
          exact hBpow_ne (by omega) (by omega) hij heq
  have hwords : {word w | w ∈ putnam_1976_b2_solution.2} =
      ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G) := by
    rw [hword]
    ext g
    simp [putnam_1976_b2_solution, eq_comm, zpow_ofNat]
  constructor
  · rw [hS, hsq]
    exact hcard
  · rw [hS, hsq, hwords]
