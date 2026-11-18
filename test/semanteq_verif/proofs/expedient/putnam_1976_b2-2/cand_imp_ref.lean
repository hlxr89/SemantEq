import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- ===== assumed statement (antecedent) =====
variable (G : Type*) [Group G]
variable (A B : G)

-- Given relations
variable (hA4 : A ^ 4 = 1)
variable (hB7 : B ^ 7 = 1)
variable (hcomm : A * B * A⁻¹ * B = 1)
variable (hA2_ne : A ^ 2 ≠ 1)
variable (hB_ne : B ≠ 1)

theorem problem_statement_assumed : {g : G | ∃ (C : G), C ^ 2 = g} = {1, A ^ 2, B, B ^ 2, B ^ 3, B ^ 4, B ^ 5, B ^ 6} := by
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
  have hsquares := problem_statement_assumed G A B
  rw [hS, hsquares]
  subst word
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hpow (i j : ℕ) (hi : i < 7) (hj : j < 7) (hij : B ^ i = B ^ j) : i = j := by
    apply Nat.ModEq.eq_of_lt_of_lt _ hi hj
    rw [← ho, ← pow_eq_pow_iff_modEq]
    exact hij
  have hAB (n : ℕ) (hn : n < 7) : A ^ 2 ≠ B ^ n := by
    intro heq
    have he : B ^ (n * 2) = 1 := calc
      B ^ (n * 2) = (B ^ n) ^ 2 := by rw [pow_mul]
      _ = (A ^ 2) ^ 2 := by rw [← heq]
      _ = A ^ 4 := by group
      _ = 1 := hA.1
    have hd : 7 ∣ n * 2 := by
      rw [← ho]
      exact orderOf_dvd_of_pow_eq_one he
    obtain ⟨k, hk⟩ := hd
    rcases n with _ | n
    · apply hA.2
      simpa using heq
    · omega
  have hOne (n : ℕ) (hn : n < 7) (hp : 0 < n) : (1 : G) ≠ B ^ n := by
    intro heq
    have := hpow 0 n (by omega) hn (by simpa using heq)
    omega
  have hBB (i j : ℕ) (hi : i < 7) (hj : j < 7) (hij : i ≠ j) : B ^ i ≠ B ^ j := by
    intro heq
    exact hij (hpow i j hi hj heq)
  classical
  constructor
  · let l : List G := [B ^ 0, A ^ 2, B ^ 1, B ^ 2, B ^ 3, B ^ 4, B ^ 5, B ^ 6]
    have hset : {1, A ^ 2, B, B ^ 2, B ^ 3, B ^ 4, B ^ 5, B ^ 6} = (l.toFinset : Set G) := by
      ext x
      simp [l]
    have hnodup : l.Nodup := by
      dsimp [l]
      simp [hOne, hAB, hBB]
      exact ⟨⟨hA.2 ∘ Eq.symm, hB.2 ∘ Eq.symm⟩,
        (by simpa using hAB 1 (by omega)),
        (by simpa using hBB 1 2 (by omega) (by omega) (by omega)),
        (by simpa using hBB 1 3 (by omega) (by omega) (by omega)),
        (by simpa using hBB 1 4 (by omega) (by omega) (by omega)),
        (by simpa using hBB 1 5 (by omega) (by omega) (by omega)),
        (by simpa using hBB 1 6 (by omega) (by omega) (by omega))⟩
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup]
    norm_num [l, putnam_1976_b2_solution]
  · norm_num only [putnam_1976_b2_solution, Set.ext_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false, Prod.fst, Prod.snd, zpow_zero, zpow_ofNat, one_mul, mul_one,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    intro x
    constructor
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨[(0, 0)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(2, 0)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 1)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 2)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 3)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 4)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 5)], by simp, by norm_num [zpow_ofNat]⟩
      · exact ⟨[(0, 6)], by simp, by norm_num [zpow_ofNat]⟩
    · rintro ⟨w, (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl), hx⟩
      all_goals norm_num [zpow_ofNat] at hx
      · left; exact hx.symm
      · right; left; exact hx.symm
      · right; right; left; exact hx.symm
      · right; right; right; left; exact hx.symm
      · right; right; right; right; left; exact hx.symm
      · right; right; right; right; right; left; exact hx.symm
      · right; right; right; right; right; right; left; exact hx.symm
      · right; right; right; right; right; right; right; exact hx.symm
