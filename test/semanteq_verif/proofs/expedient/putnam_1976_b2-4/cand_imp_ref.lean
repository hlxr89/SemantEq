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
set_option maxHeartbeats 1000000 in
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
  have hord : orderOf B = 7 := by
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hB.1 hB.2
  have hbpows : ∀ {m n : ℕ}, m < 7 → n < 7 → B ^ m = B ^ n → m = n := by
    intro m n hm hn heq
    apply Nat.ModEq.eq_of_lt_of_lt _ hm hn
    rw [← hord]
    exact pow_eq_pow_iff_modEq.mp heq
  have hconj : A * B * A⁻¹ = B⁻¹ := eq_inv_of_mul_eq_one_left (by simpa using h1)
  have hApows : ∀ {k : ℕ}, k < 7 → A ^ 2 ≠ B ^ k := by
    intro k hk hAk
    have hinv : B ^ k = (B ^ k)⁻¹ := by
      calc
        B ^ k = A ^ 2 := hAk.symm
        _ = A * A ^ 2 * A⁻¹ := by group
        _ = A * B ^ k * A⁻¹ := by rw [hAk]
        _ = (A * B * A⁻¹) ^ k := conj_pow.symm
        _ = (B⁻¹) ^ k := by rw [hconj]
        _ = (B ^ k)⁻¹ := inv_pow B k
    have hsq : (B ^ k) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [hinv]
      simp
    have hd : 7 ∣ k * 2 := by
      rw [← hord, orderOf_dvd_iff_pow_eq_one]
      simpa [pow_mul] using hsq
    have hk0 : k = 0 := by omega
    subst k
    apply hA.2
    simpa using hAk
  have hsquares : S = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    rw [hS]
    simpa [eq_comm] using
      (problem_statement_assumed G A B hA.1 hB.1 (by simpa using h1) hA.2 hB.2)
  constructor
  · rw [hsquares]
    let t : Finset G := (Finset.range 7).image (fun k => B ^ k)
    have htcard : t.card = 7 := by
      dsimp [t]
      rw [Finset.card_image_iff.mpr]
      · simp
      · rintro m hm n hn heq
        simp only [Finset.mem_coe, Finset.mem_range] at hm hn
        exact hbpows hm hn heq
    have hAnot : A ^ 2 ∉ t := by
      simp only [t, Finset.mem_image, Finset.mem_range, not_exists, and_imp]
      rintro k ⟨hk, heq⟩
      exact hApows hk heq.symm
    have hset : {1, A^2, B, B^2, B^3, B^4, B^5, B^6} =
        (↑(insert (A ^ 2) t) : Set G) := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
        Finset.mem_insert, t, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        · right; exact ⟨0, by norm_num, by simp⟩
        · exact Or.inl rfl
        · right; exact ⟨1, by norm_num, by simp⟩
        · right; exact ⟨2, by norm_num, rfl⟩
        · right; exact ⟨3, by norm_num, rfl⟩
        · right; exact ⟨4, by norm_num, rfl⟩
        · right; exact ⟨5, by norm_num, rfl⟩
        · right; exact ⟨6, by norm_num, rfl⟩
      · rintro (rfl | ⟨k, hk, rfl⟩)
        · simp
        · interval_cases k <;> simp
    change Set.ncard ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G) = 8
    rw [hset, Set.ncard_coe_finset]
    rw [Finset.card_insert_of_notMem hAnot, htcard]
  · rw [hsquares, hword]
    ext x
    simp [putnam_1976_b2_solution, eq_comm, zpow_ofNat]
