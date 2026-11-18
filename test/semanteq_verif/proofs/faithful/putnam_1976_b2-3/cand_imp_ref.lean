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
  classical
  have hsquares := problem_statement_assumed G A B hA.1 hB.1 (by simpa using h1) hA.2 hB.2
  have hset : S = {1, A^2, B, B^2, B^3, B^4, B^5, B^6} := by
    rw [hS]
    simpa [eq_comm] using hsquares
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have horder : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hBpow (n : ℕ) (hn : 0 < n) (hn7 : n < 7) : B ^ n ≠ 1 := by
    intro he
    have hd : orderOf B ∣ n := (orderOf_dvd_iff_pow_eq_one).2 he
    rw [horder] at hd
    omega
  have hBpow_ne (i j : ℕ) (hij : i < j) (hj7 : j < 7) : B ^ i ≠ B ^ j := by
    intro he
    have hp : B ^ (j - i) = 1 := by
      have hj : B ^ j = B ^ i * B ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hij)]
      calc
        B ^ (j - i) = (B ^ i)⁻¹ * B ^ j := by
          rw [hj]
          simp
        _ = 1 := by rw [← he]; simp
    exact hBpow (j - i) (Nat.sub_pos_of_lt hij) (lt_of_le_of_lt (Nat.sub_le j i) hj7) hp
  have hconj : A * B * A⁻¹ = B⁻¹ := by
    calc
      A * B * A⁻¹ = (A * B * A⁻¹ * B) * B⁻¹ := by group
      _ = B⁻¹ := by rw [show A * B * A⁻¹ * B = 1 by simpa using h1]; simp
  have hconjpow (i : ℕ) : A * (B ^ i) * A⁻¹ = (B ^ i)⁻¹ := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ]
        calc
          A * (B ^ i * B) * A⁻¹ =
              (A * B ^ i * A⁻¹) * (A * B * A⁻¹) := by group
          _ = (B ^ i)⁻¹ * B⁻¹ := by rw [ih, hconj]
          _ = (B ^ i * B)⁻¹ := by rw [mul_inv_rev]; group
  have hA2_ne_Bpow (i : ℕ) (hi : i < 7) : A ^ 2 ≠ B ^ i := by
    by_cases hi0 : i = 0
    · simpa [hi0] using hA.2
    · intro he
      have hself : B ^ i = (B ^ i)⁻¹ := by
        calc
          B ^ i = A ^ 2 := he.symm
          _ = A * (A ^ 2) * A⁻¹ := by group
          _ = A * (B ^ i) * A⁻¹ := by rw [he]
          _ = (B ^ i)⁻¹ := hconjpow i
      have hp : B ^ (2 * i) = 1 := by
        calc
          B ^ (2 * i) = (B ^ i) ^ 2 := by rw [mul_comm, pow_mul]
          _ = B ^ i * B ^ i := pow_two _
          _ = B ^ i * (B ^ i)⁻¹ := congrArg (fun x => B ^ i * x) hself
          _ = 1 := mul_inv_cancel _
      have hd : orderOf B ∣ 2 * i := (orderOf_dvd_iff_pow_eq_one).2 hp
      rw [horder] at hd
      omega
  constructor
  · rw [hset]
    change ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G).ncard = 8
    let T : Finset G := {1, A^2, B, B^2, B^3, B^4, B^5, B^6}
    rw [show ({1, A^2, B, B^2, B^3, B^4, B^5, B^6} : Set G) = ↑T by
      ext x
      simp [T]]
    rw [Set.ncard_coe_finset]
    let U : Finset G := (Finset.range 7).image (fun i => B ^ i)
    have hcardU : U.card = 7 := by
      change ((Finset.range 7).image (fun i => B ^ i)).card = 7
      have hinj : Set.InjOn (fun i : ℕ => B ^ i) (Finset.range 7) := by
        intro i hi j hj he
        have hi' : i < 7 := Finset.mem_range.mp hi
        have hj' : j < 7 := Finset.mem_range.mp hj
        rcases lt_trichotomy i j with hij | hij | hij
        · exact (hBpow_ne i j hij hj' he).elim
        · exact hij
        · exact (hBpow_ne j i hij hi' he.symm).elim
      calc
        ((Finset.range 7).image (fun i => B ^ i)).card = (Finset.range 7).card :=
          Finset.card_image_iff.mpr hinj
        _ = 7 := rfl
    have hTU : T = insert (A ^ 2) U := by
      ext x
      simp only [T, Finset.mem_insert, Finset.mem_singleton, U, Finset.mem_image,
        Finset.mem_range]
      constructor
      · intro hx
        rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
        · right; exact ⟨0, by omega, by simpa using hx.symm⟩
        · exact Or.inl hx
        · right; exact ⟨1, by omega, by simpa using hx.symm⟩
        · right; exact ⟨2, by omega, hx.symm⟩
        · right; exact ⟨3, by omega, hx.symm⟩
        · right; exact ⟨4, by omega, hx.symm⟩
        · right; exact ⟨5, by omega, hx.symm⟩
        · right; exact ⟨6, by omega, hx.symm⟩
      · rintro (hx | ⟨i, hi, rfl⟩)
        · exact Or.inr (Or.inl hx)
        · interval_cases i <;> simp
    have hnot : A ^ 2 ∉ U := by
      simp only [U, Finset.mem_image, Finset.mem_range, not_exists, not_and]
      intro i hi he
      exact hA2_ne_Bpow i hi he.symm
    rw [hTU]
    calc
      (insert (A ^ 2) U).card = U.card + 1 := Finset.card_insert_of_notMem hnot
      _ = 8 := by rw [hcardU]
  · rw [hset, hword]
    ext x
    simp [putnam_1976_b2_solution, eq_comm, zpow_ofNat]
