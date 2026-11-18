import Mathlib

open Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (G : Type*) [Group G]
(A B : G)
(hA4 : A ^ 4 = 1)
(hB7 : B ^ 7 = 1)
(hcomm : A * B * A⁻¹ * B = 1)
(hA2_ne : A ^ 2 ≠ 1)
(hB_ne : B ≠ 1) : {g : G | ∃ (C : G), C ^ 2 = g} = {1, A ^ 2, B, B ^ 2, B ^ 3, B ^ 4, B ^ 5, B ^ 6} := by
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
  have hcomm : A * B * A⁻¹ * B = 1 := by simpa using h1
  have hcand := problem_statement_assumed G A B hA.1 hB.1 hcomm hA.2 hB.2
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have horder : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hconj : A * B * A⁻¹ = B⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact hcomm
  have hAB : A * B = B⁻¹ * A := by
    calc
      A * B = (A * B * A⁻¹) * A := by simp [mul_assoc]
      _ = B⁻¹ * A := by rw [hconj]
  have hABpow : ∀ n : ℕ, A * B ^ n = (B⁻¹) ^ n * A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        calc
          A * (B ^ n * B) = (A * B ^ n) * B := by rw [mul_assoc]
          _ = ((B⁻¹) ^ n * A) * B := by rw [ih]
          _ = (B⁻¹) ^ (n + 1) * A := by rw [mul_assoc, hAB, pow_succ]; simp [mul_assoc]
  have hA2_ne_Bpow : ∀ {n : ℕ}, n < 7 → A ^ 2 ≠ B ^ n := by
    intro n hn heq
    have hinv : B ^ n = (B⁻¹) ^ n := by
      calc
        B ^ n = A ^ 2 := heq.symm
        _ = A * (A ^ 2) * A⁻¹ := by group
        _ = A * B ^ n * A⁻¹ := by rw [heq]
        _ = (B⁻¹) ^ n := by rw [hABpow]; simp
    have hp : B ^ (2 * n) = 1 := by
      calc
        B ^ (2 * n) = B ^ n * B ^ n := by rw [two_mul, pow_add]
        _ = (B⁻¹) ^ n * B ^ n := congrArg (fun x => x * B ^ n) hinv
        _ = 1 := by rw [inv_pow]; exact inv_mul_cancel _
    have hdvd : 7 ∣ 2 * n := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hp
    have hn0 : n = 0 := by omega
    subst n
    apply hA.2
    simpa using heq
  have hBpow_ne : ∀ {m n : ℕ}, m < 7 → n < 7 → m ≠ n → B ^ m ≠ B ^ n := by
    intro m n hm hn hmn heq
    have := pow_injOn_Iio_orderOf (x := B)
    have : m = n := this (by simpa [horder]) (by simpa [horder]) heq
    exact hmn this
  have hone_ne_Bpow : ∀ {n : ℕ}, 0 < n → n < 7 → 1 ≠ B ^ n := by
    intro n hn hn7
    simpa only [pow_zero] using (hBpow_ne (m := 0) (n := n) (by omega) hn7 (by omega))
  have hB_ne_Bpow : ∀ {n : ℕ}, 1 < n → n < 7 → B ≠ B ^ n := by
    intro n hn hn7
    simpa only [pow_one] using (hBpow_ne (m := 1) (n := n) (by omega) hn7 (by omega))
  have hA2_ne_B : A ^ 2 ≠ B := by
    simpa only [pow_one] using (hA2_ne_Bpow (n := 1) (by omega))
  have hone_ne_A2 : 1 ≠ A ^ 2 := Ne.symm hA.2
  have hone_ne_B : 1 ≠ B := Ne.symm hB.2
  constructor
  · rw [hS, hcand]
    simp only [putnam_1976_b2_solution]
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem]
    · simp
    all_goals simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    all_goals simp_all [hone_ne_Bpow, hB_ne_Bpow, hA2_ne_Bpow, hBpow_ne,
      hA2_ne_B, hone_ne_A2, hone_ne_B]
  · rw [hS, hcand, hword]
    ext x
    simp [putnam_1976_b2_solution, eq_comm, zpow_natCast]
    simp only [zpow_ofNat]
