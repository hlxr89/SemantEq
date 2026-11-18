import Mathlib
open Polynomial Filter Topology

set_option maxHeartbeats 800000

-- ===== unified context (both sides' local defs, merged) =====
abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

variable (G : Type*) [Group G]
variable (A B : G)

-- Given relations
variable (hA4 : A ^ 4 = 1)
variable (hB7 : B ^ 7 = 1)
variable (hcomm : A * B * A⁻¹ * B = 1)
variable (hA2_ne : A ^ 2 ≠ 1)
variable (hB_ne : B ≠ 1)

-- ===== assumed statement (antecedent) =====
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
  have hcomm : A * B * A⁻¹ * B = 1 := by simpa using h1
  have hsquares := problem_statement_assumed G A B
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf B = 7 := orderOf_eq_prime hB.1 hB.2
  have hB_inj : ∀ {m n : ℕ}, m < 7 → n < 7 → B ^ m = B ^ n → m = n := by
    intro m n hm hn he
    apply Nat.ModEq.eq_of_lt_of_lt _ hm hn
    rw [← hord]
    exact (pow_eq_pow_iff_modEq).mp he
  have hconj : A * B * A⁻¹ = B⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hcomm
  have hconjpow : ∀ n : ℕ, A * B ^ n * A⁻¹ = (B⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        calc
          A * (B ^ n * B) * A⁻¹ = (A * B ^ n * A⁻¹) * (A * B * A⁻¹) := by group
          _ = (B⁻¹) ^ n * B⁻¹ := by rw [ih, hconj]
  have hA2_ne_Bpow : ∀ n : ℕ, n < 7 → A ^ 2 ≠ B ^ n := by
    intro n hn he
    have hc := congrArg (fun x : G => A * x * A⁻¹) he
    have hfix : A * A ^ 2 * A⁻¹ = A ^ 2 := by group
    change A * A ^ 2 * A⁻¹ = A * B ^ n * A⁻¹ at hc
    rw [hfix, hconjpow n] at hc
    have hinv : B ^ n = (B ^ n)⁻¹ := by
      calc
        B ^ n = A ^ 2 := he.symm
        _ = (B⁻¹) ^ n := hc
        _ = (B ^ n)⁻¹ := by simp
    have hsquare : (B ^ n) ^ 2 = 1 := by
      calc
        (B ^ n) ^ 2 = B ^ n * B ^ n := by simp [pow_two]
        _ = (B ^ n)⁻¹ * B ^ n := congrArg (fun x => x * B ^ n) hinv
        _ = 1 := inv_mul_cancel _
    have hdvd : 7 ∣ n * 2 := by
      rw [← hord, orderOf_dvd_iff_pow_eq_one]
      simpa [pow_mul] using hsquare
    have hn : n = 0 := by omega
    subst n
    exact hA.2 (by simpa only [pow_zero] using he)
  let f : Fin 8 → G := fun i => if i = 0 then A ^ 2 else B ^ (i.val - 1)
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · exfalso
        have hij' : A ^ 2 = B ^ (j.val - 1) := by simpa [f, hi, hj] using hij
        exact hA2_ne_Bpow (j.val - 1) (by omega) hij'
    · by_cases hj : j = 0
      · exfalso
        have hij' : A ^ 2 = B ^ (i.val - 1) := by
          simpa [f, hi, hj] using hij.symm
        exact hA2_ne_Bpow (i.val - 1) (by omega) hij'
      · have hp : i.val - 1 = j.val - 1 := hB_inj (by omega) (by omega) (by simpa [f, hi, hj] using hij)
        have hiv : i.val ≠ 0 := by
          intro hiv
          apply hi
          exact Fin.ext hiv
        have hjv : j.val ≠ 0 := by
          intro hjv
          apply hj
          exact Fin.ext hjv
        omega
  let T : Set G := {1, A ^ 2, B, B ^ 2, B ^ 3, B ^ 4, B ^ 5, B ^ 6}
  have hf_mem : ∀ i : Fin 8, f i ∈ T := by
    intro i
    fin_cases i <;> simp [f, T]
  have hf_surj : ∀ x ∈ T, ∃ i : Fin 8, ∃ (_hi : i ∈ (Set.univ : Set (Fin 8))), f i = x := by
    intro x hx
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, Set.mem_univ _, by simp [f]⟩
    · exact ⟨0, Set.mem_univ _, by simp [f]⟩
    · exact ⟨2, Set.mem_univ _, by simp [f]⟩
    · exact ⟨3, Set.mem_univ _, by simp [f]⟩
    · exact ⟨4, Set.mem_univ _, by simp [f]⟩
    · exact ⟨5, Set.mem_univ _, by simp [f]⟩
    · exact ⟨6, Set.mem_univ _, by simp [f]⟩
    · exact ⟨7, Set.mem_univ _, by simp [f]⟩
  have hcardT : T.ncard = 8 := by
    symm
    simpa using Set.ncard_congr (fun i (_hi : i ∈ (Set.univ : Set (Fin 8))) => f i)
      (fun i _ => hf_mem i)
      (fun i j _ _ hij => hf_inj hij)
      hf_surj
  constructor
  · rw [hS, hsquares]
    simpa [putnam_1976_b2_solution, T] using hcardT
  · rw [hS, hsquares, hword]
    have hA2z : A ^ (2 : ℤ) = A ^ (2 : ℕ) := zpow_natCast A 2
    have hB2z : B ^ (2 : ℤ) = B ^ (2 : ℕ) := zpow_natCast B 2
    have hB3z : B ^ (3 : ℤ) = B ^ (3 : ℕ) := zpow_natCast B 3
    have hB4z : B ^ (4 : ℤ) = B ^ (4 : ℕ) := zpow_natCast B 4
    have hB5z : B ^ (5 : ℤ) = B ^ (5 : ℕ) := zpow_natCast B 5
    have hB6z : B ^ (6 : ℤ) = B ^ (6 : ℕ) := zpow_natCast B 6
    ext x
    constructor <;> intro hx <;>
      simpa [putnam_1976_b2_solution, eq_comm, hA2z, hB2z, hB3z, hB4z, hB5z, hB6z] using hx
