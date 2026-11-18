import Mathlib

open Set Real Filter Topology Polynomial

-- ===== unified context (both sides' local defs, merged) =====
noncomputable def P : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => Polynomial.C 1 + Polynomial.X
  | 2 => Polynomial.C 1 + 2 • Polynomial.X
  | m + 1 =>
    if m % 2 = 0 then
      let coeff := ((m + 2 : ℝ) / 2)
      P m + coeff • Polynomial.X * P (m - 1)
    else
      let coeff := ((m + 1 : ℝ) / 2)
      P m + coeff • Polynomial.X * P (m - 1)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∃ (a : ℕ → ℝ),
    (∀ n : ℕ, n ≥ 1 → (P n).eval (a n) = 0) ∧
    (∀ n : ℕ, n ≥ 1 → ∀ x : ℝ, (P n).eval x = 0 → x ≤ a n) ∧
    (∀ n : ℕ, n ≥ 1 → a n < a (n + 1)) ∧
    Filter.Tendsto a Filter.atTop (nhds 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_1978_b3
(P : ℕ+ → Polynomial ℝ)
(hP1 : P 1 = 1 + X)
(hP2 : P 2 = 1 + 2 * X)
(hPodd : ∀ n, P (2 * n + 1) = P (2 * n) + C ((n : ℝ) + 1) * X * P (2 * n - 1))
(hPeven : ∀ n, P (2 * n + 2) = P (2 * n + 1) + C ((n : ℝ) + 1) * X * P (2 * n))
(a : ℕ+ → ℝ)
(haroot : ∀ n, (P n).eval (a n) = 0)
(haub : ∀ n, ∀ x, (P n).eval x = 0 → x ≤ a n)
: (StrictMono a ∧ Tendsto a atTop (𝓝 0)) := by
  have hP_eq : ∀ n : ℕ+, P n = _root_.P n := by
    intro n
    have aux : ∀ m : ℕ, ∀ hm : 0 < m, P ⟨m, hm⟩ = _root_.P m := by
      intro m
      induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases m with (_ | _ | m)
      · omega
      · rw [_root_.P]
        exact hP1
      · rcases m with (_ | m)
        · rw [_root_.P]
          change P 2 = C 1 + 2 • X
          rw [hP2]
          simp only [two_mul, two_smul]
          rfl
        · have hpred : 0 < m + 2 := by omega
          by_cases he : (m + 2) % 2 = 0
          · have hdiv : 0 < (m + 2) / 2 := Nat.div_pos (by omega) (by omega)
            have hmrepr : m + 2 = 2 * ((m + 2) / 2) := by
              have hmod := Nat.mod_add_div (m + 2) 2
              omega
            rw [_root_.P] <;> try omega
            rw [if_pos he]
            let q : ℕ+ := ⟨(m + 2) / 2, hdiv⟩
            have hrec : P ⟨m + 3, by omega⟩ =
                P ⟨m + 2, hpred⟩ + C (((q : ℕ) : ℝ) + 1) * X * P ⟨m + 1, by omega⟩ := by
              convert hPodd q using 1
              · apply congrArg P
                apply Subtype.ext
                change m + 3 = 2 * ((m + 2) / 2) + 1
                omega
              · congr 3
                pnat_to_nat
                simp only [q, PNat.mk_coe]
                omega
            rw [hrec]
            rw [ih (m + 2) (by omega) hpred, ih (m + 1) (by omega) (by omega)]
            simp only [smul_eq_C_mul]
            rw [show m + 2 - 1 = m + 1 by omega]
            have hcoeff : (((q : ℕ) : ℝ) + 1) = ((m + 2 : ℝ) + 2) / 2 := by
              have hc := congrArg (fun k : ℕ => (k : ℝ)) hmrepr
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
              change ((((m + 2) / 2 : ℕ) : ℝ) + 1) = ((m + 2 : ℝ) + 2) / 2
              linarith
            rw [hcoeff]
            push_cast
            rfl
          · have hrem : (m + 2) % 2 = 1 := by omega
            have hdiv : 0 < (m + 1) / 2 := by
              have hmod := Nat.mod_add_div (m + 2) 2
              omega
            have hmrepr : m + 2 = 2 * ((m + 1) / 2) + 1 := by
              have hmod := Nat.mod_add_div (m + 2) 2
              omega
            rw [_root_.P] <;> try omega
            rw [if_neg he]
            let q : ℕ+ := ⟨(m + 1) / 2, hdiv⟩
            have hrec : P ⟨m + 3, by omega⟩ =
                P ⟨m + 2, hpred⟩ + C (((q : ℕ) : ℝ) + 1) * X * P ⟨m + 1, by omega⟩ := by
              convert hPeven q using 1
              · apply congrArg P
                apply Subtype.ext
                change m + 3 = 2 * ((m + 1) / 2) + 2
                omega
              · congr 3
                apply Subtype.ext
                simp only [q]
                change m + 1 = 2 * ((m + 1) / 2)
                omega
            rw [hrec]
            rw [ih (m + 2) (by omega) hpred, ih (m + 1) (by omega) (by omega)]
            simp only [smul_eq_C_mul]
            rw [show m + 2 - 1 = m + 1 by omega]
            have hcoeff : (((q : ℕ) : ℝ) + 1) = ((m + 2 : ℝ) + 1) / 2 := by
              have hc := congrArg (fun k : ℕ => (k : ℝ)) hmrepr
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
              change ((((m + 1) / 2 : ℕ) : ℝ) + 1) = ((m + 2 : ℝ) + 1) / 2
              linarith
            rw [hcoeff]
            push_cast
            rfl
    exact aux n n.property
  obtain ⟨b, hbroot, hbub, hbmono, hblim⟩ := problem_statement_assumed
  have hab : ∀ n : ℕ+, a n = b n := by
    intro n
    apply le_antisymm
    · apply hbub n n.property (a n)
      rw [← hP_eq n]
      exact haroot n
    · apply haub n (b n)
      rw [hP_eq n]
      exact hbroot n n.property
  constructor
  · intro i j hij
    rw [hab i, hab j]
    have hbshift : StrictMono (fun n : ℕ => b (n + 1)) :=
      strictMono_nat_of_lt_succ (fun n => hbmono (n + 1) (by omega))
    have hi : (i : ℕ) - 1 + 1 = i := Nat.sub_add_cancel i.property
    have hj : (j : ℕ) - 1 + 1 = j := Nat.sub_add_cancel j.property
    have hij' : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
    rw [← hi, ← hj]
    exact hbshift (Nat.sub_lt_sub_right (by omega) hij')
  · have hval : Tendsto (fun n : ℕ+ => (n : ℕ)) atTop atTop := by
      apply tendsto_atTop.2
      intro N
      filter_upwards [eventually_ge_atTop ⟨max N 1, by omega⟩] with n hn
      exact le_trans (Nat.le_max_left N 1) (by exact_mod_cast hn)
    have hbsub : Tendsto (fun n : ℕ+ => b n) atTop (𝓝 0) := hblim.comp hval
    apply hbsub.congr'
    filter_upwards [] with n
    exact (hab n).symm
