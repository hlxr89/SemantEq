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
  let Q : ℕ+ → Polynomial ℝ := fun n => _root_.P n
  have hQ1 : Q 1 = 1 + X := by simp [Q, _root_.P]
  have hQ2 : Q 2 = 1 + 2 * X := by simp [Q, _root_.P]
  have hQodd : ∀ n, Q (2 * n + 1) = Q (2 * n) + C ((n : ℝ) + 1) * X * Q (2 * n - 1) := by
    intro n
    have hind : ((2 * n - 1 : ℕ+) : ℕ) = 2 * (n : ℕ) - 1 := by
      have hlt : (1 : ℕ+) < 2 * n := by
        exact_mod_cast (show 1 < 2 * (n : ℕ) by have hn := n.pos; omega)
      rw [PNat.sub_coe, if_pos hlt]
      simp
    simp [Q, _root_.P, Polynomial.smul_eq_C_mul, hind]
    left
    have hc : (2 * (n : ℝ) + 2) / 2 = (n : ℝ) + 1 := by ring
    rw [hc, C_eq_algebraMap]
    simp
  have hQeven : ∀ n, Q (2 * n + 2) = Q (2 * n + 1) + C ((n : ℝ) + 1) * X * Q (2 * n) := by
    intro n
    simp [Q, _root_.P, Polynomial.smul_eq_C_mul]
    left
    have hc : (2 * (n : ℝ) + 1 + 1) / 2 = (n : ℝ) + 1 := by ring
    rw [hc, C_eq_algebraMap]
    simp
  let pos : ℕ → ℕ+ := fun k => ⟨k + 1, by omega⟩
  have hpairs : ∀ k : ℕ,
      P (2 * pos k - 1) = Q (2 * pos k - 1) ∧
      P (2 * pos k) = Q (2 * pos k) := by
    intro k
    induction k with
    | zero =>
      constructor
      · convert hP1.trans hQ1.symm using 1 <;> ext <;> norm_num [pos, PNat.sub_coe]
      · convert hP2.trans hQ2.symm using 1 <;> ext <;> norm_num [pos]
    | succ k ih =>
      let n : ℕ+ := pos k
      have hnodd : P (2 * n + 1) = Q (2 * n + 1) := by
        rw [hPodd, hQodd, ih.1, ih.2]
      have hneven : P (2 * n + 2) = Q (2 * n + 2) := by
        rw [hPeven, hQeven, hnodd, ih.2]
      constructor
      · convert hnodd using 1 <;> ext <;> simp [n, pos, PNat.sub_coe] <;> omega
      · convert hneven using 1 <;> ext <;> simp [n, pos] <;> omega
  have hPQ : ∀ n : ℕ+, P n = Q n := by
    intro n
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n : ℕ)
    · have hkpos : 0 < k := by have := n.pos; omega
      have h := (hpairs (k - 1)).2
      have hidx : n = 2 * pos (k - 1) := by
        apply PNat.eq
        simp [pos]
        omega
      rw [hidx]
      exact h
    · have h := (hpairs k).1
      have hidx : n = 2 * pos k - 1 := by
        have hlt : (1 : ℕ+) < 2 * pos k := by
          exact_mod_cast (show 1 < 2 * (k + 1) by omega)
        apply PNat.eq
        rw [PNat.sub_coe, if_pos hlt]
        simp [pos]
        omega
      rw [hidx]
      exact h
  obtain ⟨b, hbroot, hbub, hbmono_step, hblim⟩ := problem_statement_assumed
  have hab : ∀ n : ℕ+, a n = b n := by
    intro n
    apply le_antisymm
    · apply hbub (n : ℕ) n.pos
      rw [← show Q n = _root_.P (n : ℕ) by rfl, ← hPQ n]
      exact haroot n
    · apply haub n (b n)
      rw [hPQ n, show Q n = _root_.P (n : ℕ) by rfl]
      exact hbroot (n : ℕ) n.pos
  constructor
  · have htail : StrictMono (fun k : ℕ => b (k + 1)) := by
      apply strictMono_nat_of_lt_succ
      intro k
      exact hbmono_step (k + 1) (by omega)
    intro m n hmn
    rw [hab m, hab n]
    have hmpos := m.pos
    have hnpos := n.pos
    have hmn' : (m : ℕ) < (n : ℕ) := hmn
    have hsub : (m : ℕ) - 1 < (n : ℕ) - 1 := by omega
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by omega : (m : ℕ) ≠ 0)),
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by omega : (n : ℕ) ≠ 0))] using htail hsub
  · rw [show a = fun n : ℕ+ => b (n : ℕ) by funext n; exact hab n]
    apply hblim.comp
    refine Filter.tendsto_atTop.2 fun N => ?_
    filter_upwards [eventually_ge_atTop (⟨N + 1, by omega⟩ : ℕ+)] with n hn
    change N + 1 ≤ (n : ℕ) at hn
    exact le_trans (by omega) hn
