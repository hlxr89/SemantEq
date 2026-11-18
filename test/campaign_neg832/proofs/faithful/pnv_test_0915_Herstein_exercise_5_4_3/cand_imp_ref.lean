import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

set_option maxHeartbeats 2000000

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a : ℂ) (h : a ^ 5 + √(2 : ℝ) * a ^ 3 + √(5 : ℝ) * a ^ 2 + √(7 : ℝ) * a + √(11 : ℝ) = 0) : IsAlgebraic ℚ a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  have h : a ^ 5 + √(2 : ℝ) * a ^ 3 + √(5 : ℝ) * a ^ 2 + √(7 : ℝ) * a + √(11 : ℝ) = 0 := by
    simpa [hp] using ha
  have halg : IsAlgebraic ℚ a := dummy_assumed a h
  have hint : IsIntegral ℚ a := halg.isIntegral
  let g0 : ℚ[X] :=
    X^40 + 56*X^36 - 20*X^34 + 252*X^32 - 644*X^30 - 466*X^28
      - 2380*X^26 + 650*X^24 - 1312*X^22 + 7970*X^20 + 4984*X^18
      - 3979*X^16 + 6468*X^14 - 25402*X^12 + 4668*X^10 + 38107*X^8
      - 8800*X^6 + 8954*X^4 - 37268*X^2 + 14641
  let g1 : ℚ[X] := 8*X^8*(X^30 + 14*X^26 - 15*X^24 + 7*X^22 - 133*X^20
    - 57*X^18 - 210*X^16 + 323*X^14 + 37*X^12 + 1052*X^10 + 828*X^8
    - 3467*X^6 + 1144*X^4 + 847*X^2 - 1331)
  let r : ℚ[X] := g0^2 - 2*g1^2
  have hr0 : r ≠ 0 := by
    intro hr
    have := congrArg (fun f : ℚ[X] ↦ f.eval 0) hr
    norm_num [r, g0, g1] at this
  have hrdeg : r.degree ≤ 80 := by
    dsimp [r, g0, g1]
    compute_degree
  have hra : Polynomial.aeval a r = 0 := by
    let s2 : ℂ := √(2 : ℝ)
    let s5 : ℂ := √(5 : ℝ)
    let s7 : ℂ := √(7 : ℝ)
    let s11 : ℂ := √(11 : ℝ)
    have hs2 : s2 ^ 2 = 2 := by
      change ((√(2 : ℝ) : ℂ) ^ 2) = (2 : ℂ)
      set_option maxHeartbeats 500000 in
        set_option maxRecDepth 10000 in norm_cast
      set_option maxHeartbeats 500000 in exact Real.sq_sqrt (by norm_num)
    have hs5 : s5 ^ 2 = 5 := by
      change ((√(5 : ℝ) : ℂ) ^ 2) = (5 : ℂ)
      set_option maxHeartbeats 500000 in
        set_option maxRecDepth 10000 in norm_cast
      set_option maxHeartbeats 500000 in exact Real.sq_sqrt (by norm_num)
    have hs7 : s7 ^ 2 = 7 := by
      change ((√(7 : ℝ) : ℂ) ^ 2) = (7 : ℂ)
      set_option maxHeartbeats 500000 in
        set_option maxRecDepth 10000 in norm_cast
      set_option maxHeartbeats 500000 in exact Real.sq_sqrt (by norm_num)
    have hs11 : s11 ^ 2 = 11 := by
      change ((√(11 : ℝ) : ℂ) ^ 2) = (11 : ℂ)
      set_option maxHeartbeats 500000 in
        set_option maxRecDepth 10000 in norm_cast
      set_option maxHeartbeats 500000 in exact Real.sq_sqrt (by norm_num)
    have h0 : a ^ 5 + s2 * a ^ 3 + s5 * a ^ 2 + s7 * a + s11 = 0 := by
      simpa [s2, s5, s7, s11] using h
    let T (u v : ℂ) := a^5 + u*a^3 + v*a^2
    let B (u v : ℂ) :=
      let t := T u v
      let d := t^2 + 7*a^2 - 11
      let e := 2*t*a
      d^2 - 7*e^2
    have hA : (T s2 s5 + s7*a)^2 - 11 = 0 := by
      calc
        (T s2 s5 + s7*a)^2 - 11 =
            (T s2 s5 + s7*a + s11) * (T s2 s5 + s7*a - s11) := by
              rw [← hs11]
              ring
        _ = 0 := by rw [show T s2 s5 + s7*a + s11 = 0 by simpa [T] using h0]; ring
    have hB : B s2 s5 = 0 := by
      rw [show B s2 s5 = ((T s2 s5 + s7*a)^2 - 11) *
          ((T s2 s5 - s7*a)^2 - 11) by
        dsimp [B]
        rw [← hs7]
        ring, hA]
      ring
    let D (u : ℂ) := u^4*a^12 + 4*u^3*a^14 + 6*u^2*a^16 + 30*u^2*a^10
      - 14*u^2*a^8 - 22*u^2*a^6 + 4*u*a^18 + 60*u*a^12 - 28*u*a^10
      - 44*u*a^8 + a^20 + 30*a^14 - 14*a^12 - 22*a^10 + 25*a^8
      - 70*a^6 - 61*a^4 - 154*a^2 + 121
    let E (u : ℂ) := 4*a^5*(u+a^2)*(u^2*a^6 + 2*u*a^8 + a^10 + 5*a^4 - 7*a^2 - 11)
    have hs5_3 : s5^3 = 5*s5 := by calc
      s5^3 = s5^2*s5 := by ring
      _ = 5*s5 := by rw [hs5]
    have hs5_4 : s5^4 = 25 := by calc
      s5^4 = (s5^2)^2 := by ring
      _ = 25 := by rw [hs5]; norm_num
    have hDE : D s2 + s5 * E s2 = 0 := by
      rw [← hB]
      dsimp [B, T, D, E]
      ring_nf
      rw [hs5_4, hs5_3, hs5]
      ring
    have hC : D s2 ^ 2 - 5 * E s2 ^ 2 = 0 := by
      calc
        D s2 ^ 2 - 5 * E s2 ^ 2 = (D s2 + s5*E s2) * (D s2 - s5*E s2) := by
          rw [← hs5]
          ring
        _ = 0 := by rw [hDE]; ring
    let G0 : ℂ := a^40 + 56*a^36 - 20*a^34 + 252*a^32 - 644*a^30 - 466*a^28
      - 2380*a^26 + 650*a^24 - 1312*a^22 + 7970*a^20 + 4984*a^18
      - 3979*a^16 + 6468*a^14 - 25402*a^12 + 4668*a^10 + 38107*a^8
      - 8800*a^6 + 8954*a^4 - 37268*a^2 + 14641
    let G1 : ℂ := 8*a^8*(a^30 + 14*a^26 - 15*a^24 + 7*a^22 - 133*a^20
      - 57*a^18 - 210*a^16 + 323*a^14 + 37*a^12 + 1052*a^10 + 828*a^8
      - 3467*a^6 + 1144*a^4 + 847*a^2 - 1331)
    have hs2_3 : s2^3 = 2*s2 := by calc
      s2^3 = s2^2*s2 := by ring
      _ = 2*s2 := by rw [hs2]
    have hs2_4 : s2^4 = 4 := by calc
      s2^4 = (s2^2)^2 := by ring
      _ = 4 := by rw [hs2]; norm_num
    have hs2_5 : s2^5 = 4*s2 := by calc
      s2^5 = s2^4*s2 := by ring
      _ = 4*s2 := by rw [hs2_4]
    have hs2_6 : s2^6 = 8 := by calc
      s2^6 = s2^4*s2^2 := by ring
      _ = 8 := by rw [hs2_4, hs2]; norm_num
    have hs2_7 : s2^7 = 8*s2 := by calc
      s2^7 = s2^6*s2 := by ring
      _ = 8*s2 := by rw [hs2_6]
    have hs2_8 : s2^8 = 16 := by calc
      s2^8 = s2^6*s2^2 := by ring
      _ = 16 := by rw [hs2_6, hs2]; norm_num
    have hG : G0 + s2*G1 = 0 := by
      rw [← hC]
      dsimp [D, E, G0, G1]
      ring_nf
      rw [hs2_8, hs2_7, hs2_6, hs2_5, hs2_4, hs2_3, hs2]
      ring
    calc
      Polynomial.aeval a r = G0^2 - 2*G1^2 := by
        simp only [r, g0, g1, G0, G1, map_add, map_sub, map_mul, map_pow,
          Polynomial.aeval_X]
        norm_num [Polynomial.aeval_def]
      _ = (G0 + s2*G1) * (G0 - s2*G1) := by rw [← hs2]; ring
      _ = 0 := by rw [hG]; ring
  let m : ℚ[X] := minpoly ℚ a
  let q : ℂ[X] := m.map (algebraMap ℚ ℂ)
  have hm0 : m ≠ 0 := by simpa [m] using minpoly.ne_zero hint
  have hq0 : q ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hm0
  refine ⟨q, hq0, ?_, ?_, ?_⟩
  · simp only [q, Polynomial.degree_map_eq_of_injective (algebraMap ℚ ℂ).injective, m]
    calc
      (minpoly ℚ a).degree ≤ r.degree := minpoly.degree_le_of_ne_zero ℚ a hr0 hra
      _ ≤ 80 := hrdeg
  · apply (Polynomial.mem_roots hq0).mpr
    simp only [Polynomial.IsRoot, q, Polynomial.eval_map]
    simpa [m, Polynomial.aeval_def] using minpoly.aeval ℚ a
  · intro n
    let c : ℚ := m.coeff n
    refine ⟨c.num, (c.den : ℤ), ?_⟩
    simp only [q, Polynomial.coeff_map]
    change algebraMap ℚ ℂ c = (c.num : ℂ) / (c.den : ℂ)
    calc
      algebraMap ℚ ℂ c = algebraMap ℚ ℂ ((c.num : ℚ) / (c.den : ℚ)) := by
        rw [Rat.num_div_den]
      _ = (c.num : ℂ) / (c.den : ℂ) := by simp
