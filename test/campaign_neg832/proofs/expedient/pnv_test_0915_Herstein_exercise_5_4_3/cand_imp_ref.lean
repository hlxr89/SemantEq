import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

set_option maxHeartbeats 1000000

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
  let C0 : Polynomial ℤ := X^10 + 2*X^6 + 5*X^4 + 7*X^2 - 11
  let C1 : Polynomial ℤ := 2*X^8
  let D0 : Polynomial ℤ := 2*X^7
  let D1 : Polynomial ℤ := 2*X^5
  let E0 : Polynomial ℤ := 2*X^6
  let E1 : Polynomial ℤ := 2*X^4
  let F : Polynomial ℤ := 2*X^3
  let A20 : Polynomial ℤ := C0^2 + 2*C1^2 + 5*(D0^2 + 2*D1^2) -
    7*(E0^2 + 2*E1^2) - 35*F^2
  let A21 : Polynomial ℤ := 2*C0*C1 + 10*D0*D1 - 14*E0*E1
  let B20 : Polynomial ℤ := 2*(C0*D0 + 2*C1*D1) - 14*E0*F
  let B21 : Polynomial ℤ := 2*(C0*D1 + C1*D0) - 14*E1*F
  let A3 : Polynomial ℤ := A20^2 + 2*A21^2 - 5*(B20^2 + 2*B21^2)
  let B3 : Polynomial ℤ := 2*A20*A21 - 10*B20*B21
  let Q : Polynomial ℤ := A3^2 - 2*B3^2
  let q : Polynomial ℂ := Q.map (Int.castRingHom ℂ)
  have hQdeg : Q.degree = 80 := by
    simp only [Q, A3, B3, A20, A21, B20, B21, C0, C1, D0, D1, E0, E1, F]
    compute_degree
    all_goals norm_num
    all_goals decide
  have hqdeg : q.degree = 80 := by
    dsimp [q]
    rw [Polynomial.degree_map_eq_of_injective (Int.cast_injective : Function.Injective (Int.castRingHom ℂ))]
    exact hQdeg
  have hs2 : ((√(2 : ℝ) : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs5 : ((√(5 : ℝ) : ℂ)) ^ 2 = 5 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs7 : ((√(7 : ℝ) : ℂ)) ^ 2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs11 : ((√(11 : ℝ) : ℂ)) ^ 2 = 11 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hroot : q.eval a = 0 := by
    let r2 : ℂ := √(2 : ℝ)
    let r5 : ℂ := √(5 : ℝ)
    let r7 : ℂ := √(7 : ℝ)
    let r11 : ℂ := √(11 : ℝ)
    have hr2 : r2^2 = 2 := by simpa [r2] using hs2
    have hr5 : r5^2 = 5 := by simpa [r5] using hs5
    have hr7 : r7^2 = 7 := by simpa [r7] using hs7
    have hr11 : r11^2 = 11 := by simpa [r11] using hs11
    let V : ℂ := a^5 + r2*a^3
    let c0 : ℂ := a^10 + 2*a^6 + 5*a^4 + 7*a^2 - 11
    let c1 : ℂ := 2*a^8
    let d0 : ℂ := 2*a^7
    let d1 : ℂ := 2*a^5
    let e0 : ℂ := 2*a^6
    let e1 : ℂ := 2*a^4
    let f : ℂ := 2*a^3
    let a20 : ℂ := c0^2 + 2*c1^2 + 5*(d0^2 + 2*d1^2) -
      7*(e0^2 + 2*e1^2) - 35*f^2
    let a21 : ℂ := 2*c0*c1 + 10*d0*d1 - 14*e0*e1
    let b20 : ℂ := 2*(c0*d0 + 2*c1*d1) - 14*e0*f
    let b21 : ℂ := 2*(c0*d1 + c1*d0) - 14*e1*f
    let a3 : ℂ := a20^2 + 2*a21^2 - 5*(b20^2 + 2*b21^2)
    let b3 : ℂ := 2*a20*a21 - 10*b20*b21
    have h0 : V + r5*a^2 + r7*a + r11 = 0 := by simpa [V, r2, r5, r7, r11] using h
    have h1 : (V + r5*a^2 + r7*a)^2 - 11 = 0 := by
      calc
        _ = (V + r5*a^2 + r7*a - r11) * (V + r5*a^2 + r7*a + r11) := by rw [← hr11]; ring
        _ = 0 := by rw [h0]; ring
    have h2 :
        ((V + r5*a^2)^2 + 7*a^2 - 11)^2 -
          7*(2*(V + r5*a^2)*a)^2 = 0 := by
      calc
        _ = ((V + r5*a^2)^2 + 7*a^2 - 11 - r7*(2*(V + r5*a^2)*a)) *
            ((V + r5*a^2)^2 + 7*a^2 - 11 + r7*(2*(V + r5*a^2)*a)) := by rw [← hr7]; ring
        _ = 0 := by
          rw [show (V + r5*a^2)^2 + 7*a^2 - 11 + r7*(2*(V + r5*a^2)*a) =
            (V + r5*a^2 + r7*a)^2 - 11 by rw [← hr7]; ring, h1]
          ring
    have hc : (V^2 + 5*a^4 + 7*a^2 - 11) = c0 + r2*c1 := by
      simp [V, c0, c1]
      linear_combination a^6 * hr2
    have hd : 2*V*a^2 = d0 + r2*d1 := by simp [V, d0, d1, r2]; ring
    have he : 2*V*a = e0 + r2*e1 := by simp [V, e0, e1, r2]; ring
    have hlin : (a20 + r2*a21) + r5*(b20 + r2*b21) = 0 := by
      calc
        _ = ((V^2 + 5*a^4 + 7*a^2 - 11)^2 + 5*(2*V*a^2)^2 -
              7*((2*V*a)^2 + 5*f^2)) +
            r5*(2*(V^2 + 5*a^4 + 7*a^2 - 11)*(2*V*a^2) - 14*(2*V*a)*f) := by
              rw [hc, hd, he]
              simp [a20, a21, b20, b21]
              linear_combination -(c1^2 + 5*d1^2 - 7*e1^2 + r5*(2*c1*d1)) * hr2
        _ = ((V + r5*a^2)^2 + 7*a^2 - 11)^2 - 7*(2*(V + r5*a^2)*a)^2 := by
              rw [← hr5]; simp [f]; ring
        _ = 0 := h2
    have h3 : a3 + r2*b3 = 0 := by
      calc
        _ = (a20 + r2*a21)^2 - 5*(b20 + r2*b21)^2 := by
          simp [a3, b3]
          linear_combination -(a21^2 - 5*b21^2) * hr2
        _ = (a20 + r2*a21 - r5*(b20 + r2*b21)) *
            (a20 + r2*a21 + r5*(b20 + r2*b21)) := by rw [← hr5]; ring
        _ = 0 := by rw [hlin]; ring
    have h4 : a3^2 - 2*b3^2 = 0 := by
      calc
        _ = (a3 - r2*b3) * (a3 + r2*b3) := by rw [← hr2]; ring
        _ = 0 := by rw [h3]; ring
    simpa [q, Q, A3, B3, A20, A21, B20, B21, C0, C1, D0, D1, E0, E1, F,
      a3, b3, a20, a21, b20, b21, c0, c1, d0, d1, e0, e1, f] using h4
  refine ⟨q, ?_, hqdeg.le, (Polynomial.mem_roots' ).2 ⟨?_, hroot⟩, ?_⟩
  · exact fun hq => by simpa [hq] using hqdeg
  · exact fun hq => by simpa [hq] using hqdeg
  · intro n
    refine ⟨Q.coeff n, 1, ?_⟩
    simp [q]
