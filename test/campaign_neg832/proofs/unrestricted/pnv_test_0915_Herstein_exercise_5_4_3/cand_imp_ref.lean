import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

set_option maxHeartbeats 2000000

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
  have _ha := dummy_assumed a h
  let Q : Polynomial ℤ :=
    X^80 - 16 * X^76 - 40 * X^74 + 56 * X^72 + 312 * X^70 +
    812 * X^68 + 840 * X^66 - 924 * X^64 - 17808 * X^62 -
    31580 * X^60 + 336 * X^58 + 151966 * X^56 + 303384 * X^54 -
    815980 * X^52 - 85584 * X^50 + 1618666 * X^48 + 784696 * X^46 +
    14780424 * X^44 - 15529624 * X^42 - 8183302 * X^40 -
    60091064 * X^38 + 38384032 * X^36 - 326561904 * X^34 +
    495133661 * X^32 + 160385872 * X^30 - 900140804 * X^28 +
    926472368 * X^26 + 1440591982 * X^24 - 1646774472 * X^22 -
    1939426788 * X^20 + 1649794720 * X^18 + 89715899 * X^16 +
    1495670792 * X^14 - 331895256 * X^12 - 2861245376 * X^10 +
    1851940090 * X^8 - 925076944 * X^6 + 1651094852 * X^4 -
    1091281576 * X^2 + 214358881
  let q : Polynomial ℂ := Q.map (Int.castRingHom ℂ)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro hq
    have := congrArg (fun r : Polynomial ℂ => r.coeff 80) hq
    norm_num [q, Q] at this
  · change (Q.map (Int.castRingHom ℂ)).degree ≤ 80
    rw [Polynomial.degree_map_eq_of_injective (Int.cast_injective)]
    dsimp [Q]
    compute_degree
  · rw [mem_roots]
    · change Polynomial.eval a q = 0
      change Polynomial.eval a (Q.map (Int.castRingHom ℂ)) = 0
      rw [eval_map]
      simp [Q]
      have hs2 : ((√(2 : ℝ) : ℂ) ^ 2) = 2 := by
        exact_mod_cast (sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
      have hs5 : ((√(5 : ℝ) : ℂ) ^ 2) = 5 := by
        exact_mod_cast (sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))
      have hs7 : ((√(7 : ℝ) : ℂ) ^ 2) = 7 := by
        exact_mod_cast (sq_sqrt (by norm_num : (0 : ℝ) ≤ 7))
      have hs11 : ((√(11 : ℝ) : ℂ) ^ 2) = 11 := by
        exact_mod_cast (sq_sqrt (by norm_num : (0 : ℝ) ≤ 11))
      have evenPow (s c : ℂ) (hs : s^2 = c) (n : ℕ) : s^(2*n) = c^n := by
        rw [pow_mul, hs]
      have hs5_4 : ((√(5 : ℝ) : ℂ)^4) = 25 := by
        convert evenPow (√(5 : ℝ)) 5 hs5 2 using 1 <;> norm_num
      have hs7_4 : ((√(7 : ℝ) : ℂ)^4) = 49 := by
        convert evenPow (√(7 : ℝ)) 7 hs7 2 using 1 <;> norm_num
      have hs7_6 : ((√(7 : ℝ) : ℂ)^6) = 343 := by
        convert evenPow (√(7 : ℝ)) 7 hs7 3 using 1 <;> norm_num
      have hs7_8 : ((√(7 : ℝ) : ℂ)^8) = 2401 := by
        convert evenPow (√(7 : ℝ)) 7 hs7 4 using 1 <;> norm_num
      have hs11_4 : ((√(11 : ℝ) : ℂ)^4) = 121 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 2 using 1 <;> norm_num
      have hs11_6 : ((√(11 : ℝ) : ℂ)^6) = 1331 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 3 using 1 <;> norm_num
      have hs11_8 : ((√(11 : ℝ) : ℂ)^8) = 14641 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 4 using 1 <;> norm_num
      have hs11_10 : ((√(11 : ℝ) : ℂ)^10) = 161051 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 5 using 1 <;> norm_num
      have hs11_12 : ((√(11 : ℝ) : ℂ)^12) = 1771561 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 6 using 1 <;> norm_num
      have hs11_14 : ((√(11 : ℝ) : ℂ)^14) = 19487171 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 7 using 1 <;> norm_num
      have hs11_16 : ((√(11 : ℝ) : ℂ)^16) = 214358881 := by
        convert evenPow (√(11 : ℝ)) 11 hs11 8 using 1 <;> norm_num
      let f : ℂ → ℂ → ℂ → ℂ → ℂ := fun u v w z =>
        a^5 + u * a^3 + v * a^2 + w * a + z
      let G : ℂ → ℂ → ℂ → ℂ := fun v w z =>
        (a^5 + v*a^2 + w*a + z)^2 - 2*a^6
      have hf (v w z : ℂ) :
          f (√(2 : ℝ)) v w z * f (-√(2 : ℝ)) v w z = G v w z := by
        dsimp [f, G]
        ring_nf
        rw [hs2]
      have hG : G (√(5 : ℝ)) (√(7 : ℝ)) (√(11 : ℝ)) = 0 := by
        rw [← hf]
        simp [f, h]
      let H : ℂ → ℂ → ℂ := fun w z =>
        let C := a^5 + w*a + z
        let D := C^2 + 5*a^4 - 2*a^6
        D^2 - 20*a^4*C^2
      have hGH (w z : ℂ) :
          G (√(5 : ℝ)) w z * G (-√(5 : ℝ)) w z = H w z := by
        dsimp [G, H]
        ring_nf
        rw [hs5, hs5_4]
        ring
      have hH : H (√(7 : ℝ)) (√(11 : ℝ)) = 0 := by
        rw [← hGH]
        simp [hG]
      let A : ℂ → ℂ := fun z =>
        a^20 - 4*a^16 + 4*a^15*z - 10*a^14 + 46*a^12 - 8*a^11*z +
        6*a^10*z^2 - 20*a^10 - 20*a^9*z - 3*a^8 + 84*a^7*z -
        4*a^6*z^2 - 70*a^6 + 4*a^5*z^3 - 10*a^4*z^2 + 49*a^4 +
        42*a^2*z^2 + z^4
      let B : ℂ → ℂ := fun z =>
        4*a*(a^5 + z)*(a^10 - 2*a^6 + 2*a^5*z - 5*a^4 + 7*a^2 + z^2)
      let I : ℂ → ℂ := fun z => A z ^ 2 - 7 * B z ^ 2
      have hHI (z : ℂ) :
          H (√(7 : ℝ)) z * H (-√(7 : ℝ)) z = I z := by
        dsimp [H, I, A, B]
        ring_nf
        rw [hs7, hs7_4, hs7_6, hs7_8]
        ring
      have hI : I (√(11 : ℝ)) = 0 := by
        rw [← hHI]
        simp [hH]
      let C : ℂ :=
        a^40 - 8*a^36 - 20*a^34 - 4*a^32 + 348*a^30 + 174*a^28 -
        1100*a^26 - 2678*a^24 - 6496*a^22 + 12578*a^20 + 13784*a^18 -
        2571*a^16 - 15004*a^14 - 79610*a^12 + 47260*a^10 + 38107*a^8 -
        8800*a^6 + 8954*a^4 - 37268*a^2 + 14641
      let D : ℂ :=
        8*a^5*(a^30 - 6*a^26 - 15*a^24 - 9*a^22 + 97*a^20 + 95*a^18 -
        130*a^16 - 325*a^14 - 1463*a^12 + 1340*a^10 + 1378*a^8 -
        299*a^6 - 198*a^4 - 2541*a^2 + 1331)
      have hICD : I (√(11 : ℝ)) * I (-√(11 : ℝ)) = C^2 - 11*D^2 := by
        dsimp [I, A, B, C, D]
        ring_nf
        rw [hs11, hs11_4, hs11_6, hs11_8, hs11_10, hs11_12, hs11_14, hs11_16]
        ring
      have hCD : C^2 - 11*D^2 = 0 := by
        rw [← hICD, hI, zero_mul]
      rw [show
        a^80 - 16*a^76 - 40*a^74 + 56*a^72 + 312*a^70 + 812*a^68 +
          840*a^66 - 924*a^64 - 17808*a^62 - 31580*a^60 + 336*a^58 +
          151966*a^56 + 303384*a^54 - 815980*a^52 - 85584*a^50 +
          1618666*a^48 + 784696*a^46 + 14780424*a^44 - 15529624*a^42 -
          8183302*a^40 - 60091064*a^38 + 38384032*a^36 - 326561904*a^34 +
          495133661*a^32 + 160385872*a^30 - 900140804*a^28 + 926472368*a^26 +
          1440591982*a^24 - 1646774472*a^22 - 1939426788*a^20 +
          1649794720*a^18 + 89715899*a^16 + 1495670792*a^14 -
          331895256*a^12 - 2861245376*a^10 + 1851940090*a^8 -
          925076944*a^6 + 1651094852*a^4 - 1091281576*a^2 + 214358881 =
          C^2 - 11*D^2 by
            dsimp [C, D]
            ring]
      exact hCD
    · intro hq
      have := congrArg (fun r : Polynomial ℂ => r.coeff 80) hq
      norm_num [q, Q] at this
  · intro n
    refine ⟨Q.coeff n, 1, ?_⟩
    simp [q]
