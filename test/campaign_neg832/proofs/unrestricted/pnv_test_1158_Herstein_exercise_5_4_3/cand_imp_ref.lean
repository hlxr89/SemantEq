import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

set_option maxHeartbeats 4000000

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : Polynomial ℚ) (h0 : p ≠ 0) (h : p.natDegree = 5) (ha : a ∈ roots p) : ∃ q ∈ {q : Polynomial ℚ | Irreducible q ∧ q.natDegree ≤ 80}, q ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  let qz : Polynomial ℤ :=
    X^80 - 16*X^76 - 40*X^74 + 56*X^72 + 312*X^70 + 812*X^68 +
    840*X^66 - 924*X^64 - 17808*X^62 - 31580*X^60 + 336*X^58 +
    151966*X^56 + 303384*X^54 - 815980*X^52 - 85584*X^50 +
    1618666*X^48 + 784696*X^46 + 14780424*X^44 - 15529624*X^42 -
    8183302*X^40 - 60091064*X^38 + 38384032*X^36 - 326561904*X^34 +
    495133661*X^32 + 160385872*X^30 - 900140804*X^28 + 926472368*X^26 +
    1440591982*X^24 - 1646774472*X^22 - 1939426788*X^20 +
    1649794720*X^18 + 89715899*X^16 + 1495670792*X^14 - 331895256*X^12 -
    2861245376*X^10 + 1851940090*X^8 - 925076944*X^6 + 1651094852*X^4 -
    1091281576*X^2 + 214358881
  let q : Polynomial ℂ :=
    X^80 - 16*X^76 - 40*X^74 + 56*X^72 + 312*X^70 + 812*X^68 +
    840*X^66 - 924*X^64 - 17808*X^62 - 31580*X^60 + 336*X^58 +
    151966*X^56 + 303384*X^54 - 815980*X^52 - 85584*X^50 +
    1618666*X^48 + 784696*X^46 + 14780424*X^44 - 15529624*X^42 -
    8183302*X^40 - 60091064*X^38 + 38384032*X^36 - 326561904*X^34 +
    495133661*X^32 + 160385872*X^30 - 900140804*X^28 + 926472368*X^26 +
    1440591982*X^24 - 1646774472*X^22 - 1939426788*X^20 +
    1649794720*X^18 + 89715899*X^16 + 1495670792*X^14 - 331895256*X^12 -
    2861245376*X^10 + 1851940090*X^8 - 925076944*X^6 + 1651094852*X^4 -
    1091281576*X^2 + 214358881
  have hqmonic : q.Monic := by
    dsimp [q]
    set_option maxRecDepth 10000 in
      monicity <;> norm_num
  have hq0 : q ≠ 0 := hqmonic.ne_zero
  have hqdeg : q.degree ≤ 80 := by
    dsimp [q]
    compute_degree
  have ha' : a^5 + (sqrt 2 : ℂ) * a^3 + (sqrt 5 : ℂ) * a^2 +
      (sqrt 7 : ℂ) * a + (sqrt 11 : ℂ) = 0 := by
    simpa [hp] using ha
  have h2 : (sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have h5 : (sqrt 5 : ℂ)^2 = 5 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))
  have h7 : (sqrt 7 : ℂ)^2 = 7 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7))
  have h11 : (sqrt 11 : ℂ)^2 = 11 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11))
  have hroot : q.IsRoot a := by
    rw [Polynomial.IsRoot]
    let z : ℂ := a^5 + (sqrt 2 : ℂ) * a^3
    let t : ℂ := z + (sqrt 5 : ℂ) * a^2
    let U : ℂ := z^2 + 5*a^4
    let V : ℂ := 2*z*a^2
    let A : ℂ := U^2 + 5*V^2 - (14*a^2 + 22)*U + (7*a^2 - 11)^2
    let B : ℂ := 2*U*V - (14*a^2 + 22)*V
    let G : ℂ → ℂ := fun w =>
      let u := w^2 + 5*a^4
      let v := 2*w*a^2
      let aa := u^2 + 5*v^2 - (14*a^2 + 22)*u + (7*a^2 - 11)^2
      let bb := 2*u*v - (14*a^2 + 22)*v
      aa^2 - 5*bb^2
    let C : ℂ := a^40 + 56*a^36 - 20*a^34 + 252*a^32 - 644*a^30 -
      466*a^28 - 2380*a^26 + 650*a^24 - 1312*a^22 + 7970*a^20 +
      4984*a^18 - 3979*a^16 + 6468*a^14 - 25402*a^12 + 4668*a^10 +
      38107*a^8 - 8800*a^6 + 8954*a^4 - 37268*a^2 + 14641
    let D : ℂ := 8*a^8*(a^30 + 14*a^26 - 15*a^24 + 7*a^22 - 133*a^20 -
      57*a^18 - 210*a^16 + 323*a^14 + 37*a^12 + 1052*a^10 + 828*a^8 -
      3467*a^6 + 1144*a^4 + 847*a^2 - 1331)
    have ht11 : (t + (sqrt 7 : ℂ)*a)^2 - 11 = 0 := by
      calc
        (t + (sqrt 7 : ℂ)*a)^2 - 11 =
            (t + (sqrt 7 : ℂ)*a)^2 - (sqrt 11 : ℂ)^2 := by rw [h11]
        _ =
            (a^5 + (sqrt 2 : ℂ)*a^3 + (sqrt 5 : ℂ)*a^2 +
              (sqrt 7 : ℂ)*a + (sqrt 11 : ℂ)) *
            (a^5 + (sqrt 2 : ℂ)*a^3 + (sqrt 5 : ℂ)*a^2 +
              (sqrt 7 : ℂ)*a - (sqrt 11 : ℂ)) := by
                dsimp [t, z]
                ring
        _ = 0 := by rw [ha']; ring
    have ht7 : t^4 - (14*a^2 + 22)*t^2 + (7*a^2 - 11)^2 = 0 := by
      calc
        t^4 - (14*a^2 + 22)*t^2 + (7*a^2 - 11)^2 =
            t^4 - (2*(sqrt 7 : ℂ)^2*a^2 + 22)*t^2 +
              ((sqrt 7 : ℂ)^2*a^2 - 11)^2 := by rw [h7]; ring
        _ =
            ((t + (sqrt 7 : ℂ)*a)^2 - 11) *
            ((t - (sqrt 7 : ℂ)*a)^2 - 11) := by ring
        _ = 0 := by rw [ht11]; ring
    have hAB : A + (sqrt 5 : ℂ)*B = 0 := by
      have h5three : (sqrt 5 : ℂ)^3 = 5 * (sqrt 5 : ℂ) := by
        calc
          (sqrt 5 : ℂ)^3 = (sqrt 5 : ℂ)^2 * (sqrt 5 : ℂ) := by ring
          _ = 5 * (sqrt 5 : ℂ) := by rw [h5]
      have h5four : (sqrt 5 : ℂ)^4 = 25 := by
        calc
          (sqrt 5 : ℂ)^4 = ((sqrt 5 : ℂ)^2)^2 := by ring
          _ = 25 := by rw [h5]; norm_num
      calc
        A + (sqrt 5 : ℂ)*B =
            t^4 - (14*a^2 + 22)*t^2 + (7*a^2 - 11)^2 := by
              dsimp [A, B, U, V, t]
              ring_nf
              rw [h5, h5three, h5four]
              norm_num
              ring
        _ = 0 := ht7
    have hG : G z = 0 := by
      change A^2 - 5*B^2 = 0
      calc
        A^2 - 5*B^2 = A^2 - (sqrt 5 : ℂ)^2*B^2 := by rw [h5]
        _ = (A + (sqrt 5 : ℂ)*B) * (A - (sqrt 5 : ℂ)*B) := by ring
        _ = 0 := by rw [hAB]; ring
    have h4 : (sqrt 2 : ℂ)^4 = 4 := by calc
      (sqrt 2 : ℂ)^4 = ((sqrt 2 : ℂ)^2)^2 := by ring
      _ = 4 := by rw [h2]; norm_num
    have h6 : (sqrt 2 : ℂ)^6 = 8 := by calc
      (sqrt 2 : ℂ)^6 = ((sqrt 2 : ℂ)^2)^3 := by ring
      _ = 8 := by rw [h2]; norm_num
    have h8 : (sqrt 2 : ℂ)^8 = 16 := by calc
      (sqrt 2 : ℂ)^8 = ((sqrt 2 : ℂ)^2)^4 := by ring
      _ = 16 := by rw [h2]; norm_num
    have h10 : (sqrt 2 : ℂ)^10 = 32 := by calc
      (sqrt 2 : ℂ)^10 = ((sqrt 2 : ℂ)^2)^5 := by ring
      _ = 32 := by rw [h2]; norm_num
    have h12 : (sqrt 2 : ℂ)^12 = 64 := by calc
      (sqrt 2 : ℂ)^12 = ((sqrt 2 : ℂ)^2)^6 := by ring
      _ = 64 := by rw [h2]; norm_num
    have h14 : (sqrt 2 : ℂ)^14 = 128 := by calc
      (sqrt 2 : ℂ)^14 = ((sqrt 2 : ℂ)^2)^7 := by ring
      _ = 128 := by rw [h2]; norm_num
    have h16 : (sqrt 2 : ℂ)^16 = 256 := by calc
      (sqrt 2 : ℂ)^16 = ((sqrt 2 : ℂ)^2)^8 := by ring
      _ = 256 := by rw [h2]; norm_num
    have h3 : (sqrt 2 : ℂ)^3 = 2 * (sqrt 2 : ℂ) := by
      calc
        (sqrt 2 : ℂ)^3 = (sqrt 2 : ℂ)^2 * (sqrt 2 : ℂ) := by ring
        _ = 2 * (sqrt 2 : ℂ) := by rw [h2]
    have h5p : (sqrt 2 : ℂ)^5 = 4 * (sqrt 2 : ℂ) := by
      calc
        (sqrt 2 : ℂ)^5 = (sqrt 2 : ℂ)^4 * (sqrt 2 : ℂ) := by ring
        _ = 4 * (sqrt 2 : ℂ) := by rw [h4]
    have h7p : (sqrt 2 : ℂ)^7 = 8 * (sqrt 2 : ℂ) := by
      calc
        (sqrt 2 : ℂ)^7 = (sqrt 2 : ℂ)^6 * (sqrt 2 : ℂ) := by ring
        _ = 8 * (sqrt 2 : ℂ) := by rw [h6]
    have hGp : G (a^5 + (sqrt 2 : ℂ)*a^3) = C + (sqrt 2 : ℂ)*D := by
      dsimp [G, C, D]
      ring_nf
      rw [h2, h3, h4, h5p, h6, h7p, h8]
      norm_num
      ring
    have hGm : G (a^5 - (sqrt 2 : ℂ)*a^3) = C - (sqrt 2 : ℂ)*D := by
      dsimp [G, C, D]
      ring_nf
      rw [h2, h3, h4, h5p, h6, h7p, h8]
      norm_num
      ring
    calc
      Polynomial.eval a q = C^2 - 2*D^2 := by
        dsimp [q, C, D]
        simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
        ring
      _ = C^2 - (sqrt 2 : ℂ)^2*D^2 := by rw [h2]
      _ = G (a^5 + (sqrt 2 : ℂ)*a^3) *
          G (a^5 - (sqrt 2 : ℂ)*a^3) := by
            rw [hGp, hGm]
            ring
      _ = 0 := by dsimp [z] at hG; rw [hG]; ring
  refine ⟨q, hq0, hqdeg, (Polynomial.mem_roots hq0).2 hroot, ?_⟩
  intro n
  refine ⟨qz.coeff n, 1, ?_⟩
  have hmap : q = qz.map (Int.castRingHom ℂ) := by
    dsimp [q, qz]
    set_option maxRecDepth 10000 in norm_num
  calc
    q.coeff n = (qz.map (Int.castRingHom ℂ)).coeff n := congrArg (fun r => r.coeff n) hmap
    _ = (qz.coeff n : ℂ) := Polynomial.coeff_map _ _
    _ = (qz.coeff n : ℂ) / (1 : ℤ) := by norm_num
