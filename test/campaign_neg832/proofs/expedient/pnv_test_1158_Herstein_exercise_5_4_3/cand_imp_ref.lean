import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : Polynomial ℚ) (h0 : p ≠ 0) (h : p.natDegree = 5) (ha : a ∈ roots p) : ∃ q ∈ {q : Polynomial ℚ | Irreducible q ∧ q.natDegree ≤ 80}, q ∣ p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  subst p
  let qZ : Polynomial ℤ :=
    X^80 - 16*X^76 - 40*X^74 + 56*X^72 + 312*X^70 + 812*X^68 +
    840*X^66 - 924*X^64 - 17808*X^62 - 31580*X^60 + 336*X^58 +
    151966*X^56 + 303384*X^54 - 815980*X^52 - 85584*X^50 +
    1618666*X^48 + 784696*X^46 + 14780424*X^44 - 15529624*X^42 -
    8183302*X^40 - 60091064*X^38 + 38384032*X^36 - 326561904*X^34 +
    495133661*X^32 + 160385872*X^30 - 900140804*X^28 + 926472368*X^26 +
    1440591982*X^24 - 1646774472*X^22 - 1939426788*X^20 + 1649794720*X^18 +
    89715899*X^16 + 1495670792*X^14 - 331895256*X^12 - 2861245376*X^10 +
    1851940090*X^8 - 925076944*X^6 + 1651094852*X^4 - 1091281576*X^2 +
    214358881
  let q : Polynomial ℂ := qZ.map (Int.castRingHom ℂ)
  have hqne : q ≠ 0 := by
    intro hq
    have := congrArg (fun r : Polynomial ℂ => r.coeff 80) hq
    norm_num [q, qZ] at this
  have hqdeg : q.degree ≤ 80 := by
    apply (Polynomial.degree_map_le).trans
    dsimp [qZ]
    compute_degree
  refine ⟨q, hqne, hqdeg, ?_, ?_⟩
  · rw [Polynomial.mem_roots hqne]
    have h2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have h5 : (Real.sqrt 5 : ℂ)^2 = 5 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have h7 : (Real.sqrt 7 : ℂ)^2 = 7 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have h11 : (Real.sqrt 11 : ℂ)^2 = 11 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    let f (u v w z : ℂ) := a^5 + u*a^3 + v*a^2 + w*a + z
    let g (u v w : ℂ) := (a^5 + u*a^3 + v*a^2 + w*a)^2 - 11
    let t (u v : ℂ) := a^5 + u*a^3 + v*a^2
    let h (u v : ℂ) := (t u v ^ 2 + 7*a^2 - 11)^2 - 7*(2*a*t u v)^2
    let k (u : ℂ) := h u (Real.sqrt 5) * h u (-Real.sqrt 5)
    have hf : f (Real.sqrt 2) (Real.sqrt 5) (Real.sqrt 7) (Real.sqrt 11) = 0 := by
      simpa [f] using ha
    have hfg (u v w : ℂ) :
        f u v w (Real.sqrt 11) * f u v w (-Real.sqrt 11) = g u v w := by
      dsimp [f, g]
      ring_nf
      rw [h11]
      ring
    have hg : g (Real.sqrt 2) (Real.sqrt 5) (Real.sqrt 7) = 0 := by
      rw [← hfg]
      rw [hf]
      simp
    have hgh (u v : ℂ) :
        g u v (Real.sqrt 7) * g u v (-Real.sqrt 7) = h u v := by
      dsimp [g, h, t]
      ring_nf
      rw [show (Real.sqrt 7 : ℂ)^4 = ((Real.sqrt 7 : ℂ)^2)^2 by ring, h7]
      ring
    have hh : h (Real.sqrt 2) (Real.sqrt 5) = 0 := by
      rw [← hgh]
      rw [hg]
      simp
    have hk : k (Real.sqrt 2) = 0 := by
      dsimp [k]
      rw [hh]
      simp
    have hs2 (n : ℕ) : (Real.sqrt 2 : ℂ)^(2*n) = 2^n := by
      rw [show (Real.sqrt 2 : ℂ)^(2*n) = ((Real.sqrt 2 : ℂ)^2)^n by rw [pow_mul], h2]
    have hs5 (n : ℕ) : (Real.sqrt 5 : ℂ)^(2*n) = 5^n := by
      rw [show (Real.sqrt 5 : ℂ)^(2*n) = ((Real.sqrt 5 : ℂ)^2)^n by rw [pow_mul], h5]
    have h24 := hs2 2
    have h26 := hs2 3
    have h28 := hs2 4
    have h210 := hs2 5
    have h212 := hs2 6
    have h214 := hs2 7
    have h216 := hs2 8
    have h54 := hs5 2
    have h56 := hs5 3
    have h58 := hs5 4
    norm_num at h24 h26 h28 h210 h212 h214 h216 h54 h56 h58
    have hqk : q.eval a = k (Real.sqrt 2) * k (-Real.sqrt 2) := by
      simp [q, qZ]
      dsimp [k, h, t]
      ring_nf
      simp only [h2, h24, h26, h28, h210, h212, h214, h216, h5, h54, h56, h58]
      ring_nf
      simp only [h2, h24, h26, h28, h210, h212, h214, h216, h5, h54, h56, h58]
      ring
    change q.eval a = 0
    rw [hqk, hk]
    simp
  · intro n
    refine ⟨qZ.coeff n, 1, ?_⟩
    simp [q]
