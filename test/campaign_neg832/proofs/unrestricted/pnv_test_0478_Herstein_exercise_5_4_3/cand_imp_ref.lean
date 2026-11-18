import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℚ[X]} (h : p.eval a = 0) (hp : natDegree p ≤ 80) : IsAlgebraic ℚ a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem exercise_5_4_3 {a : ℂ} {p : ℂ → ℂ}
  (hp : p = λ (x : ℂ) => x^5 + sqrt 2 * x^3 + sqrt 5 * x^2 + sqrt 7 * x + sqrt 11)
  (ha : p a = 0) :
  ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.degree ≤ 80 ∧ a ∈ q.roots ∧
  ∀ n : q.support, ∃ a b : ℤ, q.coeff n = a / b := by
  let qZ : ℤ[X] :=
      X ^ 80
      + C (-16 : ℤ) * X ^ 76
      + C (-40 : ℤ) * X ^ 74
      + C (56 : ℤ) * X ^ 72
      + C (312 : ℤ) * X ^ 70
      + C (812 : ℤ) * X ^ 68
      + C (840 : ℤ) * X ^ 66
      + C (-924 : ℤ) * X ^ 64
      + C (-17808 : ℤ) * X ^ 62
      + C (-31580 : ℤ) * X ^ 60
      + C (336 : ℤ) * X ^ 58
      + C (151966 : ℤ) * X ^ 56
      + C (303384 : ℤ) * X ^ 54
      + C (-815980 : ℤ) * X ^ 52
      + C (-85584 : ℤ) * X ^ 50
      + C (1618666 : ℤ) * X ^ 48
      + C (784696 : ℤ) * X ^ 46
      + C (14780424 : ℤ) * X ^ 44
      + C (-15529624 : ℤ) * X ^ 42
      + C (-8183302 : ℤ) * X ^ 40
      + C (-60091064 : ℤ) * X ^ 38
      + C (38384032 : ℤ) * X ^ 36
      + C (-326561904 : ℤ) * X ^ 34
      + C (495133661 : ℤ) * X ^ 32
      + C (160385872 : ℤ) * X ^ 30
      + C (-900140804 : ℤ) * X ^ 28
      + C (926472368 : ℤ) * X ^ 26
      + C (1440591982 : ℤ) * X ^ 24
      + C (-1646774472 : ℤ) * X ^ 22
      + C (-1939426788 : ℤ) * X ^ 20
      + C (1649794720 : ℤ) * X ^ 18
      + C (89715899 : ℤ) * X ^ 16
      + C (1495670792 : ℤ) * X ^ 14
      + C (-331895256 : ℤ) * X ^ 12
      + C (-2861245376 : ℤ) * X ^ 10
      + C (1851940090 : ℤ) * X ^ 8
      + C (-925076944 : ℤ) * X ^ 6
      + C (1651094852 : ℤ) * X ^ 4
      + C (-1091281576 : ℤ) * X ^ 2
      + C (214358881 : ℤ)
  let q : ℂ[X] := qZ.map (Int.castRingHom ℂ)
  have hq80 : q.coeff 80 = 1 := by
    simp [q, qZ]
  have hq0 : q ≠ 0 := by
    intro h
    simpa [h] using hq80
  have hs2 : ((sqrt 2 : ℂ) ^ 2) = 2 := by
    norm_cast
    exact sq_sqrt (by norm_num)
  have hs5 : ((sqrt 5 : ℂ) ^ 2) = 5 := by
    norm_cast
    exact sq_sqrt (by norm_num)
  have hs7 : ((sqrt 7 : ℂ) ^ 2) = 7 := by
    norm_cast
    exact sq_sqrt (by norm_num)
  have hs11 : ((sqrt 11 : ℂ) ^ 2) = 11 := by
    norm_cast
    exact sq_sqrt (by norm_num)
  have hs2_3 : ((sqrt 2 : ℂ) ^ 3) = 2 * (sqrt 2 : ℂ) := by
    rw [show ((sqrt 2 : ℂ) ^ 3) = (((sqrt 2 : ℂ) ^ 2) ^ 1 * (sqrt 2 : ℂ)) by ring, hs2]
    norm_num
  have hs2_4 : ((sqrt 2 : ℂ) ^ 4) = 4 := by
    rw [show ((sqrt 2 : ℂ) ^ 4) = (((sqrt 2 : ℂ) ^ 2) ^ 2) by ring, hs2]
    norm_num
  have hs2_5 : ((sqrt 2 : ℂ) ^ 5) = 4 * (sqrt 2 : ℂ) := by
    rw [show ((sqrt 2 : ℂ) ^ 5) = (((sqrt 2 : ℂ) ^ 2) ^ 2 * (sqrt 2 : ℂ)) by ring, hs2]
    norm_num
  have hs2_6 : ((sqrt 2 : ℂ) ^ 6) = 8 := by
    rw [show ((sqrt 2 : ℂ) ^ 6) = (((sqrt 2 : ℂ) ^ 2) ^ 3) by ring, hs2]
    norm_num
  have hs2_7 : ((sqrt 2 : ℂ) ^ 7) = 8 * (sqrt 2 : ℂ) := by
    rw [show ((sqrt 2 : ℂ) ^ 7) = (((sqrt 2 : ℂ) ^ 2) ^ 3 * (sqrt 2 : ℂ)) by ring, hs2]
    norm_num
  have hs2_8 : ((sqrt 2 : ℂ) ^ 8) = 16 := by
    rw [show ((sqrt 2 : ℂ) ^ 8) = (((sqrt 2 : ℂ) ^ 2) ^ 4) by ring, hs2]
    norm_num
  have hs5_3 : ((sqrt 5 : ℂ) ^ 3) = 5 * (sqrt 5 : ℂ) := by
    rw [show ((sqrt 5 : ℂ) ^ 3) = (((sqrt 5 : ℂ) ^ 2) ^ 1 * (sqrt 5 : ℂ)) by ring, hs5]
    norm_num
  have hs5_4 : ((sqrt 5 : ℂ) ^ 4) = 25 := by
    rw [show ((sqrt 5 : ℂ) ^ 4) = (((sqrt 5 : ℂ) ^ 2) ^ 2) by ring, hs5]
    norm_num
  have hs5_5 : ((sqrt 5 : ℂ) ^ 5) = 25 * (sqrt 5 : ℂ) := by
    rw [show ((sqrt 5 : ℂ) ^ 5) = (((sqrt 5 : ℂ) ^ 2) ^ 2 * (sqrt 5 : ℂ)) by ring, hs5]
    norm_num
  have hs5_6 : ((sqrt 5 : ℂ) ^ 6) = 125 := by
    rw [show ((sqrt 5 : ℂ) ^ 6) = (((sqrt 5 : ℂ) ^ 2) ^ 3) by ring, hs5]
    norm_num
  have hs5_7 : ((sqrt 5 : ℂ) ^ 7) = 125 * (sqrt 5 : ℂ) := by
    rw [show ((sqrt 5 : ℂ) ^ 7) = (((sqrt 5 : ℂ) ^ 2) ^ 3 * (sqrt 5 : ℂ)) by ring, hs5]
    norm_num
  have hs5_8 : ((sqrt 5 : ℂ) ^ 8) = 625 := by
    rw [show ((sqrt 5 : ℂ) ^ 8) = (((sqrt 5 : ℂ) ^ 2) ^ 4) by ring, hs5]
    norm_num
  have hs7_3 : ((sqrt 7 : ℂ) ^ 3) = 7 * (sqrt 7 : ℂ) := by
    rw [show ((sqrt 7 : ℂ) ^ 3) = (((sqrt 7 : ℂ) ^ 2) ^ 1 * (sqrt 7 : ℂ)) by ring, hs7]
    norm_num
  have hs7_4 : ((sqrt 7 : ℂ) ^ 4) = 49 := by
    rw [show ((sqrt 7 : ℂ) ^ 4) = (((sqrt 7 : ℂ) ^ 2) ^ 2) by ring, hs7]
    norm_num
  have hs7_5 : ((sqrt 7 : ℂ) ^ 5) = 49 * (sqrt 7 : ℂ) := by
    rw [show ((sqrt 7 : ℂ) ^ 5) = (((sqrt 7 : ℂ) ^ 2) ^ 2 * (sqrt 7 : ℂ)) by ring, hs7]
    norm_num
  have hs7_6 : ((sqrt 7 : ℂ) ^ 6) = 343 := by
    rw [show ((sqrt 7 : ℂ) ^ 6) = (((sqrt 7 : ℂ) ^ 2) ^ 3) by ring, hs7]
    norm_num
  have hs7_7 : ((sqrt 7 : ℂ) ^ 7) = 343 * (sqrt 7 : ℂ) := by
    rw [show ((sqrt 7 : ℂ) ^ 7) = (((sqrt 7 : ℂ) ^ 2) ^ 3 * (sqrt 7 : ℂ)) by ring, hs7]
    norm_num
  have hs7_8 : ((sqrt 7 : ℂ) ^ 8) = 2401 := by
    rw [show ((sqrt 7 : ℂ) ^ 8) = (((sqrt 7 : ℂ) ^ 2) ^ 4) by ring, hs7]
    norm_num
  have hs11_3 : ((sqrt 11 : ℂ) ^ 3) = 11 * (sqrt 11 : ℂ) := by
    rw [show ((sqrt 11 : ℂ) ^ 3) = (((sqrt 11 : ℂ) ^ 2) ^ 1 * (sqrt 11 : ℂ)) by ring, hs11]
    norm_num
  have hs11_4 : ((sqrt 11 : ℂ) ^ 4) = 121 := by
    rw [show ((sqrt 11 : ℂ) ^ 4) = (((sqrt 11 : ℂ) ^ 2) ^ 2) by ring, hs11]
    norm_num
  have hs11_5 : ((sqrt 11 : ℂ) ^ 5) = 121 * (sqrt 11 : ℂ) := by
    rw [show ((sqrt 11 : ℂ) ^ 5) = (((sqrt 11 : ℂ) ^ 2) ^ 2 * (sqrt 11 : ℂ)) by ring, hs11]
    norm_num
  have hs11_6 : ((sqrt 11 : ℂ) ^ 6) = 1331 := by
    rw [show ((sqrt 11 : ℂ) ^ 6) = (((sqrt 11 : ℂ) ^ 2) ^ 3) by ring, hs11]
    norm_num
  have hs11_7 : ((sqrt 11 : ℂ) ^ 7) = 1331 * (sqrt 11 : ℂ) := by
    rw [show ((sqrt 11 : ℂ) ^ 7) = (((sqrt 11 : ℂ) ^ 2) ^ 3 * (sqrt 11 : ℂ)) by ring, hs11]
    norm_num
  have hs11_8 : ((sqrt 11 : ℂ) ^ 8) = 14641 := by
    rw [show ((sqrt 11 : ℂ) ^ 8) = (((sqrt 11 : ℂ) ^ 2) ^ 4) by ring, hs11]
    norm_num
  let e2 (u v : ℂ) : ℂ :=
    a^20 + 4*a^18*u + 4*a^17*v + 6*a^16*u^2 + 12*a^15*u*v +
    4*a^14*u^3 + 6*a^14*v^2 + 12*a^13*u^2*v + a^12*u^4 +
    12*a^12*u*v^2 - 14*a^12 + 4*a^11*u^3*v + 4*a^11*v^3 +
    6*a^10*u^2*v^2 - 28*a^10*u - 22*a^10 + 4*a^9*u*v^3 -
    28*a^9*v - 14*a^8*u^2 - 44*a^8*u + a^8*v^4 - 28*a^7*u*v -
    44*a^7*v - 22*a^6*u^2 - 14*a^6*v^2 - 44*a^5*u*v -
    22*a^4*v^2 + 49*a^4 - 154*a^2 + 121
  have hprod : q.eval a =
      e2 (sqrt 2) (sqrt 5) * e2 (sqrt 2) (-(sqrt 5)) *
      e2 (-(sqrt 2)) (sqrt 5) * e2 (-(sqrt 2)) (-(sqrt 5)) := by
    simp [q, qZ, e2]
    ring_nf
    simp [hs2, hs5, hs2_3, hs2_4, hs2_5, hs2_6, hs2_7, hs2_8,
      hs5_3, hs5_4, hs5_5, hs5_6, hs5_7, hs5_8]
    ring_nf
    simp [hs2, hs5, hs2_3, hs2_4, hs2_5, hs2_6, hs2_7, hs2_8,
      hs5_3, hs5_4, hs5_5, hs5_6, hs5_7, hs5_8]
    ring_nf
  have hbase : a^5 + sqrt 2 * a^3 + sqrt 5 * a^2 + sqrt 7 * a + sqrt 11 = 0 := by
    rw [hp] at ha
    exact ha
  have he2factor : e2 (sqrt 2) (sqrt 5) =
      (a^5 + sqrt 2 * a^3 + sqrt 5 * a^2 + sqrt 7 * a + sqrt 11) *
      (a^5 + sqrt 2 * a^3 + sqrt 5 * a^2 + sqrt 7 * a - sqrt 11) *
      (a^5 + sqrt 2 * a^3 + sqrt 5 * a^2 - sqrt 7 * a + sqrt 11) *
      (a^5 + sqrt 2 * a^3 + sqrt 5 * a^2 - sqrt 7 * a - sqrt 11) := by
    simp [e2]
    ring_nf
    simp [hs7, hs11, hs7_3, hs7_4, hs7_5, hs7_6, hs7_7, hs7_8,
      hs11_3, hs11_4, hs11_5, hs11_6, hs11_7, hs11_8]
    ring_nf
  have he2zero : e2 (sqrt 2) (sqrt 5) = 0 := by
    simp [he2factor, hbase]
  have hroot : q.eval a = 0 := by
    simp [hprod, he2zero]
  have hqZdeg : qZ.natDegree ≤ 80 := by
    dsimp [qZ]
    compute_degree
  refine ⟨q, hq0, ?_, ?_, ?_⟩
  · apply degree_le_of_natDegree_le
    have hmap : q.natDegree ≤ qZ.natDegree := by
      simpa [q] using (natDegree_map_le :
        (qZ.map (Int.castRingHom ℂ)).natDegree ≤ qZ.natDegree)
    exact hmap.trans hqZdeg
  · rw [mem_roots hq0]
    exact hroot
  · intro n
    refine ⟨qZ.coeff n, 1, ?_⟩
    simp [q]

