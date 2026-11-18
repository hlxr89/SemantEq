import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

set_option maxHeartbeats 1000000

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2c_assumed : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : Irreducible (Polynomial.C (1 : ℤ) + Polynomial.X + 6 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
  let p : Polynomial (ZMod 2) := X^4 + X + 1
  have hpimd : IsMonicOfDegree p 4 := by
    dsimp [p]
    rw [show X ^ 4 + X + 1 = X ^ 4 + (X + 1) by ring]
    apply (isMonicOfDegree_X_pow (ZMod 2) 4).add_right
    compute_degree <;> norm_num
  have hpmonic : p.Monic := hpimd.monic
  have hpdeg : p.natDegree = 4 := hpimd.natDegree_eq
  have hp : Irreducible p := by
    apply (hpmonic.irreducible_iff_lt_natDegree_lt (by
      intro h
      have h' := congrArg Polynomial.natDegree h
      simp [hpdeg] at h')).2
    intro q hq hqd
    rw [hpdeg] at hqd
    simp only [Finset.mem_Ioc] at hqd
    by_cases hq1 : q.natDegree = 1
    · obtain ⟨a, ha⟩ := isMonicOfDegree_one_iff.mp
        (show IsMonicOfDegree q 1 from ⟨hq1, hq⟩)
      rw [ha]
      intro hdvd
      fin_cases a
      · have hz := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd (x := (0 : ZMod 2)) (by norm_num)
        exact (by decide : (1 : ZMod 2) ≠ 0) (by simpa [p] using hz)
      · have hz := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd (x := (1 : ZMod 2))
          (by simpa using CharTwo.add_self_eq_zero (1 : ZMod 2))
        exact (by decide : (1 : ZMod 2) ≠ 0)
          (by simpa [p, CharTwo.add_self_eq_zero] using hz)
    · have hq2 : q.natDegree = 2 := by omega
      obtain ⟨a, b, hab⟩ := isMonicOfDegree_two_iff.mp
        (show IsMonicOfDegree q 2 from ⟨hq2, hq⟩)
      rw [hab]
      rintro ⟨r, hr⟩
      have hrmonic : r.Monic := (isMonicOfDegree_add_add_two a b).monic.of_mul_monic_left
        (hr ▸ hpmonic)
      have hrdeg : r.natDegree = 2 := by
        have h := (isMonicOfDegree_add_add_two a b).monic.natDegree_mul hrmonic
        rw [← hr, hpdeg, (isMonicOfDegree_add_add_two a b).natDegree_eq] at h
        omega
      obtain ⟨c, d, hcd⟩ := isMonicOfDegree_two_iff.mp
        (show IsMonicOfDegree r 2 from ⟨hrdeg, hrmonic⟩)
      rw [hcd] at hr
      ring_nf at hr
      have bad := congrArg (fun s : Polynomial (ZMod 2) =>
        (s.coeff 0, s.coeff 1, s.coeff 2, s.coeff 3, s.coeff 4)) hr
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [p] at bad <;> simp [CharTwo.add_self_eq_zero] at bad <;>
        have htwo : (2 : ZMod 2) = 0 := (by decide) <;>
        exact one_ne_zero (bad.1.trans htwo)
  let f : Polynomial ℤ := C 1 + X + 6*X^2 + 4*X^3 + X^4
  have hfimd : IsMonicOfDegree f 4 := by
    have heq : f = X^4 + (4*X^3 + 6*X^2 + X + 1) := by
      dsimp [f]
      simp
      ring
    rw [heq]
    apply (isMonicOfDegree_X_pow ℤ 4).add_right
    compute_degree <;> norm_num
  apply hfimd.monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
  have hmap : f.map (Int.castRingHom (ZMod 2)) = p := by
    dsimp [f, p]
    have h6 : (6 : Polynomial (ZMod 2)) = 0 := by
      change C (6 : ZMod 2) = 0
      rw [show (6 : ZMod 2) = 0 by decide]
      simp
    have h4 : (4 : Polynomial (ZMod 2)) = 0 := by
      change C (4 : ZMod 2) = 0
      rw [show (4 : ZMod 2) = 0 by decide]
      simp
    simp [h6, h4]
    ring
  rw [hmap]
  exact hp
