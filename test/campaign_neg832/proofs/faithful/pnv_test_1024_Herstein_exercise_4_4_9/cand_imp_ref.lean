import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact p.Prime] : (∃ n, n = (p - 1) / 2 ∧ (∃ (quadratic_residues : Finset (ZMod p)) (quadratic_nonresidues : Finset (ZMod p)), quadratic_residues.card = n ∧ quadratic_nonresidues.card = n ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ quadratic_residues ∨ x ∈ quadratic_nonresidues) ∧ (x ∈ quadratic_residues ↔ ¬ (x ∈ quadratic_nonresidues)))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, A, B, hA, hB, hpart⟩ := dummy_assumed p
  let D : Finset (ZMod p) := Finset.univ.erase 0
  let R : Finset (ZMod p) := D.image (fun x => x ^ 2)
  let N : Finset (ZMod p) := D \ R
  have htwo : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hp2 : 2 ≤ p := hp.two_le
    have hpne : p ≠ 2 := by
      intro heq
      subst p
      simp at hodd
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hDcard : D.card = p - 1 := by
    rw [show D = Finset.univ.erase 0 from rfl,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
  have hfiber : ∀ b ∈ R, ({a ∈ D | a ^ 2 = b}).card = 2 := by
    intro b hb
    obtain ⟨a, haD, ha⟩ := Finset.mem_image.mp hb
    rw [Finset.card_eq_two]
    refine ⟨a, -a, ?_, ?_⟩
    · intro haa
      have hzero : (2 : ZMod p) * a = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp haa
      exact (Finset.mem_erase.mp haD).1 ((mul_eq_zero.mp hzero).resolve_left htwo)
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxD, hx⟩
        exact sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans ha.symm)
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨haD, ha⟩
        · exact ⟨by simpa [D] using haD, by simpa using ha⟩
  have hcount : D.card = R.card * 2 := by
    calc
      D.card = ∑ b ∈ R, ({a ∈ D | a ^ 2 = b}).card :=
        Finset.card_eq_sum_card_fiberwise (by
          intro a haD
          exact Finset.mem_image.mpr ⟨a, haD, rfl⟩)
      _ = R.card * 2 := Finset.sum_const_nat hfiber
  have hRcard_n : R.card = n := by
    rw [hn]
    rw [hDcard] at hcount
    omega
  have hRcard : R.card = (p - 1) / 2 := hRcard_n.trans hn
  have hRsub : R ⊆ D := by
    intro q hq
    obtain ⟨x, hxD, rfl⟩ := Finset.mem_image.mp hq
    have hx0 := (Finset.mem_erase.mp hxD).1
    simp only [D, Finset.mem_erase, Finset.mem_univ, and_true]
    exact pow_ne_zero 2 hx0
  have hNcard : N.card = (p - 1) / 2 := by
    rw [show N = D \ R from rfl, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hRsub, hDcard, hRcard]
    omega
  constructor
  · refine ⟨R, ?_, hRcard, ?_⟩
    · intro h0
      exact (Finset.mem_erase.mp (hRsub h0)).1 rfl
    · intro q hq
      obtain ⟨x, hxD, hx⟩ := Finset.mem_image.mp hq
      exact ⟨x, hx⟩
  · refine ⟨N, ?_, hNcard, ?_⟩
    · intro h0
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp h0).1).1 rfl
    · intro q hq
      intro hsquare
      obtain ⟨x, hx⟩ := hsquare
      have hqD := (Finset.mem_sdiff.mp hq).1
      have hx0 : x ≠ 0 := by
        intro hxzero
        subst x
        exact (Finset.mem_erase.mp hqD).1 (by simpa using hx.symm)
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_image.mpr ⟨x, by
        simp only [D, Finset.mem_erase, Finset.mem_univ, and_true]
        exact hx0, hx⟩)
