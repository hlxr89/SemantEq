import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℕ) [Fact p.Prime] : (∃ n, n = (p - 1) / 2 ∧ (∃ (quadratic_residues : Finset (ZMod p)) (quadratic_nonresidues : Finset (ZMod p)), quadratic_residues.card = n ∧ quadratic_nonresidues.card = n ∧ ∀ x : ZMod p, x ≠ 0 → (x ∈ quadratic_residues ∨ x ∈ quadratic_nonresidues) ∧ (x ∈ quadratic_residues ↔ ¬ (x ∈ quadratic_nonresidues)))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  letI : Fact p.Prime := ⟨hp⟩
  let nonzero : Finset (ZMod p) := Finset.univ.erase 0
  let residues : Finset (ZMod p) := nonzero.image (fun x => x ^ 2)
  let nonresidues : Finset (ZMod p) := nonzero.filter (fun q => q ∉ residues)
  have hp2 : p ≠ 2 := by omega
  have hres0 : 0 ∉ residues := by
    intro h
    rcases Finset.mem_image.mp h with ⟨x, hx, hx2⟩
    have hx0 : x ≠ 0 := by simpa [nonzero] using hx
    have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    exact this hx2
  have hres_sq : ∀ q ∈ residues, ∃ x : ZMod p, x ^ 2 = q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hnonres0 : 0 ∉ nonresidues := by
    simp [nonresidues, nonzero]
  have hnonres_nsq : ∀ q ∈ nonresidues, ¬ ∃ x : ZMod p, x ^ 2 = q := by
    intro q hq
    simp only [nonresidues, Finset.mem_filter] at hq
    have hq0 : q ≠ 0 := by simpa [nonzero] using hq.1
    rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro hxzero
      apply hq0
      rw [← hx]
      simp [hxzero]
    apply hq.2
    apply Finset.mem_image.mpr
    exact ⟨x, by simp [nonzero, hx0], hx⟩
  have hnonzero_card : nonzero.card = p - 1 := by
    simp [nonzero, ZMod.card]
  have hfiber (q : ZMod p) (hq : q ∈ residues) :
      (nonzero.filter fun x => x ^ 2 = q).card = 2 := by
    have hq0 : q ≠ 0 := by
      intro hqzero
      subst q
      exact hres0 hq
    rcases hres_sq q hq with ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro hbzero
      apply hq0
      rw [← hb]
      simp [hbzero]
    have hbneg : b ≠ -b := by
      intro heq
      have : b = 0 :=
        (Ring.eq_self_iff_eq_zero_of_char_ne_two
          ((ZMod.ringChar_zmod_n p).substr hp2)).mp heq.symm
      exact hb0 this
    have heq : (nonzero.filter fun x => x ^ 2 = q) = {b, -b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        exact hx.2.trans hb.symm
      · rintro (rfl | rfl)
        · exact ⟨by simp [nonzero, hb0], hb⟩
        · exact ⟨by simp [nonzero, hb0], by simpa using hb⟩
    rw [heq]
    exact Finset.card_pair hbneg
  have hcount : nonzero.card = residues.card * 2 := by
    calc
      nonzero.card = ∑ q ∈ residues, (nonzero.filter fun x => x ^ 2 = q).card :=
        Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      _ = ∑ _q ∈ residues, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hfiber q hq
      _ = residues.card * 2 := by simp
  have hres_card : residues.card = (p - 1) / 2 := by
    omega
  have hpartition : nonzero = residues ∪ nonresidues := by
    ext q
    by_cases hq : q ∈ residues
    · have hq_nonzero : q ∈ nonzero := by
        rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
        have hx0 : x ≠ 0 := by simpa [nonzero] using hx
        simp [nonzero, pow_ne_zero 2 hx0]
      simp [hq, hq_nonzero]
    · simp [nonresidues, hq]
  have hdisj : Disjoint residues nonresidues := by
    rw [Finset.disjoint_left]
    intro a ha hna
    have hna' : a ∈ nonzero ∧ a ∉ residues := by simpa [nonresidues] using hna
    exact hna'.2 ha
  have hnonres_card : nonresidues.card = (p - 1) / 2 := by
    have hc := congrArg Finset.card hpartition
    rw [Finset.card_union_of_disjoint hdisj, hnonzero_card, hres_card] at hc
    omega
  exact ⟨⟨residues, hres0, hres_card, hres_sq⟩,
    ⟨nonresidues, hnonres0, hnonres_card, hnonres_nsq⟩⟩
