import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_4_9_assumed (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {p : ℕ} (hp : p.Prime) : ∃ (S : Finset ℕ) (T : Finset ℕ), S.card = (p - 1) / 2 ∧ T.card = (p - 1) / 2 ∧ ∀ (k : ℕ), k ∈ S → ∃ (a : ℕ), a ∈ Finset.range (p - 1) ∧ a ≠ 0 ∧ a ^ 2 ≡ k [MOD p] ∧ ∀ (k : ℕ), k ∈ T → ¬∃ (a : ℕ), a ∈ Finset.range (p - 1) ∧ a ≠ 0 ∧ a ^ 2 ≡ k [MOD p] := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · refine ⟨∅, ∅, by norm_num, by norm_num, ?_⟩
    simp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases exercise_4_4_9_assumed p hp hodd with
    ⟨⟨S, hS0, hScard, hSsq⟩, ⟨T, hT0, hTcard, hTnsq⟩⟩
  refine ⟨S.image ZMod.val, T.image ZMod.val, ?_, ?_, ?_⟩
  · simpa using (Finset.card_image_of_injective S (ZMod.val_injective p)).trans hScard
  · simpa using (Finset.card_image_of_injective T (ZMod.val_injective p)).trans hTcard
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨q, hqS, rfl⟩
    rcases hSsq q hqS with ⟨x, hxq⟩
    have hq0 : q ≠ 0 := fun h => hS0 (h ▸ hqS)
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hxq
      exact hq0 hxq.symm
    letI : NeZero x := ⟨hx0⟩
    let y : ZMod p := if x.val = p - 1 then -x else x
    have hyq : y ^ 2 = q := by
      simp only [y]
      split <;> simp_all
    have hy0 : y ≠ 0 := by
      simp only [y]
      split <;> simp_all
    have hyval_ne : y.val ≠ p - 1 := by
      simp only [y]
      split
      · rw [ZMod.val_neg_of_ne_zero]
        omega
      · assumption
    refine ⟨y.val, ?_, (ZMod.val_eq_zero y).not.mpr hy0, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have := ZMod.val_lt y
      omega
    · apply (ZMod.natCast_eq_natCast_iff (y.val ^ 2) q.val p).mp
      simp only [Nat.cast_pow, ZMod.natCast_zmod_val, hyq]
    · intro k hk
      rcases Finset.mem_image.mp hk with ⟨q, hqT, rfl⟩
      intro ha
      rcases ha with ⟨a, haRange, ha0, haMod⟩
      apply hTnsq q hqT
      refine ⟨(a : ZMod p), ?_⟩
      have hcast := (ZMod.natCast_eq_natCast_iff (a ^ 2) q.val p).mpr haMod
      simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hcast
