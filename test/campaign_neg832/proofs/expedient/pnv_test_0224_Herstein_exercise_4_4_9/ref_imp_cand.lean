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
  rcases hp.eq_two_or_odd with h2 | hodd
  · subst p
    exact ⟨∅, ∅, by simp⟩
  · obtain ⟨⟨S, hS0, hScard, hS⟩, ⟨T, hT0, hTcard, hT⟩⟩ :=
      exercise_4_4_9_assumed p hp hodd
    letI : NeZero p := ⟨hp.ne_zero⟩
    let SN : Finset ℕ := S.image ZMod.val
    let TN : Finset ℕ := T.image ZMod.val
    have hvalinj : Function.Injective (ZMod.val : ZMod p → ℕ) := ZMod.val_injective p
    have hSN : SN.card = (p - 1) / 2 := by
      simp only [SN]
      rw [Finset.card_image_of_injective S hvalinj, hScard]
    have hTN : TN.card = (p - 1) / 2 := by
      simp only [TN]
      rw [Finset.card_image_of_injective T hvalinj, hTcard]
    refine ⟨SN, TN, hSN, hTN, ?_⟩
    intro k hk
    simp only [SN, Finset.mem_image] at hk
    obtain ⟨q, hqS, rfl⟩ := hk
    obtain ⟨x, hx⟩ := hS q hqS
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      apply hS0
      have hq0 : q = 0 := by simpa using hx.symm
      exact hq0 ▸ hqS
    let a := if x.val = p - 1 then 1 else x.val
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have ha0 : a ≠ 0 := by
      simp only [a]
      split_ifs with h
      · norm_num
      · exact fun hv => hx0 (by rw [← ZMod.natCast_zmod_val x, hv]; simp)
    have halt : a < p - 1 := by
      simp only [a]
      split_ifs with h
      · omega
      · have hxlt := x.val_lt
        omega
    refine ⟨a, Finset.mem_range.2 halt, ha0, ?_, ?_⟩
    · rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp only [a]
      split_ifs with h
      · have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
          rw [Nat.cast_sub (by omega)]
          simp
        calc
          ((1 : ℕ) : ZMod p) ^ 2 = (-1 : ZMod p) ^ 2 := by ring
          _ = ((p - 1 : ℕ) : ZMod p) ^ 2 := by rw [hcast]
          _ = x ^ 2 := by rw [← h, ZMod.natCast_zmod_val]
          _ = q := hx
      · simpa [ZMod.natCast_zmod_val] using hx
    · intro k hk
      simp only [TN, Finset.mem_image] at hk
      obtain ⟨q, hqT, rfl⟩ := hk
      rintro ⟨b, hb, hb0, hbmod⟩
      apply hT q hqT
      refine ⟨(b : ZMod p), ?_⟩
      rw [← ZMod.natCast_zmod_val q]
      simpa only [Nat.cast_pow] using
        (ZMod.natCast_eq_natCast_iff (b ^ 2) q.val p).2 hbmod
