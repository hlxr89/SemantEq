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
  by_cases hp2 : p = 2
  · subst p
    exact ⟨∅, ∅, by simp⟩
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd.resolve_left hp2)
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases exercise_4_4_9_assumed p hp hodd with
    ⟨⟨S, h0S, hcardS, hsquare⟩, ⟨T, h0T, hcardT, hnonsquare⟩⟩
  let S' : Finset ℕ := S.image ZMod.val
  let T' : Finset ℕ := T.image ZMod.val
  refine ⟨S', T', ?_, ?_, ?_⟩
  · dsimp [S']
    rw [Finset.card_image_of_injective S (ZMod.val_injective p)]
    exact hcardS
  · dsimp [T']
    rw [Finset.card_image_of_injective T (ZMod.val_injective p)]
    exact hcardT
  · intro k hk
    simp only [S', Finset.mem_image] at hk
    rcases hk with ⟨q, hqS, rfl⟩
    rcases hsquare q hqS with ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hx
      exact h0S (hx ▸ hqS)
    have hq0 : q ≠ 0 := fun hq => h0S (hq ▸ hqS)
    by_cases hlt : x.val < p - 1
    · refine ⟨x.val, Finset.mem_range.mpr hlt, (ZMod.val_ne_zero x).mpr hx0, ?_, ?_⟩
      · rw [← ZMod.natCast_eq_natCast_iff]
        simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hx
      · intro k hkT
        simp only [T', Finset.mem_image] at hkT
        rcases hkT with ⟨r, hrT, rfl⟩
        intro ha
        rcases ha with ⟨a, haRange, ha0, haMod⟩
        apply hnonsquare r hrT
        refine ⟨(a : ZMod p), ?_⟩
        simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using
          (ZMod.natCast_eq_natCast_iff (a ^ 2) r.val p).mpr haMod
    · have hxval : x.val = p - 1 := by
        have hxlt : x.val < p := ZMod.val_lt x
        omega
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      refine ⟨1, Finset.mem_range.mpr (by omega), one_ne_zero, ?_, ?_⟩
      · rw [← ZMod.natCast_eq_natCast_iff]
        have hxneg : x = (-1 : ZMod p) := by
          rw [← ZMod.natCast_zmod_val x, hxval]
          rw [Nat.cast_sub hp.one_le, ZMod.natCast_self]
          simp
        rw [← ZMod.natCast_zmod_val q, ← hx, hxneg]
        simp
      · intro k hkT
        simp only [T', Finset.mem_image] at hkT
        rcases hkT with ⟨r, hrT, rfl⟩
        intro ha
        rcases ha with ⟨a, haRange, ha0, haMod⟩
        apply hnonsquare r hrT
        refine ⟨(a : ZMod p), ?_⟩
        simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using
          (ZMod.natCast_eq_natCast_iff (a ^ 2) r.val p).mpr haMod
