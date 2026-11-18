import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (hp : p.Prime) : ∃ (S : Finset ℕ) (T : Finset ℕ), S.card = (p - 1) / 2 ∧ T.card = (p - 1) / 2 ∧ ∀ (k : ℕ), k ∈ S → ∃ (a : ℕ), a ∈ Finset.range (p - 1) ∧ a ≠ 0 ∧ a ^ 2 ≡ k [MOD p] ∧ ∀ (k : ℕ), k ∈ T → ¬∃ (a : ℕ), a ∈ Finset.range (p - 1) ∧ a ≠ 0 ∧ a ^ 2 ≡ k [MOD p] := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let H : Subgroup (ZMod p)ˣ := (powMonoidHom 2).range
  letI : Fintype H := Fintype.ofFinite H
  have hgcd : (p - 1).gcd 2 = 2 := by
    rw [Nat.gcd_eq_right_iff_dvd]
    omega
  have hHcard : Fintype.card H = (p - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    rw [show H = (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range from rfl]
    rw [IsCyclic.card_powMonoidHom_range]
    rw [Nat.card_eq_fintype_card, ZMod.card_units p, hgcd]
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rcases FiniteField.exists_nonsquare (F := ZMod p) hchar with ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    intro hnzero
    apply hn
    subst n
    exact ⟨0, by simp⟩
  let N : (ZMod p)ˣ := Units.mk0 n hn0
  let S : Finset (ZMod p) := Finset.univ.image (fun u : H => ((u : (ZMod p)ˣ) : ZMod p))
  let T : Finset (ZMod p) := Finset.univ.image (fun u : H => ((N * (u : (ZMod p)ˣ) : (ZMod p)ˣ) : ZMod p))
  have hcardS : S.card = (p - 1) / 2 := by
    dsimp [S]
    rw [Finset.card_image_of_injective Finset.univ]
    exact hHcard
    exact fun a b hab => Subtype.ext (Units.val_injective hab)
  have hmul_inj : Function.Injective (fun u : H => (N : ZMod p) * ((u : (ZMod p)ˣ) : ZMod p)) := by
    intro a b hab
    apply Subtype.ext
    have hab' : N * (a : (ZMod p)ˣ) = N * (b : (ZMod p)ˣ) := Units.val_injective hab
    exact mul_left_cancel hab'
  have hcardT : T.card = (p - 1) / 2 := by
    dsimp [T]
    rw [Finset.card_image_of_injective Finset.univ hmul_inj]
    exact hHcard
  constructor
  · refine ⟨S, ?_, hcardS, ?_⟩
    · intro hzero
      simp only [S, Finset.mem_image] at hzero
      rcases hzero with ⟨u, hu, hu0⟩
      exact (u : (ZMod p)ˣ).ne_zero hu0
    · intro q hq
      simp only [S, Finset.mem_image] at hq
      rcases hq with ⟨u, hu, rfl⟩
      have huH : (u : (ZMod p)ˣ) ∈ H := u.property
      rcases huH with ⟨v, hv⟩
      refine ⟨(v : ZMod p), ?_⟩
      simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val] using congrArg Units.val hv
  · refine ⟨T, ?_, hcardT, ?_⟩
    · intro hzero
      simp only [T, Finset.mem_image] at hzero
      rcases hzero with ⟨u, hu, hu0⟩
      exact (N * (u : (ZMod p)ˣ)).ne_zero hu0
    · intro q hq
      simp only [T, Finset.mem_image] at hq
      rcases hq with ⟨u, hu, rfl⟩
      have huH : (u : (ZMod p)ˣ) ∈ H := u.property
      rcases huH with ⟨v, hv⟩
      intro hsquare
      rcases hsquare with ⟨x, hx⟩
      apply hn
      refine ⟨x / (v : ZMod p), ?_⟩
      symm
      rw [← pow_two, div_pow, hx]
      simp only [N, Units.val_mul, Units.val_mk0]
      simp only [powMonoidHom_apply] at hv
      rw [← hv]
      simp
