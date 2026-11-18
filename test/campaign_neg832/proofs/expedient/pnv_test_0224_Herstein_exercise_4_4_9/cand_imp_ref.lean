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
  let H := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  let K := {u : (ZMod p)ˣ // u ∉ H}
  let A : Finset (ZMod p) := Finset.univ.image (fun u : H => (u.1 : ZMod p))
  let B : Finset (ZMod p) := Finset.univ.image (fun u : K => (u.1 : ZMod p))
  have hp2 : 2 ≤ p := hp.two_le
  have heven : Even (p - 1) := by
    rw [Nat.even_iff]
    omega
  have hgcd : (p - 1).gcd 2 = 2 := Nat.gcd_eq_right_iff_dvd.2 heven.two_dvd
  have hH : Nat.card H = (p - 1) / 2 := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card,
      ZMod.card_units p, hgcd]
  have hK : Nat.card K = (p - 1) / 2 := by
    simp only [K, Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl,
      show Fintype.card (ZMod p)ˣ = p - 1 by exact ZMod.card_units p,
      show Fintype.card H = (p - 1) / 2 by simpa [Nat.card_eq_fintype_card] using hH]
    omega
  have hA : A.card = (p - 1) / 2 := by
    simp only [A]
    rw [Finset.card_image_iff.mpr]
    · simpa [Nat.card_eq_fintype_card] using hH
    · intro a _ b _ hab
      exact Subtype.ext (Units.ext hab)
  have hB : B.card = (p - 1) / 2 := by
    simp only [B]
    rw [Finset.card_image_iff.mpr]
    · simpa [Nat.card_eq_fintype_card] using hK
    · intro a _ b _ hab
      exact Subtype.ext (Units.ext hab)
  constructor
  · refine ⟨A, ?_, hA, ?_⟩
    · simp [A]
    · intro q hq
      simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨u, rfl⟩ := hq
      obtain ⟨v, hv⟩ := u.2
      exact ⟨(v : ZMod p), congrArg Units.val hv⟩
  · refine ⟨B, ?_, hB, ?_⟩
    · simp [B]
    · intro q hq
      simp only [B, Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨u, rfl⟩ := hq
      rintro ⟨x, hx⟩
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        exact u.1.ne_zero (by simpa using hx.symm)
      let v : (ZMod p)ˣ := Units.mk0 x hx0
      apply u.2
      refine ⟨v, ?_⟩
      apply Units.ext
      simpa [v, Units.val_pow_eq_pow_val] using hx
