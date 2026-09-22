import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_5_52_assumed {G : Type*} [Group G] [Fintype G]
  (φ : G ≃* G) {I : Finset G} (hI : ∀ x ∈ I, φ x = x⁻¹)
  (hI1 : (0.75 : ℚ) * card G ≤ card I) :
  (∀ x : G, φ x = x⁻¹) ∧ ∀ x y : G, x*y = y*x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] [Fintype G] (φ : G →* G) (hφ : ∃ S : Finset G, S.card > (3 * Fintype.card G) / 4 ∧ ∀ x ∈ S, φ x = x⁻¹) : ∀ y : G, φ y = y⁻¹ ∧ ∀ a b : G, a * b = b * a := by
  classical
  obtain ⟨S, hScard, hS⟩ := hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    let c := a * b⁻¹
    have hc : φ c = 1 := by
      simp [c, hab]
    let T := S.image (fun x => c * x)
    have hTcard : T.card = S.card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      exact mul_left_cancel hxy
    have hnotdisj : ¬ Disjoint S T := by
      intro hd
      have hu := Finset.card_le_univ (S ∪ T)
      rw [Finset.card_union_of_disjoint hd, hTcard] at hu
      omega
    obtain ⟨z, hzS, hzT⟩ := Finset.not_disjoint_iff.mp hnotdisj
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hzT
    have hx := hS x hxS
    have hcx := hS (c * x) hzS
    have : x⁻¹ = x⁻¹ * c⁻¹ := by
      calc
        x⁻¹ = φ (c * x) := by simp [hc, hx]
        _ = x⁻¹ * c⁻¹ := by simpa only [mul_inv_rev] using hcx
    have hc1 : c = 1 := by
      have : c⁻¹ = 1 := by
        apply mul_left_cancel (a := x⁻¹)
        simpa using this
      simpa using congrArg Inv.inv this
    exact mul_inv_eq_one.mp hc1
  have hφbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).2 ⟨hφinj, rfl⟩
  let ψ : G ≃* G := MulEquiv.ofBijective φ hφbij
  have hrat : (0.75 : ℚ) * card G ≤ card S := by
    have hn : 3 * card G ≤ 4 * S.card := by omega
    have hnq : (3 : ℚ) * card G ≤ 4 * S.card := by
      exact_mod_cast hn
    norm_num
    linarith
  obtain ⟨hall, hcomm⟩ := exercise_2_5_52_assumed ψ (fun x hx => hS x hx) hrat
  intro y
  exact ⟨hall y, hcomm⟩
