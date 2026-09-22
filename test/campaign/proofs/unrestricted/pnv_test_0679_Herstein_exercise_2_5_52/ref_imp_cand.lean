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
  have hker : ∀ x : G, φ x = 1 → x = 1 := by
    intro x hx
    let T : Finset G := S.image (fun y => y * x⁻¹)
    have hTcard : T.card = S.card := by
      dsimp [T]
      apply Finset.card_image_of_injective
      intro a b hab
      exact mul_right_cancel hab
    have hlarge : Fintype.card G < S.card + T.card := by omega
    have hinter : (S ∩ T).Nonempty := by
      by_contra hn
      have hzero : (S ∩ T).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
      have hunion := Finset.card_le_univ (S ∪ T)
      have hcount := Finset.card_union_add_card_inter S T
      omega
    obtain ⟨z, hz⟩ := hinter
    obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
    obtain ⟨y, hyS, hyz⟩ := Finset.mem_image.mp hzT
    have hy : φ y = y⁻¹ := hS y hyS
    have hz : φ z = z⁻¹ := hS z hzS
    have hy_eq : y = z * x := by
      rw [← hyz]
      simp
    have hinv : y⁻¹ = z⁻¹ := by
      rw [← hy, ← hz, hy_eq, map_mul, hx, mul_one]
    have : y = z := by simpa using congrArg Inv.inv hinv
    rw [this] at hyz
    simpa using hyz
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hk : φ (x * y⁻¹) = 1 := by simp [hxy]
    exact mul_inv_eq_one.mp (hker _ hk)
  have hsurj : Function.Surjective φ := (Finite.injective_iff_surjective).mp hinj
  let e : G ≃* G := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hnat' : 3 * card G ≤ S.card * 4 := by omega
  have hrat : (0.75 : ℚ) * card G ≤ card S := by
    rw [show (0.75 : ℚ) = 3 / 4 by norm_num, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 4)).2
    norm_cast
    simpa using hnat'
  have href := exercise_2_5_52_assumed e hS hrat
  intro y
  exact ⟨href.1 y, href.2⟩
