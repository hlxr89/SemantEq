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
  have hhalf : Fintype.card G < 2 * S.card := by
    omega
  have hmeet (x : G) : ∃ z ∈ S, z * x ∈ S := by
    by_contra h
    push_neg at h
    have hmap : Set.MapsTo (fun z : G => z * x) (S : Set G) (Sᶜ : Finset G) := by
      intro z hz
      simpa using h z hz
    have hinj : Set.InjOn (fun z : G => z * x) (S : Set G) :=
      fun _ _ _ _ hz => mul_right_cancel hz
    have hle : S.card ≤ Sᶜ.card :=
      Finset.card_le_card_of_injOn (fun z : G => z * x) hmap hinj
    rw [Finset.card_compl] at hle
    omega
  have hinj : Function.Injective φ := by
    intro a b hab
    let x := a * b⁻¹
    have hxφ : φ x = 1 := by
      simp [x, hab]
    obtain ⟨z, hz, hzx⟩ := hmeet x
    have hxinv : x⁻¹ = 1 := by
      apply mul_right_cancel (b := z⁻¹)
      calc
        x⁻¹ * z⁻¹ = (z * x)⁻¹ := by simp
        _ = φ (z * x) := (hS (z * x) hzx).symm
        _ = φ z * φ x := map_mul φ z x
        _ = z⁻¹ * 1 := by rw [hS z hz, hxφ]
        _ = 1 * z⁻¹ := by simp
    have hx : x = 1 := inv_eq_one.mp hxinv
    change a * b⁻¹ = 1 at hx
    calc
      a = (a * b⁻¹) * b := by simp
      _ = 1 * b := by rw [hx]
      _ = b := one_mul b
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, rfl⟩
  let e : G ≃* G := MulEquiv.ofBijective φ hbij
  have hrat : (0.75 : ℚ) * card G ≤ card S := by
    have hn : 3 * Fintype.card G ≤ 4 * S.card := by omega
    have hc : (3 * Fintype.card G : ℚ) ≤ 4 * S.card := by
      exact_mod_cast hn
    norm_num
    linarith
  have href := exercise_2_5_52_assumed e (I := S) (by
    intro x hx
    exact hS x hx) hrat
  intro y
  exact ⟨href.1 y, href.2⟩
