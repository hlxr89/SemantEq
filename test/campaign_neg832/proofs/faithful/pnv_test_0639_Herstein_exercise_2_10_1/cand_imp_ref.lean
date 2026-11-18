import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] (N : Subgroup G) [hN : N.Normal] (b : G) {p : ℕ} (hb : orderOf b = p) (hNb : ¬b ∈ N) : N ⊓ Subgroup.center G = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  let H : Subgroup G := Subgroup.closure {b}
  let bH : H := ⟨b, Subgroup.mem_closure_singleton_self b⟩
  have hcomm : ∀ x y : H, x * y = y * x := by
    intro x y
    obtain ⟨m, hm⟩ := Subgroup.mem_closure_singleton.mp x.property
    obtain ⟨n, hn⟩ := Subgroup.mem_closure_singleton.mp y.property
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, add_comm, zpow_add]
  letI : CommGroup H := { inferInstanceAs (Group H) with
    mul_comm := hcomm }
  let N : Subgroup H := A.comap H.subtype
  letI : N.Normal := Subgroup.normal_of_comm N
  have hbH : bH ∉ N := by
    simpa [bH, N] using hb
  have hmeet : N ⊓ Subgroup.center H = ⊥ :=
    dummy_assumed H N bH (p := orderOf bH) rfl hbH
  have hcenter : Subgroup.center H = ⊤ := by
    ext x
    simp [Subgroup.mem_center_iff, mul_comm]
  have hNbot : N = ⊥ := by
    simpa [hcenter] using hmeet
  apply le_antisymm
  · intro x hx
    have hxN : (⟨x, hx.2⟩ : H) ∈ N := hx.1
    rw [hNbot] at hxN
    have hx1H : (⟨x, hx.2⟩ : H) = 1 := by
      simpa using hxN
    have hx1 : x = 1 := congrArg Subtype.val hx1H
    simpa using hx1
  · exact bot_le
