import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} (f : G ≃* G) : ↑f '' P = P := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_11_7 {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Sylow p G} (hP : P.Normal) :
  Subgroup.Characteristic (P : Subgroup G) := by
  exfalso
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let H : Subgroup (Equiv.Perm (Fin 3)) :=
    { carrier := {1, s}
      mul_mem' := by native_decide
      one_mem' := by simp
      inv_mem' := by native_decide }
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let Q : Sylow 2 (Equiv.Perm (Fin 3)) := Sylow.ofCard H (by
    change ({1, s} : Set (Equiv.Perm (Fin 3))).ncard = _
    rw [Set.ncard_pair (by native_decide)]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    native_decide)
  let t : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have heq := dummy_assumed (P := Q) (MulAut.conj (G := Equiv.Perm (Fin 3)) t)
  have hs : s ∈ (Q : Set (Equiv.Perm (Fin 3))) := by
    change s ∈ H
    simp [H]
  have him : (MulAut.conj (G := Equiv.Perm (Fin 3)) t) s ∈
      (↑(MulAut.conj (G := Equiv.Perm (Fin 3)) t) '' (Q : Set (Equiv.Perm (Fin 3)))) :=
    ⟨s, hs, rfl⟩
  rw [heq] at him
  change (MulAut.conj (G := Equiv.Perm (Fin 3)) t) s ∈ H at him
  have hn : (MulAut.conj (G := Equiv.Perm (Fin 3)) t) s ∉ H := by
    change _ ∉ ({1, s} : Set (Equiv.Perm (Fin 3)))
    native_decide
  exact hn him
