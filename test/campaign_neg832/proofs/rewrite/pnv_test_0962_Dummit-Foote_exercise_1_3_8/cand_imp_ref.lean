import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {Ω : Type*} [Infinite Ω] : Infinite (Sym2 Ω) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_3_8 : Infinite (Equiv.Perm ℕ) := by
  letI : Infinite (Sym2 ℕ) := @dummy_assumed ℕ inferInstance
  have toMultiset_injective : Function.Injective (@Sym2.toMultiset ℕ) := by
    intro x y h
    induction x, y using Sym2.inductionOn₂ with
    | _ a b c d =>
      change a ::ₘ ({b} : Multiset ℕ) = c ::ₘ ({d} : Multiset ℕ) at h
      rw [Sym2.eq_iff]
      rw [Multiset.cons_eq_cons] at h
      rcases h with ⟨hac, hbd⟩ | ⟨_, cs, hbc, hda⟩
      · exact Or.inl ⟨hac, Multiset.singleton_inj.mp hbd⟩
      · rw [Multiset.singleton_eq_cons_iff] at hbc hda
        exact Or.inr ⟨hda.1.symm, hbc.1⟩
  exact Infinite.of_injective
    (fun x : Sym2 ℕ => Equiv.swap 0 (Encodable.encode x.toMultiset + 1)) (by
      intro x y h
      have h0 : Encodable.encode x.toMultiset + 1 =
          Encodable.encode y.toMultiset + 1 := by
        simpa only [Equiv.swap_apply_left] using
          congrArg (fun e : Equiv.Perm ℕ => e 0) h
      exact toMultiset_injective
        (Encodable.encode_injective (Nat.add_right_cancel h0)))
