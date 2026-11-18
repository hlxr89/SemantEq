import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Set

open Filter Topology

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

end Set

namespace Erdos26

def IsThick {ι : Type*} (A : ι → ℕ) : Prop := ¬Summable (fun i ↦ (1 : ℝ) / A i)

def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ := Set.range fun (n, i) ↦ n * A i

def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop := (MultiplesOf A).HasDensity 1

-- ===== assumed statement (antecedent) =====
theorem erdos_26_assumed (A : ℕ → ℕ) (hA : StrictMono A) (h : IsThick A) :
    ¬ ∃ k, IsBehrend (A · + k) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_26 :
    ¬ ∀ A : ℕ → ℕ, StrictMono A → IsThick A →
    ∃ k, IsBehrend (A · + k) := by
  push_neg
  refine ⟨fun n ↦ n + 1, ?_, ?_, ?_⟩
  · intro a b hab
    exact Nat.add_lt_add_right hab 1
  · exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast
  · intro k hk
    exact erdos_26_assumed (fun n ↦ n + 1) (by
      intro a b hab
      exact Nat.add_lt_add_right hab 1) (by
      exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast) ⟨k, hk⟩

end Erdos26
