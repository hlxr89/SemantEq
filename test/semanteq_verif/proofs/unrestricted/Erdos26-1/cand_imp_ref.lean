import Mathlib

open Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
namespace Set

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
theorem erdos_26_goal :
    ¬ ∀ A : ℕ → ℕ, StrictMono A → IsThick A →
    ∃ k, IsBehrend (A · + k) := by
  intro hall
  let A : ℕ → ℕ := fun n ↦ n + 1
  have hA : StrictMono A := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp [A]
  have h : IsThick A := by
    intro hs
    apply Real.not_summable_one_div_natCast
    apply (summable_nat_add_iff 1).mp
    simpa [A] using hs
  exact erdos_26_assumed A hA h (hall A hA h)

end Erdos26
