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

namespace Erdos845

-- ===== assumed statement (antecedent) =====
theorem erdos_845_assumed (C : ℝ) (hC : 0 < C) :
    ¬ (let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
      { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
        (hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_845 :
    ¬ ∀ᵉ (C : ℝ) (hC : 0 < C),
      let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
      { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
        (hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0 := by
  intro h
  exact erdos_845_assumed 1 zero_lt_one (h 1 zero_lt_one)

end Erdos845
