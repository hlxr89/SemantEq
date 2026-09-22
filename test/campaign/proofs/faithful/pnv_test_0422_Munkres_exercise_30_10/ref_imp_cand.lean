import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_30_10_assumed
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ S : Set (X i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, X i), S.Countable ∧ Dense S := by
  let Z : Option ι → Type _ := fun o =>
    match o with
    | none => PUnit
    | some i => X i
  letI instZ : ∀ o, TopologicalSpace (Z o) := fun o => by
    cases o with
    | none => exact inferInstanceAs (TopologicalSpace PUnit)
    | some i => exact inferInstanceAs (TopologicalSpace (X i))
  obtain ⟨g, hg⟩ := exists_surjective_nat (Option ι)
  let Y : ℕ → Type _ := fun n => Z (g n)
  letI instY : ∀ n, TopologicalSpace (Y n) := fun n => instZ (g n)
  have hZ : ∀ o, ∃ s : Set (Z o), s.Countable ∧ Dense s := by
    intro o
    cases o with
    | none =>
        exact ⟨Set.univ, Set.countable_univ, dense_univ⟩
    | some i =>
        exact h i
  have hY : ∀ n, ∃ s : Set (Y n), s.Countable ∧ Dense s := fun n => hZ (g n)
  obtain ⟨s, hs, hd⟩ := exercise_30_10_assumed hY
  choose r hr using fun i => hg (some i)
  let F : (∀ n, Y n) → (∀ i, X i) := fun x i =>
    cast (congrArg Z (hr i)) (x (r i))
  have hF : Continuous F := by
    apply continuous_pi
    intro i
    have hcast (n : ℕ) (o : Option ι) (e : g n = o) :
        Continuous fun x : (∀ n, Y n) => cast (congrArg Z e) (x n) := by
      subst o
      simpa using (continuous_apply n : Continuous fun x : (∀ n, Y n) => x n)
    exact hcast (r i) (some i) (hr i)
  have hFsurj : Function.Surjective F := by
    intro y
    let q : ∀ o, Z o := fun o =>
      match o with
      | none => PUnit.unit
      | some i => y i
    let x : ∀ n, Y n := fun n => q (g n)
    refine ⟨x, ?_⟩
    funext i
    have hcastVal (o : Option ι) (i : ι) (e : o = some i) :
        cast (congrArg Z e) (q o) = y i := by
      subst o
      rfl
    simpa [F, x, q, Y, Z] using hcastVal (g (r i)) i (hr i)
  refine ⟨F '' s, Set.Countable.image hs F, ?_⟩
  have hcoe : DenseRange ((↑) : s → (∀ n, Y n)) := by
    simpa [DenseRange] using hd
  have hcomp := hFsurj.denseRange.comp hcoe hF
  simpa [DenseRange, Set.range_comp, Subtype.range_coe] using hcomp
