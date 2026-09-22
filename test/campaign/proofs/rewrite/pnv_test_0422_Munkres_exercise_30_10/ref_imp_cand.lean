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
  letI : Encodable ι := Encodable.ofCountable ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI : IsEmpty ι := hι
    have hP : ∀ n : ℕ, ∃ S : Set Unit, S.Countable ∧ Dense S := fun _ =>
      ⟨Set.univ, Set.countable_univ, dense_univ⟩
    obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed hP
    let f : (ℕ → Unit) → (∀ i, X i) := fun _ i => isEmptyElim i
    refine ⟨f '' S, (Set.countable_coe_iff.mp hSc).image f, ?_⟩
    apply DenseRange.dense_image (f := f) ?_ ?_ hSd
    · apply Function.Surjective.denseRange
      intro q
      refine ⟨fun _ => Unit.unit, ?_⟩
      funext i
      exact isEmptyElim i
    · apply continuous_pi
      intro i
      exact isEmptyElim i
  · letI : Nonempty ι := hι
    let e : ι → ℕ := Encodable.encode
    have he : Function.Injective e := Encodable.encode_injective
    let Y : ℕ → Type _ := fun n => X (Function.invFun e n)
    let f : (∀ n, Y n) → (∀ i, X i) := fun p i =>
      cast (congrArg X (Function.leftInverse_invFun he i)) (p (e i))
    have cast_apply {a b : ι} (hab : a = b) (q : ∀ i, X i) :
        cast (congrArg X hab) (q a) = q b := by
      subst b
      rfl
    have continuous_cast {a b : ι} (hab : a = b) :
        Continuous (cast (congrArg X hab) : X a → X b) := by
      subst b
      exact continuous_id
    have hY : ∀ n, ∃ S : Set (Y n), S.Countable ∧ Dense S := by
      intro n
      simpa [Y] using h (Function.invFun e n)
    obtain ⟨S, hSc, hSd⟩ := exercise_30_10_assumed hY
    refine ⟨f '' S, (Set.countable_coe_iff.mp hSc).image f, ?_⟩
    apply DenseRange.dense_image (f := f) ?_ ?_ hSd
    · apply Function.Surjective.denseRange
      intro q
      let p : (n : ℕ) → Y n := fun n => q (Function.invFun e n)
      refine ⟨p, ?_⟩
      funext i
      exact cast_apply (Function.leftInverse_invFun he i) q
    · apply continuous_pi
      intro i
      exact (continuous_cast (Function.leftInverse_invFun he i)).comp
        (continuous_apply (A := Y) (e i))
