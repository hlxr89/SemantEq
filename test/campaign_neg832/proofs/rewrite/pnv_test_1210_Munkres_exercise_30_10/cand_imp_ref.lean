import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u_1} {κ : Type u_2} [TopologicalSpace X] [T2Space X] (s : κ → Set X) (hs : ∀ (i : κ), Dense (s i)) (hX : SecondCountableTopology X) (hκ : Countable κ) : ∃ (t : Set X), Dense t ∧ t.Countable := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_30_10
  {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s := by
  classical
  by_cases hp : Nonempty (Π i, X i)
  · let x₀ : Π i, X i := Classical.choice hp
    choose s hs_countable hs_dense using h
    have he : ∀ i, ∃ e : ℕ → X i, DenseRange e := by
      intro i
      letI : Nonempty (X i) := ⟨x₀ i⟩
      letI : Nonempty (s i) := (hs_dense i).nonempty.to_subtype
      letI : Countable (s i) := Set.Countable.to_subtype (hs_countable i)
      obtain ⟨e, he_surj⟩ := exists_surjective_nat (s i)
      refine ⟨fun n => e n, ?_⟩
      exact (hs_dense i).denseRange_val.comp he_surj.denseRange continuous_subtype_val
    choose e he_dense using he
    obtain ⟨t, ht_dense, ht_countable⟩ :=
      dummy_assumed (X := ℕ → ℕ) (κ := Unit) (fun _ => Set.univ)
        (fun _ => dense_univ) (inferInstance : SecondCountableTopology (ℕ → ℕ))
        (inferInstance : Countable Unit)
    let F : (ℕ → ℕ) → (Π i, X i) := Pi.map e
    refine ⟨F '' t, Set.Countable.image ht_countable F, ?_⟩
    have hF_dense : DenseRange F := DenseRange.piMap he_dense
    have hF_cont : Continuous F := continuous_pi fun i =>
      continuous_of_discreteTopology.comp (continuous_apply i)
    exact hF_dense.dense_image hF_cont ht_dense
  · letI : IsEmpty (Π i, X i) := ⟨fun x => hp ⟨x⟩⟩
    obtain ⟨t, ht_dense, ht_countable⟩ :=
      dummy_assumed (X := Π i, X i) (κ := Unit) (fun _ => Set.univ)
        (fun _ => dense_univ) (inferInstance : SecondCountableTopology (Π i, X i))
        (inferInstance : Countable Unit)
    exact ⟨t, ht_countable, ht_dense⟩
