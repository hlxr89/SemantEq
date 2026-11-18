import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (f : ℕ → X) : IsClopen (Set.range f) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_32a (A : Set ℕ) : IsClopen A := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    let f : ℕ → ℕ := fun n => if n ∈ A then n else a
    have hrange : Set.range f = A := by
      ext n
      constructor
      · rintro ⟨m, rfl⟩
        simp only [f]
        split_ifs with hm
        · exact hm
        · exact ha
      · intro hn
        exact ⟨n, by simp [f, hn]⟩
    rw [← hrange]
    exact dummy_assumed f
  · have hsingleton : IsClopen (Set.range (fun _ : ℕ => 0)) :=
      dummy_assumed (fun _ : ℕ => 0)
    have hempty : IsClopen
        (Set.range (fun _ : ℕ => 0) ∩ (Set.range (fun _ : ℕ => 0))ᶜ) :=
      hsingleton.inter hsingleton.compl
    simpa [Set.not_nonempty_iff_eq_empty.mp hA] using hempty
