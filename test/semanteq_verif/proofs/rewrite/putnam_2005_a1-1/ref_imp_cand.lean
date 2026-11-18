import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
/-- Numbers of the form 2^r * 3^s for nonnegative integers r and s -/
def IsPowerOf2And3 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

/-- A finite set of numbers where no element divides another -/
def NoElementDividesAnother (S : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b → ¬(a ∣ b)

-- ===== assumed statement (antecedent) =====
theorem putnam_2005_a1_assumed
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) :
  ∃ S : Finset ℕ, S.Nonempty ∧ 
    (∀ x ∈ S, IsPowerOf2And3 x) ∧
    NoElementDividesAnother S ∧
    S.sum id = n := by
  classical
  have hn_int : (0 : ℤ) < (n : ℤ) := Int.natCast_pos.mpr hn
  obtain ⟨k, a, hsum, hndiv⟩ := putnam_2005_a1_assumed (n : ℤ) hn_int
  let f : Fin k → ℕ := fun i => 2^(a i 0)*3^(a i 1)
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Decidable.not_not.mp
    intro hne
    have hnot := hndiv i j hne
    change ¬(f i ∣ f j) at hnot
    apply hnot
    rw [hij]
  let S : Finset ℕ := Finset.univ.image f
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have himage : Finset.univ.image f = ∅ := by
      simpa only [S] using hempty
    have huniv : (Finset.univ : Finset (Fin k)) = ∅ :=
      Finset.image_eq_empty.mp himage
    have hsum_zero : ∑ i : Fin k, f i = 0 := by
      change Finset.univ.sum f = 0
      rw [huniv, Finset.sum_empty]
    have hn_zero : (n : ℤ) = 0 := by
      have hsum_nat : n = ∑ i : Fin k, f i := by
        exact_mod_cast hsum
      exact_mod_cast hsum_nat.trans hsum_zero
    exact (ne_of_gt hn_int) hn_zero
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    apply hndiv i j
    intro hij
    apply hxy
    rw [hij]
  · rw [Finset.sum_image]
    · exact_mod_cast hsum.symm
    · exact hf_inj.injOn
