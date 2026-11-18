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
  obtain ⟨k, a, hsum, hdiv⟩ := putnam_2005_a1_assumed (n : ℤ) (by exact_mod_cast hn)
  let f : Fin k → ℕ := fun i => 2^(a i 0) * 3^(a i 1)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hij_ne
    apply hdiv i j hij_ne
    rw [show 2^(a i 0) * 3^(a i 1) = 2^(a j 0) * 3^(a j 1) by simpa [f] using hij]
  have hsum_nat : ∑ i : Fin k, f i = n := by
    exact_mod_cast hsum.symm
  refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : n = 0 := by
      have huniv : (Finset.univ : Finset (Fin k)) = ∅ := Finset.image_eq_empty.mp hempty
      rw [← hsum_nat, huniv]
      rfl
    omega
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    apply hdiv i j
    intro hij
    apply hxy
    exact congrArg f hij
  · rw [Finset.sum_image hf.injOn]
    simpa [id] using hsum_nat
