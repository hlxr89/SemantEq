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
  let f : Fin k → ℕ := fun i => 2 ^ (a i 0) * 3 ^ (a i 1)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact hdiv i j hne (by simp [f, hij])
  have hk : k ≠ 0 := by
    intro hk
    subst k
    simp at hsum
    omega
  refine ⟨Finset.univ.image f, ?_, ?_, ?_, ?_⟩
  · exact ⟨f ⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hdiv i j (fun hij => hxy (congrArg f hij))
  · rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
    exact_mod_cast hsum.symm
