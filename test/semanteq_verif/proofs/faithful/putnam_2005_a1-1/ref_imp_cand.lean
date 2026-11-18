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
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    by_contra hne
    apply hdiv i j hne
    simpa [f] using (show f i ∣ f j by rw [hij])
  have hk : 0 < k := by
    by_contra hk
    have : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simp at hsum
    omega
  let S : Finset ℕ := Finset.univ.image f
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact ⟨f ⟨0, hk⟩, Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a i 0, a i 1, rfl⟩
  · intro x y hx hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg f h)
    exact hdiv i j hij
  · have himage : S.sum id = ∑ i : Fin k, f i := by
      simpa [S] using (Finset.sum_image hinj :
        ∑ x ∈ Finset.univ.image f, id x = ∑ x ∈ Finset.univ, id (f x))
    rw [himage]
    exact_mod_cast hsum.symm
