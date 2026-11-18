import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
-- (empty)

-- ===== assumed statement (antecedent) =====
theorem putnam_2000_b5_assumed
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (S₀ : Finset ℕ), (∀ x ∈ S₀, 0 < x) →
  ∃ (S : ℕ → Finset ℕ),
    S 0 = S₀ ∧
    (∀ n, ∀ a, a ∈ S (n + 1) ↔ (a - 1 ∈ S n) ≠ (a ∈ S n)) ∧
    (∀ n, ∀ a, a ∈ S n → 0 < a) ∧
    Set.Infinite {N : ℕ | S N = S₀ ∪ (Finset.image (fun a => N + a) S₀)} := by
  classical
  intro S₀ hS₀pos
  let U : ℕ → Set ℤ := fun n => Nat.rec ((fun a : ℕ => (a : ℤ)) '' (S₀ : Set ℕ))
    (fun _ A => {z : ℤ | Xor' (z - 1 ∈ A) (z ∈ A)}) n
  have hU0 : U 0 = (fun a : ℕ => (a : ℤ)) '' (S₀ : Set ℕ) := rfl
  have hUdef : ∀ n z, z ∈ U (n + 1) ↔ Xor' (z - 1 ∈ U n) (z ∈ U n) := by
    intro n z
    rfl
  have hUfin : ∀ n, Set.Finite (U n) := by
    intro n
    induction n with
    | zero =>
        rw [hU0]
        exact S₀.finite_toSet.image _
    | succ n ih =>
        apply Set.Finite.subset (ih.union (ih.image fun z : ℤ => z + 1))
        intro z hz
        rw [hUdef] at hz
        rcases hz with ⟨hzprev, _⟩ | ⟨hznow, _⟩
        · right
          exact ⟨z - 1, hzprev, by ring⟩
        · exact Or.inl hznow
  have hUpos : ∀ n, ∀ z ∈ U n, z > 0 := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [hU0] at hz
        rcases hz with ⟨a, ha, rfl⟩
        have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast hS₀pos a ha
        simpa using ha'
    | succ n ih =>
        intro z hz
        rw [hUdef] at hz
        rcases hz with ⟨hzprev, _⟩ | ⟨hznow, _⟩
        · have := ih (z - 1) hzprev
          omega
        · exact ih z hznow
  let F : ℕ → Finset ℕ := fun n => (hUfin n).toFinset.image Int.toNat
  have hmem (n a : ℕ) : a ∈ F n ↔ (a : ℤ) ∈ U n := by
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, hza⟩
      have hzU : z ∈ U n := (Set.Finite.mem_toFinset (hUfin n)).mp hz
      have hz0 : 0 ≤ z := le_of_lt (hUpos n z hzU)
      have : z = (a : ℤ) := by rw [← hza, Int.toNat_of_nonneg hz0]
      simpa [this] using hzU
    · intro ha
      exact Finset.mem_image.mpr ⟨(a : ℤ),
        (Set.Finite.mem_toFinset (hUfin n)).mpr ha, by simp⟩
  have hF0 : F 0 = S₀ := by
    ext a
    have hm := hmem 0 a
    rw [hU0] at hm
    simpa using hm
  have xor_ne (p q : Prop) : (p ∧ ¬q ∨ q ∧ ¬p) ↔ (p ≠ q) := by
    classical
    tauto
  have hFdef : ∀ n, ∀ a, a ∈ F (n + 1) ↔ (a - 1 ∈ F n) ≠ (a ∈ F n) := by
    intro n a
    rw [hmem (n + 1) a, hUdef, hmem n (a - 1), hmem n a]
    simp only [Xor']
    by_cases ha : a = 0
    · subst a
      have hzero : (0 : ℤ) ∉ U n := by
        intro h
        have := hUpos n 0 h
        omega
      have hneg : (-1 : ℤ) ∉ U n := by
        intro h
        have := hUpos n (-1) h
        omega
      simp [hzero, hneg]
    · have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
      rw [hcast]
      exact xor_ne _ _
  have hFpos : ∀ n, ∀ a, a ∈ F n → 0 < a := by
    intro n a ha
    have := hUpos n (a : ℤ) ((hmem n a).mp ha)
    exact_mod_cast this
  refine ⟨F, hF0, hFdef, hFpos, ?_⟩
  have hlarge := putnam_2000_b5_assumed U hUfin hUpos hUdef
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨N, hNge, hUN⟩ := hlarge (n + 1)
  refine ⟨N, ?_, ?_⟩
  · ext a
    rw [hmem N a, hUN, Set.mem_union, Set.mem_setOf_eq]
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · intro ha
      rcases ha with ha0 | hashift
      · exact Or.inl (by simpa [hU0] using ha0)
      · right
        rw [hU0] at hashift
        rcases hashift with ⟨b, hb, hab⟩
        refine ⟨b, hb, ?_⟩
        have habZ : (b : ℤ) = (a : ℤ) - (N : ℤ) := by simpa using hab
        omega
    · intro ha
      rcases ha with ha0 | ⟨b, hb, hab⟩
      · left
        simpa [hU0] using ha0
      · right
        rw [hU0]
        refine ⟨b, hb, ?_⟩
        have habZ : (N : ℤ) + (b : ℤ) = (a : ℤ) := by exact_mod_cast hab
        change (b : ℤ) = (a : ℤ) - (N : ℤ)
        omega
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hNge
