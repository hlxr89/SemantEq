import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
-- (empty)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ (S₀ : Finset ℕ), (∀ x ∈ S₀, 0 < x) →
  ∃ (S : ℕ → Finset ℕ),
    S 0 = S₀ ∧
    (∀ n, ∀ a, a ∈ S (n + 1) ↔ (a - 1 ∈ S n) ≠ (a ∈ S n)) ∧
    (∀ n, ∀ a, a ∈ S n → 0 < a) ∧
    Set.Infinite {N : ℕ | S N = S₀ ∪ (Finset.image (fun a => N + a) S₀)} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2000_b5
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  classical
  let F : ℕ → Finset ℕ := fun n => (hSfin n).toFinset.image Int.toNat
  have hmem (n a : ℕ) : a ∈ F n ↔ (a : ℤ) ∈ S n := by
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, hza⟩
      have hzS : z ∈ S n := (Set.Finite.mem_toFinset (hSfin n)).mp hz
      have hz0 : 0 ≤ z := le_of_lt (hSpos n z hzS)
      have : z = (a : ℤ) := by
        rw [← hza, Int.toNat_of_nonneg hz0]
      simpa [this] using hzS
    · intro ha
      apply Finset.mem_image.mpr
      refine ⟨(a : ℤ), ?_, ?_⟩
      · exact (Set.Finite.mem_toFinset (hSfin n)).mpr ha
      · simp
  have hFpos : ∀ x ∈ F 0, 0 < x := by
    intro x hx
    have hxS := (hmem 0 x).mp hx
    exact_mod_cast hSpos 0 (x : ℤ) hxS
  rcases problem_statement_assumed (F 0) hFpos with
    ⟨T, hT0, hTdef, hTpos, hTinf⟩
  have hFdef : ∀ n, ∀ a, a ∈ F (n + 1) ↔ (a - 1 ∈ F n) ≠ (a ∈ F n) := by
    intro n a
    rw [hmem, hmem, hmem]
    rw [hSdef]
    simp only [Xor']
    by_cases ha : a = 0
    · subst a
      simp
      have hzero : (0 : ℤ) ∉ S n := by
        intro h
        have := hSpos n 0 h
        omega
      have hneg : (-1 : ℤ) ∉ S n := by
        intro h
        have := hSpos n (-1) h
        omega
      simp [hzero, hneg]
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
      rw [hcast]
      tauto
  have hTF : ∀ n, T n = F n := by
    intro n
    induction n with
    | zero => exact hT0
    | succ n ih =>
        ext a
        rw [hTdef, hFdef, ih]
  have hFinf : Set.Infinite {N : ℕ | F N = F 0 ∪ (Finset.image (fun a => N + a) (F 0))} := by
    have heq : {N : ℕ | T N = F 0 ∪ Finset.image (fun a => N + a) (F 0)} =
        {N : ℕ | F N = F 0 ∪ Finset.image (fun a => N + a) (F 0)} := by
      ext N
      simp only [Set.mem_setOf_eq, hTF N]
    rw [← heq]
    simpa [hT0] using hTinf
  intro n
  obtain ⟨N, hNmem, hNgt⟩ := hFinf.exists_gt n
  refine ⟨N, Nat.le_of_lt hNgt, ?_⟩
  have hFN := hNmem
  simp only [Set.mem_setOf_eq] at hFN
  ext z
  by_cases hz : 0 < z
  · let a := z.toNat
    have hza : (a : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hz)
    have heqmem := Finset.ext_iff.mp hFN a
    rw [hmem N a, Finset.mem_union, hmem 0 a, Finset.mem_image] at heqmem
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rw [← hza]
    constructor
    · intro hzSN
      rcases heqmem.mp (by simpa [hza] using hzSN) with ha0 | ⟨b, hb, hab⟩
      · exact Or.inl ha0
      · right
        have hbS : (b : ℤ) ∈ S 0 := (hmem 0 b).mp hb
        have hab' : a = N + b := hab.symm
        convert hbS using 1 <;> omega
    · intro hzrhs
      apply heqmem.mpr
      rcases hzrhs with ha0 | hshift
      · exact Or.inl ha0
      · right
        have hposShift := hSpos 0 ((a : ℤ) - (N : ℤ)) hshift
        have hNa : N ≤ a := by omega
        have hcast : ((a - N : ℕ) : ℤ) = (a : ℤ) - (N : ℤ) := by omega
        refine ⟨a - N, ?_, ?_⟩
        · apply (hmem 0 (a - N)).mpr
          simpa [hcast] using hshift
        · omega
  · have hz0 : z ≤ 0 := le_of_not_gt hz
    have hnotSN : z ∉ S N := by
      intro h
      have := hSpos N z h
      omega
    have hnotS0 : z ∉ S 0 := by
      intro h
      have := hSpos 0 z h
      omega
    have hnotShift : z - (N : ℤ) ∉ S 0 := by
      intro h
      have := hSpos 0 (z - (N : ℤ)) h
      omega
    simp [hnotSN, hnotS0, hnotShift]
