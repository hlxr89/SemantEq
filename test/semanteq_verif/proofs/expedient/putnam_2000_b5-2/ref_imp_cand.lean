import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
-- empty

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
  intro S₀ h₀
  let S : ℕ → Finset ℕ := fun n => Nat.rec S₀ (fun _ t => symmDiff (t.image Nat.succ) t) n
  have hzero : S 0 = S₀ := rfl
  have hpos : ∀ n a, a ∈ S n → 0 < a := by
    intro n
    induction n with
    | zero => simpa [S] using h₀
    | succ n ih =>
        intro a ha
        simp only [S, Nat.rec_add_one, Finset.mem_symmDiff, Finset.mem_image] at ha
        rcases ha with ⟨⟨b, hb, rfl⟩, -⟩ | ⟨ha, -⟩
        · omega
        · exact ih _ ha
  have hrec : ∀ n a, a ∈ S (n + 1) ↔ (a - 1 ∈ S n) ≠ (a ∈ S n) := by
    have himage : ∀ (t : Finset ℕ) a, a ∈ t.image Nat.succ ↔ 0 < a ∧ a - 1 ∈ t := by
      intro t a
      rw [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨by omega, by simpa using hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨a - 1, hb, by omega⟩
    intro n a
    by_cases ha : a = 0
    · subst a
      have hn : 0 ∉ S n := by
        intro hn
        have := hpos n 0 hn
        omega
      simp [S] at hn
      simp [S, Finset.mem_symmDiff, himage, hn]
    · have ha' : 0 < a := Nat.pos_of_ne_zero ha
      simp [S, Finset.mem_symmDiff, himage, ha']
      tauto
  let U : ℕ → Set ℤ := fun n => {z | 0 < z ∧ z.toNat ∈ S n}
  have hUfin : ∀ n, Set.Finite (U n) := by
    intro n
    have heq : U n = Int.ofNat '' {a | a ∈ S n} := by
      ext z
      constructor
      · rintro ⟨hz, hzS⟩
        exact ⟨z.toNat, hzS, Int.toNat_of_nonneg (le_of_lt hz)⟩
      · rintro ⟨a, ha, rfl⟩
        have hp := hpos n a ha
        exact ⟨by simpa [Int.ofNat_eq_coe] using hp, by simpa using ha⟩
    rw [heq]
    exact (Finset.finite_toSet (S n)).image _
  have hUpos : ∀ n, ∀ z ∈ U n, z > 0 := by
    intro n z hz
    exact hz.1
  have hxor (p q : Prop) : (p ≠ q) ↔ Xor' p q := by
    constructor
    · intro h
      rw [xor_iff_not_iff]
      exact fun hpq => h (propext hpq)
    · intro h hpq
      subst q
      simpa [Xor'] using h
  have hUrec : ∀ n, ∀ z, z ∈ U (n + 1) ↔ Xor' (z - 1 ∈ U n) (z ∈ U n) := by
    intro n z
    simp only [U, Set.mem_setOf_eq]
    by_cases hz : z ≤ 0
    · have hz1 : z - 1 ≤ 0 := by omega
      simp only [not_lt.mpr hz, not_lt.mpr hz1, false_and, Xor']
      simp
    · have hzpos : 0 < z := by omega
      have hto : (z - 1).toNat = z.toNat - 1 := by omega
      rw [hrec n z.toNat]
      rw [hto]
      by_cases hz1 : z = 1
      · subst z
        have hn : 0 ∉ S n := by
          intro hn
          have := hpos n 0 hn
          omega
        simp [Xor', hn]
      · have hz1pos : 0 < z - 1 := by omega
        simp only [hzpos, hz1pos, true_and]
        exact hxor _ _
  have hcof := putnam_2000_b5_assumed U hUfin hUpos hUrec
  refine ⟨S, hzero, hrec, hpos, Set.infinite_of_forall_exists_gt ?_⟩
  intro n
  obtain ⟨N, hN, hUN⟩ := hcof (n + 1)
  have hgood : S N = S₀ ∪ Finset.image (fun a => N + a) S₀ := by
    ext a
    by_cases ha0 : a = 0
    · subst a
      have hSN : 0 ∉ S N := by
        intro h
        have := hpos N 0 h
        omega
      have hS₀ : 0 ∉ S₀ := by
        intro h
        have := h₀ 0 h
        omega
      simp [hSN, hS₀]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hm := Set.ext_iff.mp hUN (a : ℤ)
      simp only [U, Set.mem_union, Set.mem_setOf_eq] at hm
      norm_num at hm
      rw [hzero] at hm
      constructor
      · intro ha
        have hu : 0 < a ∧ a ∈ S N := ⟨hapos, ha⟩
        rw [hm] at hu
        simp only [Finset.mem_union, Finset.mem_image]
        rcases hu with hu | hu
        · exact Or.inl (by simpa using hu.2)
        · right
          have heq : ((a : ℤ) - N).toNat = a - N := by omega
          refine ⟨((a : ℤ) - N).toNat, by simpa [heq] using hu.2, ?_⟩
          omega
      · intro ha
        have hu : 0 < a ∧ a ∈ S N := by
          rw [hm]
          simp only [Finset.mem_union, Finset.mem_image] at ha
          rcases ha with ha | ⟨b, hb, hab⟩
          · exact Or.inl ⟨by exact_mod_cast hapos, by simpa using ha⟩
          · subst a
            have hp := h₀ b hb
            exact Or.inr ⟨by omega, by simpa using hb⟩
        exact hu.2
  exact ⟨N, hgood, by omega⟩
