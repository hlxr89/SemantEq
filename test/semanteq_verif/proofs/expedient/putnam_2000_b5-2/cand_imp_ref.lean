import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
-- empty

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
  let S₀ : Finset ℕ := (hSfin 0).toFinset.image Int.toNat
  have hS₀pos : ∀ x ∈ S₀, 0 < x := by
    intro x hx
    simp only [S₀, Finset.mem_image, Set.Finite.mem_toFinset] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hp := hSpos 0 z hz
    omega
  obtain ⟨T, hT0, hTrec, hTpos, hTinf⟩ := problem_statement_assumed S₀ hS₀pos
  let U : ℕ → Set ℤ := fun n => {z | 0 < z ∧ z.toNat ∈ T n}
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
      rw [hTrec n z.toNat]
      rw [hto]
      by_cases hz1 : z = 1
      · subst z
        have hn : 0 ∉ T n := by
          intro hn
          have := hTpos n 0 hn
          omega
        simp [Xor', hn]
      · have hz1pos : 0 < z - 1 := by omega
        simp only [hzpos, hz1pos, true_and]
        exact hxor _ _
  have hU0 : U 0 = S 0 := by
    ext z
    constructor
    · rintro ⟨hzpos, hz⟩
      rw [hT0] at hz
      simp only [S₀, Finset.mem_image, Set.Finite.mem_toFinset] at hz
      obtain ⟨w, hw, hto⟩ := hz
      have hwpos := hSpos 0 w hw
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
      have hwcast : (w.toNat : ℤ) = w := Int.toNat_of_nonneg (le_of_lt hwpos)
      have hzw : z = w := by
        calc
          z = (z.toNat : ℤ) := hzcast.symm
          _ = (w.toNat : ℤ) := by exact_mod_cast hto.symm
          _ = w := hwcast
      simpa [hzw] using hw
    · intro hz
      have hzpos := hSpos 0 z hz
      refine ⟨hzpos, ?_⟩
      rw [hT0]
      simp only [S₀, Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨z, hz, rfl⟩
  have hSU : ∀ n, S n = U n := by
    intro n
    induction n with
    | zero => exact hU0.symm
    | succ n ih =>
        ext z
        rw [hSdef, hUrec, ← ih]
  intro n
  obtain ⟨N, hNgood, hnN⟩ := hTinf.exists_gt n
  refine ⟨N, Nat.le_of_lt hnN, ?_⟩
  rw [hSU N, hSU 0]
  ext z
  simp only [U, Set.mem_union, Set.mem_setOf_eq]
  by_cases hz : z ≤ 0
  · have hzN : z - N ≤ 0 := by omega
    constructor
    · rintro ⟨hzpos, -⟩
      omega
    · rintro (⟨hzpos, -⟩ | ⟨hzNpos, -⟩) <;> omega
  · have hzpos : 0 < z := by omega
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
    have hNgood' : T N = S₀ ∪ Finset.image (fun a => N + a) S₀ := hNgood
    have hmem := Finset.ext_iff.mp hNgood' z.toNat
    simp only [Finset.mem_union, Finset.mem_image] at hmem
    rw [hT0]
    simp only [hzpos, true_and]
    rw [hmem]
    constructor
    · rintro (hz0 | ⟨a, ha, hza⟩)
      · exact Or.inl hz0
      · right
        have hapos := hS₀pos a ha
        have hza' : z = (N + a : ℕ) := by
          rw [← hzcast]
          exact_mod_cast hza.symm
        constructor
        · omega
        · have hto : (z - N).toNat = a := by omega
          simpa [hto] using ha
    · rintro (hz0 | hzshift)
      · exact Or.inl hz0
      · right
        have hzNpos : 0 < z - N := hzshift.1
        refine ⟨(z - N).toNat, hzshift.2, ?_⟩
        have hdiff : ((z - N).toNat : ℤ) = z - N :=
          Int.toNat_of_nonneg (le_of_lt hzNpos)
        omega
