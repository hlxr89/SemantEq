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
  have prop_ne_iff (P Q : Prop) : (P ≠ Q) ↔ ¬(P ↔ Q) := by
    constructor
    · exact fun h he => h (propext he)
    · exact fun h he => h (eq_iff_iff.mp he)
  let A : Finset ℕ := (hSfin 0).toFinset.image Int.toNat
  have hA : ∀ a : ℕ, a ∈ A ↔ (a : ℤ) ∈ S 0 := by
    intro a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, hza⟩
      have hzS : z ∈ S 0 := (hSfin 0).mem_toFinset.mp hz
      have hzpos := hSpos 0 z hzS
      have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
      rw [← hza, hcast]
      exact hzS
    · intro ha
      apply Finset.mem_image.mpr
      refine ⟨(a : ℤ), (hSfin 0).mem_toFinset.mpr ha, ?_⟩
      simp
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    have := hSpos 0 (a : ℤ) ((hA a).mp ha)
    exact_mod_cast this
  obtain ⟨T, hT0, hTdef, hTpos, hTinf⟩ := problem_statement_assumed A hApos
  have hmatch : ∀ n (a : ℕ), (a : ℤ) ∈ S n ↔ a ∈ T n := by
    intro n
    induction n with
    | zero =>
      intro a
      rw [hT0]
      exact (hA a).symm
    | succ n ih =>
      intro a
      by_cases ha : a = 0
      · subst a
        have hleft : (0 : ℤ) ∉ S (n + 1) := by
          intro h
          have := hSpos (n + 1) 0 h
          omega
        have hright : 0 ∉ T (n + 1) := by
          intro h
          have := hTpos (n + 1) 0 h
          omega
        simp [hleft, hright]
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha
        rw [hSdef, hTdef]
        have hpred : ((a : ℤ) - 1 ∈ S n) ↔ a - 1 ∈ T n := by
          rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega]
          exact ih (a - 1)
        rw [hpred, ih]
        rw [prop_ne_iff, ← xor_iff_not_iff]
  intro n
  obtain ⟨N, hNgood, hnN⟩ := hTinf.exists_gt n
  refine ⟨N, le_of_lt hnN, ?_⟩
  apply Set.ext
  intro z
  by_cases hz : 0 < z
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hz)
    have haT : a ∈ T N ↔ a ∈ A ∨ ∃ b ∈ A, N + b = a := by
      rw [hNgood]
      simp only [Finset.mem_union, Finset.mem_image]
    rw [hmatch]
    constructor
    · intro ha
      rcases haT.mp ha with ha | ⟨b, hb, hba⟩
      · exact Or.inl ((hA a).mp ha)
      · right
        change (a : ℤ) - (N : ℤ) ∈ S 0
        have hbS := (hA b).mp hb
        have heq : (a : ℤ) - (N : ℤ) = (b : ℤ) := by
          push_cast
          omega
        rw [heq]
        exact hbS
    · intro ha
      apply haT.mpr
      rcases ha with ha | ha
      · exact Or.inl ((hA a).mpr ha)
      · right
        have hadiffpos := hSpos 0 ((a : ℤ) - (N : ℤ)) ha
        have hNle : N ≤ a := by omega
        refine ⟨a - N, (hA (a - N)).mpr ?_, by omega⟩
        have heq : ((a - N : ℕ) : ℤ) = (a : ℤ) - (N : ℤ) := by
          push_cast
          omega
        rw [heq]
        exact ha
  · have hzle : z ≤ 0 := le_of_not_gt hz
    have hleft : z ∉ S N := by
      intro h
      have := hSpos N z h
      omega
    have hbase : z ∉ S 0 := by
      intro h
      have := hSpos 0 z h
      omega
    have hshift : z - (N : ℤ) ∉ S 0 := by
      intro h
      have := hSpos 0 (z - (N : ℤ)) h
      omega
    simp [hleft, hbase, hshift]
