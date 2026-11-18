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
  have hS₀mem : ∀ a : ℕ, a ∈ S₀ ↔ (a : ℤ) ∈ S 0 := by
    intro a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, hza⟩
      have hzS : z ∈ S 0 := by
        simpa only [Set.Finite.mem_toFinset] using hz
      have hzpos := hSpos 0 z hzS
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
      rw [← hza, hzcast]
      exact hzS
    · intro ha
      apply Finset.mem_image.mpr
      refine ⟨(a : ℤ), ?_, ?_⟩
      · simpa only [Set.Finite.mem_toFinset] using ha
      · exact Int.toNat_natCast a
  have hS₀pos : ∀ a ∈ S₀, 0 < a := by
    intro a ha
    have := hSpos 0 (a : ℤ) ((hS₀mem a).mp ha)
    exact_mod_cast this
  obtain ⟨T, hTzero, hTdef, hTpos, hTinf⟩ := problem_statement_assumed S₀ hS₀pos
  have hne_iff_xor : ∀ p q : Prop, p ≠ q ↔ Xor' p q := by
    intro p q
    rw [xor_iff_not_iff]
    constructor
    · intro h he
      exact h (propext he)
    · intro h he
      exact h (Iff.of_eq he)
  have hTS : ∀ n a, a ∈ T n ↔ (a : ℤ) ∈ S n := by
    intro n
    -- non-rewrite step: the two recursive sequences are identified by uniqueness
    induction n with
    | zero =>
        intro a
        rw [hTzero]
        exact hS₀mem a
    | succ n ih =>
        intro a
        by_cases ha : a = 0
        · subst a
          have hTzero_mem : 0 ∉ T (n + 1) := by
            intro h
            exact (Nat.not_lt_zero 0) (hTpos (n + 1) 0 h)
          have hSzero_mem : (0 : ℤ) ∉ S (n + 1) := by
            intro h
            exact (Int.lt_irrefl 0) (hSpos (n + 1) 0 h)
          exact iff_of_false hTzero_mem hSzero_mem
        · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
          rw [hTdef, hSdef, hne_iff_xor, Nat.succ_sub_one, ih b, ih b.succ]
          simp only [Int.natCast_succ, Int.add_sub_cancel]
  intro n
  rcases hTinf.exists_gt n with ⟨N, hTN, hnN⟩
  refine ⟨N, Nat.le_of_lt hnN, ?_⟩
  ext z
  by_cases hz : 0 < z
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hz)
    have ha : 0 < a := by exact_mod_cast hz
    rw [← hTS N a, hTN]
    simp only [Finset.mem_union, Finset.mem_image, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h with h | ⟨b, hb, hab⟩
      · exact Or.inl ((hS₀mem a).mp h)
      · right
        have hbS := (hS₀mem b).mp hb
        have hc : (N : ℤ) + (b : ℤ) = (a : ℤ) := by exact_mod_cast hab
        have : (a : ℤ) - (N : ℤ) = (b : ℤ) := sub_eq_iff_eq_add'.mpr hc.symm
        exact this ▸ hbS
    · intro h
      rcases h with h | h
      · exact Or.inl ((hS₀mem a).mpr h)
      · right
        have hpos := hSpos 0 ((a : ℤ) - (N : ℤ)) h
        obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hpos)
        refine ⟨b, (hS₀mem b).mpr (hb ▸ h), ?_⟩
        apply Int.natCast_inj.mp
        exact (sub_eq_iff_eq_add'.mp hb).symm
  · constructor
    · intro h
      exact (hz (hSpos N z h)).elim
    · intro h
      rcases h with h | h
      · exact (hz (hSpos 0 z h)).elim
      · have hp := hSpos 0 (z - (N : ℤ)) h
        exfalso
        exact hz (lt_of_lt_of_le hp (sub_le_self z (Int.ofNat_zero_le N)))
