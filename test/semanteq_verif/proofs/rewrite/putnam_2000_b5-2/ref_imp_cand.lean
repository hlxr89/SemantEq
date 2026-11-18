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
  intro S₀ hS₀pos
  let T : ℕ → Finset ℕ := fun n =>
    Nat.rec S₀ (fun _ t => symmDiff (t.image Nat.succ) t) n
  have hTzero : T 0 = S₀ := by
    rfl
  have hTsucc : ∀ n, T (n + 1) = symmDiff ((T n).image Nat.succ) (T n) := by
    intro n
    simp only [T, Nat.rec_add_one]
  have hTpos : ∀ n, ∀ a ∈ T n, 0 < a := by
    intro n
    -- non-rewrite step: positivity is propagated through the recursive sequence
    induction n with
    | zero =>
        simpa only [hTzero] using hS₀pos
    | succ n ih =>
        intro a ha
        rw [hTsucc n, Finset.mem_symmDiff] at ha
        rcases ha with ha | ha
        · rcases Finset.mem_image.mp ha.1 with ⟨b, hb, rfl⟩
          exact Nat.succ_pos b
        · exact ih a ha.1
  have hne_iff_xor : ∀ p q : Prop, p ≠ q ↔ Xor' p q := by
    intro p q
    rw [xor_iff_not_iff]
    constructor
    · intro h he
      exact h (propext he)
    · intro h he
      exact h (Iff.of_eq he)
  have hTdef : ∀ n, ∀ a, a ∈ T (n + 1) ↔ (a - 1 ∈ T n) ≠ (a ∈ T n) := by
    intro n a
    rw [hTsucc n, Finset.mem_symmDiff]
    by_cases ha : a = 0
    · subst a
      have hz : 0 ∉ T n := by
        intro h
        exact (Nat.not_lt_zero 0) (hTpos n 0 h)
      simp only [Finset.mem_image, Nat.succ_ne_zero, exists_const, hz, not_false_eq_true,
        Nat.zero_sub, ne_eq, not_true_eq_false, and_false]
      tauto
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
      simp only [Finset.mem_image, Nat.succ.injEq, exists_eq_right, Nat.succ_sub_one,
        ne_eq]
      exact (hne_iff_xor (b ∈ T n) (b.succ ∈ T n)).symm
  let U : ℕ → Set ℤ := fun n => {z | ∃ a ∈ T n, (a : ℤ) = z}
  have hUfin : ∀ n, Set.Finite (U n) := by
    intro n
    exact (T n).finite_toSet.image (fun a : ℕ => (a : ℤ))
  have hUpos : ∀ n, ∀ z ∈ U n, z > 0 := by
    intro n z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact_mod_cast hTpos n a ha
  have hU_nat : ∀ n (a : ℕ), (a : ℤ) ∈ U n ↔ a ∈ T n := by
    intro n a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (Int.ofNat_inj.mp hba) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hU_pred : ∀ n (a : ℕ), 0 < a → ((a : ℤ) - 1 ∈ U n ↔ a - 1 ∈ T n) := by
    intro n a ha
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    simpa only [Nat.succ_sub_one, Int.ofNat_eq_coe, Int.natCast_succ, Int.add_sub_cancel]
      using hU_nat n b
  have hUdef : ∀ n, ∀ z, z ∈ U (n + 1) ↔ Xor' (z - 1 ∈ U n) (z ∈ U n) := by
    intro n z
    by_cases hz : 0 < z
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hz)
      have ha : 0 < a := by exact_mod_cast hz
      rw [hU_nat (n + 1) a, hU_pred n a ha, hU_nat n a, hTdef]
      exact hne_iff_xor (a - 1 ∈ T n) (a ∈ T n)
    · constructor
      · intro hu
        exact (hz (hUpos (n + 1) z hu)).elim
      · intro hx
        rcases hx with hx | hx
        · have hp := hUpos n (z - 1) hx.1
          exfalso
          exact hz (lt_trans hp (sub_lt_self z (by exact Int.zero_lt_one)))
        · exact (hz (hUpos n z hx.1)).elim
  have hcofinal := putnam_2000_b5_assumed U hUfin hUpos hUdef
  refine ⟨T, hTzero, hTdef, hTpos, ?_⟩
  rw [Set.infinite_iff_exists_gt]
  intro n
  rcases hcofinal (n + 1) with ⟨N, hN, hUN⟩
  refine ⟨N, ?_, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hN⟩
  ext a
  constructor
  · intro ha
    have hua : (a : ℤ) ∈ U N := (hU_nat N a).mpr ha
    rw [hUN] at hua
    rcases hua with hua | hua
    · rw [Finset.mem_union]
      have ha0 : a ∈ T 0 := (hU_nat 0 a).mp hua
      exact Or.inl (hTzero ▸ ha0)
    · rw [Finset.mem_union]
      right
      rcases hua with ⟨b, hb, hba⟩
      refine Finset.mem_image.mpr ⟨b, (hTzero ▸ hb), ?_⟩
      apply Int.natCast_inj.mp
      exact (sub_eq_iff_eq_add'.mp hba.symm).symm
  · intro ha
    rw [Finset.mem_union] at ha
    apply (hU_nat N a).mp
    rw [hUN]
    rcases ha with ha | ha
    · left
      apply (hU_nat 0 a).mpr
      exact hTzero.symm ▸ ha
    · right
      rcases Finset.mem_image.mp ha with ⟨b, hb, hab⟩
      refine ⟨b, hTzero ▸ hb, ?_⟩
      apply eq_sub_iff_add_eq'.mpr
      exact_mod_cast hab
