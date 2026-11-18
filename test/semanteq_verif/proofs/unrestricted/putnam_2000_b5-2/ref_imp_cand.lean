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
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (S₀ : Finset ℕ), (∀ x ∈ S₀, 0 < x) →
  ∃ (S : ℕ → Finset ℕ),
    S 0 = S₀ ∧
    (∀ n, ∀ a, a ∈ S (n + 1) ↔ (a - 1 ∈ S n) ≠ (a ∈ S n)) ∧
    (∀ n, ∀ a, a ∈ S n → 0 < a) ∧
    Set.Infinite {N : ℕ | S N = S₀ ∪ (Finset.image (fun a => N + a) S₀)} := by
  intro S₀ hS₀
  classical
  have prop_ne_iff (P Q : Prop) : (P ≠ Q) ↔ ¬(P ↔ Q) := by
    constructor
    · exact fun h he => h (propext he)
    · exact fun h he => h (eq_iff_iff.mp he)
  let T : ℕ → Finset ℕ := fun n =>
    Nat.rec S₀ (fun _ t => symmDiff (t.image Nat.succ) t) n
  have hT0 : T 0 = S₀ := by rfl
  have hTpos : ∀ n a, a ∈ T n → 0 < a := by
    intro n
    induction n with
    | zero => simpa [T] using hS₀
    | succ n ih =>
      intro a ha
      simp only [T, Nat.rec_add_one, Finset.mem_symmDiff] at ha
      rcases ha with ha | ha
      · rcases Finset.mem_image.mp ha.1 with ⟨b, hb, rfl⟩
        exact Nat.succ_pos b
      · exact ih a ha.1
  have hTdef : ∀ n a, a ∈ T (n + 1) ↔ (a - 1 ∈ T n) ≠ (a ∈ T n) := by
    intro n a
    have himage : a ∈ (T n).image Nat.succ ↔ a - 1 ∈ T n := by
      constructor
      · rintro ha
        rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
        simpa using hb
      · intro ha
        have hp : 0 < a - 1 := hTpos n (a - 1) ha
        apply Finset.mem_image.mpr
        exact ⟨a - 1, ha, by omega⟩
    rw [show T (n + 1) = symmDiff ((T n).image Nat.succ) (T n) by rfl]
    rw [Finset.mem_symmDiff, himage]
    rw [prop_ne_iff, ← xor_iff_not_iff]
    rfl
  let R : ℕ → Set ℤ := fun n => {z | ∃ a ∈ T n, (a : ℤ) = z}
  have hRfin : ∀ n, Set.Finite (R n) := by
    intro n
    exact (T n).finite_toSet.image (fun a : ℕ => (a : ℤ))
  have hRpos : ∀ n, ∀ z ∈ R n, z > 0 := by
    rintro n z ⟨a, ha, rfl⟩
    exact_mod_cast hTpos n a ha
  have hRdef : ∀ n, ∀ z, z ∈ R (n + 1) ↔ Xor' (z - 1 ∈ R n) (z ∈ R n) := by
    intro n z
    by_cases hz : 0 < z
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hz)
      have ha : 0 < a := by exact_mod_cast hz
      have hpred : ((a : ℤ) - 1 ∈ R n) ↔ a - 1 ∈ T n := by
        rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega]
        simp [R]
      have hhere : ((a : ℤ) ∈ R n) ↔ a ∈ T n := by simp [R]
      have hnext : ((a : ℤ) ∈ R (n + 1)) ↔ a ∈ T (n + 1) := by simp [R]
      rw [hnext, hpred, hhere, hTdef]
      rw [prop_ne_iff, ← xor_iff_not_iff]
    · have hnpos : z ≤ 0 := le_of_not_gt hz
      have hfalse : ∀ k, z ∉ R k := by
        intro k hk
        have := hRpos k z hk
        omega
      have hpredfalse : z - 1 ∉ R n := by
        intro hk
        have := hRpos n (z - 1) hk
        omega
      simp [hfalse, hpredfalse]
  have href := putnam_2000_b5_assumed R hRfin hRpos hRdef
  refine ⟨T, hT0, hTdef, hTpos, ?_⟩
  intro hfinite
  obtain ⟨m, hm⟩ := hfinite.exists_le
  obtain ⟨N, hN, hRN⟩ := href (m + 1)
  have hgood : T N = S₀ ∪ Finset.image (fun a => N + a) S₀ := by
    apply Finset.ext
    intro a
    have heq := Set.ext_iff.mp hRN (a : ℤ)
    have heq' : a ∈ T N ↔ a ∈ S₀ ∨ ∃ b ∈ S₀, (b : ℤ) = (a : ℤ) - (N : ℤ) := by
      simpa only [R, Int.ofNat_inj, exists_eq_right, hT0, Set.mem_union,
        Set.mem_setOf_eq] using heq
    constructor
    · intro ha
      rcases heq'.mp ha with ha | ⟨b, hb, hab⟩
      · exact Finset.mem_union_left _ ha
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨b, hb, by omega⟩
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact heq'.mpr (Or.inl ha)
      · rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
        apply heq'.mpr
        exact Or.inr ⟨b, hb, by push_cast; omega⟩
  have := hm N hgood
  omega
