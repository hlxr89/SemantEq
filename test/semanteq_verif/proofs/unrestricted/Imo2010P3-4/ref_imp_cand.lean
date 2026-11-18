import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem imo2010_p3_assumed (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ g : ℕ+ → ℕ+, 
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) →
    ∃ c : ℕ, ∀ n : ℕ+, g n = n + c := by
  intro g hs
  let toZ : ℕ+ → ℤ>0 := fun n => ⟨n.1, by exact_mod_cast n.2⟩
  let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.toNat, by omega⟩
  have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
    apply Subtype.ext
    simp [toZ, toN, Int.toNat_of_nonneg (le_of_lt z.2)]
  have toN_toZ (n : ℕ+) : toN (toZ n) = n := by
    apply Subtype.ext
    simp [toZ, toN]
  have toN_val (z : ℤ>0) : ((toN z).1 : ℤ) = z.1 := by
    simp [toN, Int.toNat_of_nonneg (le_of_lt z.2)]
  let gz : ℤ>0 → ℤ>0 := fun z => toZ (g (toN z))
  have hgz : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
    intro m n
    rcases hs (toN m) (toN n) with ⟨k, hk⟩
    have hk0 : 0 < k := by
      by_contra h
      have : k = 0 := by omega
      simp [this] at hk
    let kz : ℤ>0 := ⟨k, by exact_mod_cast hk0⟩
    refine ⟨kz, ?_⟩
    apply Subtype.ext
    dsimp [gz, toZ, toN, kz]
    norm_num
    have hv : (((g (toN m)).1 : ℤ) + (toN n).1) *
        (((g (toN n)).1 : ℤ) + (toN m).1) = (k : ℤ) ^ 2 := by
      exact_mod_cast hk
    rw [toN_val m, toN_val n] at hv
    simpa [pow_two] using hv
  rcases (imo2010_p3_assumed gz).2 hgz with h | ⟨c, hc⟩
  · refine ⟨0, ?_⟩
    intro n
    have hn := congrFun h (toZ n)
    dsimp [gz] at hn
    rw [toN_toZ] at hn
    have hv := congrArg Subtype.val hn
    norm_num [toZ] at hv
    exact_mod_cast hv
  · refine ⟨c.1.toNat, ?_⟩
    intro n
    have hn := hc (toZ n)
    dsimp [gz] at hn
    rw [toN_toZ] at hn
    have hv := congrArg Subtype.val hn
    norm_num [toZ, Int.toNat_of_nonneg (le_of_lt c.2)] at hv ⊢
    apply Int.ofNat_inj.mp
    norm_num [Int.toNat_of_nonneg (le_of_lt c.2)]
    exact hv
