import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+, 
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) →
    ∃ c : ℕ, ∀ n : ℕ+, g n = n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let toZ : ℕ+ → ℤ>0 := fun n => ⟨n.1, by exact_mod_cast n.2⟩
  let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.toNat, by omega⟩
  have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
    apply Subtype.ext
    simp [toZ, toN, Int.toNat_of_nonneg (le_of_lt z.2)]
  constructor
  · intro hg m n
    rcases hg with hg | ⟨c, hc⟩
    · refine ⟨m + n, ?_⟩
      simpa only [hg, id_eq, add_comm]
    · refine ⟨m + n + c, ?_⟩
      rw [hc m, hc n]
      have h1 : m + c + n = m + n + c := by
        apply Subtype.ext
        norm_num
        omega
      have h2 : n + c + m = m + n + c := by
        apply Subtype.ext
        norm_num
        omega
      rw [h1, h2]
  · intro hs
    let gn : ℕ+ → ℕ+ := fun n => toN (g (toZ n))
    have hgn : ∀ m n : ℕ+, ∃ k : ℕ, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      rcases hs (toZ m) (toZ n) with ⟨k, hk⟩
      refine ⟨k.1.toNat, ?_⟩
      have hv := congrArg Subtype.val hk
      dsimp [gn, toN, toZ]
      dsimp [toZ] at hv
      norm_num at hv ⊢
      apply Int.ofNat_inj.mp
      norm_num [Int.toNat_of_nonneg (le_of_lt (g _).2),
        Int.toNat_of_nonneg (le_of_lt k.2)]
      simpa [pow_two] using hv
    rcases problem_statement_assumed gn hgn with ⟨c, hc⟩
    by_cases hc0 : c = 0
    · left
      funext z
      have h := hc (toN z)
      dsimp [gn] at h
      rw [toZ_toN] at h
      norm_num [toN, Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2), hc0] at h
      have hi := congrArg (fun q : ℕ => (q : ℤ)) h
      norm_num [Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2)] at hi
      apply Subtype.ext
      exact hi
    · right
      let cz : ℤ>0 := ⟨c, by omega⟩
      refine ⟨cz, ?_⟩
      intro z
      have h := hc (toN z)
      dsimp [gn] at h
      rw [toZ_toN] at h
      norm_num [toN, Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2)] at h
      have hi := congrArg (fun q : ℕ => (q : ℤ)) h
      norm_num [Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2)] at hi
      apply Subtype.ext
      dsimp [cz]
      exact hi
