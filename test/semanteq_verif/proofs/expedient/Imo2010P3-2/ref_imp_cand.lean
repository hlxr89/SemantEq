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
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let toZ : ℕ+ → ℤ>0 := fun n => ⟨n, by exact_mod_cast n.property⟩
  let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.natAbs, by
    rw [Int.natAbs_pos]
    omega⟩
  have toN_toZ (n : ℕ+) : toN (toZ n) = n := by
    apply Subtype.ext
    change Int.natAbs (Int.ofNat n.1) = n.1
    simp
  have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
    apply Subtype.ext
    simp [toN, toZ, Int.natAbs_of_nonneg (le_of_lt z.2)]
  let gz : ℤ>0 → ℤ>0 := fun z => toZ (g (toN z))
  constructor
  · intro hsquare
    have hzsquare : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      obtain ⟨k, hk⟩ := hsquare (toN m) (toN n)
      have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
        subst k
        norm_num at hk
      refine ⟨toZ ⟨k, hkpos⟩, ?_⟩
      apply Subtype.ext
      simp [gz, toZ]
      have hmval : (Int.ofNat (toN m).1) = m.1 := by
        simp [toN, Int.natAbs_of_nonneg (le_of_lt m.2)]
      have hnval : (Int.ofNat (toN n).1) = n.1 := by
        simp [toN, Int.natAbs_of_nonneg (le_of_lt n.2)]
      rw [← hmval, ← hnval]
      simp only [pow_two] at hk
      change
        ((g (toN m)).1 + (toN n).1) * ((g (toN n)).1 + (toN m).1) =
          k * k at hk
      have hi := congrArg (fun x : ℕ => (x : ℤ)) hk
      norm_num at hi
      exact hi
    have hzsol := (imo2010_p3_assumed gz).2 hzsquare
    rcases hzsol with h | ⟨c, hc⟩
    · refine ⟨0, fun n => ?_⟩
      have hn := congrFun h (toZ n)
      change toZ (g (toN (toZ n))) = toZ n at hn
      rw [toN_toZ] at hn
      have hv := congrArg toN hn
      simp only [toN_toZ] at hv
      change (g n).1 = n.1 + 0
      simpa using congrArg Subtype.val hv
    · refine ⟨c.1.natAbs, fun n => ?_⟩
      have hcn := hc (toZ n)
      change toZ (g (toN (toZ n))) = toZ n + c at hcn
      rw [toN_toZ] at hcn
      change (g n).1 = n.1 + c.1.natAbs
      have hv := congrArg Subtype.val hcn
      change ((g n).1 : ℤ) = (n.1 : ℤ) + c.1 at hv
      have hcval : (c.1.natAbs : ℤ) = c.1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt c.2)]
      rw [← hcval] at hv
      exact_mod_cast hv
  · rintro ⟨c, hc⟩
    have hzsol : gz ∈ SolutionSet := by
      rcases c with _ | c
      · left
        funext z
        have hn : g (toN z) = toN z := by
          apply Subtype.ext
          exact hc (toN z)
        simpa [gz, hn, toZ_toN]
      · right
        refine ⟨toZ ⟨c + 1, by omega⟩, fun z => ?_⟩
        apply Subtype.ext
        dsimp [gz, toZ]
        rw [hc]
        simp [toN, Int.natAbs_of_nonneg (le_of_lt z.2)]
    have hzsquare := (imo2010_p3_assumed gz).1 hzsol
    intro m n
    obtain ⟨k, hk⟩ := hzsquare (toZ m) (toZ n)
    refine ⟨k.1.natAbs, ?_⟩
    change
      (toZ (g (toN (toZ m))) + toZ n) *
          (toZ (g (toN (toZ n))) + toZ m) = k * k at hk
    rw [toN_toZ, toN_toZ] at hk
    have hv := congrArg Subtype.val hk
    change
      (((g m).1 : ℤ) + n.1) * (((g n).1 : ℤ) + m.1) = k.1 * k.1 at hv
    have hkval : (k.1.natAbs : ℤ) = k.1 := by
      simp [Int.natAbs_of_nonneg (le_of_lt k.2)]
    rw [← hkval] at hv
    simp only [pow_two] at ⊢
    exact_mod_cast hv
