import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let toP : PosInt → ℕ+ := fun x => ⟨x.1.toNat, by omega⟩
  let toZ : ℕ+ → PosInt := fun n => ⟨n.1, by exact_mod_cast n.2⟩
  have toP_toZ (n : ℕ+) : toP (toZ n) = n := by
    apply PNat.eq
    simp [toP, toZ]
  have toZ_toP (x : PosInt) : toZ (toP x) = x := by
    apply Subtype.ext
    simp [toP, toZ, Int.toNat_of_nonneg (le_of_lt x.2)]
  have toZ_add (a b : ℕ+) : toZ (a + b) = toZ a + toZ b := by
    apply Subtype.ext
    simp [toZ]
    norm_cast
  let gn : ℕ+ → ℕ+ := fun n => toP (g (toZ n))
  constructor
  · rintro (h_id | ⟨c, hc⟩) m n
    · refine ⟨m + n, ?_⟩
      rw [h_id]
      simp [id, add_comm]
    · refine ⟨g m + n, ?_⟩
      rw [hc m, hc n]
      congr 1
      apply Subtype.ext
      simp
      ring
  · intro hs
    have hsN : ∀ m n : ℕ+, ∃ k : ℕ+, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      rcases hs (toZ m) (toZ n) with ⟨k, hk⟩
      refine ⟨toP k, ?_⟩
      apply PNat.eq
      have hk' := congrArg (fun x : PosInt => x.1) hk
      simp at hk'
      have hkN := congrArg Int.toNat hk'
      rw [Int.toNat_mul
          (add_nonneg (le_of_lt (g (toZ m)).2) (le_of_lt (toZ n).2))
          (add_nonneg (le_of_lt (g (toZ n)).2) (le_of_lt (toZ m).2)),
        Int.toNat_add (le_of_lt (g (toZ m)).2) (le_of_lt (toZ n).2),
        Int.toNat_add (le_of_lt (g (toZ n)).2) (le_of_lt (toZ m).2),
        Int.toNat_mul (le_of_lt k.2) (le_of_lt k.2)] at hkN
      simpa [gn, toP, toZ, pow_two] using hkN
    rcases (problem_statement_assumed gn).1 hsN with ⟨c, hc⟩
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · left
      funext x
      have hp : gn (toP x) = toP x := by
        apply PNat.eq
        simpa using hc (toP x)
      have hz := congrArg toZ hp
      simpa [gn, toZ_toP] using hz
    · right
      let cp : ℕ+ := ⟨c, hpos⟩
      refine ⟨toZ cp, fun x => ?_⟩
      have hp : gn (toP x) = toP x + cp := by
        apply PNat.eq
        simpa [cp] using hc (toP x)
      have hz := congrArg toZ hp
      simpa [gn, toZ_toP, toZ_add] using hz
