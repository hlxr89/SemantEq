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
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let toP : PosInt → ℕ+ := fun x => ⟨x.1.toNat, by omega⟩
  let toZ : ℕ+ → PosInt := fun n => ⟨n.1, by exact_mod_cast n.2⟩
  have toP_toZ (n : ℕ+) : toP (toZ n) = n := by
    apply PNat.eq
    simp [toP, toZ]
  have toZ_toP (x : PosInt) : toZ (toP x) = x := by
    apply Subtype.ext
    simp [toP, toZ, Int.toNat_of_nonneg (le_of_lt x.2)]
  let gz : PosInt → PosInt := fun x => toZ (g (toP x))
  constructor
  · intro h
    have hs : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      rcases h (toP m) (toP n) with ⟨k, hk⟩
      refine ⟨toZ k, ?_⟩
      have hk' := congrArg (fun x : ℕ+ => x.1) hk
      change ((g (toP m)).1 + (toP n).1) *
        ((g (toP n)).1 + (toP m).1) = k.1 ^ 2 at hk'
      apply Subtype.ext
      simp [gz, toZ]
      rw [← Int.toNat_of_nonneg (le_of_lt m.2),
        ← Int.toNat_of_nonneg (le_of_lt n.2)]
      norm_cast
      simpa [toP, pow_two] using hk'
    rcases (imo2010_p3_assumed gz).2 hs with h_id | ⟨c, hc⟩
    · refine ⟨0, fun n => ?_⟩
      have hn := congrFun h_id (toZ n)
      change (g n).1 = n.1 + 0
      simpa [gz, toP_toZ, toZ] using congrArg (fun x : PosInt => x.1.toNat) hn
    · refine ⟨c.1.toNat, fun n => ?_⟩
      have hn := hc (toZ n)
      change (g n).1 = n.1 + c.1.toNat
      simpa [gz, toP_toZ, toZ, Int.toNat_add (show 0 ≤ (n.1 : ℤ) from by positivity)
        (le_of_lt c.2)] using congrArg (fun x : PosInt => x.1.toNat) hn
  · rintro ⟨c, hc⟩ m n
    let k : ℕ+ := ⟨g m + n, by positivity⟩
    refine ⟨k, ?_⟩
    apply PNat.eq
    change ((g m).1 + n.1) * ((g n).1 + m.1) = ((g m).1 + n.1) ^ 2
    have hm := hc m
    have hn := hc n
    have hfac : (g n).1 + m.1 = (g m).1 + n.1 := by
      calc
        (g n).1 + m.1 = (n.1 + c) + m.1 := congrArg (fun x => x + m.1) hn
        _ = (m.1 + c) + n.1 := by omega
        _ = (g m).1 + n.1 := congrArg (fun x => x + n.1) hm.symm
    rw [hfac]
    simp [pow_two]
