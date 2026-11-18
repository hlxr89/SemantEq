import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
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
  let gn : ℕ+ → ℕ+ := fun n => toN (g (toZ n))
  constructor
  · intro hg
    have hnsol : ∃ c : ℕ, ∀ n : ℕ+, gn n = n + c := by
      rcases hg with h | ⟨c, hc⟩
      · refine ⟨0, fun n => ?_⟩
        have hn := congrFun h (toZ n)
        change g (toZ n) = toZ n at hn
        have hv := congrArg toN hn
        change (gn n).1 = n.1 + 0
        simpa [gn, toN_toZ] using congrArg Subtype.val hv
      · refine ⟨c.1.natAbs, fun n => ?_⟩
        have hn := hc (toZ n)
        change g (toZ n) = toZ n + c at hn
        change (gn n).1 = n.1 + c.1.natAbs
        have hv := congrArg Subtype.val hn
        change (g (toZ n)).1 = (n.1 : ℤ) + c.1 at hv
        have hcval : (c.1.natAbs : ℤ) = c.1 := by
          simp [Int.natAbs_of_nonneg (le_of_lt c.2)]
        rw [← hcval] at hv
        dsimp [gn, toN]
        have hva := congrArg Int.natAbs hv
        rw [hcval] at hva
        rw [Int.natAbs_add_of_nonneg (by positivity) (le_of_lt c.2)] at hva
        simpa [Int.natAbs_of_nonneg (le_of_lt (g (toZ n)).2)] using hva
    have hnsquare := (problem_statement_assumed gn).2 hnsol
    intro m n
    obtain ⟨k, hk⟩ := hnsquare (toN m) (toN n)
    have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
      subst k
      norm_num at hk
    refine ⟨toZ ⟨k, hkpos⟩, ?_⟩
    apply Subtype.ext
    simp [gn, toZ]
    have hmval : (Int.ofNat (toN m).1) = m.1 := by
      simp [toN, Int.natAbs_of_nonneg (le_of_lt m.2)]
    have hnval : (Int.ofNat (toN n).1) = n.1 := by
      simp [toN, Int.natAbs_of_nonneg (le_of_lt n.2)]
    rw [← hmval, ← hnval]
    simp only [pow_two] at hk
    change
      ((gn (toN m)).1 + (toN n).1) * ((gn (toN n)).1 + (toN m).1) =
        k * k at hk
    have hi := congrArg (fun x : ℕ => (x : ℤ)) hk
    norm_num at hi
    have hgmval : (Int.ofNat (gn (toN m)).1) = (g m).1 := by
      simp [gn, toN, toZ_toN, Int.natAbs_of_nonneg (le_of_lt (g m).2)]
    have hgnval : (Int.ofNat (gn (toN n)).1) = (g n).1 := by
      simp [gn, toN, toZ_toN, Int.natAbs_of_nonneg (le_of_lt (g n).2)]
    change
      (Int.ofNat (gn (toN m)).1 + Int.ofNat (toN n).1) *
          (Int.ofNat (gn (toN n)).1 + Int.ofNat (toN m).1) =
        Int.ofNat k * Int.ofNat k at hi
    rw [hgmval, hgnval] at hi
    exact hi
  · intro hsquare
    have hnsquare : ∀ m n : ℕ+, ∃ k : ℕ, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      obtain ⟨k, hk⟩ := hsquare (toZ m) (toZ n)
      refine ⟨k.1.natAbs, ?_⟩
      change
        (g (toZ m) + toZ n) * (g (toZ n) + toZ m) = k * k at hk
      have hv := congrArg Subtype.val hk
      change
        ((g (toZ m)).1 + (n.1 : ℤ)) * ((g (toZ n)).1 + (m.1 : ℤ)) =
          k.1 * k.1 at hv
      have hkval : (k.1.natAbs : ℤ) = k.1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt k.2)]
      rw [← hkval] at hv
      change
        ((gn m).1 + n.1) * ((gn n).1 + m.1) = k.1.natAbs ^ 2
      dsimp [gn, toN]
      have hgmval : (Int.ofNat (g (toZ m)).1.natAbs) = (g (toZ m)).1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt (g (toZ m)).2)]
      have hgnval : (Int.ofNat (g (toZ n)).1.natAbs) = (g (toZ n)).1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt (g (toZ n)).2)]
      rw [← hgmval, ← hgnval] at hv
      simp only [pow_two]
      apply_fun (fun x : ℕ => (x : ℤ)) using Int.ofNat_injective
      norm_num
      rw [abs_of_pos (g (toZ m)).2, abs_of_pos (g (toZ n)).2]
      simpa [Int.natAbs_of_nonneg (le_of_lt (g (toZ m)).2),
        Int.natAbs_of_nonneg (le_of_lt (g (toZ n)).2),
        Int.natAbs_of_nonneg (le_of_lt k.2), abs_of_pos] using hv
    obtain ⟨c, hc⟩ := (problem_statement_assumed gn).1 hnsquare
    rcases c with _ | c
    · left
      funext z
      have hn := hc (toN z)
      change (gn (toN z)).1 = (toN z).1 + 0 at hn
      have hsub : gn (toN z) = toN z := by
        apply Subtype.ext
        simpa using hn
      have hz := congrArg toZ hsub
      simpa [gn, toN_toZ, toZ_toN] using hz
    · right
      refine ⟨toZ ⟨c + 1, by omega⟩, fun z => ?_⟩
      have hn := hc (toN z)
      change (gn (toN z)).1 = (toN z).1 + (c + 1) at hn
      apply Subtype.ext
      have hn' : (g z).1.natAbs = z.1.natAbs + (c + 1) := by
        simpa [gn, toN, toZ_toN] using hn
      have hi := congrArg (fun x : ℕ => (x : ℤ)) hn'
      norm_num at hi
      have hgz : (Int.ofNat (g z).1.natAbs) = (g z).1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt (g z).2)]
      have hz : (Int.ofNat z.1.natAbs) = z.1 := by
        simp [Int.natAbs_of_nonneg (le_of_lt z.2)]
      simp [abs_of_pos (g z).2, abs_of_pos z.2] at hi
      simpa [toZ] using hi
