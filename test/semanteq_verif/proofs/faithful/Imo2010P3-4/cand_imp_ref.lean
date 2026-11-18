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
  constructor
  · rintro (hid | ⟨c, hc⟩)
    · subst g
      intro m n
      rw [isSquare_iff_exists_sq]
      refine ⟨m + n, ?_⟩
      apply Subtype.ext
      change (m.1 + n.1) * (n.1 + m.1) = (m.1 + n.1) ^ 2
      ring
    · intro m n
      rw [hc m, hc n, isSquare_iff_exists_sq]
      refine ⟨m + n + c, ?_⟩
      apply Subtype.ext
      change (m.1 + c.1 + n.1) * (n.1 + c.1 + m.1) =
        (m.1 + n.1 + c.1) ^ 2
      ring
  · intro h
    let gn : ℕ+ → ℕ+ := fun n =>
      ⟨(g ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩).1.toNat, by
        have := (g ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩).2
        omega⟩
    have hn : ∀ m n : ℕ+, ∃ k : ℕ, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      have hs := h ⟨(m.1 : ℤ), by exact_mod_cast m.2⟩
        ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩
      rw [isSquare_iff_exists_sq] at hs
      obtain ⟨k, hk⟩ := hs
      refine ⟨k.1.toNat, ?_⟩
      dsimp [gn]
      have hgm := (g ⟨(m.1 : ℤ), by exact_mod_cast m.2⟩).2
      have hgn := (g ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩).2
      have hk' := congrArg Subtype.val hk
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg (le_of_lt hgm),
        Int.toNat_of_nonneg (le_of_lt hgn),
        Int.toNat_of_nonneg (le_of_lt k.2)]
      simpa using hk'
    obtain ⟨c, hc⟩ := problem_statement_assumed gn hn
    by_cases hzero : c = 0
    · left
      funext x
      apply Subtype.ext
      have hx := hc ⟨x.1.toNat, by omega⟩
      dsimp [gn] at hx
      have hcanon : (⟨(x.1.toNat : ℤ), by omega⟩ : ℤ>0) = x := by
        apply Subtype.ext
        exact Int.toNat_of_nonneg (le_of_lt x.2)
      have hx' : (g ⟨(x.1.toNat : ℤ), by omega⟩).1 = x.1.toNat + c := by
        have hgpos := (g ⟨(x.1.toNat : ℤ), by omega⟩).2
        have hcast := congrArg (fun z : ℕ => (z : ℤ)) hx
        push_cast at hcast
        rw [Int.toNat_of_nonneg (le_of_lt hgpos)] at hcast
        exact hcast
      rw [hcanon] at hx'
      have hxval := Int.toNat_of_nonneg (le_of_lt x.2)
      simp only [id_eq]
      omega
    · right
      let cz : ℤ>0 := ⟨(c : ℤ), by omega⟩
      refine ⟨cz, fun x => ?_⟩
      apply Subtype.ext
      have hx := hc ⟨x.1.toNat, by omega⟩
      dsimp [gn] at hx
      have hcanon : (⟨(x.1.toNat : ℤ), by omega⟩ : ℤ>0) = x := by
        apply Subtype.ext
        exact Int.toNat_of_nonneg (le_of_lt x.2)
      have hx' : (g ⟨(x.1.toNat : ℤ), by omega⟩).1 = x.1.toNat + c := by
        have hgpos := (g ⟨(x.1.toNat : ℤ), by omega⟩).2
        have hcast := congrArg (fun z : ℕ => (z : ℤ)) hx
        push_cast at hcast
        rw [Int.toNat_of_nonneg (le_of_lt hgpos)] at hcast
        exact hcast
      rw [hcanon] at hx'
      dsimp [cz]
      have hxval := Int.toNat_of_nonneg (le_of_lt x.2)
      omega
