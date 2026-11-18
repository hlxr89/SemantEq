import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

def pnatToPosInt (n : ℕ+) : PosInt :=
  ⟨n, by exact_mod_cast n.prop⟩

def posIntToPNat (z : PosInt) : ℕ+ :=
  ⟨z.1.toNat, Int.lt_toNat.mpr z.2⟩

@[simp] lemma pnatToPosInt_posIntToPNat (z : PosInt) :
    pnatToPosInt (posIntToPNat z) = z := by
  apply Subtype.ext
  exact Int.toNat_of_nonneg (le_of_lt z.2)

@[simp] lemma posIntToPNat_pnatToPosInt (n : ℕ+) :
    posIntToPNat (pnatToPosInt n) = n := by
  apply PNat.eq
  change Int.toNat (n : ℕ) = (n : ℕ)
  exact Int.toNat_natCast n

lemma candSquare_to_refSquare (g : ℕ+ → ℕ+)
    (h : ∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) :
    ∀ m n : PosInt,
      IsSquare
        (((pnatToPosInt ∘ g ∘ posIntToPNat) m + n) *
          ((pnatToPosInt ∘ g ∘ posIntToPNat) n + m)) := by
  intro m n
  obtain ⟨k, hk⟩ := h (posIntToPNat m) (posIntToPNat n)
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    subst k
    simp only [pow_two, mul_zero] at hk
    have hp : 0 <
        ((g (posIntToPNat m) : ℕ) + (posIntToPNat n : ℕ)) *
          ((g (posIntToPNat n) : ℕ) + (posIntToPNat m : ℕ)) :=
      Nat.mul_pos (Nat.add_pos_left (g (posIntToPNat m)).prop _)
        (Nat.add_pos_left (g (posIntToPNat n)).prop _)
    exact (Nat.ne_of_gt hp) hk
  refine ⟨pnatToPosInt ⟨k, hkpos⟩, ?_⟩
  apply Subtype.ext
  change
    ((↑(g (posIntToPNat m)) : ℤ) + n.1) *
        ((↑(g (posIntToPNat n)) : ℤ) + m.1) = (k : ℤ) * (k : ℤ)
  rw [← Int.toNat_of_nonneg (le_of_lt m.2),
    ← Int.toNat_of_nonneg (le_of_lt n.2)]
  have hk' :
      ((g (posIntToPNat m) : ℕ) + (posIntToPNat n : ℕ)) *
          ((g (posIntToPNat n) : ℕ) + (posIntToPNat m : ℕ)) = k * k := by
    simpa only [pow_two] using hk
  exact_mod_cast hk'

lemma refSquare_to_candSquare (g : ℕ+ → ℕ+)
    (h : ∀ m n : PosInt,
      IsSquare
        (((pnatToPosInt ∘ g ∘ posIntToPNat) m + n) *
          ((pnatToPosInt ∘ g ∘ posIntToPNat) n + m))) :
    ∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2 := by
  intro m n
  obtain ⟨r, hr⟩ := h (pnatToPosInt m) (pnatToPosInt n)
  refine ⟨r.1.toNat, ?_⟩
  have hrval := congrArg (fun z : PosInt => z.1) hr
  change
    ((↑(g m) : ℤ) + (n : ℕ)) * ((↑(g n) : ℤ) + (m : ℕ)) =
      r.1 * r.1 at hrval
  change
    ((g m : ℕ) + (n : ℕ)) * ((g n : ℕ) + (m : ℕ)) = r.1.toNat ^ 2
  rw [pow_two]
  rw [← Int.toNat_of_nonneg (le_of_lt r.2)] at hrval
  exact_mod_cast hrval

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
  constructor
  · intro h
    have hsol := (imo2010_p3_assumed (pnatToPosInt ∘ g ∘ posIntToPNat)).2
      (candSquare_to_refSquare g h)
    rcases hsol with hid | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have hn := congrFun hid (pnatToPosInt n)
      simpa only [Function.comp_apply, posIntToPNat_pnatToPosInt, id_eq,
        Nat.add_zero] using congrArg (fun z : PosInt => z.1.toNat) hn
    · refine ⟨c.1.toNat, ?_⟩
      intro n
      have hn := hc (pnatToPosInt n)
      change pnatToPosInt (g n) = pnatToPosInt n + c at hn
      have hnval := congrArg (fun z : PosInt => z.1) hn
      change (↑(g n) : ℤ) = (n : ℕ) + c.1 at hnval
      rw [← Int.toNat_of_nonneg (le_of_lt c.2)] at hnval
      exact_mod_cast hnval
  · rintro ⟨c, hc⟩
    have hmem : (pnatToPosInt ∘ g ∘ posIntToPNat) ∈ SolutionSet := by
      by_cases hc0 : c = 0
      · left
        funext z
        apply Subtype.ext
        have hz := hc (posIntToPNat z)
        change (↑(g (posIntToPNat z)) : ℤ) = z.1
        rw [← Int.toNat_of_nonneg (le_of_lt z.2)]
        have hz' : (g (posIntToPNat z)).val = (posIntToPNat z).val := by
          simpa only [hc0, Nat.add_zero] using hz
        exact congrArg (fun a : ℕ => (a : ℤ)) hz'
      · right
        have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        refine ⟨pnatToPosInt ⟨c, hcpos⟩, ?_⟩
        intro z
        apply Subtype.ext
        have hz := hc (posIntToPNat z)
        change (↑(g (posIntToPNat z)) : ℤ) = z.1 + (c : ℤ)
        rw [← Int.toNat_of_nonneg (le_of_lt z.2)]
        exact_mod_cast hz
    exact refSquare_to_candSquare g ((imo2010_p3_assumed
      (pnatToPosInt ∘ g ∘ posIntToPNat)).1 hmem)
