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
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let f : ℕ+ → ℕ+ := posIntToPNat ∘ g ∘ pnatToPosInt
  have hconj : pnatToPosInt ∘ f ∘ posIntToPNat = g := by
    funext z
    simp only [f, Function.comp_apply, pnatToPosInt_posIntToPNat]
  constructor
  · intro hmem
    have hfsol : ∃ c : ℕ, ∀ n : ℕ+, f n = n + c := by
      rcases hmem with hid | ⟨c, hc⟩
      · refine ⟨0, ?_⟩
        intro n
        have hn := congrFun hid (pnatToPosInt n)
        change (g (pnatToPosInt n)).1.toNat = (n : ℕ) + 0
        rw [Nat.add_zero]
        rw [hn]
        exact Int.toNat_natCast n
      · refine ⟨c.1.toNat, ?_⟩
        intro n
        have hn := hc (pnatToPosInt n)
        change (g (pnatToPosInt n)).1.toNat = (n : ℕ) + c.1.toNat
        rw [hn]
        exact Int.toNat_add (le_of_lt (pnatToPosInt n).2) (le_of_lt c.2)
    have hfsq := (problem_statement_assumed f).2 hfsol
    rw [← hconj]
    exact candSquare_to_refSquare f hfsq
  · intro hsq
    have hfsq : ∀ m n : ℕ+, ∃ k : ℕ, (f m + n) * (f n + m) = k^2 := by
      apply refSquare_to_candSquare f
      rw [hconj]
      exact hsq
    obtain ⟨c, hc⟩ := (problem_statement_assumed f).1 hfsq
    by_cases hc0 : c = 0
    · left
      funext z
      apply Subtype.ext
      have hz := hc (posIntToPNat z)
      simp only [f, Function.comp_apply, pnatToPosInt_posIntToPNat] at hz
      change (g z).1.toNat = z.1.toNat + c at hz
      rw [hc0, Nat.add_zero] at hz
      have hz' := congrArg (fun a : ℕ => (a : ℤ)) hz
      change ((g z).1.toNat : ℤ) = (z.1.toNat : ℤ) at hz'
      rw [Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2)] at hz'
      exact hz'
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      refine ⟨pnatToPosInt ⟨c, hcpos⟩, ?_⟩
      intro z
      apply Subtype.ext
      have hz := hc (posIntToPNat z)
      simp only [f, Function.comp_apply, pnatToPosInt_posIntToPNat] at hz
      change (g z).1.toNat = z.1.toNat + c at hz
      have hz' := congrArg (fun a : ℕ => (a : ℤ)) hz
      change ((g z).1.toNat : ℤ) = ((z.1.toNat + c : ℕ) : ℤ) at hz'
      rw [Nat.cast_add, Int.toNat_of_nonneg (le_of_lt (g z).2),
        Int.toNat_of_nonneg (le_of_lt z.2)] at hz'
      exact hz'
