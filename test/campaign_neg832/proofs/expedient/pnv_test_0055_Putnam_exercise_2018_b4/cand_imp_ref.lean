import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a : ℝ) (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = a) (h2 : x 2 = a) (h_rec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (h_zero : ∃ n, x n = 0) : ∃ p, ∀ k, x (k + p) = x k := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  have hT : ∀ n : ℕ, x n = (Polynomial.Chebyshev.T ℝ (Nat.fib n : ℤ)).eval a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with (_ | _ | _ | n)
      · simpa using hx0
      · simpa using hx1
      · simpa using hx2
      · rw [hxn (n + 2) (by omega), ih (n + 2) (by omega),
          show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega,
          ih (n + 1) (by omega), ih n (by omega)]
        have hp := congrArg (fun P : Polynomial ℝ => P.eval a)
          (Polynomial.Chebyshev.T_mul_T ℝ (Nat.fib (n + 2) : ℤ)
            (Nat.fib (n + 1) : ℤ))
        have hsum : Nat.fib (n + 2) + Nat.fib (n + 1) = Nat.fib (n + 3) := by
          rw [add_comm, ← Nat.fib_add_two]
        have hsumZ : (Nat.fib (n + 2) : ℤ) + (Nat.fib (n + 1) : ℤ) =
            (Nat.fib (n + 3) : ℤ) := by exact_mod_cast hsum
        have hdiffZ : (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) =
            (Nat.fib n : ℤ) := by
          have hrZ : (Nat.fib (n + 2) : ℤ) =
              (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
            exact_mod_cast (Nat.fib_add_two (n := n))
          omega
        rw [hsumZ, hdiffZ] at hp
        norm_num [Polynomial.eval_add, Polynomial.eval_mul] at hp ⊢
        linarith
  obtain ⟨m, hm⟩ := h
  have hm0 : m ≠ 0 := by
    intro he
    subst m
    linarith [hx0]
  have hfm0 : Nat.fib m ≠ 0 := by simpa using hm0
  have ha : |a| ≤ 1 := by
    apply (Polynomial.Chebyshev.abs_eval_T_real_le_one_iff
      (show (Nat.fib m : ℤ) ≠ 0 by exact_mod_cast hfm0) a).mpr
    rw [← hT m, hm]
    norm_num
  let θ := Real.arccos a
  have haθ : Real.cos θ = a := Real.cos_arccos (neg_le_of_abs_le ha) (le_of_abs_le ha)
  have hxcos : ∀ n : ℕ, x n = Real.cos ((Nat.fib n : ℝ) * θ) := by
    intro n
    rw [hT n, ← haθ, Polynomial.Chebyshev.T_real_cos]
    norm_num
  have hmcos : Real.cos ((Nat.fib m : ℝ) * θ) = 0 := by
    rw [← hxcos m, hm]
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp hmcos
  let q := 4 * Nat.fib m
  have hq : q ≠ 0 := by
    dsimp [q]
    omega
  letI : NeZero q := ⟨hq⟩
  let e : Equiv.Perm (ZMod q × ZMod q) :=
    { toFun := fun z => (z.2, z.1 + z.2)
      invFun := fun z => (z.2 - z.1, z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
  have heFib : ∀ n : ℕ,
      (e ^ n) (0, 1) = ((Nat.fib n : ZMod q), (Nat.fib (n + 1) : ZMod q)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change e ((e ^ n) (0, 1)) = _
      rw [ih]
      simp only [e, Equiv.coe_fn_mk]
      ext
      · rfl
      · push_cast
        rw [show n + 1 + 1 = n + 2 by omega, Nat.fib_add_two]
        norm_cast
  obtain ⟨p, hp, hep⟩ := (isOfFinOrder_of_finite e).exists_pow_eq_one
  refine ⟨p, Nat.ne_of_gt hp, ?_⟩
  intro k
  rw [hxcos (k + p), hxcos k]
  have hstate :
      ((Nat.fib (k + p) : ZMod q), (Nat.fib (k + p + 1) : ZMod q)) =
        ((Nat.fib k : ZMod q), (Nat.fib (k + 1) : ZMod q)) := by
    rw [← heFib, ← heFib, pow_add, hep, mul_one]
  have hcast : (Nat.fib (k + p) : ZMod q) = (Nat.fib k : ZMod q) :=
    congrArg Prod.fst hstate
  have hdiv : (q : ℤ) ∣ (Nat.fib k : ℤ) - (Nat.fib (k + p) : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp (by exact_mod_cast hcast)
  obtain ⟨t, ht⟩ := hdiv
  rw [show (Nat.fib (k + p) : ℝ) * θ =
      (Nat.fib k : ℝ) * θ + ((-t * (2 * j + 1) : ℤ) : ℝ) * (2 * Real.pi) by
        have htR : (Nat.fib k : ℝ) - (Nat.fib (k + p) : ℝ) =
            4 * (Nat.fib m : ℝ) * (t : ℝ) := by
          exact_mod_cast ht
        calc
          (Nat.fib (k + p) : ℝ) * θ =
              ((Nat.fib k : ℝ) - 4 * (Nat.fib m : ℝ) * (t : ℝ)) * θ := by
                rw [← htR]
                ring
          _ = (Nat.fib k : ℝ) * θ + ((-t * (2 * j + 1) : ℤ) : ℝ) *
                (2 * Real.pi) := by
                  calc
                    ((Nat.fib k : ℝ) - 4 * (Nat.fib m : ℝ) * (t : ℝ)) * θ =
                        (Nat.fib k : ℝ) * θ - 4 * (t : ℝ) *
                          ((Nat.fib m : ℝ) * θ) := by ring
                    _ = (Nat.fib k : ℝ) * θ + ((-t * (2 * j + 1) : ℤ) : ℝ) *
                          (2 * Real.pi) := by
                      rw [hj]
                      push_cast
                      ring
                  ]
  exact Real.cos_add_int_mul_two_pi _ _
