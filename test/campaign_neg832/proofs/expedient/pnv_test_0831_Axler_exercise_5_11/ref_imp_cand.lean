import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_11_assumed {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (S T : End F V) :
  (S * T).Eigenvalues = (T * S).Eigenvalues := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {S T : Module.End K V} : S.eigenspace = T.eigenspace := by
  let L : Module.End ℚ (ℕ → ℚ) :=
    { toFun := fun x n => x (n + 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let R : Module.End ℚ (ℕ → ℚ) :=
    { toFun := fun x n => match n with
        | 0 => 0
        | n + 1 => x n
      map_add' := by
        intro x y
        funext n
        cases n <;> simp
      map_smul' := by
        intro c x
        funext n
        cases n <;> simp }
  have hLR : L * R = 1 := by
    ext x n
    rfl
  have hs : Subsingleton (L * R).Eigenvalues := by
    rw [hLR]
    constructor
    intro a b
    apply Subtype.ext
    have value_eq_one : ∀ e : (1 : Module.End ℚ (ℕ → ℚ)).Eigenvalues, e.1 = 1 := by
      intro e
      obtain ⟨v, hv, hv0⟩ := HasEigenvalue.exists_hasEigenvector e.property
      have hv_eq : v = e.1 • v := by
        simpa [mem_eigenspace_iff] using hv
      have hn : ∃ n, v n ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply hv0
        funext n
        exact hn n
      obtain ⟨n, hn⟩ := hn
      have he := congrFun hv_eq n
      simp only [Pi.smul_apply, smul_eq_mul] at he
      exact (mul_right_cancel₀ hn) (by simpa using he.symm)
    exact (value_eq_one a).trans (value_eq_one b).symm
  have h := exercise_5_11_assumed L R
  rw [h] at hs
  let v0 : ℕ → ℚ := fun n => if n = 0 then 1 else 0
  let v1 : ℕ → ℚ := fun n => if n = 1 then 1 else 0
  have hv0 : (R * L).HasEigenvalue 0 := by
    apply hasEigenvalue_of_hasEigenvector (x := v0)
    constructor
    · rw [mem_eigenspace_iff]
      funext n
      cases n with
      | zero => simp [L, R, v0]
      | succ n => simp [L, R, v0]
    · intro hv
      have := congrFun hv 0
      simp [v0] at this
  have hv1 : (R * L).HasEigenvalue 1 := by
    apply hasEigenvalue_of_hasEigenvector (x := v1)
    constructor
    · rw [mem_eigenspace_iff]
      funext n
      cases n with
      | zero => simp [L, R, v1]
      | succ n => simp [L, R, v1]
    · intro hv
      have := congrFun hv 1
      simp [v1] at this
  have bad := congrArg Subtype.val (hs.elim (⟨0, hv0⟩ : (R * L).Eigenvalues) ⟨1, hv1⟩)
  norm_num at bad
