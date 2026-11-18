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
theorem dummy {V : Type*} [AddCommGroup V] [Module.{0} ℂ V] (S T : Module.End ℂ V) : ∀ (v : V), S (T v) = T (S v) := by
  let L : Module.End ℂ (ℕ → ℂ) :=
    { toFun := fun f n => f (n + 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let R : Module.End ℂ (ℕ → ℂ) :=
    { toFun := fun f n => if n = 0 then 0 else f (n - 1)
      map_add' := by intros; ext n; split <;> simp_all
      map_smul' := by intros; ext n; split <;> simp_all }
  have hEq := exercise_5_11_assumed L R
  have hLR : ∀ f, (L * R) f = f := by
    intro f
    ext n
    simp [L, R, Module.End.mul_apply]
  have source_subsingleton : Subsingleton (L * R).Eigenvalues := by
    constructor
    intro a b
    apply Subtype.ext
    have eigenvalue_eq_one : ∀ c : (L * R).Eigenvalues, c.1 = 1 := by
      intro c
      obtain ⟨x, hx⟩ := HasEigenvalue.exists_hasEigenvector c.2
      have happ := hx.apply_eq_smul
      rw [hLR x] at happ
      have hx0 : x ≠ 0 := hx.2
      obtain ⟨n, hn⟩ : ∃ n, x n ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx0 (funext h)
      have hn_eq := congrFun happ n
      simp only [Pi.smul_apply, smul_eq_mul] at hn_eq
      exact mul_left_cancel₀ hn (by simpa [mul_comm] using hn_eq.symm)
    exact (eigenvalue_eq_one a).trans (eigenvalue_eq_one b).symm
  rw [hEq] at source_subsingleton
  have hRLeval : ∀ f, (R * L) f = fun n => if n = 0 then 0 else f n := by
    intro f
    ext n
    by_cases hn : n = 0
    · simp [L, R, Module.End.mul_apply, hn]
    · have hnplus : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
      simp [L, R, Module.End.mul_apply, hn, hnplus]
  let e : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  have e_ne_zero : e ≠ 0 := by
    intro he
    have := congrFun he 0
    simpa [e] using this
  have hzero : (R * L).HasEigenvalue 0 := by
    apply hasEigenvalue_of_hasEigenvector
    constructor
    · rw [mem_eigenspace_iff, hRLeval e]
      ext n
      simp [e]
    · exact e_ne_zero
  have hone : (R * L).HasEigenvalue 1 := by
    apply hasEigenvalue_of_hasEigenvector
    let o : ℕ → ℂ := fun n => if n = 0 then 0 else 1
    have o_ne_zero : o ≠ 0 := by
      intro ho
      have := congrFun ho 1
      simpa [o] using this
    refine ⟨?_, o_ne_zero⟩
    rw [mem_eigenspace_iff, hRLeval o]
    ext n
    simp [o]
  have heq : (⟨0, hzero⟩ : (R * L).Eigenvalues) = ⟨1, hone⟩ :=
    source_subsingleton.elim _ _
  have : (0 : ℂ) = 1 := congrArg Subtype.val heq
  exact (zero_ne_one this).elim
