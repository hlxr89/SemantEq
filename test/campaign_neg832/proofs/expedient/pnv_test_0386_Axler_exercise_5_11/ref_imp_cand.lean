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
  let L : End ℂ (ℕ → ℂ) :=
    { toFun := fun f n => f (n + 1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let R : End ℂ (ℕ → ℂ) :=
    { toFun := fun f n => match n with | 0 => 0 | k + 1 => f k
      map_add' := by
        intro f g
        funext n
        cases n <;> simp
      map_smul' := by
        intro c f
        funext n
        cases n <;> simp }
  have hLR : L * R = 1 := by
    ext f n
    simp [L, R]
  have h := exercise_5_11_assumed L R
  have hs : Subsingleton (R * L).Eigenvalues := by
    rw [← h, hLR]
    constructor
    intro a b
    apply Subtype.ext
    have ha := HasEigenvalue.exists_hasEigenvector a.property
    have hb := HasEigenvalue.exists_hasEigenvector b.property
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    have hax := hx.apply_eq_smul
    have hby := hy.apply_eq_smul
    simp only [Module.End.one_apply] at hax hby
    have xa : (a : ℂ) = 1 := by
      apply smul_left_injective ℂ hx.2
      simpa using hax.symm
    have yb : (b : ℂ) = 1 := by
      apply smul_left_injective ℂ hy.2
      simpa using hby.symm
    exact xa.trans yb.symm
  let e₀ : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  let e₁ : ℕ → ℂ := fun n => if n = 1 then 1 else 0
  have he₀ : (R * L).HasEigenvector 0 e₀ := by
    constructor
    · rw [mem_eigenspace_iff]
      funext n
      cases n <;> simp [R, L, e₀]
    · intro he
      have := congrFun he 0
      simp [e₀] at this
  have he₁ : (R * L).HasEigenvector 1 e₁ := by
    constructor
    · rw [mem_eigenspace_iff]
      funext n
      cases n with
      | zero => simp [R, L, e₁]
      | succ n => simp [R, L, e₁]
    · intro he
      have := congrFun he 1
      simp [e₁] at this
  have hz : (R * L).HasEigenvalue 0 := hasEigenvalue_of_hasEigenvector he₀
  have ho : (R * L).HasEigenvalue 1 := hasEigenvalue_of_hasEigenvector he₁
  have heq : (⟨0, hz⟩ : (R * L).Eigenvalues) = ⟨1, ho⟩ := hs.elim _ _
  have : (0 : ℂ) = 1 := congrArg Subtype.val heq
  exact (zero_ne_one this).elim
