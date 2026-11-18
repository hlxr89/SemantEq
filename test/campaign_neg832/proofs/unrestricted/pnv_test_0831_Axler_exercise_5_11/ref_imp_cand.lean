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
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
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
  have htypes := exercise_5_11_assumed L R
  rw [hLR] at htypes
  have hone : Subsingleton (Module.End.Eigenvalues (1 : Module.End ℚ (ℕ → ℚ))) := by
    constructor
    intro a b
    apply Subtype.ext
    have ha := Module.End.HasEigenvalue.exists_hasEigenvector a.property
    obtain ⟨x, hxmem, hxne⟩ := ha
    have hax := Module.End.mem_eigenspace_iff.mp hxmem
    have hcoord : ∃ n, x n ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hxne
      funext n
      exact hn n
    obtain ⟨n, hn⟩ := hcoord
    have ha1 : a.val = 1 := by
      have heq := congrFun hax n
      simp only [one_apply] at heq
      apply mul_right_cancel₀ hn
      simpa using heq.symm
    have hb := Module.End.HasEigenvalue.exists_hasEigenvector b.property
    obtain ⟨y, hymem, hyne⟩ := hb
    have hby := Module.End.mem_eigenspace_iff.mp hymem
    have hcoord' : ∃ n, y n ≠ 0 := by
      by_contra hn'
      push_neg at hn'
      apply hyne
      funext n
      exact hn' n
    obtain ⟨n, hn⟩ := hcoord'
    have hb1 : b.val = 1 := by
      have heq := congrFun hby n
      simp only [one_apply] at heq
      apply mul_right_cancel₀ hn
      simpa using heq.symm
    exact ha1.trans hb1.symm
  have hsub : Subsingleton (Module.End.Eigenvalues (R * L)) := by
    rw [← htypes]
    exact hone
  let e0 : ℕ → ℚ := fun n => if n = 0 then 1 else 0
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  have hz : (R * L).HasEigenvalue 0 := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, he0ne⟩
    rw [Module.End.mem_eigenspace_iff]
    funext n
    cases n with
    | zero => simp [R, L]
    | succ n =>
      simp [R, L, e0]
  have ho : (R * L).HasEigenvalue 1 := by
    let tail : ℕ → ℚ := fun n => if n = 0 then 0 else 1
    have htailne : tail ≠ 0 := by
      intro h
      have := congrFun h 1
      simp [tail] at this
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, htailne⟩
    rw [Module.End.mem_eigenspace_iff]
    funext n
    cases n with
    | zero => simp [R, L, tail]
    | succ n =>
      simp [R, L, tail]
  let z : Module.End.Eigenvalues (R * L) := ⟨0, hz⟩
  let o : Module.End.Eigenvalues (R * L) := ⟨1, ho⟩
  have hzo : z = o := hsub.elim z o
  have : (0 : ℚ) = 1 := congrArg Subtype.val hzo
  norm_num at this
