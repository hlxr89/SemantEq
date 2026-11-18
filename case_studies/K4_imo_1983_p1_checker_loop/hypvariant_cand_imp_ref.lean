import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosReal : Type := { x : ℝ // 0 < x }

notation "ℝ+" => PosReal

def SolutionSet : Set (ℝ+ → ℝ+) := { fun x ↦ 1 / x }

def Imo1983P1_solution : Set (ℝ → ℝ) := {f | ∀ x : ℝ, 0 < x → f x = 1 / x}

theorem Imo1983P1_assumed (f : ℝ → ℝ) (hf_pos : ∀ x : ℝ, 0 < x → 0 < f x) :
    ((∀ x y : ℝ, 0 < x → 0 < y → f (x * f y) = y * f x) ∧
      Tendsto f atTop (nhds 0)) ↔
    f ∈ Imo1983P1_solution := by
  sorry

theorem Imo1983P1_refs (f : ℝ+ → ℝ+) :
    f ∈ SolutionSet ↔
    ((∀ x y, f (x * f y) = y * f x) ∧
     (∀ ε, ∃ x, ∀ y, x < y → f y < ε)) := by
  let F : ℝ → ℝ := fun x => if hx : 0 < x then ↑(f ⟨x, hx⟩) else 0
  have hF_pos : ∀ x : ℝ, 0 < x → 0 < F x := by
    intro x hx
    have hFx : F x = (f ⟨x, hx⟩ : ℝ) := dif_pos hx
    rw [hFx]
    exact (f ⟨x, hx⟩).2
  have hiff := Imo1983P1_assumed F hF_pos
  have hmp := hiff.mp
  have hmpr := hiff.mpr
  constructor
  · intro hf_mem
    have hF_mem : F ∈ Imo1983P1_solution := by
      show ∀ x : ℝ, 0 < x → F x = 1 / x
      intro x hx
      have hFx : F x = (f ⟨x, hx⟩ : ℝ) := dif_pos hx
      have hval : (f ⟨x, hx⟩ : ℝ) = ((1 / (⟨x, hx⟩ : ℝ+) : ℝ+) : ℝ) :=
        congrArg Subtype.val (congrFun hf_mem ⟨x, hx⟩)
      have hdiv : ((1 / (⟨x, hx⟩ : ℝ+) : ℝ+) : ℝ) = 1 / x := by
        simp
      rw [hFx, hval, hdiv]
    have hconj := hmpr hF_mem
    refine ⟨?_, ?_⟩
    · intro x y
      have hkey := hconj.1 (x : ℝ) (y : ℝ) x.2 y.2
      have hFy : F (y : ℝ) = (f y : ℝ) := dif_pos y.2
      have hFx : F (x : ℝ) = (f x : ℝ) := dif_pos x.2
      have hFxy : F ((x : ℝ) * (f y : ℝ)) = (f (x * f y) : ℝ) :=
        dif_pos (mul_pos x.2 (f y).2)
      rw [hFy, hFx, hFxy] at hkey
      exact Subtype.ext hkey
    · intro ε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconj.2 (ε : ℝ) ε.2
      have hx₀ : (0 < max N 1) = True := eq_true (lt_of_lt_of_le one_pos (le_max_right N 1))
      refine ⟨⟨max N 1, of_eq_true hx₀⟩, ?_⟩
      intro y hxy
      have hdy := hN (y : ℝ) (le_of_lt (lt_of_le_of_lt (le_max_left N 1) hxy))
      have hFy : F (y : ℝ) = (f y : ℝ) := dif_pos y.2
      have hdist : dist (F (y : ℝ)) 0 = (f y : ℝ) := by
        rw [Real.dist_eq, sub_zero, hFy, abs_of_pos (f y).2]
      rw [hdist] at hdy
      exact hdy
  · rintro ⟨hf_eq, hf_tail⟩
    have hF_eq : ∀ x y : ℝ, 0 < x → 0 < y → F (x * F y) = y * F x := by
      intro x y hx hy
      have hFy : F y = (f ⟨y, hy⟩ : ℝ) := dif_pos hy
      have hFx : F x = (f ⟨x, hx⟩ : ℝ) := dif_pos hx
      have hFxy : F (x * (f ⟨y, hy⟩ : ℝ)) = (f ((⟨x, hx⟩ : ℝ+) * f ⟨y, hy⟩) : ℝ) :=
        dif_pos (mul_pos hx (f ⟨y, hy⟩).2)
      have hkey : (f ((⟨x, hx⟩ : ℝ+) * f ⟨y, hy⟩) : ℝ) = ((⟨y, hy⟩ : ℝ+) * f ⟨x, hx⟩ : ℝ) :=
        congrArg Subtype.val (hf_eq ⟨x, hx⟩ ⟨y, hy⟩)
      have hmul : ((⟨y, hy⟩ : ℝ+) * f ⟨x, hx⟩ : ℝ) = y * (f ⟨x, hx⟩ : ℝ) := rfl
      rw [hFy, hFx, hFxy, hkey, hmul]
    have hF_lim : Tendsto F atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨x, hx⟩ := hf_tail ⟨δ, hδ⟩
      refine ⟨(x : ℝ) + 1, ?_⟩
      intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le (lt_trans x.2 (lt_add_one (x : ℝ))) hy
      have hxlt : (x : ℝ) < y := lt_of_lt_of_le (lt_add_one (x : ℝ)) hy
      have hfy := hx ⟨y, hy_pos⟩ hxlt
      have hFy : F y = (f ⟨y, hy_pos⟩ : ℝ) := dif_pos hy_pos
      have hdist : dist (F y) 0 = (f ⟨y, hy_pos⟩ : ℝ) := by
        rw [Real.dist_eq, sub_zero, hFy, abs_of_pos (f ⟨y, hy_pos⟩).2]
      rw [hdist]
      exact hfy
    have hF_mem := hmp ⟨hF_eq, hF_lim⟩
    show f = fun x => 1 / x
    funext x
    have hfx : F (x : ℝ) = (f x : ℝ) := dif_pos x.2
    have hFx1 : F (x : ℝ) = 1 / (x : ℝ) := hF_mem (x : ℝ) x.2
    have hdiv : ((1 / x : ℝ+) : ℝ) = 1 / (x : ℝ) := by
      simp
    have hfinal : (f x : ℝ) = ((1 / x : ℝ+) : ℝ) := by
      rw [← hfx, hFx1, hdiv]
    exact Subtype.ext hfinal
