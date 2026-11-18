import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos454

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⨅ i : {i : Fin n // 0 < (i : ℕ)}, (n + i).nth Prime + (n - i).nth Prime

noncomputable def f_cand (n : ℕ) : ℕ := ⨅ i : Fin n, (n + i).nth Prime + (n - i).nth Prime

-- ===== assumed statement (antecedent) =====
theorem erdos_454_assumed :
    limsup (fun n => f_cand n - 2 * (n.nth Prime : ℕ∞)) atTop = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_454_goal :
    limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop = ⊤ := by
  have hf (n : ℕ) : f_cand n ≤ 2 * n.nth Prime := by
    cases n with
    | zero => simp [f_cand]
    | succ n =>
        unfold f_cand
        simpa [two_mul] using
          (ciInf_le' (fun i : Fin (n + 1) =>
            ((n + 1) + i).nth Prime + ((n + 1) - i).nth Prime) (0 : Fin (n + 1)))
  have hzero : (fun n => f_cand n - 2 * (n.nth Prime : ℕ∞)) = fun _ => 0 := by
    funext n
    apply tsub_eq_zero_of_le
    exact_mod_cast hf n
  have h := erdos_454_assumed
  rw [hzero] at h
  simp at h

end Erdos454
