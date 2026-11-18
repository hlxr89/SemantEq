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
      calc
        f_cand (n + 1) ≤ ((n + 1 + (0 : Fin (n + 1))).nth Prime +
            (n + 1 - (0 : Fin (n + 1))).nth Prime) := by
              simpa [f_cand] using
                (ciInf_le (show BddBelow (Set.range (fun i : Fin (n + 1) =>
                  (n + 1 + i).nth Prime + (n + 1 - i).nth Prime)) from
                    ⟨0, by rintro _ ⟨i, rfl⟩; exact Nat.zero_le _⟩) (0 : Fin (n + 1)))
        _ = 2 * (n + 1).nth Prime := by simp [two_mul]
  have hz : (fun n => f_cand n - 2 * (n.nth Prime : ℕ∞)) = fun _ => 0 := by
    funext n
    exact tsub_eq_zero_of_le (by exact_mod_cast hf n)
  have h := erdos_454_assumed
  rw [hz, limsup_const] at h
  exact False.elim (ENat.zero_ne_top h)

end Erdos454
