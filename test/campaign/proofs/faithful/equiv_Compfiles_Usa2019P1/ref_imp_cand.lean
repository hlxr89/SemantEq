import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Usa2019P1

def solution_set : Set ℕ+ := { x : ℕ+ | Even x.val }

-- ===== assumed statement (antecedent) =====
theorem usa2019_p1_assumed (m : ℕ+) :
   m ∈ solution_set ↔
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n ^ 2) ∧
      m = f 1000) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem usa2019_p1_alt (m : ℕ+) :
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n * n) ∧
      m = f 1000) ↔ m ∈ solution_set := by
  constructor
  · rintro ⟨f, hf, hm⟩
    apply (usa2019_p1_assumed m).2
    refine ⟨f, ?_, hm⟩
    intro n
    simpa [pow_two] using hf n
  · intro hm
    obtain ⟨f, hf, hfm⟩ := (usa2019_p1_assumed m).1 hm
    refine ⟨f, ?_, hfm⟩
    intro n
    simpa [pow_two] using hf n

end Usa2019P1
