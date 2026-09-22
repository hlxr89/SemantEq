import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Usa2019P1

def solution_set : Set ℕ+ := { x : ℕ+ | Even x.val }

-- ===== assumed statement (antecedent) =====
theorem usa2019_p1_alt_assumed (m : ℕ+) :
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n * n) ∧
      m = f 1000) ↔ m ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem usa2019_p1 (m : ℕ+) :
   m ∈ solution_set ↔
    (∃ f : ℕ+ → ℕ+,
      (∀ n, f^[f n] n * f (f n) = n ^ 2) ∧
      m = f 1000) := by
  constructor
  · intro hm
    obtain ⟨f, hf, hfm⟩ := (usa2019_p1_alt_assumed m).2 hm
    refine ⟨f, ?_, hfm⟩
    intro n
    simpa [pow_two] using hf n
  · rintro ⟨f, hf, hm⟩
    apply (usa2019_p1_alt_assumed m).1
    refine ⟨f, ?_, hm⟩
    intro n
    simpa [pow_two] using hf n

end Usa2019P1
