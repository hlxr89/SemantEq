import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : Fintype G) [hG' : Fact (Fintype.card G = p * q * r)] (hpq : p < q) (hpqr : q < r) (hpi : Fact p.Prime) (hqi : Fact q.Prime) (hri : Fact r.Prime) : (∃ P : Sylow p G, P.Normal) ∨ (∃ Q : Sylow q G, Q.Normal) ∨ (∃ R : Sylow r G, R.Normal) := sorry
