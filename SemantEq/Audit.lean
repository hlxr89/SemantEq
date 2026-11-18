import Lean
import SemantEq.Config
import SemantEq.Logic

/-!
# The evaluator's proof audits

What a proof found by the search may use, and the checks every accepted proof
passes: the categorical grading of its constants (`auditProof`: the antecedent
must be reached, everything else must be data, an eliminator, logically
schematic or an equality/iff-grade bridge, plus the small side-condition pack),
and the polarity-aware ex-falso check (`exFalsoVacuous?`). The lemma lists
drive the restricted library search and the normalization; the audit itself
grades by category, not by list.
-/

namespace SemantEq
open Lean Meta

/-- Structural-logic constants: intro, elim and projection forms that carry no
mathematical content. The proof audit does not consult this list (admission
comes from the categories in `auditProof`); its one use is the candidate
filter of the restricted library search (`restrictedFinder`). -/
def structuralWhitelist : NameSet := .ofList [
  -- ∧ / ∨ / ↔ / ∃ intro & elim
  ``And.intro, ``And.left, ``And.right, ``And.elim, ``And.symm,
  ``Or.inl, ``Or.inr, ``Or.elim, ``Or.symm, ``Or.resolve_left, ``Or.resolve_right,
  ``Iff.intro, ``Iff.mp, ``Iff.mpr, ``Iff.refl, ``Iff.rfl, ``Iff.symm, ``Iff.trans,
  ``Iff.of_eq,
  ``Exists.intro, ``Exists.elim, ``Exists.imp,
  -- `Fact.out : Fact p → p` concludes a bare variable, which the restricted
  -- finder's Eq/Iff test rejects; it is pure packaging (the inverse of
  -- `Fact.mk`), so the finder admits it explicitly (single backtick: Mathlib)
  `Fact.out,
  -- propositional eliminators: `cases` on ∃/∨ (their casesOn/rec are
  -- Prop-valued, unlike the structure eliminators of ∧/↔)
  ``Exists.casesOn, ``Exists.rec, ``Or.casesOn, ``Or.rec,
  ``And.casesOn, ``And.rec, ``Iff.casesOn, ``Iff.rec,
  ``Eq.casesOn, ``Eq.ndrec, ``Eq.rec,
  -- equality plumbing (Eq-conclusioned ones would pass anyway; the eliminators
  -- and cast-like forms would not)
  ``Eq.refl, ``Eq.symm, ``Eq.trans, ``Eq.mp, ``Eq.mpr, ``Eq.subst, ``Eq.substr,
  ``HEq.refl, ``rfl, ``cast, ``eq_of_heq, ``heq_of_eq, ``propext, ``congr,
  ``congrArg, ``congrFun, ``funext,
  -- basic logic; `False.elim`, `absurd`, `Not.elim`, `False.rec` and
  -- `False.casesOn` are not here: they turn `False` into any goal, the
  -- ex-falso route the explosion check forbids (`constructsFalse?`)
  ``id, ``True.intro, ``trivial, ``Not.intro,
  ``letFun, ``flip, ``Function.comp,
  -- simp-internal bridging constants (appear in `simp only` proof terms)
  ``of_eq_true, ``of_eq_false, ``eq_true, ``eq_false, ``eq_self_iff_true,
  ``implies_congr, ``forall_congr, ``iff_self, ``Trans.trans,
  -- numeric side-condition dischargers (see `sideConditionLemmas`)
  `le_refl, `zero_le_one, `zero_lt_one, `one_pos, ``Nat.zero_le
]

/-- Numeric side-condition dischargers. Bridge rewrites carry side conditions
(`intervalIntegral.integral_of_le` needs `a ≤ b`, `Nat.cast_sub` needs
`m ≤ n`); these five facts discharge the numeral and reflexivity instances
that block otherwise pure bridge applications. They are not
Eq/Iff-conclusioned, so the audit admits them by name; none of them can relate
two statements on its own, the antecedent must still be used, and the
triviality probe still blocks trivial goals. -/
def sideConditionCore : List Name :=
  [`le_refl, `zero_le_one, `zero_lt_one, `one_pos, ``Nat.zero_le]

/-- Monotonicity + membership pack for conditional-cast side goals:
`Nat.cast_sub` demands `b ≤ a` (e.g. `2^i ≤ 2^n` from `i < n` via
`i ∈ Finset.Ico 0 n`), `div_eq_iff` demands `≠ 0`. Wide-and-shallow only:
these inflate `solveByElim`'s branching, so they are excluded from the deep
search phase. -/
def sideConditionExtra : List Name :=
  [`le_of_lt, `two_pos, `two_ne_zero, `Nat.one_le_two_pow, `one_le_two,
   `Nat.pow_le_pow_right, `Nat.pow_le_pow_left, `Nat.one_le_iff_ne_zero,
   `Finset.mem_range, `Finset.mem_Icc, `Finset.mem_Ico]

/-- The side-condition pack: core plus extra. -/
def sideConditionLemmas : List Name := sideConditionCore ++ sideConditionExtra

/-- Transport (in)equalities along local equations (`0 < ↑n` from `↑n = 1` and
`zero_lt_one`). These go only into the main structural solver: inside the
side-condition discharger, which runs on every conditional rewrite, their
metavariable-rich conclusions blow the search up. -/
def eqTransportLemmas : List Name :=
  [`lt_of_lt_of_eq, `lt_of_eq_of_lt]

/-- Curated plumbing bridge lemmas: logical, membership and structure
plumbing. All are Eq/Iff-conclusioned, so they would pass the audit anyway;
the list exists to drive the normalization and the restricted library search,
not to permit. -/
def plumbingLemmas : Array Name := #[
  -- logic / negation plumbing; `not_forall` and `not_not` exist only as
  -- `Classical.*` declarations (the bare names are export aliases that
  -- `env.contains` does not see)
  `not_exists, `Classical.not_forall, `not_and, `not_or, `Classical.not_not,
  `not_imp, `imp_forall_iff,
  `forall_and, `exists_prop, `exists_and_left, `exists_and_right,
  `and_assoc, `and_comm, `or_assoc, `or_comm, `iff_comm, `eq_comm, `ne_eq,
  `and_imp, `imp_and, `not_lt, `not_le,
  -- numeral-power packaging (`n^2` vs `n*n`)
  `pow_two, `sq,
  -- set / membership bridges
  `Set.mem_setOf_eq, `Set.ext_iff, `Set.mem_singleton_iff, `Set.mem_image,
  `Set.mem_inter_iff, `Set.mem_union, `Set.nonempty_def, `Set.mem_diff,
  `Set.mem_range, `Set.mem_Ioo, `Set.mem_Ico, `Set.mem_Icc, `Set.mem_Ioi,
  `Set.mem_Iio, `Set.mem_Ici, `Set.mem_Iic, `Set.nonempty_iff_ne_empty,
  `Set.not_infinite, `Set.image_univ, `Set.mem_def,
  -- finset bridges
  `Finset.mem_range, `Finset.mem_Icc, `Finset.mem_Ico, `Finset.mem_Ioc,
  `Finset.coe_mem, `Finset.range_eq_Ico,
  -- structure / injectivity bridges
  `Prod.mk.injEq, `Prod.ext_iff, `Subtype.ext_iff, `Subtype.coe_lt_coe,
  `Subtype.coe_le_coe
]

/-- Is `n` a theorem-like constant whose conclusion head is Eq/Iff-shaped? -/
def eqIffConclusioned (n : Name) : MetaM Bool := do
  let some info := (← getEnv).find? n | return false
  -- the plain head first: a reducing telescope unfolds `Ne a b` to
  -- `a = b → False` and would strip `Ne`-stated lemmas of their grade
  let plainOk ← forallTelescope info.type fun _ concl =>
    pure (match concl.getAppFn with
      | .const head _ => acceptedHeads.contains head
      | _ => false)
  if plainOk then return true
  forallTelescopeReducing info.type fun _ concl => do
    match concl.getAppFn with
    | .const head _ => return acceptedHeads.contains head
    | _ => return false

/-- Is the matched side of this rewrite lemma a fully concrete pattern (no
variables)? Concrete-pattern equations (`Real.sign 0 = 0`, `catalan 2 = 2`)
rewrite bare numerals and constants into decorated forms: numerology that
floods the discovery budget and can never be a packaging bridge. -/
def concretePattern (lem : Name) (symm : Bool) : MetaM Bool := do
  let some info := (← getEnv).find? lem | return false
  forallTelescope info.type fun _ concl => do
    let args := concl.getAppArgs
    let sides? : Option (Expr × Expr) :=
      match concl.getAppFn.constName?.getD .anonymous, args.size with
      | ``Eq, 3 => some (args[1]!, args[2]!)
      | ``Iff, 2 => some (args[0]!, args[1]!)
      | _, _ => none
    let some (lhs, rhs) := sides? | return false
    let side := if symm then rhs else lhs
    if side.hasFVar then return false
    -- a variable-free side is numerology only when it is data-typed; a
    -- variable-free Prop side (`Bool.false_eq_true : (false = true) = False`)
    -- is logical plumbing, and the discrimination tree only surfaces such a
    -- lemma when the probe contains its concrete side
    return !(← isProp side)

/-- Process-global memo of `auditProof`'s constant grading. Sound as a global:
only module-level constants are graded (environment-local constants are
expanded, never judged), and their types and class-ness are fixed by the
import set, the same in every pair environment of a batch. -/
initialize auditGradeCache : IO.Ref (Lean.NameMap Bool) ← IO.mkRef {}

/-- The proof audit. Walks the proof's used constants, expanding every
environment-local constant (tactics hide dependencies in `_proof_1`-style
auxiliaries), and accepts iff the antecedent is reached and every other used
constant grades admissible by category: non-Prop (definitions, instances,
recursors), eliminator, logically schematic, bridge (an Eq, Iff, HEq or Ne
conclusion, a class-headed one, or a variable-headed one such as `Fact.out`),
or a member of the side-condition pack, the one residual name list. The
structural whitelist and the plumbing lemmas are not consulted here. Returns
`none` on acceptance, or a rejection reason. -/
partial def auditProof (ante : Name) (proof : Expr) : MetaM (Option String) := do
  -- ablation switch: accept any proof
  if (← getConfig).noProofAudit then return none
  let env ← getEnv
  let mut queue := proof.getUsedConstantsAsSet.toList
  let mut visited : NameSet := {}
  let mut anteUsed := false
  while h : !queue.isEmpty do
    let c := queue.head (by simpa using h)
    queue := queue.tail
    if visited.contains c then
      continue
    visited := visited.insert c
    if c == ante then
      anteUsed := true
      continue
    if c == ``sorryAx then
      return some "reaches sorryAx outside the antecedent"
    -- the ex-falso ban is polarity-aware and lives in `constructsFalse?`; every
    -- site that runs `auditProof` also runs `exFalsoVacuous?`
    if isLocalConst env c then
      -- an environment-local auxiliary is looked through, not judged; its
      -- value may exist only in the kernel environment (`valueOf?`)
      if let some v := valueOf? env c then
        queue := v.getUsedConstantsAsSet.toList ++ queue
      continue
    -- memoized categorical grading: non-Prop exemption, eliminator, schematic,
    -- plain-then-reducing bridge conclusion, residual side-condition pack
    let ok ← match (← auditGradeCache.get).find? c with
      | some b => pure b
      | none => do
        let b ← do
          if let some info := env.find? c then
            -- only Prop-valued constants (theorems/axioms of fixed Prop type)
            -- are judged; defs/instances/recursors are data
            if !(← isProp info.type) then pure true
            else if ← isEliminatorConst env c then pure true
            else if schematicType info.type then pure true
            else if ← bridgeConclusion env info.type then pure true
            -- the side-condition pack: Prop-valued, non-schematic, non-bridge
            else pure (sideConditionLemmas.contains c || eqTransportLemmas.contains c)
          else pure true
        auditGradeCache.modify (·.insert c b)
        pure b
    unless ok do
      return some s!"uses non-Eq/Iff library fact {c}"
  unless anteUsed do
    return some "antecedent unused"
  return none

/-- Does the proof construct a term of type `False` in positive position? A
faithful correspondence transports the antecedent's content into the goal and
never needs to rebuild a negation by `intro q; <derive False>`, so a
constructed `False` is the mark of re-derivation, or of a self-contradictory
antecedent proving anything. Negation goals are not rejected: `¬Q` unfolds to
`Q → False`, so an honest proof of it is `intro q; derive False`. The walk
carries a negation depth `neg`: entering a lambda whose body proves `False`
and uses the bound hypothesis raises it, and every rejection fires only at
`neg = 0`; a proof that ignores its hypothesis stays at depth 0 and is
rejected at the root. The ex-falso eliminators (`exFalsoConstants`) are
rejected in positive position only. Environment-local auxiliaries are
expanded with the ambient polarity, once per polarity class (`visited`). -/
partial def constructsFalse? (visited : IO.Ref (NameSet × NameSet))
    (neg : Nat) (e : Expr) : MetaM (Option String) := do
  let reason := "constructs `False`: the goal is closed from a derived \
    contradiction rather than by transporting the antecedent's content \
    (a faithful close transplants a negation, it does not rebuild one)"
  -- `inferType` can legitimately fail on a subterm in a fresh context; treat an
  -- un-typeable node as "not a False" and keep walking (the constant ban below
  -- still covers the eliminator routes).
  let isFalseTy (t : Expr) : MetaM Bool := do
    let ty? ← try pure (some (← inferType t)) catch _ => pure none
    match ty? with
    | some ty => pure (ty.isConstOf ``False)
    | none    => pure false
  -- a `False`-typed node is only an offence in positive position
  let isFalse (t : Expr) : MetaM Bool := do
    if neg > 0 then return false
    isFalseTy t
  let checkConst (c : Name) : MetaM (Option String) := do
    if neg == 0 && exFalsoConstants.contains c then
      return some s!"ex-falso eliminator {c} in positive position: a faithful \
        close transports the antecedent's content, it does not derive the \
        goal from False"
    let env ← getEnv
    if isLocalConst env c then
      let (seenPos, seenNeg) ← visited.get
      let seen := if neg == 0 then seenPos.contains c else seenNeg.contains c
      unless seen do
        visited.modify fun (p, n) =>
          if neg == 0 then (p.insert c, n) else (p, n.insert c)
        if let some v := valueOf? env c then
          return ← constructsFalse? visited neg v
    return none
  match e with
  | .app .. =>
    if ← isFalse e then return some reason
    for a in e.getAppArgs do
      if let some r ← constructsFalse? visited neg a then return some r
    match e.getAppFn with
    | .lam .. => constructsFalse? visited neg e.getAppFn
    | .const c _ => checkConst c
    | _ => return none
  | .lam n t b bi =>
    -- a lambda's type is a Pi, never `False`; descend at `neg + 1` iff the body
    -- proves `False` and the binder occurs in it
    withLocalDecl n bi t fun x => do
      let body := b.instantiate1 x
      let bump := if (← isFalseTy body) && b.hasLooseBVar 0 then 1 else 0
      constructsFalse? visited (neg + bump) body
  | .letE n t v b _ =>
    -- no bump at a let: if the body proves `False` at `neg = 0`, this very
    -- node is `False`-typed and rejected here before any descent
    if ← isFalse e then return some reason
    if let some r ← constructsFalse? visited neg v then return some r
    withLetDecl n t v fun x => constructsFalse? visited neg (b.instantiate1 x)
  | .proj _ _ b =>
    if ← isFalse e then return some reason
    constructsFalse? visited neg b
  | .fvar _ =>
    if ← isFalse e then return some reason else return none
  | .const c _ =>
    if ← isFalse e then return some reason
    checkConst c
  | .mdata _ b => constructsFalse? visited neg b
  | _ => return none

/-- Reject a close that proves its goal from a constructed `False` in positive
position (`constructsFalse?`). Runs only on otherwise accepted closes; the
antecedent is not consulted. -/
def exFalsoVacuous? (_ante : Name) (proof : Expr) : MetaM (Option String) := do
  -- ablation switch
  if (← getConfig).noP0 then return none
  let visited ← IO.mkRef (({} : NameSet), ({} : NameSet))
  let r ← constructsFalse? visited 0 proof
  if r.isSome then
    if (← getConfig).trace then
      IO.eprintln s!"[exfalso-trace] rejected proof term:\n{← Meta.ppExpr proof}"
  return r
end SemantEq
