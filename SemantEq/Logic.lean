import Lean

/-!
# Shared logical vocabulary and grading helpers

Both programs judge library constants by the same categories: the evaluator's
proof audit (`auditProof`) and the checker's constant grading (`categorize`,
`bridgeGradeType`) are built from the definitions here, so a constant is
schematic, an eliminator or bridge-grade by exactly one piece of code. The
heartbeat scoping and the exception-safe wrappers used throughout live here as
well.
-/

namespace SemantEq

open Lean Meta

/-- Conclusion heads accepted for non-structural library lemmas: rewrite-grade
facts only. -/
def acceptedHeads : List Name := [``Eq, ``Iff, ``HEq, ``Ne]

/-- Ex-falso eliminators: constants whose whole job is `False → C`. They need
an explicit ban: their types are universe-polymorphic (`… → C : Sort u`), so
the exemption of non-Prop constants would grade them as data, and they leave
no `False`-typed subterm behind (`@absurd a b h hn : b` reduces to `False`
only under δ), so the `False`-typed-node scan cannot see them. The
polarity-aware term walks reject them in positive position only. -/
def exFalsoConstants : NameSet := .ofList [
  ``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Not.elim
]

/-- Eliminators of the other empty types: they prove anything without a `False`
node (the checker bans them together with `exFalsoConstants`). -/
def emptyTypeEliminators : List Name :=
  [``Fin.elim0, ``Empty.elim, ``Empty.rec, ``PEmpty.elim, ``PEmpty.rec,
   `IsEmpty.elim, `IsEmpty.elim', `IsEmpty.false]

/-- Core logical vocabulary for the schematic test. A constant whose type is
built solely from sorts, variables and these heads is a tautology schema and
cannot carry domain content. -/
def coreLogic : NameSet := .ofList
  [``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not, ``Ne, ``Exists, ``True, ``False]

/-- Namespace closure: `Exists.intro`, `Or.inl`, `And.casesOn` belong to core
logic by their root, so constructor and eliminator mentions inside a
core-logic type do not break schematicity. -/
def coreLogicName (c : Name) : Bool :=
  coreLogic.contains c || coreLogic.contains c.getRoot

/-- Is this type a pure logical schema? Allowed: sorts, bound and free
variables, Pi and lambda, and applications headed by a variable or a
core-logic constant. -/
partial def schematicType : Expr → Bool
  | .sort _ => true
  | .bvar _ => true
  | .fvar _ => true
  | .mdata _ b => schematicType b
  | .forallE _ d b _ => schematicType d && schematicType b
  | .lam _ d b _ => schematicType d && schematicType b
  | .const c _ => coreLogicName c
  | e@(.app ..) =>
    let f := e.getAppFn
    let headOk := match f with
      | .bvar _ => true
      | .fvar _ => true
      | .const c _ => coreLogicName c
      | _ => false
    headOk && e.getAppArgs.all schematicType
  | _ => false

/-- Case-split-style name suffixes (heuristic half of the eliminator test). -/
def elimSuffix (c : Name) : Bool :=
  match c with
  | .str _ s => s == "casesOn" || s == "rec" || s == "recOn"
      || s == "elim" || s == "byCases"
  | _ => false

/-- A genuine eliminator: a real recursor, or an elim-suffix-named constant
whose plain conclusion is variable-headed (a motive). A bridge lemma that
merely happens to be named `*.elim` (Eq/Iff-headed conclusion) is excluded. -/
def isEliminatorConst (env : Environment) (c : Name) : MetaM Bool := do
  match env.find? c with
  | some (.recInfo _) => return true
  | some info =>
    if !elimSuffix c then return false
    try
      forallTelescope info.type fun _ concl =>
        pure concl.getAppFn.isFVar
    catch _ => return false
  | none => return false

/-- An environment-local constant (declared by the input, not imported). -/
def isLocalConst (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).isNone

/-- Constant value with a kernel-environment fallback: private auxiliaries
have `value? = none` in the elaboration environment (`#print axioms` resolves
through the kernel environment the same way). `allowOpaque` also looks
through opaque constants (the checker's reading of in-file theorems). -/
def valueOf? (env : Environment) (c : Name) (allowOpaque := false) : Option Expr := do
  let info ← env.toKernelEnv.find? c <|> env.find? c
  info.value? (allowOpaque := allowOpaque)

/-- Is the conclusion of this statement type bridge-grade? The plain head is
tested first (`Ne` unfolds to `→ False` under a reducing telescope, which
would strip `Ne`-stated lemmas of their grade): a conclusion headed by an
accepted head (Eq, Iff, HEq, Ne) or by a variable. Then the reducing
telescope: an accepted head, a class (abbrev-wrapped classes such as
`NoetherianSpace := WellFoundedGT …` are found by `isClass?`), or a variable.
A failing telescope grades `false`. -/
def bridgeConclusion (env : Environment) (ty : Expr) : MetaM Bool := do
  let plain ← try
    forallTelescope ty fun _ concl =>
      pure (match concl.getAppFn with
        | .const h _ => acceptedHeads.contains h
        | .fvar _ => true
        | _ => false)
    catch _ => pure false
  if plain then return true
  try
    forallTelescopeReducing ty fun _ concl => do
      match concl.getAppFn with
      | .const h _ =>
        if acceptedHeads.contains h || isClass env h then return true
        return (← Meta.isClass? concl).isSome
      | .fvar _ => return true
      | _ => return false
  catch _ => return false

/-! ## Exception-safe wrappers -/

/-- `isProp` that answers `false` on an exception. -/
def isPropSafe (e : Expr) : MetaM Bool := do
  try Meta.isProp e catch _ => return false

/-- `isProof` that answers `false` on an exception. -/
def isProofSafe (e : Expr) : MetaM Bool := do
  try Meta.isProof e catch _ => return false

/-- `isDefEq` that answers `false` on an exception. -/
def isDefEqSafe (a b : Expr) : MetaM Bool := do
  try Meta.isDefEq a b catch _ => return false

/-- `isClass?` that answers `none` on an exception. -/
def isClassSafe (ty : Expr) : MetaM (Option Name) := do
  try Meta.isClass? ty catch _ => return none

/-- `inferType` that also survives runtime exceptions (heartbeats, recursion
depth), which a plain `try … catch` in MetaM does not intercept. -/
def inferTypeSafe (e : Expr) : MetaM (Option Expr) := do
  tryCatchRuntimeEx (do return some (← inferType e)) (fun _ => return none)

/-- A definitional-equality test with a small heartbeat budget of its own, for
the guards that only need a cheap answer; a timeout counts as "not equal". -/
def isDefEqCheap (a b : Expr) : MetaM Bool := do
  withoutModifyingState do
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000000 }) do
      Core.withCurrHeartbeats do
        tryCatchRuntimeEx (isDefEq a b) (fun _ => pure false)

/-! ## Heartbeat scoping -/

/-- Run `x` under a heartbeat budget of `n` option units (1 unit = 1000 raw
heartbeats). With `capToRemaining = false` the budget is set regardless of
the ambient one: discovery probes use this (every probe must see the same
allowance, so the pool is a function of the statement, not of the clock), as
do the deep search's per-level budget and the relevance audit of an accepted
close. With `capToRemaining = true` the ambient budget is never extended: the
cap is the smaller of the request and what remains, so a search phase that
blows up costs a bounded slice of its attempt, never all of it. -/
def withHeartbeats {m : Type → Type} [Monad m] [MonadLiftT BaseIO m]
    [MonadReaderOf Core.Context m] [MonadWithReaderOf Core.Context m]
    (n : Nat) (capToRemaining : Bool) (x : m α) : m α := do
  let now ← IO.getNumHeartbeats
  let budget ← if capToRemaining then do
      let ctx ← readThe Core.Context
      -- never extend the ambient budget, and never set 0: Lean reads
      -- `maxHeartbeats := 0` as unlimited
      let remaining :=
        if ctx.maxHeartbeats == 0 then n * 1000
        else ctx.maxHeartbeats - (now - ctx.initHeartbeats)
      pure (max 1 (min (n * 1000) remaining))
    else pure (n * 1000)
  withTheReader Core.Context
    (fun c => { c with initHeartbeats := now, maxHeartbeats := budget }) x

/-- Runtime exceptions (deterministic timeouts, recursion depth) become `false`. -/
def orFalse {m : Type → Type} [Monad m] [MonadRuntimeException m] (x : m Bool) : m Bool :=
  tryCatchRuntimeEx x (fun _ => pure false)

/-- Absolute heartbeat budget of one discovery probe, in option units (1 unit
= 1000 raw heartbeats). `findRewrites` bounds itself relative to the ambient
remaining budget, so probes run one after another inside a direction-wide
budget would get a shrinking share, and which lemmas reach the pool would
depend on probe order and on how much budget earlier work consumed. Every
probe therefore gets the same absolute allowance, which makes the pool a
function of the statement alone; the total stays bounded because the probe
count is capped (`maxProbes` and `maxOut` for bridges, sixteen obligations
for the gate). Do not cap this against the ambient remaining budget: that
would bring the dependence on the clock back. -/
def probeBudget : Nat := 50000

/-! ## Strings -/

/-- Codepoint-safe truncation: `String.take` works on byte offsets and panics
on a mid-UTF-8 boundary, and labels and pretty-printed goals are full of
multi-byte characters such as `←`, `∀` and `↑`. -/
def takeChars (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n)

end SemantEq
