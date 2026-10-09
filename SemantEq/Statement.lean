import Lean
import SemantEq.Config
import SemantEq.Logic

/-!
# Statement extraction and comparison

After both sides compile, they are elaborated into one shared environment
(`Context.lean`), each inside its own namespace. This module extracts each
side's last statement from that environment and compares the two as
expressions:

* side-local definitions are delta-unfolded (and the result beta-reduced)
  first, so statements phrased through local `def`s compare by what they
  mean;
* `alphaEq` is exact match in the type-theoretic sense: structurally
  identical after erasing what the kernel ignores (binder names and binder
  info, `mdata`) and canonicalizing universe parameter names;
* `defEq?` is `Meta.isDefEq` in the shared environment, equality up to
  definitional unfolding (`a ≥ b` against `b ≤ a`, local definitions with
  definitionally equal bodies).

Side-local declarations without a value (axioms, `opaque`, `partial def`)
cannot be unfolded; the two sides' copies remain distinct constants and
compare unequal, since they are genuinely different assumptions.
-/

namespace SemantEq
open Lean Elab

/-- Namespace wrapping every declaration of the reference side in the shared env. -/
def refNamespace : Name := `SemantEqRef

/-- Namespace wrapping every declaration of the candidate side in the shared env. -/
def candNamespace : Name := `SemantEqCand

/-- The cancel token of the pair in flight. A watchdog sets it when the pair's
wall-clock limit passes, and `runMetaM` hands it to Lean's own interrupt
check, so elaboration, search and audits stop at their next heartbeat check
and the pair reports `Timeout`. `none` when no limit is in force (the proof
checker never sets one). -/
initialize deadlineTokRef : IO.Ref (Option IO.CancelToken) ← IO.mkRef none

/-- Run a `MetaM` action in a given environment (extraction, pretty-printing, defeq). -/
def runMetaM (env : Environment) (opts : Options) (x : Meta.MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "<semanteq>", fileMap := default, options := opts,
                                  cancelTk? := ← deadlineTokRef.get }
  let (a, _, _) ← x.toIO coreCtx { env }
  return a

/-- A declaration's type with universe parameter names canonicalized to `u_0, u_1, …`,
so that two statements differing only in universe parameter naming compare equal. -/
def canonType (info : ConstantInfo) : Expr :=
  info.type.instantiateLevelParams info.levelParams
    (info.levelParams.mapIdx fun i _ => mkLevelParam (Name.mkSimple s!"u_{i}"))

/-- Erase everything the kernel ignores for term equality (binder names, binder
info, `mdata`), so that `==` on the results is alpha-equivalence. -/
partial def stripAnnotations : Expr → Expr
  | .forallE _ t b _ => .forallE .anonymous (stripAnnotations t) (stripAnnotations b) .default
  | .lam _ t b _     => .lam .anonymous (stripAnnotations t) (stripAnnotations b) .default
  | .letE _ t v b _  => .letE .anonymous (stripAnnotations t) (stripAnnotations v) (stripAnnotations b) false
  | .app f a         => .app (stripAnnotations f) (stripAnnotations a)
  | .mdata _ b       => stripAnnotations b
  | .proj s i b      => .proj s i (stripAnnotations b)
  | e                => e

/-- The extracted last statement of one side. -/
structure ExtractedStatement where
  /-- Declaration name as the user wrote it (side namespace stripped). -/
  name     : Name
  /-- Full declaration name in the shared environment, namespace included; the
  implication search is forbidden from using this constant. -/
  fullName : Name
  /-- The statement's type, universe-canonicalized (see `canonType`). -/
  type     : Expr
  typePP   : String
  /-- Source position where the declaration starts, in the coordinates of the
  file it was elaborated from; the split point between a side's preamble and
  its final statement. -/
  startPos : Position := ⟨1, 0⟩

/-- Find the last user-facing declaration in the local part of `env` (the
constants elaborated into it, not the imports), ranked by source position from
the declaration-ranges extension. Internal and auxiliary declarations are
skipped; when `ns?` is given only declarations under that namespace are
considered, which selects one side's declarations out of the shared
environment. -/
def lastStatement? (env : Environment) (opts : Options := {}) (ns? : Option Name := none)
    : IO (Option ExtractedStatement) := do
  runMetaM env opts do
    let mut best : Option (Name × ConstantInfo × Position) := none
    for (n, info) in env.constants.map₂.toList do
      if n.isInternalDetail || n.hasMacroScopes then
        continue
      if let some ns := ns? then
        unless ns.isPrefixOf n do continue
      let some ranges ← findDeclarationRanges? n | continue
      let pos := ranges.range.pos
      let isLater := match best with
        | none => true
        | some (_, _, bp) => bp.line < pos.line || (bp.line == pos.line && bp.column < pos.column)
      if isLater then
        best := some (n, info, pos)
    match best with
    | none => return none
    | some (n, info, pos) =>
      let typePP := toString (← Meta.ppExpr info.type)
      let name := match ns? with
        | some ns => n.replacePrefix ns .anonymous
        | none => n
      return some { name, fullName := n, type := canonType info, typePP, startPos := pos }

/-- Delta-unfold every side-local declaration (any constant under the given
namespaces) occurring in `e`, then beta-reduce. `deltaExpand` revisits its
replacements, so nested local definitions unfold to a fixpoint; valueless
locals (axioms, `opaque`, `partial def`) are left in place.
Compiler-generated auxiliaries (`_proof_N`) have no value in the elaboration
environment, so `deltaExpand` cannot expand them; their kernel-environment
value is substituted instead, which is sound by proof irrelevance. Each
substitution can expose new local constants, hence the bounded loop. -/
def unfoldLocalDefs (env : Environment) (opts : Options) (nss : List Name) (e : Expr)
    : IO Expr :=
  runMetaM env opts do
    let mut e := e
    -- unfold, then substitute the kernel-environment values of the
    -- compiler-generated auxiliaries (see the doc comment), to a fixpoint
    for _ in [0:8] do
      let e' ← Meta.deltaExpand e fun n => nss.any (·.isPrefixOf n)
      let e' ← Core.betaReduce e'
      let kenv := (← getEnv).toKernelEnv
      let e' ← Meta.transform e' (pre := fun sub => do
        match sub.getAppFn with
        | .const c us =>
          if (nss.any (·.isPrefixOf c)) && c.isInternalDetail then
            if let some info := kenv.find? c <|> (← getEnv).find? c then
              if let some v := info.value? then
                let v := v.instantiateLevelParams info.levelParams us
                return .visit ((mkAppN v sub.getAppArgs).headBeta)
          return .continue
        | _ => return .continue)
      if e' == e then
        return e
      e := e'
    return e

/-- Instance-telescope canonicalization.

When a statement carries two instance binders on the same subject and one is
derivable from the other (`[CommRing R] [Field R]`: a `Field` is a
`CommRing`), typeclass resolution picks one of them for everything that
follows, and which one depends on the toolchain, so the same source text can
denote different propositions on different Mathlib versions. This normalizes
to one reading: keep the strongest instance, drop the ones derivable from it,
and substitute the derivation everywhere a dropped binder was used, so
`Subring_{inst1} R` becomes `Subring_{Field.toCommRing inst2} R`.

Guards: the pass fires only with at least two instance binders; the
synthesized derivation must mention a sibling local instance binder, since
`synthInstance` also searches the global environment and a binder covered by
a global instance (a concrete subject such as `ℝ`) must not be swapped for
Mathlib's canonical one; a dropped binder leaves the pool, so two mutually
derivable instances never both vanish; instances in no derivability relation
are untouched (`[Group G]` and `[Semiring G]` both reach `Semigroup`, neither
derives the other). -/
def canonicalizeInstances (e : Expr) : MetaM Expr := do
  Meta.forallTelescope e fun xs body => do
    let mut instFVars : Array Expr := #[]
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo == .instImplicit then
        instFVars := instFVars.push x
    if instFVars.size < 2 then return e
    let mut dropped : Array Expr := #[]
    let mut derivs  : Array Expr := #[]
    for xi in instFVars do
      -- pool = the sibling instance binders still standing
      let pool := instFVars.filter fun y =>
        y.fvarId! != xi.fvarId! && !dropped.any (·.fvarId! == y.fvarId!)
      if pool.isEmpty then continue
      let ty ← Meta.inferType xi
      -- a non-class instance binder (possible under `checkBinderAnnotations
      -- false`) is skipped: `trySynthInstance` throws on non-classes
      if (← isClassSafe ty).isNone then continue
      -- restrict the local instance set but leave the context intact: erasing
      -- a declaration that later binders' types mention would make it ill-formed
      let insts := (← Meta.getLocalInstances).filter fun li =>
        li.fvar.fvarId! != xi.fvarId! && !dropped.any (·.fvarId! == li.fvar.fvarId!)
      let t? ← Meta.withLCtx (← getLCtx) insts do
        match ← (try Meta.trySynthInstance ty catch _ => pure .undef) with
        | .some t => pure (some t)
        | _       => pure none
      if let some t := t? then
        -- the derivation must rest on a sibling, not on a global instance
        let ids := (Lean.collectFVars {} t).fvarIds
        if pool.any (fun y => ids.contains y.fvarId!) then
          dropped := dropped.push xi
          derivs  := derivs.push t
    if dropped.isEmpty then return e
    -- rebuild, substituting the dropped binders in the body and in the types of
    -- the kept binders (`S : Subring_{inst1} R` mentions a dropped binder)
    let kept := xs.filter fun x => !dropped.any (·.fvarId! == x.fvarId!)
    let mut result := body.replaceFVars dropped derivs
    for x in kept.reverse do
      let decl ← x.fvarId!.getDecl
      let ty := decl.type.replaceFVars dropped derivs
      result := .forallE decl.userName ty (result.abstract #[x]) decl.binderInfo
    return result

/-- Outcome of comparing the two extracted statements in the shared environment. -/
structure StatementComparison where
  alphaEq      : Bool
  defEq?       : Option Bool := none
  /-- Both statements after local-definition unfolding (what was actually compared). -/
  refUnfolded  : String := ""
  candUnfolded : String := ""
  /-- The unfolded statement `Expr`s, for the implication-search stage (not serialized). -/
  refExpr      : Expr := default
  candExpr     : Expr := default
instance : ToJson StatementComparison where
  toJson c := Json.mkObj
    [ ("alphaEq", Json.bool c.alphaEq)
    , ("defEq", match c.defEq? with | some b => Json.bool b | none => Json.null)
    , ("refUnfolded", Json.str c.refUnfolded)
    , ("candUnfolded", Json.str c.candUnfolded) ]

/-- Compare the two statement types in the shared environment: unfold
side-local definitions, then check alpha-equality and, failing that,
definitional equality. An `isDefEq` failure (a deterministic timeout, for
instance) leaves `defEq? = none`. -/
def compareStatements (env : Environment) (refT candT : Expr) (opts : Options := {})
    : IO StatementComparison := do
  let nss := [refNamespace, candNamespace]
  -- unfold side-local definitions, then canonicalize the instance telescope;
  -- the comparison and the direction searches both see this canonical reading
  let refU ← runMetaM env opts (canonicalizeInstances (← unfoldLocalDefs env opts nss refT))
  let candU ← runMetaM env opts (canonicalizeInstances (← unfoldLocalDefs env opts nss candT))
  let refUnfolded := toString (← runMetaM env opts <| Meta.ppExpr refU)
  let candUnfolded := toString (← runMetaM env opts <| Meta.ppExpr candU)
  let alphaEq := stripAnnotations refU == stripAnnotations candU
  let base : StatementComparison :=
    { alphaEq, refUnfolded, candUnfolded, refExpr := refU, candExpr := candU }
  if alphaEq then
    return { base with defEq? := some true }
  try
    let defEq ← runMetaM env opts <| Meta.withNewMCtxDepth <| Meta.isDefEq refU candU
    return { base with defEq? := some defEq }
  catch _ =>
    return base
end SemantEq
