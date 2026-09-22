import Lean
import SemantEq.Env

/-!
# Statement extraction and type-theoretic comparison 

After both sides compile, they are re-elaborated into ONE shared
environment (`SemantEq/Context.lean`), each inside its own namespace. This module
extracts each side's *last open statement* from that environment and compares the two
as `Expr`s:

* side-local definitions are **delta-unfolded** (and the result beta-reduced) first, so
  statements phrased via local `def`s compare by what they *mean*: identical or
  alpha-equal definitions, and one-side-inlined bodies, all become alpha-equal;
* `alphaEq`: exact match in the type-theory sense — structurally identical after
  erasing what the kernel ignores (binder names/info, `mdata`) and canonicalizing
  universe parameter names (de Bruijn indices make this precisely alpha-equivalence);
* `defEq?`: `Meta.isDefEq` in the shared environment — equality up to definitional
  unfolding (e.g. `a ≥ b` vs `b ≤ a`, or local defs with definitionally-equal bodies).

Side-local declarations *without* a value (axioms, `opaque`, `partial def`) cannot be
unfolded; the two sides' copies remain distinct constants and compare unequal — a
deliberate conservative choice (they are genuinely different assumptions).
-/

namespace SemantEq

open Lean Elab

/-- Namespace wrapping every declaration of the reference side in the shared env. -/
def refNamespace : Name := `SemantEqRef

/-- Namespace wrapping every declaration of the candidate side in the shared env. -/
def candNamespace : Name := `SemantEqCand

/-- Run a `MetaM` action in a given environment (extraction, pretty-printing, defeq). -/
def runMetaM (env : Environment) (opts : Options) (x : Meta.MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "<semanteq>", fileMap := default, options := opts }
  let (a, _, _) ← x.toIO coreCtx { env }
  return a

/-- A declaration's type with universe parameter names canonicalized to `u_0, u_1, …`,
so that two statements differing only in universe parameter naming compare equal. -/
def canonType (info : ConstantInfo) : Expr :=
  info.type.instantiateLevelParams info.levelParams
    (info.levelParams.mapIdx fun i _ => mkLevelParam (Name.mkSimple s!"u_{i}"))

/-- Erase everything the kernel ignores for term equality — binder names, binder info,
`mdata` — so that `==` on the results is alpha-equivalence. -/
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
  /-- Full declaration name in the shared environment (namespace included) — the
  implication search must be forbidden from using this constant. -/
  fullName : Name
  /-- The statement's type, universe-canonicalized (see `canonType`). -/
  type     : Expr
  typePP   : String
  /-- Source position where the declaration starts (in the coordinates of the file it
  was elaborated from) — used to split a side into preamble and final statement. -/
  startPos : Position := ⟨1, 0⟩

/-- Find the last user-facing declaration in the *local* part of `env` (the constants
elaborated into it, not imports), ranked by source position from the declaration-ranges
extension. Internal/auxiliary declarations are skipped; when `ns?` is given only
declarations under that namespace are considered (used to select one side's
declarations out of the shared environment). -/
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

/-- Delta-unfold every side-local declaration (any constant under the given namespaces)
occurring in `e`, then beta-reduce. `deltaExpand` revisits its replacements, so nested
local definitions unfold to a fixpoint; valueless locals (axioms, `opaque`,
`partial def`) are left in place. -/
def unfoldLocalDefs (env : Environment) (opts : Options) (nss : List Name) (e : Expr)
    : IO Expr :=
  runMetaM env opts do
    let mut e := e
    -- Fix 0: iterate unfolding with an INTERNAL-AUXILIARY elimination pass.
    -- Def elaboration mints `_proof_N`-style auxiliaries whose `value?` is `none`
    -- in the elaboration env (async outlining — the same phenomenon `auditProof`
    -- resolves through the kernel env). `deltaExpand` therefore cannot expand
    -- them, they survive into the canonical statement expr, and the per-direction
    -- envs RE-ELABORATE the preamble where the auxiliaries can come out under
    -- different names — the missing-constants check then kills the pair
    -- (observed: a research pair/a research pair, `lipJacobian._proof_5`, `IsMetricForm._proof_1`).
    -- They are Prop-valued proof terms, so substituting the kernel-env value is
    -- sound by proof irrelevance (and defeq by δ). Each substitution can expose
    -- fresh local constants, hence the bounded fixpoint loop.
    for _ in [0:8] do
      let e' ← Meta.deltaExpand e fun n => nss.any (·.isPrefixOf n)
      let e' ← Core.betaReduce e'
      let kenv := (← getEnv).toKernelEnv
      let hits ← IO.mkRef (0, 0, 0)  -- (matched, noInfo, noValue) — debug counters
      let e' ← Meta.transform e' (pre := fun sub => do
        match sub.getAppFn with
        | .const c us =>
          if (nss.any (·.isPrefixOf c)) && c.isInternalDetail then
            hits.modify fun (a,b,c') => (a+1,b,c')
            let info? := kenv.find? c <|> (← getEnv).find? c
            match info? with
            | none => hits.modify fun (a,b,c') => (a,b+1,c')
            | some info =>
              match info.value? with
              | none => hits.modify fun (a,b,c') => (a,b,c'+1)
              | some v =>
                let v := v.instantiateLevelParams info.levelParams us
                return .visit ((mkAppN v sub.getAppArgs).headBeta)
          return .continue
        | _ => return .continue)
      if (← envVar "TRACE").isSome then
        let (a,b,c') ← hits.get
        IO.eprintln s!"[unfold] aux pass: matched={a} noInfo={b} noValue={c'}"
      if e' == e then
        return e
      e := e'
    return e

/-- Instance-telescope canonicalization .

When a statement carries two instance binders on the same subject and one is
DERIVABLE from the other (`[CommRing R] [Field R]` — a `Field` is a `CommRing`),
typeclass resolution picks ONE of them for everything that follows, and WHICH one
is version-dependent: verified with `pp.explicit`, Mathlib v4.8 resolves
`Subring R` through the `Field` (`inst2`, leaving `inst1` unused) while v4.30
resolves it through the `CommRing`. The same source text therefore denotes
different propositions on different toolchains — silent semantic drift, and the
reason one benchmark pair is `EquivalentRestricted` for the original reference
implementation but `LikelyTooStrong` for us.

This normalizes to the intended reading — keep the STRONGEST instance, drop the
ones derivable from it — substituting the derivation everywhere the dropped
binder was used, so `Subring_{inst1} R` becomes
`Subring_{Field.toCommRing inst2} R`. That is what v4.8 already does by itself.

Guards (each earns its place):
* fires only with ≥2 instance binders — a cheap exit for nearly every statement,
  since most carry instances on *different* subjects;
* the synthesized derivation MUST mention a sibling LOCAL instance binder.
  `synthInstance` searches the global environment too, so without this a binder
  covered by a GLOBAL instance (a concrete subject like `ℝ`) would be dropped and
  the author's assumption silently swapped for Mathlib's canonical one;
* a dropped binder leaves the pool, so two mutually-derivable instances never
  both vanish;
* instances in NO derivability relation are untouched — `[Group G]` and
  `[Semiring G]` both reach `Semigroup` but neither derives the other, so this is
  a converging tree, not a diamond, and nothing is dropped. -/
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
      -- a NON-CLASS instImplicit binder (imported past `set_option
      -- checkBinderAnnotations false` by defective gold — `[CofiniteTopology X]`,
      -- Munkres 23.4 ×9) must be skipped, not synthesized: `trySynthInstance`
      -- throws on non-classes, and the uncaught throw surfaced as InternalError
      -- for the whole pair .
      if (← try Meta.isClass? ty catch _ => pure none).isNone then continue
      -- restrict the LOCAL instance set (leave the lctx intact: erasing a decl
      -- that later binders' types mention would make the context ill-formed)
      let insts := (← Meta.getLocalInstances).filter fun li =>
        li.fvar.fvarId! != xi.fvarId! && !dropped.any (·.fvarId! == li.fvar.fvarId!)
      let t? ← Meta.withLCtx (← getLCtx) insts do
        match ← (try Meta.trySynthInstance ty catch _ => pure .undef) with
        | .some t => pure (some t)
        | _       => pure none
      if let some t := t? then
        -- GUARD: the derivation must rest on a sibling, not on a global instance
        let ids := (Lean.collectFVars {} t).fvarIds
        if pool.any (fun y => ids.contains y.fvarId!) then
          dropped := dropped.push xi
          derivs  := derivs.push t
    if dropped.isEmpty then return e
    -- rebuild, substituting the dropped binders in the body AND in the types of
    -- the binders we keep (`S : Subring_{inst1} R` mentions a dropped binder)
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

/-- Compare the two statement types in the shared environment: unfold side-local
definitions, then check alpha-equality and (failing that) definitional equality.
`isDefEq` failures (e.g. deterministic timeout) leave `defEq? = none`. -/
def compareStatements (env : Environment) (refT candT : Expr) (opts : Options := {})
    : IO StatementComparison := do
  let nss := [refNamespace, candNamespace]
  -- δ-unfold side-local defs, then canonicalize the instance telescope:
  -- both feed the comparison AND the per-direction proving envs, so the whole
  -- pipeline downstream sees one canonical reading of each statement.
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
