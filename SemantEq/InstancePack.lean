import Lean
import SemantEq.Logic

/-!
# Instance packaging

Constructing a typeclass instance the goal context does not hold from the
material it does hold: the curated pack/unpack moves, the generated index of
packaging lemmas (class-conclusioned, non-instance Mathlib lemmas), the
per-pair memos, and the backtracking argument filler `fillFromLocals` that the
structural closer's forward instantiation runs on.
-/

namespace SemantEq
open Lean Meta

/-- Curated instance-plumbing moves, pack column: constructors that build an
instance of the keyed class from hypotheses and instances in scope. Every
constructor is class-headed, so the audit admits it. Single-backtick names:
these are Mathlib constants and this file imports core only; an absent
constant never elaborates and the move fails closed. -/
def instancePackMoves : List (Name × Name) := [
  (`Nontrivial,          `nontrivial_of_ne),
  (`Fintype,             `Fintype.ofFinite),
  (`Fact,                `Fact.mk),
  (`MulDistribMulAction, `MulDistribMulAction.compHom)
]

/-- Unpack column: extractors producing a Prop fact from ambient instances,
keyed by the fact's head. `Fact.out` is not listed: its conclusion is a bare
variable, so it is attempted generically (it self-guards through `[Fact _]`
synthesis). `zero_ne_one` passes the audit through the plain-head test. -/
def propUnpackMoves : List (Name × Name) := [
  (`Ne, `zero_ne_one),
  (`Ne, `one_ne_zero)
]

/-- The generated packaging index: the environment's packaging lemmas, the
theorems, definitions and constructors whose conclusion head is a class but
which are not registered instances (`Fintype.ofFinite`, `nontrivial_of_ne`,
`MulDistribMulAction.compHom`). They convert hypothesis-form facts into
instance-form ones, which rewrite discovery cannot see and `synthInstance`
never consults; the index generalizes the curated table to the whole import,
keyed by the conclusion's class head. Admission: at most six non-instance
binders. Built once per process on first use; class heads and binder shapes
are fixed by the import set, so a global cache is sound. -/
initialize packIndexCache : IO.Ref (Option (Lean.NameMap (Array Name))) ← IO.mkRef none

/-- Scan the environment for packaging lemmas (see `packIndexCache`). -/
def buildPackIndex : MetaM (Lean.NameMap (Array Name)) := do
  let env ← getEnv
  -- gates: class-headed conclusion, not a registered instance, at most six
  -- non-instance binders (instance binders are synthesized, not searched);
  -- constructors are admitted, large class constructors fall to the cap
  let pre ← IO.mkRef (#[] : Array (Name × Name))
  env.constants.forM fun c info => do
    if c.isInternal then return ()
    if isLocalConst env c then return ()
    match info with
    | .thmInfo _ | .defnInfo _ | .ctorInfo _ =>
      -- count the leading non-instance binders and read the conclusion head,
      -- all syntactic
      let mut ty := info.type
      let mut nb := 0
      while ty.isForall && nb ≤ 6 do
        unless ty.bindingInfo! == .instImplicit do
          nb := nb + 1
        ty := ty.bindingBody!
      if nb > 6 then return ()
      match ty.getAppFn with
      | .const h _ =>
        if isClass env h then
          pre.modify (·.push (h, c))
      | _ => return ()
    | _ => return ()
  let mut idx : Lean.NameMap (Array Name) := {}
  for (h, c) in (← pre.get) do
    try
      if ← Meta.isInstance c then continue
      idx := idx.insert h ((idx.find? h |>.getD #[]).push c)
    catch _ => continue
  return idx

/-- The packaging index, built on first use. -/
def getPackIndex : MetaM (Lean.NameMap (Array Name)) := do
  match ← packIndexCache.get with
  | some idx => return idx
  | none =>
    let idx ← try buildPackIndex catch _ => pure {}
    packIndexCache.set (some idx)
    return idx

/-- The instance-packing memos. `failed` and `recipes` are keyed by
`head|pp(classType)`: binder names are stable across an arm's rebuilds (every
arm intros the same statement), so the printed demand (`Fintype G`)
identifies it across all arms of a pair; the driver clears both per pair
(`PackMemo.resetPair`). `failed` holds the demands every mover failed, skipped
next time; `recipes` maps a demand to the mover that worked, replayed first.
A failure recorded in one arm also suppresses retries in arms whose rewritten
hypotheses might have enabled the construction; pack material is rarely what
arms rewrite. `built` holds the instances one `forwardInstantiate` pass
constructed (type and value, valid in that goal's context), asserted back for
sharing and reset per pass. -/
structure PackMemo where
  failed  : List String := []
  recipes : List (String × Name) := []
  built   : Array (Expr × Expr) := #[]
  deriving Inhabited

/-- The memos of the pair in flight. -/
initialize packMemoRef : IO.Ref PackMemo ← IO.mkRef {}

/-- Clear the per-pair memos (the driver calls this before each pair). -/
def PackMemo.resetPair : IO Unit :=
  packMemoRef.modify fun m => { m with failed := [], recipes := [] }

/-- The memo key of a demanded class type. -/
def packKey (mTy : Expr) : MetaM String := do
  let head := mTy.getAppFn.constName?.getD .anonymous
  return s!"{head}|{← ppExpr mTy}"

/-- Pack-construction depth: how deep converters may nest (`compHom` needing
`ofFinite` for its own instance binder is depth two). Each extra step
multiplies the worst-case attempts by the per-head cap of eight. -/
def packDepthMax : Nat := 2

/-- Try one curated move to construct a term of type `ty`: elaborate the
mover, unify its conclusion with `ty`, then fill its arguments, Prop
arguments first from `locals` (their types usually determine the data
arguments: `nontrivial_of_ne`'s `h : x ≠ y` fixes `x` and `y` by
unification), then instance arguments by synthesis, then the remaining data
arguments from `locals`. A mover's own failed instance argument recurses into
the packaging machinery up to `packDepthMax` levels (`Fintype.ofFinite`
feeding `compHom`'s `[Fintype G]`). -/
partial def tryCuratedMove (budget : IO.Ref Nat) (locals : Array Expr) (mover : Name)
    (ty : Expr) (depth : Nat := 0) : MetaM (Option Expr) := do
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let s ← saveState
  try
    let f ← mkConstWithFreshMVarLevels mover
    let (args, binfos, concl) ← forallMetaTelescope (← inferType f)
    unless ← isDefEq concl ty do
      restoreState s
      return none
    -- pass 1: Prop-typed arguments, from locals
    for h : idx in [0:args.size] do
      let a := args[idx]
      if !(← a.mvarId!.isAssigned) && binfos[idx]! != .instImplicit then
        let aTy ← instantiateMVars (← a.mvarId!.getType)
        if ← isProp aTy then
          let mut done := false
          for l in locals do
            unless done do
              let s2 ← saveState
              let hit ← isDefEqSafe a l
              if hit then done := true else restoreState s2
          unless done do
            restoreState s
            return none
    -- pass 2: instances by synthesis, remaining data from locals
    for h : idx in [0:args.size] do
      let a := args[idx]
      unless ← a.mvarId!.isAssigned do
        let aTy ← instantiateMVars (← a.mvarId!.getType)
        if binfos[idx]! == .instImplicit then
          match ← trySynthInstance aTy with
          | .some v =>
            unless ← isDefEq a v do
              restoreState s
              return none
          | _ =>
            -- synthesis failed for a mover's own instance binder: recurse into
            -- the packaging machinery (curated rows first, then the generated
            -- index), up to `packDepthMax` nesting levels
            let mut filled := false
            if depth + 1 < packDepthMax then
              let ihead := aTy.getAppFn.constName?.getD .anonymous
              for (h, m2) in instancePackMoves do
                if h == ihead && !filled then
                  if let some v ← tryCuratedMove budget locals m2 aTy (depth := depth + 1) then
                    if ← isDefEq a v then filled := true
              unless filled do
                if let some cands := (← getPackIndex).find? ihead then
                  for j in [0:min 8 cands.size] do
                    if !filled then
                      if let some v ← tryCuratedMove budget locals cands[j]! aTy (depth := depth + 1) then
                        if ← isDefEq a v then filled := true
            unless filled do
              restoreState s
              return none
        else
          let mut done := false
          for l in locals do
            unless done do
              let s2 ← saveState
              let hit ← isDefEqSafe a l
              if hit then done := true else restoreState s2
          unless done do
            restoreState s
            return none
    let res ← instantiateMVars (mkAppN f args)
    if res.hasExprMVar || res.hasSorry then
      restoreState s
      return none
    return some res
  catch _ =>
    restoreState s
    return none

/-- Backtracking argument filler for `forwardInstantiate`: assign each
metavariable binder from the local candidates (instances by synthesis), a
depth-first search with a shared defeq budget. -/
partial def fillFromLocals (budget : IO.Ref Nat) (locals : Array Expr)
    (ms : Array Expr) (infos : Array BinderInfo) (i : Nat) : MetaM Bool := do
  if i ≥ ms.size then
    return true
  let m := ms[i]!
  if ← m.mvarId!.isAssigned then
    return ← fillFromLocals budget locals ms infos (i + 1)
  let mTy ← instantiateMVars (← m.mvarId!.getType)
  if infos[i]! == .instImplicit then
    match ← trySynthInstance mTy with
    | .some val =>
      if ← isDefEq m val then
        return ← fillFromLocals budget locals ms infos (i + 1)
      return false
    | _ =>
      -- synthesis failed. (a) hypothesis promotion: a local whose type is the
      -- needed class, written as a plain hypothesis, which `trySynthInstance`
      -- never consults
      for l in locals do
        if (← budget.get) == 0 then
          return false
        budget.modify (· - 1)
        let s ← saveState
        let ok ← try
          if ← isDefEq m l then
            fillFromLocals budget locals ms infos (i + 1)
          else
            pure false
        catch _ => pure false
        if ok then
          return true
        restoreState s
      -- (b) curated construction: build the instance from context material
      -- (`nontrivial_of_ne 0 1 hR`, `Fintype.ofFinite`, `compHom G φ`)
      let head := mTy.getAppFn.constName?.getD .anonymous
      let key ← packKey mTy
      -- a demand every mover already failed: skip the whole search
      if (← packMemoRef.get).failed.contains key then
        return false
      let record (mover : Name) (v : Expr) : MetaM Unit := do
        packMemoRef.modify fun m =>
          { m with recipes := (key, mover) :: m.recipes, built := m.built.push (mTy, v) }
      -- recipe replay: the mover that worked for this demand before
      if let some (_, mover) := (← packMemoRef.get).recipes.find? (·.1 == key) then
        if let some v ← tryCuratedMove budget locals mover mTy then
          if ← isDefEq m v then
            packMemoRef.modify fun m => { m with built := m.built.push (mTy, v) }
            return ← fillFromLocals budget locals ms infos (i + 1)
      for (h, mover) in instancePackMoves do
        if h == head then
          if let some v ← tryCuratedMove budget locals mover mTy then
            if ← isDefEq m v then
              record mover v
              return ← fillFromLocals budget locals ms infos (i + 1)
      -- the generated packaging index: every admissible packaging lemma for
      -- this class head, after the curated rows, under a per-head try cap
      if let some cands := (← getPackIndex).find? head then
        for j in [0:min 8 cands.size] do
          if let some v ← tryCuratedMove budget locals cands[j]! mTy then
            if ← isDefEq m v then
              record cands[j]! v
              return ← fillFromLocals budget locals ms infos (i + 1)
      packMemoRef.modify fun m => { m with failed := key :: m.failed }
      return false
  for l in locals do
    if (← budget.get) == 0 then
      return false
    budget.modify (· - 1)
    let s ← saveState
    let ok ← try
      if ← isDefEq m l then
        fillFromLocals budget locals ms infos (i + 1)
      else
        pure false
    catch _ => pure false
    if ok then
      return true
    restoreState s
  -- no local supplies this argument; a Prop may still follow from an ambient
  -- instance through an unpack extractor (`0 ≠ 1` from `[Nontrivial R]` via
  -- `zero_ne_one`; any `p` from `[Fact p]` via `Fact.out`)
  if ← isProp mTy then
    if let some v ← tryCuratedMove budget locals `Fact.out mTy then
      if ← isDefEq m v then
        return ← fillFromLocals budget locals ms infos (i + 1)
    let head := mTy.getAppFn.constName?.getD .anonymous
    for (h, mover) in propUnpackMoves do
      if h == head then
        if let some v ← tryCuratedMove budget locals mover mTy then
          if ← isDefEq m v then
            return ← fillFromLocals budget locals ms infos (i + 1)
  return false
end SemantEq
