import Lean
import SemantEq.Logic
import SemantEq.Search
import SemantEq.ProofAudit.Rules

/-!
# The confiscated-instances reproof

On an otherwise passing direction: the proof's own antecedent-free
constructions and local facts are re-asserted, wherever they sit, and a weak
prover is asked to close the goal without the antecedent; a close that needs
those constructions convicts the proof as a middleman.
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- Outcome of the differential reproof. An armed probe's success has two
possible causes: the confiscated constructions enabled the antecedent-free
close (middleman, convict), or the goal was provable bare, which is a
property of the pair and not of the proof (never convicted, not reported). -/
inductive ReproofOutcome | silent | middleman | bareProvable
deriving BEq

/-- Per-direction state of the reproof's extended collection: the outer
conclusion and the pristine telescope context (fallback target of the bare
probe), the leaf budget, and the aggregate outcome (middleman dominates
bare-provable dominates silent). -/
structure DeepReplay where
  concl     : Expr
  baseLCtx  : LocalContext
  baseInsts : LocalInstances
  leaves    : IO.Ref Nat
  outcome   : IO.Ref ReproofOutcome

/-- At most this many leaf probes per direction in the extended collection
(each leaf costs an `assumption` + `exact?` attempt; case splits multiply
leaves). -/
def deepReplayLeafBudget : Nat := 4

/-- Confiscated-instances reproof: on an otherwise passing direction, rebuild
the goal's telescope, re-assert every antecedent-free local binding the proof
itself constructed (data bindings as instances: the proof's own packaging is
turned against it), and ask a weak prover to close the conclusion without
the antecedent; collection stops at the first antecedent-involved binding.
Differential form: an armed success alone does not convict; a bare probe
without the confiscation then classifies it. Bare failure means the proof's
own packaging was load-bearing for the antecedent-free close: middleman,
convict. Bare success means the conclusion is library-provable outright,
which says nothing about the proof: not convicted, not reported. When the
leading-chain collection is silent, `deep` extends it to bindings under case
splits, intros and conversions (`SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1` disables). -/
partial def confiscatedReproof (ctx : Ctx) (goalName : Name)
    (goalType proofVal : Expr) : Term.TermElabM ReproofOutcome := do
  try
    forallTelescope goalType fun xs concl => do
      let mut body := proofVal
      for x in xs do
        match body with
        | .lam _ _ b _ => body := b.instantiate1 x
        | .mdata _ (.lam _ _ b _) => body := b.instantiate1 x
        | _ => break
      let baseline ← do
        if !(← collect concl body) then pure ReproofOutcome.silent
        else if ← probe concl then pure .bareProvable
        else pure .middleman
      if !ctx.replayLocalFacts || baseline != .silent then return baseline
      -- the leading-chain collection speaks first (its verdicts stand; a
      -- bare-provable conclusion is never a conviction); on a silent direction
      -- the extended collection walks the proof and probes its branch goals
      let dr : DeepReplay := {
        concl, baseLCtx := ← getLCtx, baseInsts := ← getLocalInstances
        leaves := ← IO.mkRef 0, outcome := ← IO.mkRef .silent }
      deep dr concl {} {} false false body
      return ← dr.outcome.get
  catch _ => return .silent
where
  /-- The probe searches the fixture's own environment, which contains the
  proven goal theorem and the sorried antecedent and assumed statements; a
  probe proof reaching any of them is circular, not evidence of
  antecedent-free provability. -/
  legalProof (proof : Expr) : Term.TermElabM Bool := do
    let forbidden : NameSet := (ctx.assumed.insert ctx.ante).insert goalName
    let mut queue := proof.getUsedConstantsAsSet.toList
    let mut visited : NameSet := {}
    while h : !queue.isEmpty do
      let c := queue.head (by simpa using h)
      queue := queue.tail
      if visited.contains c then continue
      visited := visited.insert c
      if forbidden.contains c then return false
      if isLocalConst ctx.env c then
        if let some v := valueOf? ctx.env c (allowOpaque := true) then
          queue := v.getUsedConstantsAsSet.toList ++ queue
    return true
  probe (concl : Expr) : Term.TermElabM Bool := do
    for script in #["assumption", "exact?"] do
      if let some proof ← tryScript concl script then
        if ← legalProof proof then
          return true
    return false
  collect (concl : Expr) : Expr → Term.TermElabM Bool
    | e => do
      match asBinding? e with
      | some b => do
        let tInv ← anteInvolved ctx b.binderType
        let vInv ← anteInvolved ctx b.value
        if tInv || vInv then
          probe concl   -- stop confiscating at the first antecedent-involved binding
        else
          -- confiscate by value (`withLetDecl`): an opaque hypothesis of the
          -- same class is useless, since the goal's operations are pinned to
          -- the goal's own instances and only the constructed value (which
          -- extends them) is definitionally linked to the goal
          Meta.withLetDecl b.binderName b.binderType b.value fun x => do
            match ← isClassSafe b.binderType with
            | some cls => Meta.withNewLocalInstance cls x <| collect concl (b.mkBody x)
            | none => collect concl (b.mkBody x)
      | none => do
        -- `letI` is often zeta-inlined: the constructed instance sits inline as
        -- an argument of the terminal application (`assumed … (toCommRing {…}) …`);
        -- every antecedent-free, non-fvar, class-typed argument is confiscated
        inline concl e.getAppArgs 0
  inline (concl : Expr) (args : Array Expr) (i : Nat) : Term.TermElabM Bool := do
    if h : i < args.size then
      let a := args[i]
      let take ← do
        if a.isFVar then pure none
        else if ← anteInvolved ctx a then pure none
        else match ← inferTypeSafe a with
          | some ty =>
            match ← isClassSafe ty with
            | some cls => pure (some (cls, ty))
            | none => pure none
          | none => pure none
      match take with
      | some (cls, ty) =>
        Meta.withLetDecl `inst ty a fun x =>
          Meta.withNewLocalInstance cls x <| inline concl args (i+1)
      | none => inline concl args (i+1)
    else
      probe concl
  /-- The extended collection: probe the goal with every locally defined
  instance and every antecedent-free local lemma re-asserted, wherever it
  sits in the proof term. Re-asserts antecedent-free bindings by value
  exactly as `collect`, but walks the whole goal-side structure of the proof
  (`intro` lambdas, `Eq.mpr`/`Eq.mp` goal conversions, the minor premises of
  eliminations and matches) and probes each branch goal at its leaves.
  Bound variables are introduced as goal-side fvars, visible to both
  probes. Antecedent-freeness is transitive: a binding whose type or value
  reaches the antecedent, or mentions a tainted fvar, is introduced opaque
  and tainted, never re-asserted; the products of an elimination whose
  discriminant is tainted are tainted. The probed goal is refined only
  through untainted structure (an antecedent-derived rewrite or
  destructuring keeps the enclosing goal). `armed` collects the fvars only
  the armed probe may see. -/
  deep (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed frozen : Bool)
      (e : Expr)
      : Term.TermElabM Unit := do
    if (← dr.outcome.get) == .middleman then return ()
    let taints (x : Expr) : Bool := x.hasAnyFVar tainted.contains
    match asBinding? e with
    | some b =>
      if taints b.binderType || taints b.value || (← anteInvolved ctx b.binderType)
          || (← anteInvolved ctx b.value) then
        -- antecedent-involved (transitively): opaque, tainted, never re-asserted
        Meta.withLocalDecl b.binderName b.binderInfo b.binderType fun x =>
          deep dr goal (tainted.insert x.fvarId!) armed viaArmed frozen (b.mkBody x)
      else
        Meta.withLetDecl b.binderName b.binderType b.value fun x => do
          if ← auditTrace then
            IO.eprintln s!"[trace] replay re-asserts {b.binderName} : {← Meta.ppExpr b.binderType}"
          let k := deep dr goal tainted (armed.insert x.fvarId!) viaArmed frozen (b.mkBody x)
          match ← isClassSafe b.binderType with
          | some cls => Meta.withNewLocalInstance cls x k
          | none => k
    | none =>
      match e with
      | .mdata _ b => deep dr goal tainted armed viaArmed frozen b
      | .lam .. => deepLam dr goal tainted armed viaArmed frozen frozen e
      | .app .. =>
        let args := e.getAppArgs
        match e.getAppFn with
        | .const c _ =>
          if (c == ``Eq.mpr || c == ``Eq.mp) && args.size == 4 then
            -- goal conversion: with an antecedent-free record the converted
            -- proof proves the other side, which becomes the goal; with an
            -- antecedent-derived record the enclosing goal stands
            let record := args[2]!
            let refine := !frozen && !(taints record || (← anteInvolved ctx record))
            let goal' := if refine then (if c == ``Eq.mpr then args[1]! else args[0]!).headBeta
              else goal
            -- a goal refined through a re-asserted fact carries that fact's power
            -- into its statement; only the pristine outer conclusion is bare then
            let viaArmed' := viaArmed || (refine && record.hasAnyFVar armed.contains)
            -- an antecedent-derived conversion freezes the goal for the rest of
            -- the path: everything beneath proves the rewritten goal, so later
            -- refinements would be relative to a statement that embeds the
            -- antecedent
            deep dr goal' tainted armed viaArmed' (frozen || !refine) args[3]!
          else if (← isEliminatorConst ctx.env c) || isMatcherCore ctx.env c then
            -- the minor premises each prove a branch goal, read off the
            -- eliminator's own type (the reproof runs in the pristine import
            -- environment, where type inference over the proof body can fail
            -- on fixture-local auxiliaries); their products are tainted iff a
            -- discriminant or the major is
            let minors ← elimMinors c args
            let mut dirty := false
            let mut armedDisc := false
            for i in [0:args.size] do
              if (minors.find? (·.1 == i)).isNone then
                let a := args[i]!
                if taints a || (← anteInvolved ctx a) then dirty := true
                if a.hasAnyFVar armed.contains then armedDisc := true
            -- a frozen goal stays frozen: the branch goals beneath are relative
            -- to the rewritten statement
            let keep := dirty || frozen
            if minors.isEmpty then deepLeaf dr goal tainted armed viaArmed e
            else
              for (i, ty) in minors do
                let goal' := if keep then goal else ty.headBeta
                -- a `subst` or `cases` on a re-asserted fact refines the branch
                -- goal through that fact (`subst a` with `ha0 : a = 0`)
                let viaArmed' := viaArmed || (!keep && armedDisc)
                deepLam dr goal' tainted armed viaArmed' keep keep args[i]!
          else deepLeaf dr goal tainted armed viaArmed e
        | _ => deepLeaf dr goal tainted armed viaArmed e
      | _ => deepLeaf dr goal tainted armed viaArmed e
  /-- The minor premises of an eliminator or matcher application (argument
  positions whose binder type in the constant's telescope concludes in a
  parameter-headed application: `motive ⟨w, h⟩`, `c` of `Or.elim`) with the
  expected type of each, instantiated at the actual arguments. Read from the
  fixture environment (matchers are fixture-local); empty on any failure. -/
  elimMinors (c : Name) (args : Array Expr) : Term.TermElabM (Array (Nat × Expr)) := do
    let some info := ctx.env.find? c | return #[]
    try
      forallBoundedTelescope info.type args.size fun params _ => do
        let mut out := #[]
        for i in [0:min params.size args.size] do
          let ty ← inferType params[i]!
          let isMinor ← forallTelescope ty fun _ concl =>
            pure (match concl.getAppFn with
              | .fvar id => params.any (·.fvarId! == id)
              | _ => false)
          if isMinor then
            out := out.push (i, ty.replaceFVars params[0:i] args[0:i])
        return out
    catch _ => return #[]
  /-- Peel a lambda chain (an `intro`, or a minor premise's products),
  introducing each binder as a goal-side fvar, tainted when `taint` (products
  of an antecedent-derived destructuring) or when its type mentions a tainted
  fvar. The goal loses one Pi per binder while it has one to lose; under a
  tainted destructuring or a frozen goal the enclosing goal is kept. -/
  deepLam (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed frozen taint : Bool)
      : Expr → Term.TermElabM Unit
    | .lam n t b bi =>
      Meta.withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        let tainted' := if taint || t.hasAnyFVar tainted.contains then tainted.insert x.fvarId!
          else tainted
        let goal' ← do
          if taint then pure (some goal)
          else
            let g ← if goal.isForall then pure goal
              else try whnf goal catch _ => pure goal
            match g with
            | .forallE _ _ gb _ => pure (some (gb.instantiate1 x).headBeta)
            | _ => pure ((← inferTypeSafe body).map (·.headBeta))
        -- no goal to track (inference failed in the pristine environment)
        if let some goal' := goal' then deepLam dr goal' tainted' armed viaArmed frozen taint body
    | e => deep dr goal tainted armed viaArmed frozen e
  /-- A leaf of the extended collection: budgeted; `letI`-inlined instances of
  the terminal application are confiscated as in `inline`, then the branch
  goal is probed. -/
  deepLeaf (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      (e : Expr)
      : Term.TermElabM Unit := do
    if goal.hasAnyFVar tainted.contains then return ()  -- no honest goal to probe here
    if (← dr.leaves.get) ≥ deepReplayLeafBudget then return ()
    dr.leaves.modify (· + 1)
    deepInline dr goal.headBeta tainted armed viaArmed e.getAppArgs 0
  deepInline (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      (args : Array Expr) (i : Nat) : Term.TermElabM Unit := do
    if h : i < args.size then
      let a := args[i]
      let take ← do
        if a.isFVar || a.hasAnyFVar tainted.contains then pure none
        else if ← anteInvolved ctx a then pure none
        else match ← inferTypeSafe a with
          | some ty =>
            match ← isClassSafe ty with
            | some cls => pure (some (cls, ty))
            | none => pure none
          | none => pure none
      match take with
      | some (cls, ty) =>
        Meta.withLetDecl `inst ty a fun x =>
          Meta.withNewLocalInstance cls x <|
            deepInline dr goal tainted (armed.insert x.fvarId!) viaArmed args (i+1)
      | none => deepInline dr goal tainted armed viaArmed args (i+1)
    else
      deepProbe dr goal tainted armed viaArmed
  /-- Differential probe at a leaf: the weak prover and the differential logic
  of the leading-chain replay. Armed: the branch goal, the goal-side binders
  and every re-asserted binding (tainted binders cleared; they are
  dependency-closed by construction). Bare: the same with the re-asserted
  bindings cleared too (when the goal or a remaining binder depends on one,
  or the goal was refined through one, the baseline's bare probe on the
  pristine outer conclusion stands in). Middleman at any leaf refuses the
  direction; bare success is recorded as bare-provable and not reported. -/
  deepProbe (dr : DeepReplay) (goal : Expr) (tainted armed : FVarIdSet) (viaArmed : Bool)
      : Term.TermElabM Unit := do
    let trace ← auditTrace
    if trace then
      IO.eprintln s!"[trace] replay probes {← Meta.ppExpr goal} with {armed.size} re-asserted binding(s), {tainted.size} tainted"
    -- `withErasedFVars`: a class-typed let-decl is registered as a local
    -- instance twice (by `withLetDecl` and by `withNewLocalInstance`), and
    -- erasing one entry would leave a dangling instance. A Pi goal (an
    -- eliminator's motive, the antecedent's `∀ a b` conclusion) is opened
    -- first: `exact?` cannot replay its own suggestion on a Pi.
    Meta.withErasedFVars tainted.toList.toArray <| forallTelescope goal fun _ goal => do
      unless ← probe goal do return ()
      let touches (x : Expr) : Bool := x.hasAnyFVar armed.contains
      let dependent := touches goal || (← getLCtx).any fun d =>
        !armed.contains d.fvarId && (touches d.type || (d.value?.map touches).getD false)
      let bareLeaf ← if dependent || viaArmed then pure false
        else Meta.withErasedFVars armed.toList.toArray (probe goal)
      -- the baseline's own bare probe (pristine outer conclusion) as the
      -- second opinion: a branch goal refined through intros or
      -- antecedent-free rewrites can miss the library proof the outer
      -- conclusion has, and a bare-provable conclusion is never a conviction
      let bare ← if bareLeaf then pure true
        else Meta.withLCtx dr.baseLCtx dr.baseInsts (probe dr.concl)
      if trace then
        IO.eprintln s!"[trace] replay armed probe closed; bare probe {if bare then "closed (bare-provable)" else "failed (middleman)"}"
      if bare then
        if (← dr.outcome.get) == .silent then dr.outcome.set .bareProvable
      else dr.outcome.set .middleman
end ProofAudit
end SemantEq
