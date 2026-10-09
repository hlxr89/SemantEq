import Lean
import SemantEq.Logic
import SemantEq.ProofAudit.Rules

/-!
# The proof-term walk

The role- and polarity-aware walk of a proof term: lambda chains, bindings,
applications dispatched by the head's family (the antecedent, transitions,
records, eliminators, extensionality introductions, bridges, everything
else), the goal-part ablations, and the reading of local bridges' proofs
direction by direction.
-/

namespace SemantEq
namespace ProofAudit
open Lean Elab Meta

/-- A direction `fun h : A => body` of a local bridge's proof is an
implication proof of its own, with `h` in the antecedent's role (every Prop
binder met under `localProofCtx` joins `anteFVars` for the scope of its
body). A proof part of the direction (the body, a constructor component, a
binding's continuation, a conversion's payload) whose type is a goal-spine
proposition other than `True`, mentions no hypothesis, and whose pruned cone
never load-bears on a hypothesis of the direction is a goal part closed
without any hypothesis (`⟨fun _ => qProof, fun _ => pProof⟩` between two
library-true statements). At goal role this fails the proof; at
antecedent-argument role only the direction's conclusion is judged, and one
proved without the hypothesis is the severe grade. A reflexive conclusion is
not a claim; data binders are opened, nested Prop binders join the hypotheses. -/
partial def directionAblation (ctx : Ctx) (role : Role) (memo : IO.Ref (Std.HashMap Expr Bool))
    (locus : String) (concl : Option Expr) (e : Expr) : MetaM Unit := do
  let e := e.headBeta
  -- the part itself (a lambda over a hypothesis is opened instead; a lambda
  -- over data is a proof of a quantified statement, judged as a whole first)
  let hypLam ← match e with
    | .lam _ t _ _ => (isPropSafe t)
    | _ => pure false
  unless hypLam || e.isMData do
    if ← isProofSafe e then
      if let some ty ← inferTypeSafe e then
        -- a conclusion that holds by reflexivity (`x ∈ ↑i ↔ x ∈ i` after a
        -- `simp`, `a = a`) is not a claim; `simp`-built `Set.ext` proofs bind
        -- such hypotheses and never use them
        let refl ← match ty.iff? with
          | some (a, b) => (do if a == b then pure true else isDefEqCheap a b)
          | none => match ty.eq? with
            | some (_, a, b) => (do if a == b then pure true else isDefEqCheap a b)
            | none => pure false
        unless ty.isConstOf ``True || refl || (← anteInvolved ctx ty) do
          -- at goal role: a part on the goal's spine, as opened so far or as
          -- stated (a direction that proves a quantified goal part carries its
          -- own binder); at antecedent-argument role: the direction's conclusion itself,
          -- the fact that meets the antecedent's hypothesis (an auxiliary fact
          -- inside the direction is free not to use the hypothesis)
          let onSpine ← if role == .goal then
              (do if ← isGoalSpineProp ctx ty then pure true else spinePropOf ctx.goalStmt ty)
            else match concl with
              | some c => (do if matchWild c ty then pure true else isDefEqCheap c ty)
              | none => pure false
          if onSpine && !(← lbInvolvedGo ctx memo e) then
            if role == .goal then
              ctx.fail s!"goal part closes without the bridge's hypothesis ({locus}: {← Meta.ppExpr ty})"
            else
              ctx.severe s!"antecedent hypothesis met by a bridge direction proved without its hypothesis ({locus}: {← Meta.ppExpr ty})"
            return
  -- its structural components
  match e with
  | .mdata _ b => directionAblation ctx role memo locus concl b
  | .lam n t b bi =>
    withLocalDecl n bi t fun y => do
      let isPf ← isPropSafe t
      if isPf then ctx.anteFVars.modify (·.insert y.fvarId!)
      directionAblation ctx role memo locus concl (b.instantiate1 y)
      if isPf then ctx.anteFVars.modify (·.erase y.fvarId!)
  | .letE n t v b _ =>
    -- the binding's value is walked in its own right (at its use); a value
    -- that load-bears on a hypothesis makes its binder one
    withLetDecl n t v fun y => do
      let carries ← lbInvolvedGo ctx memo v
      if carries then ctx.anteFVars.modify (·.insert y.fvarId!)
      directionAblation ctx role memo locus concl (b.instantiate1 y)
      if carries then ctx.anteFVars.modify (·.erase y.fvarId!)
  | .app .. =>
    if let some bind := asBinding? e then
      withLocalDecl bind.binderName bind.binderInfo bind.binderType fun y => do
        let carries ← lbInvolvedGo ctx memo bind.value
        if carries then ctx.anteFVars.modify (·.insert y.fvarId!)
        directionAblation ctx role memo locus concl (bind.mkBody y)
        if carries then ctx.anteFVars.modify (·.erase y.fvarId!)
      return
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := f then
      if (c == ``And.intro || c == ``Iff.intro) && args.size == 4 then
        directionAblation ctx role memo locus concl args[2]!
        directionAblation ctx role memo locus concl args[3]!
      else if c == ``Exists.intro && args.size == 4 then
        directionAblation ctx role memo locus concl args[3]!
      else if (c == ``Eq.mpr || c == ``Eq.mp || c == ``cast) && args.size == 4 then
        directionAblation ctx role memo locus concl args[3]!
      else if c == ``id && args.size == 2 then
        directionAblation ctx role memo locus concl args[1]!
  | _ => pure ()

/-- A Prop binder met under a local bridge's proof at a non-side role is the
hypothesis of a direction. It joins `anteFVars` for the scope of its body, and
the outermost such lambda is read as an implication proof of its own. Returns
whether the binder was entered (then `leaveDirection` closes the scope). -/
def enterDirection (ctx : Ctx) (role : Role) (n : Name) (t : Expr) (x : Expr) (body : Expr)
    : MetaM Bool := do
  unless (← ctx.localProofCtx.get) > 0 && role != .side do return false
  unless ← (isPropSafe t) do return false
  ctx.anteFVars.modify (·.insert x.fvarId!)
  if (← ctx.dirCtx.get) == 0 then
    let memo ← IO.mkRef ({} : Std.HashMap Expr Bool)
    let concl ← if role == .anteArg then inferTypeSafe body else pure none
    directionAblation ctx role memo s!"direction with hypothesis {n.eraseMacroScopes}" concl body
  ctx.dirCtx.modify (·+1)
  return true
def leaveDirection (ctx : Ctx) (x : Expr) : MetaM Unit := do
  ctx.dirCtx.modify (·-1)
  ctx.anteFVars.modify (·.erase x.fvarId!)

/-- Options of the lambda-chain walker (`walkLamWith`). -/
structure LamOpts where
  /-- every binder joins `anteFVars`: the products of an antecedent-involved
  elimination -/
  bindersAnte : Bool := false
  /-- collect the binder ids (the destructuring products' identities) -/
  collect? : Option (IO.Ref (Array FVarId)) := none
  /-- every binder is a pair-aligned surface object: the products of a
  surface-rooted destructuring are the goal's own objects (a witness
  extracted from a surface hypothesis is surface) -/
  markAllSurface : Bool := false
  /-- the goal proof's leading lambdas, or an extensionality introduction (a
  `funext` binder is the goal speaking at the pair-aligned depth): open the
  goal's statement with each binder, mark data binders surface while the
  alignment budget lasts (Prop binders are exempt from the conviction, so
  they neither consume nor need marking), and keep peeling through bindings
  and `mdata`, since the goal's own binders may be intro'd after have/let
  steps -/
  surface : Bool := false
mutual

/-- Peel a lambda chain. Per lambda: open the binder; collect, taint or mark
it per the options (the taint is recorded before `enterDirection`, which
reads it); bump the polarity when the body proves `False`; enter a direction
when the binder is a hypothesis under a local bridge's proof; recurse;
leave. `mdata` is transparent. For any other non-lambda: in `surface` mode
the chain continues through bindings (`handleBinding … true`); in
`markAllSurface` mode it hands over to the surface walker, so conclusion
binders intro'd after an `obtain` still reach the alignment budget;
otherwise to `walk`. -/
partial def walkLamWith (ctx : Ctx) (role : Role) (neg : Nat) (o : LamOpts) (e : Expr)
    : MetaM Unit := do
  match e with
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      if let some acc := o.collect? then acc.modify (·.push x.fvarId!)
      if o.bindersAnte then ctx.anteFVars.modify (·.insert x.fvarId!)
      if o.markAllSurface then ctx.surfaceFVars.modify (·.insert x.fvarId!)
      if o.surface then
        -- open the goal's statement with the walk's own fvars
        let rem ← ctx.goalTypeRem.get
        if let .forallE _ d body _ := rem then
          ctx.goalOpenParts.modify (·.push d)
          ctx.goalTypeRem.set (body.instantiate1 x)
        -- data binders consume the alignment budget; Prop binders are exempt
        let isPf ← isPropSafe t
        if !isPf then
          if (← ctx.surfaceLeft.get) > 0 then
            ctx.surfaceLeft.modify (· - 1)
            ctx.surfaceFVars.modify (·.insert x.fvarId!)
      let body := b.instantiate1 x
      let neg' := neg + (← negBump body (b.hasLooseBVar 0))
      let hyp ← enterDirection ctx role n t x body
      walkLamWith ctx role neg' o body
      if hyp then leaveDirection ctx x
  | .mdata _ b =>
    -- metadata between two lambdas is transparent in every mode
    walkLamWith ctx role neg o b
  | .letE n t v b _ =>
    if o.surface then
      handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩ true
    else if o.markAllSurface then walkLamSurface ctx role neg e
    else walk ctx role neg e
  | _ =>
    if o.surface then
      if let some bind := asBinding? e then handleBinding ctx role neg bind true
      else walk ctx role neg e
    else if o.markAllSurface then walkLamSurface ctx role neg e
    else walk ctx role neg e

/-- The plain chain: binders taint when `bindersAnte`. -/
partial def walkLam (ctx : Ctx) (role : Role) (neg : Nat) (bindersAnte : Bool)
    : Expr → MetaM Unit :=
  walkLamWith ctx role neg { bindersAnte }

/-- The chain of an elimination's minor premise: binders collected, tainted
when `bindersAnte`, all surface when `markSurface`. -/
partial def walkLamCollect (ctx : Ctx) (role : Role) (neg : Nat)
    (bindersAnte : Bool) (markSurface : Bool) (acc : IO.Ref (Array FVarId))
    : Expr → MetaM Unit :=
  walkLamWith ctx role neg { bindersAnte, collect? := some acc, markAllSurface := markSurface }

/-- The goal proof's leading lambdas and extensionality introductions: see
`LamOpts.surface`. -/
partial def walkLamSurface (ctx : Ctx) (role : Role) (neg : Nat) : Expr → MetaM Unit :=
  walkLamWith ctx role neg { surface := true }

/-- An antecedent-involved in-file helper (theorem, def or instance) is walked
inline, its body instantiated at the call's arguments, at the call's role and
polarity, so the conjunct ablation, the witness audit and the polarity rules
reach inside it. Capped per helper; beyond the cap the constant grading
stands in. Internal auxiliaries (`_simp_N`, `_proof_N`) are read inline too
when they sit inside a record or a local bridge's proof: the collapse heads
inside them are what convicts there. Returns whether the body was walked. -/
partial def walkInlineHelper (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (f : Expr)
    (args : Array Expr)
    : MetaM Bool := do
  let n := ((← ctx.helperWalks.get).find? c).getD 0
  if n < 2 then
    if let some info := ctx.env.find? c then
      if let some v := valueOf? ctx.env c (allowOpaque := true) then
        let us := match f with | .const _ us => us | _ => []
        let v := v.instantiateLevelParams info.levelParams us
        ctx.helperWalks.modify (·.insert c (n+1))
        if ← auditTrace then IO.eprintln s!"[trace] inline walk of helper {c} @ {role.str}"
        -- the residual lambdas prove the goal part at this position,
        -- so at goal role their binders are the goal's own objects
        let body := (mkAppN v args).headBeta
        if role == .goal then walkLamSurface ctx role neg body
        else walk ctx role neg body
        return true
  return false

/-- The antecedent (or an antecedent-involved local lemma) applied: the
carrier-affinity audit, the data-surface and instance-slot audits of every
surface data slot, the closed-witness audit of its existential hypotheses,
then every argument walks at antecedent-argument role. -/
partial def auditAnteApplication (ctx : Ctx) (neg : Nat) (c : Name) (e : Expr)
    (args : Array Expr)
    : MetaM Unit := do
  -- carrier-affinity audit: a Sort-valued instantiation of the antecedent
  -- that is foreign to the goal's carriers convicts iff it occurs in what the
  -- antecedent delivers here (a dead junk parameter is harmless) and the goal
  -- does not itself existentially bind a Sort
  if c == ctx.ante then
    let delivered? ← inferTypeSafe e
    if !ctx.goalSortExists then
      for a in args do
        if let some ty ← inferTypeSafe a then
          if ty.isSort && foreignCarrier ctx a then
            if let some rty := delivered? then
              if (rty.find? (· == a)).isSome then
                ctx.fail s!"ante instantiated at a carrier foreign to the goal statement ({← Meta.ppExpr a})"
    -- data-surface audit: the antecedent's surface data slots must be filled
    -- at the goal's own surface objects; an argument capturing an off-surface
    -- data fvar uses the antecedent as a schema at objects the pair never
    -- speaks about. Prop fvars are exempt.
    let slotData ← ctx.anteSlotData.get
    for i in [0:min args.size slotData.size] do
      if slotData[i]! then
        let a := args[i]!
        if a.hasFVar then
          -- instance-slot rule: the antecedent must be applied at the goal's
          -- own structures. A class-typed argument in a data slot whose class
          -- sits on a goal-surface carrier, and which is not the goal's own
          -- instance binder, convicts when the class is not a subsingleton and
          -- the goal binds an instance (a replaced structure), or when it is a
          -- content-bearing subsingleton (`Fintype`) the goal does not grant.
          -- Exempt: defeq to the goal's instance, occurring in the goal's
          -- statement, classically-free scaffolding, granted finiteness.
          if let some clsType ← inferTypeSafe a then
            if let some clsName ← (isClassSafe clsType) then
              let surfSet ← ctx.surfaceFVars.get
              let surfCarrier := clsType.getAppArgs.any fun ca =>
                ca.isFVar && surfSet.contains ca.fvarId!
              let argCore ← resolveLocal ctx a
              let argIsSurfFvar := argCore.isFVar && surfSet.contains argCore.fvarId!
              if surfCarrier && !argIsSurfFvar then
                let mut goalInst : Option FVarId := none
                for fv in surfSet.toList do
                  if goalInst.isNone then
                    if let some d ← fv.findDecl? then
                      if (← isDefEqSafe d.type clsType) then
                        goalInst := some fv
                let defeqGoal ← match goalInst with
                  | some g => isDefEqSafe a (mkFVar g)
                  | none => pure false
                let subsing ← do
                  match ← (try Meta.synthInstance? (← Meta.mkAppM ``Subsingleton #[clsType]) catch _ => pure none) with
                  | some _ => pure true
                  | none => pure false
                -- classically-free scaffolding (`Decidable`, `DecidableEq`):
                -- synthesizable given a universal classical `Decidable` provider?
                let synthCl ← do
                  try
                    let decProv := Expr.forallE `p (mkSort Level.zero)
                      (mkApp (mkConst ``Decidable) (Expr.bvar 0)) BinderInfo.default
                    Meta.withLocalDecl `cd BinderInfo.instImplicit decProv fun cd =>
                      Meta.withNewLocalInstance ``Decidable cd do
                        pure (← Meta.synthInstance? clsType).isSome
                  catch _ => pure false
                -- does the goal statement grant finiteness (`Finite`/`Fintype`)?
                let goalFin := ctx.goalHasFin
                let occGoal := (← occursInGoalStmt ctx a) || (← occursInGoalStmt ctx argCore)
                unless defeqGoal || occGoal do
                  if !subsing then
                    -- a replaced non-subsingleton structure the goal binds
                    if goalInst.isSome then
                      ctx.fail s!"ante instance slot at a surface carrier filled with a replaced {clsName} structure ({← Meta.ppExpr a}); the goal's own instance is unused"
                  else
                    -- a content subsingleton manufactured, the goal grants none;
                    -- classically-free scaffolding stays exempt
                    if !synthCl && !goalFin then
                      ctx.fail s!"ante instance slot at a surface carrier filled with a manufactured {clsName} instance ({← Meta.ppExpr a}) the goal statement does not grant"
          let isSortSlot ← do
            match ← inferTypeSafe a with
            | some ty => pure ty.isSort
            | none => pure false
          if isSortSlot && !ctx.goalSortExists then
            -- a Sort-valued surface slot must be the goal's own carrier (a type
            -- constructed from goal data, `↥(s 0)`, is related but not the same
            -- carrier); `PLift`/`ULift` adapters are content-free, so the wrapped
            -- core is tested, let-bound names resolved first
            let mut core ← resolveLocal ctx a
            while core.isAppOfArity ``PLift 1 || core.isAppOfArity ``ULift 1 do
              core ← resolveLocal ctx (core.getArg! 0)
            let bareSurface := core.isFVar &&
              (← ctx.surfaceFVars.get).contains core.fvarId!
            if !bareSurface then
              -- a type the goal's own statement mentions is the goal's own
              -- object (`↥F` inside `IsAlgebraic F a`)
              if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx core) then
                if let some rty := delivered? then
                  if (rty.find? (· == a)).isSome then
                    ctx.fail s!"ante carrier slot instantiated at a type constructed from, not identical to, the goal's carriers ({← Meta.ppExpr a})"
          else
            -- a value slot whose argument the delivered conclusion uses as a
            -- type (the coercion `↥arg` appears) induces a carrier, which must
            -- be the goal's own object; plain value use keeps the lenient
            -- transport rule
            let vcore ← resolveLocal ctx a
            let bareSurface := vcore.isFVar &&
              (← ctx.surfaceFVars.get).contains vcore.fvarId!
            let carrierUse :=
              if bareSurface then false
              else match delivered? with
                | some rty =>
                  (rty.find? (fun t =>
                    t.isAppOfArity ``Subtype 2 &&
                    ((t.getArg! 1).find? (· == a)).isSome)).isSome
                | none => false
            if carrierUse then
              if !(← occursInGoalStmt ctx a) && !(← occursInGoalStmt ctx vcore) then
                ctx.fail s!"ante value slot used as a carrier of the delivered statement but instantiated at a constructed object ({← Meta.ppExpr a})"
            else
              if let some fv ← surfaceViolation? ctx a then
                if let some rty := delivered? then
                  if (rty.find? (· == a)).isSome then
                    ctx.fail s!"ante surface slot instantiated at an object outside the statements' shared surface ({← Meta.ppExpr a}; foreign object {← Meta.ppExpr (mkFVar fv)})"
  -- closed-witness audit of the antecedent's existential hypotheses
  if c == ctx.ante && ctx.witnessCheck then
    if let some info := ctx.env.find? c then
      witnessAudit ctx info.type args
  -- the antecedent, or an antecedent-involved local lemma: its arguments
  -- feed the antecedent pipeline
  for a in args do walk ctx .anteArg neg a

/-- A role transition (`Iff.mp` / `Iff.mpr` / `Eq.mp` / `Eq.mpr`): the converted
proof (last argument) inherits the conversion's role; the record
(second-to-last) walks at the enclosing role inside `recordCtx`; an
antecedent-involved record that actually rewrites freezes the converted proof. -/
partial def walkTransitionApp (ctx : Ctx) (role : Role) (neg : Nat) (args : Array Expr)
    : MetaM Unit := do
  -- a transition transports the role with the content: the converted proof
  -- (last argument) inherits the conversion's position; the record walks at
  -- the enclosing role inside `recordCtx`, where content is a flag and a
  -- collapsed goal part is refused
  ctx.chainCtx.modify (·+1)
  -- an antecedent-involved justification that actually rewrites freezes the
  -- converted proof
  let recInv ← if args.size ≥ 2 then
      (do if ← anteInvolved ctx args[args.size - 2]! then recordRewrites args[args.size - 2]! else pure false)
    else pure false
  for i in [0:args.size] do
    if args.size ≥ 2 && i == args.size - 2 then
      ctx.recordCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.recordCtx.modify (·-1)
    else if recInv && i == args.size - 1 then
      ctx.frozenCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.frozenCtx.modify (·-1)
    else walk ctx role neg args[i]!
  ctx.chainCtx.modify (·-1)

/-- Simp's goal-conversion wrappers (`of_eq_true` / `of_eq_false`): the last
argument is a rewrite record, walked at the enclosing role inside
`recordCtx`. -/
partial def walkRecordApp (ctx : Ctx) (role : Role) (neg : Nat) (args : Array Expr)
    : MetaM Unit := do
  ctx.chainCtx.modify (·+1)
  for i in [0:args.size] do
    if i == args.size - 1 then
      ctx.recordCtx.modify (·+1)
      walk ctx role neg args[i]!
      ctx.recordCtx.modify (·-1)
    else walk ctx role neg args[i]!
  ctx.chainCtx.modify (·-1)

/-- An eliminator application: the minors are walked first with their
products collected, a branch is a goal part unless the major is
antecedent-involved, an elimination whose products are all unused earns no
exemption (dead elimination), and an `Eq.rec`-family substitution along an
antecedent-involved equation that rewrites freezes its minor. -/
partial def walkEliminatorApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (args : Array Expr)
    : MetaM Unit := do
  -- an `Eq.rec`-family substitution is a transport position
  if eqRecFamily c then ctx.chainCtx.modify (·+1)
  let mut majorInv := false
  let mut majorSurface := true
  for a in args do
    if !a.isLambda then
      if (← isProofSafe a) && (← anteInvolved ctx a) then majorInv := true
      if a.hasFVar then
        if (← surfaceViolation? ctx a).isSome then majorSurface := false
  -- the minors are walked first, collecting product binders; a destructured
  -- local's occurrence then takes its products' role join
  let products ← IO.mkRef (#[] : Array FVarId)
  let mut minors := #[]
  -- a substitution along an antecedent-involved equation that actually
  -- rewrites freezes its minor (the goal transported by the rewrite)
  let mut majorRewrites := true
  if eqRecFamily c && majorInv then
    for a in args do
      if !a.isLambda then
        if (← isProofSafe a) && (← anteInvolved ctx a) then
          majorRewrites ← recordRewrites a
  let eqFrozen := eqRecFamily c && majorInv && majorRewrites
  if eqFrozen then ctx.frozenCtx.modify (·+1)
  for a in args do
    if a.isLambda then
      if ← isProofSafe a then
        -- a genuine minor: its binders are the destructuring products
        walkLamCollect ctx role neg majorInv majorSurface products a
        minors := minors.push a
        if role == .goal && !majorInv then
          branchAblation ctx a s!"branch of {c}"
      else
        -- motive / predicate lambda: type-level, no products to collect
        walkLam ctx role neg majorInv a
  -- dead-elimination audit: the ablation exemption for an antecedent-involved
  -- elimination is earned only if some product is used; a destructuring whose
  -- products are all unused distributed nothing, and the default rule resumes
  -- on its branches
  if role == .goal && majorInv && minors.size > 0 then
    let prods ← products.get
    if prods.size > 0 then
      let mut anyUsed := false
      for p in prods do
        if ← usedAnywhere ctx p then anyUsed := true
      if !anyUsed then
        for m in minors do
          branchAblation ctx m s!"branch of {c} (ante destructured to unused products)"
  if eqRecFamily c then ctx.chainCtx.modify (·-1)
  for a in args do
    unless a.isLambda do
      match a with
      | .fvar id =>
        let occ ← ctx.occRoles.get
        let pj := (← products.get).foldl (init := (none : Option Role))
          fun r? pid => match occ.get? pid with
            | some r => some ((r?.map (Role.join r)).getD r)
            | none => r?
        recordOcc ctx id (pj.getD role)
        checkFalseNode ctx neg a "hypothesis of type False"
      | _ => walk ctx role neg a
  if eqFrozen then ctx.frozenCtx.modify (·-1)

/-- An extensionality introduction: the pointwise proof's binders inherit
surface (budgeted) and the proof is a goal part; a motive lambda gets no
surface budget. -/
partial def walkExtIntroApp (ctx : Ctx) (role : Role) (neg : Nat) (args : Array Expr)
    : MetaM Unit := do
  for a in args do
    if a.isLambda then
      if ← isProofSafe a then
        -- the pointwise proof: its binders inherit surface (budgeted)
        walkLamSurface ctx role neg a
        if role == .goal then branchAblation ctx a "lambda argument"
      else
        -- motive / type-family lambda: no surface budget
        walkLam ctx role neg false a
    else walk ctx role neg a

/-- A bridge applied forward: role-transparent (its hypotheses are
constitutive inputs, not side conditions), the bare-bridge rule at goal
role, and the equational-chain legs (`Eq.trans`, `congrArg`) as transport
positions. -/
partial def walkBridgeApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (e : Expr)
    (args : Array Expr) (isAss isLoc : Bool)
    : MetaM Unit := do
  -- a bridge applied forward is role-transparent: its hypotheses are
  -- constitutive inputs (`le_antisymm h1 h2`), not side conditions. The
  -- bare-bridge rule: a plain Eq/Iff library lemma is licensed to transport
  -- content between phrasings; asserted at goal role outside every transport
  -- position with an antecedent-free cone, its conclusion stands as
  -- mathematical content and the proof fails. Not inside a record or a local
  -- bridge's proof, where a value applies equations bare without asserting
  -- them as goal content.
  if role == .goal && (← ctx.chainCtx.get) == 0 && !isLoc && !isAss
      && !(← ablationSuspended ctx) then
    if ← plainEqIffConcl ctx.env c then
      if !(← anteInvolved ctx e) then
        ctx.fail s!"bridge conclusion asserted as content at goal role (bare, ante-free, outside transport position): {c}"
  let chain := c == ``Eq.trans || c == ``Eq.symm || c == ``Iff.trans ||
    c == ``Iff.symm || c == ``congrArg || c == ``congrFun ||
    c == ``congr || c == ``Trans.trans || c == ``HEq.trans || c == ``HEq.symm
  for a in args do
    if chain then
      ctx.chainCtx.modify (·+1)
      walk ctx role neg a
      ctx.chainCtx.modify (·-1)
    else walk ctx role neg a

/-- An application headed by a constant of no special family: `cast` (a transport
position, frozen when its equation is antecedent-involved and rewrites), the
constructors (`And.intro` / `Iff.intro` / `Exists.intro`: proof-typed lambda
components are the goal's own quantified objects), and everything else; a
lambda argument at goal role is a goal part and is ablated unless the head is
data. -/
partial def walkOtherApp (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) (args : Array Expr)
    (isAss isLoc : Bool)
    : MetaM Unit := do
  let dataHead ← if isAss || isLoc then pure false
    else pure ((← categorize ctx c) == .data)
  if c == ``cast then ctx.chainCtx.modify (·+1)
  -- `cast` along an antecedent-involved equation that actually rewrites
  -- freezes its value
  let castFrozen ← if c == ``cast && args.size == 4 then
      (do if ← anteInvolved ctx args[2]! then recordRewrites args[2]! else pure false)
    else pure false
  let ctorHead := c == ``And.intro || c == ``Iff.intro || c == ``Exists.intro
  for i in [0:args.size] do
    let a := args[i]!
    if castFrozen && i == 3 then
      ctx.frozenCtx.modify (·+1)
      walk ctx role neg a
      ctx.frozenCtx.modify (·-1)
    else if ctx.conjunctSurface && role == .goal && ctorHead && a.isLambda
        && (← isProofSafe a) then
      -- `⟨…, fun n => A n⟩`: the component's binders are the goal statement's
      -- own quantified objects (budgeted)
      walkLamSurface ctx role neg a
    else walk ctx role neg a
    if role == .goal && a.isLambda && !dataHead then
      branchAblation ctx a "lambda argument"
  if c == ``cast then ctx.chainCtx.modify (·-1)

/-- The walk of a proof term at a role and polarity: locals record their
occurrence, constants are judged by family, bindings go to `handleBinding`,
lambdas to the chain walker, and applications dispatch on the head. -/
partial def walk (ctx : Ctx) (role : Role) (neg : Nat) (e : Expr) : MetaM Unit := do
  match e with
  | .bvar _ | .mvar _ | .sort _ | .lit _ => pure ()
  | .fvar id =>
    recordOcc ctx id role
    checkFalseNode ctx neg e "hypothesis of type False"
  | .const c us => do
    let nFlagsBefore := (← ctx.flags.get).size
    if c == ctx.ante then pure ()
    else if ctx.assumed.contains c then judgeOutsideLocal ctx role c
    else if isLocalConst ctx.env c then
      if c.isInternalDetail && !(← ablationSuspended ctx) then expandLocal ctx role neg c
      else if c.isInternalDetail || (← constReaches ctx ctx.reachMemo ctx.ante c) then
        -- inline walk of the helper's body (capped)
        let n := ((← ctx.helperWalks.get).find? c).getD 0
        match (if n < 2 then valueOf? ctx.env c (allowOpaque := true) else none), ctx.env.find? c with
        | some v, some info =>
          ctx.helperWalks.modify (·.insert c (n+1))
          let body := v.instantiateLevelParams info.levelParams us
          if role == .goal then walkLamSurface ctx role neg body
          else walk ctx role neg body
        | _, _ => expandLocal ctx role neg c
      else
        judgeOutsideLocal ctx role c
        if role != .side then walkOutsideLocalProof ctx role neg c
    else judgeConst ctx role neg c "bare constant"
    if role == .anteArg then severeIfClosed ctx nFlagsBefore c #[]
  | .mdata _ b => walk ctx role neg b
  | .proj _ _ b =>
    checkFalseNode ctx neg e "projection"
    walk ctx role neg b
  | .lam .. => walkLam ctx role neg false e
  | .forallE .. => pure ()   -- a Pi in proof position is a type; nothing to judge
  | .letE n t v b _ =>
    handleBinding ctx role neg ⟨n, t, v, fun x => b.instantiate1 x, .default, b.hasLooseBVar 0⟩
  | .app .. =>
    if let some bind := asBinding? e then
      handleBinding ctx role neg bind
    else do
      checkFalseNode ctx neg e "application"
      if role == .goal && (← ablationSuspended ctx) then
        if let some ty ← inferTypeSafe e then checkCollapseEquation ctx e ty
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const c _ =>
        -- an ex-falso head fed by a benign `noConfusion` `False` is
        -- impossible-branch elimination: the branch is computationally dead,
        -- so its arguments walk at side role
        if exFalso5.contains c then
          let mut benign := false
          for a in args do
            unless benign do
              if let some ty ← inferTypeSafe a then
                if (← whnf ty).isConstOf ``False then
                  benign ← benignNoConfusionFalse ctx a
          if benign then
            for a in args do walk ctx .side neg a
            return
        -- a `noConfusion`-family discriminator on a derived equation proves
        -- anything from an absurd equation without a `False` node: ex falso at
        -- positive polarity
        if neg == 0 && nameHasNoConfusion c && !isLocalConst ctx.env c then
          unless ← benignNoConfusionFalse ctx e do
            ctx.fail s!"explosion through {c} on a derived equation in positive position"
        -- head judging, by family
        let isAss := ctx.assumed.contains c
        let isLoc := !isAss && c != ctx.ante && isLocalConst ctx.env c
        let locInternal := isLoc && c.isInternalDetail
        let locInvolved ← if isLoc && !locInternal then
            constReaches ctx ctx.reachMemo ctx.ante c
          else pure false
        let isLocFree := isLoc && !locInternal && !locInvolved
        -- an antecedent-involved in-file helper is walked inline at the
        -- call's role and polarity (`walkInlineHelper`); internal auxiliaries
        -- are read inline inside a record or a local bridge's proof, where
        -- their collapse heads are what convicts
        if locInvolved || (locInternal && (← ablationSuspended ctx)) then
          if ← walkInlineHelper ctx role neg c f args then return
        let nFlagsBefore := (← ctx.flags.get).size
        if c == ctx.ante then pure ()
        else if isAss || isLocFree then
          judgeOutsideLocal ctx role c
          -- a bridge-shaped antecedent-free in-file lemma keeps its shape
          -- admission, and its proof is read once at the use role
          if isLocFree && role != .side then walkOutsideLocalProof ctx role neg c
        else if isLoc then expandLocal ctx role neg c
        else judgeConst ctx role neg c "application head"
        if role == .anteArg then severeIfClosed ctx nFlagsBefore c args
        -- a goal part collapsed to `True` (or a conjunct dropped) by a content
        -- fact inside a record or a local bridge's proof is a goal part closed
        -- without the antecedent
        if role == .goal && collapseHead c
            && ((← ctx.recordCtx.get) > 0 || (← ctx.localProofCtx.get) > 0) then
          for a in args do
            collapseAblation ctx a s!"goal part collapsed by {c} inside a rewrite record or a local bridge's proof" (spine := true)
        -- conjunct-level ablation: at goal role the components of `And.intro`
        -- and `Iff.intro` are goal parts, so an atomic or applicative
        -- component (`rfl`, a `decide` term, a goal hypothesis) that closes
        -- without the antecedent is a redundant goal part (`⟨ante, rfl⟩`);
        -- lambda components are ablated by the generic arm. Not under a
        -- conversion justified by the antecedent (`frozenCtx`), where the
        -- components are the antecedent's residual obligation, and not in
        -- antecedent-argument position.
        if ctx.conjunctAblation && role == .goal && (← ctx.frozenCtx.get) == 0
            && !(← ablationSuspended ctx) && (c == ``And.intro || c == ``Iff.intro) then
          for a in args do
            unless a.isLambda do
              branchAblation ctx a s!"constructor component ({c})"
        -- argument dispatch
        if c == ctx.ante || locInvolved then
          auditAnteApplication ctx neg c e args
        else if transitionHead c then
          walkTransitionApp ctx role neg args
        else if recordHead c then
          walkRecordApp ctx role neg args
        else if let some majorIdx ← projConsumerAnte ctx c args then
          -- a projection consuming an antecedent-derived record: the arguments
          -- after it feed an antecedent-derived fact
          for i in [0:args.size] do
            walk ctx (if i > majorIdx then .anteArg else role) neg args[i]!
        else if ← isEliminatorConst ctx.env c then
          walkEliminatorApp ctx role neg c args
        else if extIntroHead c then
          walkExtIntroApp ctx role neg args
        else if ← headIsBridge ctx c (isAss || isLocFree) then
          walkBridgeApp ctx role neg c e args isAss isLoc
        else
          walkOtherApp ctx role neg c args isAss isLoc
      | .fvar id =>
        recordOcc ctx id role
        let anteHead := (← ctx.anteFVars.get).contains id
        for a in args do
          walk ctx (if anteHead then .anteArg else role) neg a
      | .proj sName _ s =>
        -- Iff/Eq projections are transitions: the record walks at the
        -- enclosing role inside `recordCtx`, the converted proof inherits the
        -- role; other projections follow the projection-consumer rule
        checkFalseNode ctx neg f "projection"
        if sName == ``Iff || sName == ``Eq then
          ctx.chainCtx.modify (·+1)
          ctx.recordCtx.modify (·+1)
          walk ctx role neg s
          ctx.recordCtx.modify (·-1)
          -- an antecedent-involved record that rewrites freezes the converted proofs
          let recInv ← (do if ← anteInvolved ctx s then recordRewrites s else pure false)
          if recInv then ctx.frozenCtx.modify (·+1)
          for a in args do walk ctx role neg a
          if recInv then ctx.frozenCtx.modify (·-1)
          ctx.chainCtx.modify (·-1)
        else
          walk ctx role neg s
          let inv ← anteInvolved ctx s
          for a in args do walk ctx (if inv then .anteArg else role) neg a
      | _ =>
        walk ctx role neg f
        for a in args do walk ctx role neg a

/-- Bridge-arm test for an application head: globals via `categorize`, assumed
or antecedent-free local lemmas via their graded statement. -/
partial def headIsBridge (ctx : Ctx) (c : Name) (outsideLocal : Bool) : MetaM Bool := do
  if outsideLocal then
    return ((← ctx.localGrade.get).find? c).getD false
  else
    return (← categorize ctx c) == .bridge

/-- Ablation check: at goal role, a proof whose dependency cone and whose
type's cone are both antecedent-free closes a goal part without the
antecedent. -/
partial def branchAblation (ctx : Ctx) (a : Expr) (locus : String) : MetaM Unit := do
  -- inside a rewrite record (a conditional bridge's side conditions, a
  -- `forall_congr` pointwise lambda) or a local bridge's proof the sub-proof
  -- proves the record or the bridge, not the goal: positional goal-part
  -- ablation is suspended there, and only the collapse heads convict
  if ← ablationSuspended ctx then return ()
  collapseAblation ctx a locus

/-- The dependency-cone test itself (load-bearing involvement):
a proof-typed part whose pruned cone and whose type never reach the antecedent
closes a goal part without it. Used directly for collapse heads, which are
judged even inside a local bridge's proof. -/
partial def collapseAblation (ctx : Ctx) (a : Expr) (locus : String) (spine : Bool := false)
    : MetaM Unit := do
  unless ← isProofSafe a do return ()
  let some ty ← inferTypeSafe a | return ()
  if ty.isConstOf ``True then return ()   -- a proof of `True` carries nothing
  if ← anteInvolved ctx ty then return ()
  -- on the collapse path the position does not certify a goal part: the
  -- collapsed proposition must sit on the goal's spine (`simp [hc]` on an `if`
  -- condition is a reduction, not a part proved)
  if spine then
    unless ← isGoalSpineProp ctx ty do return ()
  -- a constructor bundle is judged part by part (`eq_true ⟨A, X⟩`)
  let a' := a.headBeta
  if a'.isAppOfArity ``And.intro 4 || a'.isAppOfArity ``Iff.intro 4 then
    let args := a'.getAppArgs
    collapseAblation ctx args[2]! locus
    collapseAblation ctx args[3]! locus
    return
  if ← anteInvolvedLB ctx a then return ()
  ctx.fail s!"goal part closes ante-free ({locus})"

/-- Read the proof of a bridge-shaped, antecedent-free in-file lemma once, at
the role where the lemma is used, with goal-part ablations suspended and
content at the flag tier (the shape admission stays the floor); its
directions are read by `directionAblation`. Runs in both modes. -/
partial def walkOutsideLocalProof (ctx : Ctx) (role : Role) (neg : Nat) (c : Name) : MetaM Unit := do
  unless ((← ctx.localGrade.get).find? c).getD false do return ()
  let n := ((← ctx.helperWalks.get).find? c).getD 0
  if n ≥ 1 then return ()
  let some info := ctx.env.find? c | return ()
  let some v := valueOf? ctx.env c (allowOpaque := true) | return ()
  if v.getUsedConstantsAsSet.contains ``sorryAx then return ()
  ctx.helperWalks.modify (·.insert c (n+1))
  ctx.localProofCtx.modify (·+1)
  walk ctx role neg (v.instantiateLevelParams info.levelParams [])
  ctx.localProofCtx.modify (·-1)

/-- A binding (`have`, `let`, a beta-redex): the body is walked at the
enclosing role and ablated after an antecedent-free binding at goal role;
the value is walked at the role of its use. An antecedent-free Prop binding
is an outside lemma: its statement is graded, and when bridge-shaped its
proof is read at the use role. -/
partial def handleBinding (ctx : Ctx) (role : Role) (neg : Nat) (b : Binding)
    (surfaceMode : Bool := false) : MetaM Unit := do
  let vInv ← anteInvolved ctx b.value
  let propT ← isPropSafe b.binderType
  withLocalDecl b.binderName b.binderInfo b.binderType fun x => do
    if vInv then ctx.anteFVars.modify (·.insert x.fvarId!)
    -- a data binding whose value is built from surface objects is
    -- itself a surface object (transitive surface; closed values included)
    if propT then ctx.propValues.modify (·.insert x.fvarId! b.value)
    if !propT then
      ctx.localValues.modify (·.insert x.fvarId! b.value)
      if !b.value.hasFVar || (← surfaceViolation? ctx b.value).isNone then
        ctx.surfaceFVars.modify (·.insert x.fvarId!)
    let body := b.mkBody x
    let neg' := neg + (← negBump body b.bodyUses)
    if surfaceMode then walkLamSurface ctx role neg' body
    else walk ctx role neg' body
    -- ablation locus (i): the rest of the proof after this binding
    if role == .goal && !(← ablationSuspended ctx) then
      if !(← anteInvolvedLB ctx body) then
        if ← isProofSafe body then
          let tyOk ← do
            match ← inferTypeSafe body with
            | some ty => pure !(← anteInvolved ctx ty)
            | none => pure false
          if tyOk then
            ctx.fail s!"goal part closes ante-free (body after binding {b.binderName})"
    let jr := ((← ctx.occRoles.get).get? x.fvarId!)
    -- a binding used only inside records or local bridge proofs is judged in
    -- that regime: its value is walked at the record's role under `recordCtx`
    let jrRec := ((← ctx.recordOccRoles.get).get? x.fvarId!)
    let walkAtUse (v : Expr) : MetaM Unit := do
      match jr, jrRec with
      | some r, _ => walk ctx r neg v
      | none, some r =>
        ctx.recordCtx.modify (·+1); ctx.chainCtx.modify (·+1)
        walk ctx r neg v
        ctx.chainCtx.modify (·-1); ctx.recordCtx.modify (·-1)
      | none, none => walk ctx role neg v
    if vInv then
      if ← auditTrace then IO.eprintln s!"[trace] ante-involved binding {b.binderName} walked @ {((jr.getD (jrRec.getD role))).str}{if jr.isNone && jrRec.isSome then " (record use)" else ""}"
      walkAtUse b.value
    else if propT then
      -- an antecedent-free Prop local is an outside lemma; sorry scan on the value
      if ← auditTrace then do
        let jrs := (jr.map Role.str).getD "unused"
        IO.eprintln s!"[trace] RULE2 have {b.binderName} jr={jrs}"
      if ← reachesSorry ctx b.value then ctx.sorryHit.set true
      if ← bridgeGradeType ctx.env b.binderType then
        -- a local bridge is admitted; flag it if it quotes the goal
        if ← goalShaped ctx b.binderType then
          ctx.flag s!"goal-shaped local bridge (have {b.binderName})"
        -- the shape admission is the floor; the bridge's proof is read at its
        -- use role, with goal-part ablations suspended (it proves the bridge,
        -- not the goal) and content at the flag tier, while a goal part
        -- collapsed inside it is refused and each direction is read as an
        -- implication proof of its own (`directionAblation`), in both modes
        match jr.orElse (fun _ => jrRec) with
        | some r =>
          if r != .side then
            ctx.localProofCtx.modify (·+1)
            walk ctx r neg b.value
            ctx.localProofCtx.modify (·-1)
        | none => pure ()
      else
        match jr with
        | some .goal =>
          ctx.fail s!"bare-Prop local hypothesis {b.binderName} used on goal spine"
        | some .anteArg =>
          ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
          let (prop, data) ← localityOf ctx b.value
          unless prop do
            let note := if data then "" else ", nor on any local variable"
            ctx.severe s!"bare-Prop local hypothesis {b.binderName} feeding ante application is proved without any local hypothesis{note}"
        | some .side => pure ()
        | none =>
          match jrRec with
          | some .goal =>
            -- a side condition of a conditional rewrite: tolerated and recorded
            ctx.flag s!"bare-Prop local hypothesis {b.binderName} used inside a rewrite record or a local bridge's proof"
          | some .anteArg =>
            ctx.flag s!"bare-Prop local hypothesis {b.binderName} feeding ante application"
            let (prop, data) ← localityOf ctx b.value
            unless prop do
              let note := if data then "" else ", nor on any local variable"
              ctx.severe s!"bare-Prop local hypothesis {b.binderName} feeding ante application is proved without any local hypothesis{note}"
          | _ => pure ()
    else
      walkAtUse b.value
end

/-- Split a goal conclusion into its ∧-parts (goal-part support). -/
partial def splitAnd (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    splitAnd (e.getArg! 1) (splitAnd (e.getArg! 0) acc)
  else acc.push e

/-- The ∧-parts of the goal's conclusion (`Ctx.goalParts`). -/
def computeGoalParts (goalType : Expr) : MetaM (Array Expr) := do
  try
    let (_, _, concl) ← forallMetaTelescope goalType
    return splitAnd concl
  catch _ => return #[]
end ProofAudit
end SemantEq
