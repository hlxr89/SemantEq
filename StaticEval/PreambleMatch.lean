import Lean
import StaticEval.Statement

/-!
# Level-2 preamble matching (α-modulo-namespace, partial)

Self-contained support for the shared-preamble context (fix (a), level 2).
Level 1 (`Context.lean`) shares a preamble only when the two sides' CODE
TOKENS are identical. This module implements the exact version of the same
idea on the ELABORATED declarations: two preamble declarations are
interchangeable copies iff they are α-equal after renaming the cand
namespace prefix to the ref one — compared on the finished expression trees,
so comments, whitespace, declaration order, and attribute placement are all
invisible, and NOTHING is ever re-elaborated during matching.

Matching is name-keyed (`StaticEvalCand.<ns>.X` ↔ `StaticEvalRef.<ns>.X`;
renamed declarations deliberately stay unmatched — for `def`s that costs
nothing, they cross namespaces by δ-unfolding; renamed STRUCTURES are level-3
territory) and runs to a FIXPOINT: a declaration matches only if every
pair-local constant it references is itself matched, so the matched set is
dependency-closed by construction (Henry's remove-into-shared-list loop).

Prop-valued content (theorem statements, `_proof_N` auxiliaries) is compared
by TYPE only — proof irrelevance makes same-statement/different-proof copies
interchangeable. Value-carrying defs compare type AND value; inductives
compare type plus every constructor's type.

The second half (`candRemainder`) builds the cand-side REMAINDER source: the
cand preamble text with matched declarations deleted and `open` lines
injected so bare references to matched names resolve to the shared (ref)
copies. The ref side needs no surgery at all — its full preamble IS the
shared block.

Failure anywhere degrades to "no match" / `none`, and the caller falls back
to the legacy two-namespace path — this module can shrink the wall, never
add one.
-/

namespace StaticEval

open Lean Meta

/-- Names minted by the elaborator that never appear in source and are only
meaningful for the matching verdict via the declarations that REFERENCE them
(`_proof_N`, match auxiliaries, …). They participate in matching (a value
referencing an unmatched auxiliary must fail honestly) but are never
declaration CHUNKS of their own in the remainder builder. -/
def isAuxDetail (n : Name) : Bool :=
  n.isInternalDetail || n.hasMacroScopes

/-- Rename every constant under `fromNs` whose STRIPPED name is in `matched`
(plus `self`, for recursive occurrences of the declaration under test) to its
`toNs` counterpart. Constants under `fromNs` NOT in the set are left alone —
so a body referencing an unmatched pair-local constant fails its α-comparison
against the ref body (which references the ref counterpart) honestly. -/
def mapMatchedPrefix (fromNs toNs : Name) (matched : NameSet) (self : Name)
    (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      if fromNs.isPrefixOf n then
        let stripped := n.replacePrefix fromNs .anonymous
        if matched.contains stripped || stripped == self then
          some (.const (toNs ++ stripped) us)
        else none
      else none
    | _ => none

/-- α-comparison of two declaration expressions modulo the matched-set
namespace mapping (annotations stripped, same as statement comparison). -/
def eqModuloNs (fromNs toNs : Name) (matched : NameSet) (self : Name)
    (cand ref : Expr) : Bool :=
  stripAnnotations (mapMatchedPrefix fromNs toNs matched self cand)
    == stripAnnotations ref

/-- Does ONE cand declaration match its same-named ref counterpart, given the
current matched set? Kind must agree; types always compare; values compare
only for value-carrying non-Prop definitions (proof irrelevance covers
theorems and Prop-valued auxiliaries); inductives additionally compare every
constructor's type (field names AND order — reordered fields are genuinely
different constructors and belong to level 3). -/
def declMatches (env : Environment) (candNs refNs : Name) (matched : NameSet)
    (stripped : Name) : MetaM Bool := do
  let candName := candNs ++ stripped
  let refName  := refNs ++ stripped
  let some ci := env.find? candName | return false
  let some ri := env.find? refName | return false
  let eq := eqModuloNs candNs refNs matched stripped
  match ci, ri with
  | .defnInfo c, .defnInfo r =>
    unless eq c.type r.type do return false
    -- Prop-valued defs are proofs: type-only (proof irrelevance)
    if (← Meta.isProp c.type) then return true
    return eq c.value r.value
  | .thmInfo c, .thmInfo r => return eq c.type r.type
  | .axiomInfo c, .axiomInfo r => return eq c.type r.type
  | .inductInfo c, .inductInfo r =>
    unless c.numParams == r.numParams && c.numIndices == r.numIndices
        && c.ctors.length == r.ctors.length && eq c.type r.type do
      return false
    -- constructor names (stripped) and types must line up pairwise
    for (cc, rc) in c.ctors.zip r.ctors do
      unless cc.replacePrefix candNs .anonymous
          == rc.replacePrefix refNs .anonymous do return false
      let some (.ctorInfo cci) := env.find? cc | return false
      let some (.ctorInfo rci) := env.find? rc | return false
      unless eq cci.type rci.type do return false
    return true
  | .ctorInfo _, .ctorInfo _ =>
    -- constructors are matched via their inductive; standalone occurrences
    -- (in the constants map) just mirror that verdict cheaply by type
    let some (.ctorInfo c) := env.find? candName | return false
    let some (.ctorInfo r) := env.find? refName | return false
    return eq c.type r.type
  | .recInfo _, .recInfo _ =>
    -- generated with the inductive: match iff the parent inductive matched
    return matched.contains stripped.getPrefix
  | _, _ => return false

/-- The FIXPOINT matcher: all cand-namespace declarations of `env` (the
throwaway environment holding BOTH elaborated preambles) that are
interchangeable copies of their same-named ref counterparts. Sweeps until no
new matches appear — matches enable matches, and the result is
dependency-closed by construction. Returns the STRIPPED names. -/
def matchPreambles (env : Environment) (candNs refNs : Name)
    : MetaM NameSet := do
  -- collect candidate stripped names: local (map₂) constants under candNs
  let mut cands : Array Name := #[]
  for (n, _) in env.constants.map₂.toList do
    if candNs.isPrefixOf n then
      cands := cands.push (n.replacePrefix candNs .anonymous)
  let mut matched : NameSet := {}
  let mut grew := true
  while grew do
    grew := false
    for stripped in cands do
      unless matched.contains stripped do
        if ← declMatches env candNs refNs matched stripped then
          matched := matched.insert stripped
          grew := true
  return matched

/-! ## The cand-side remainder builder -/

/-- One parsed preamble command. -/
structure PreChunk where
  /-- verbatim source slice of the command -/
  text : String
  /-- stripped declaration name (user-namespace path included) when this is a
  matchable declaration chunk; `none` for scope commands and for declarations
  whose name cannot be read off the syntax (anonymous instances — those stay
  in the remainder, a harmless per-side copy) -/
  name? : Option Name := none
  /-- `some N` when this command is `namespace N` (used for open-injection) -/
  nsPush? : Option Name := none
  /-- number of namespace levels this command closes (`end` chunks) -/
  nsPop : Nat := 0

/-- Parse a preamble into command chunks with declaration names qualified by
the user-namespace path in force at each point. Pure parsing — nothing is
elaborated; `env` only supplies the syntax tables (notations). `none` on any
parse hiccup: the caller falls back to the legacy path. -/
def chunkPreamble (env : Environment) (opts : Options) (pre : String)
    : IO (Option (Array PreChunk)) := do
  try
    let ictx := Parser.mkInputContext pre "<preamble-chunks>"
    let pmctx : Parser.ParserModuleContext := { env := env, options := opts }
    let mut state : Parser.ModuleParserState := {}
    let msgs : MessageLog := {}
    let mut out : Array PreChunk := #[]
    let mut nsPath : Name := .anonymous
    let mut nsStack : List Name := []
    repeat
      let prevPos := state.pos
      let (stx, state', msgs') := Parser.parseCommand ictx pmctx state msgs
      if Parser.isTerminalCommand stx then break
      if msgs'.hasErrors then return none
      state := state'
      let text := (Substring.Raw.mk pre prevPos state.pos).toString
      if stx.isOfKind ``Parser.Command.namespace then
        let n := stx[1].getId
        nsStack := nsPath :: nsStack
        nsPath := nsPath ++ n
        out := out.push { text, nsPush? := some n }
      else if stx.isOfKind ``Parser.Command.end then
        -- pop as many levels as the `end` names components (best effort)
        let n := stx[1].getOptionalIdent?.getD .anonymous
        let levels := if n == .anonymous then 1 else n.getNumParts
        for _ in [0:levels] do
          match nsStack with
          | top :: rest => nsPath := top; nsStack := rest
          | [] => pure ()
        out := out.push { text, nsPop := levels }
      else if stx.isOfKind ``Parser.Command.declaration then
        let name? := do
          let declId ← stx.find? (·.isOfKind ``Parser.Command.declId)
          let raw := declId[0].getId
          guard (raw != .anonymous)
          some (nsPath ++ raw)
        out := out.push { text, name? }
      else
        out := out.push { text }
    return some out
  catch _ =>
    return none

/-- Build the cand-side REMAINDER source: matched declaration chunks deleted,
`open _root_.<refNs>.<path>` injected at the top and after every `namespace`
command so bare references to matched (now shared) names resolve to the ref
copies. Scope commands are all preserved verbatim, so the remainder
elaborates exactly like the original preamble minus the shared content. -/
def candRemainder (refNs : Name) (chunks : Array PreChunk)
    (matched : NameSet) : String := Id.run do
  let mut out := s!"open _root_.{refNs}\n"
  let mut nsPath : Name := .anonymous
  let mut nsStack : List Name := []
  for c in chunks do
    match c.name? with
    | some n =>
      unless matched.contains n do
        out := out ++ c.text
    | none =>
      out := out ++ c.text
      if let some n := c.nsPush? then
        nsStack := nsPath :: nsStack
        nsPath := nsPath ++ n
        out := out ++ s!"\nopen _root_.{refNs ++ nsPath}\n"
      for _ in [0:c.nsPop] do
        match nsStack with
        | top :: rest => nsPath := top; nsStack := rest
        | [] => pure ()
  return out

end StaticEval
