import Lean

/-!
# Restricted proof search (Milestone 4.2)

The strict tier's search engine: library search and structural solving that are
*restricted by construction and by audit* to the antecedent theorem, pure logical
structure, and equality/iff-shaped library facts. The design charter:

* A strict-tier proof may use: the antecedent (that is the point), structural-logic
  constants (intro/elim forms of ∧/∨/↔/∃, congruence, extensionality — carrying no
  mathematical content), and library lemmas whose conclusion is `Eq`/`Iff`/`HEq`/`Ne`
  (rewrite-grade facts). Nothing else — in particular no decision procedures and no
  Prop-conclusioned library facts that could close a goal on their own.
* Restriction happens **during** search wherever the machinery allows it (explicit
  lemma lists for `solveByElim`; a filtering `CandidateFinder` for library search),
  and every produced proof is still audited (`auditProof`) — candidates are checked
  one by one as they stream out of the search, so one unusable proof does not
  discard a direction.

Built on the public pieces of `Lean.Meta.LibrarySearch` (`librarySearchSymm`,
`tryOnEach`, `mkLibrarySearchLemma`, `libSearchFindDecls`, `CandidateFinder`) —
`librarySearch'` itself hard-codes its finder, so its ~30-line body is re-composed
here with our restricted finder. Calling the Meta layer directly also bypasses the
`TryThis` suggestion machinery (which panics on synthetic syntax).
-/

namespace StaticEval

open Lean Meta

/-- Conclusion heads accepted for non-structural library lemmas: rewrite-grade
facts only. -/
def acceptedHeads : List Name := [``Eq, ``Iff, ``HEq, ``Ne]

/-- Ex-falso eliminators — constants whose whole job is `False → C`.

These need an EXPLICIT ban: their types are universe-polymorphic
(`… → C : Sort u`), so `auditProof`'s "only Prop-valued constants are judged"
exemption would grade them admissible as data and skip them silently. They also leave NO `False`-typed
subterm behind (`@absurd a b h hn : b` reduces to `False` only under δ), so the
`False`-typed-node scan cannot see them either. Enforced in `constructsFalse?`
(the polarity-aware term walk — positive position only, 2026-08-16), not in
`auditProof`'s flat constant walk. -/
def exFalsoConstants : NameSet := .ofList [
  ``False.elim, ``False.rec, ``False.casesOn, ``absurd, ``Not.elim
]

/-- Structural-logic constants: intro/elim/projection forms that carry no
mathematical content. SINCE the categorical grading (2026-08-18, adoption item
(b)) the AUDIT no longer consults this list — its one remaining functional use
is `restrictedFinder`'s candidate filter for `restricted exact?`. Kept as the
curated inventory of structural vocabulary; audit admission now comes from the
schematic/eliminator/bridge categories in `auditProof`. -/
def structuralWhitelist : NameSet := .ofList [
  -- ∧ / ∨ / ↔ / ∃ intro & elim
  ``And.intro, ``And.left, ``And.right, ``And.elim, ``And.symm,
  ``Or.inl, ``Or.inr, ``Or.elim, ``Or.symm, ``Or.resolve_left, ``Or.resolve_right,
  ``Iff.intro, ``Iff.mp, ``Iff.mpr, ``Iff.refl, ``Iff.rfl, ``Iff.symm, ``Iff.trans,
  ``Iff.of_eq,
  ``Exists.intro, ``Exists.elim, ``Exists.imp,
  -- P2-2: `Fact.out : Fact p → p` concludes a BARE VARIABLE, so the
  -- restricted finder's Eq/Iff discrimination-tree test rejects it; it is pure
  -- packaging (the inverse of `Fact.mk`), so the finder admits it explicitly.
  -- The AUDIT needs no help — `auditProof` grades variable-conclusioned
  -- constants bridge-grade on its own. Single backtick: `Fact` is Mathlib and
  -- this file imports core Lean only.
  `Fact.out,
  -- propositional eliminators: `cases` on ∃/∨ (small elimination — their
  -- casesOn/rec are Prop-valued, unlike the universe-polymorphic structure
  -- eliminators of ∧/↔ which the non-Prop exemption already covers)
  ``Exists.casesOn, ``Exists.rec, ``Or.casesOn, ``Or.rec,
  ``And.casesOn, ``And.rec, ``Iff.casesOn, ``Iff.rec,
  ``Eq.casesOn, ``Eq.ndrec, ``Eq.rec,
  -- equality plumbing (Eq-conclusioned ones would pass anyway; the eliminators
  -- and cast-like forms would not)
  ``Eq.refl, ``Eq.symm, ``Eq.trans, ``Eq.mp, ``Eq.mpr, ``Eq.subst, ``Eq.substr,
  ``HEq.refl, ``rfl, ``cast, ``eq_of_heq, ``heq_of_eq, ``propext, ``congr,
  ``congrArg, ``congrFun, ``funext,
  -- basic logic
  -- NB `False.elim`/`absurd`/`Not.elim`/`False.rec`/`False.casesOn` are NOT here:
  -- they exist only to turn `False` into an arbitrary goal, which is the
  -- ex-falso route P0 forbids. Exclusion from THIS list has no audit effect
  -- (the audit no longer consults it); the ban lives in `exFalsoConstants` +
  -- `constructsFalse?`.
  ``id, ``True.intro, ``trivial, ``Not.intro,
  ``letFun, ``flip, ``Function.comp,
  -- simp-internal bridging constants (appear in `simp only` proof terms)
  ``of_eq_true, ``of_eq_false, ``eq_true, ``eq_false, ``eq_self_iff_true,
  ``implies_congr, ``forall_congr, ``iff_self, ``Trans.trans,
  -- numeric side-condition dischargers (see `sideConditionLemmas`)
  `le_refl, `zero_le_one, `zero_lt_one, `one_pos, ``Nat.zero_le
]

/-- Numeric side-condition dischargers (D4). Bridge rewrites carry side
conditions (`intervalIntegral.integral_of_le` needs `a ≤ b`, `Nat.cast_sub`
needs `m ≤ n`); these five facts discharge the numeral/reflexivity instances
that block otherwise-pure bridge applications. They are not Eq/Iff-conclusioned,
so they need explicit audit whitelisting — the exposure is minimal: none of them
can relate two statements on its own, `anteUsed` is still required, and the
probe gate still blocks trivial goals. -/
def sideConditionCore : List Name :=
  [`le_refl, `zero_le_one, `zero_lt_one, `one_pos, ``Nat.zero_le]

/-- Monotonicity + membership pack for conditional-cast side goals (M4.4):
`Nat.cast_sub` demands `b ≤ a` (e.g. `2^i ≤ 2^n` from `i < n` via
`i ∈ Finset.Ico 0 n`), `div_eq_iff` demands `≠ 0`. Wide-and-shallow only:
these inflate `solveByElim`'s branching, so they are excluded from the deep
search phase. -/
def sideConditionExtra : List Name :=
  [`le_of_lt, `two_pos, `two_ne_zero, `Nat.one_le_two_pow, `one_le_two,
   `Nat.pow_le_pow_right, `Nat.pow_le_pow_left, `Nat.one_le_iff_ne_zero,
   `Finset.mem_range, `Finset.mem_Icc, `Finset.mem_Ico]

def sideConditionLemmas : List Name := sideConditionCore ++ sideConditionExtra

/-- Transport (in)equalities along local equations (`0 < ↑n` from `↑n = 1` +
`zero_lt_one`). These go ONLY into the main structural solver — inside the
side-condition discharger (invoked on every conditional rewrite) their
metavariable-rich conclusions blow the search up. -/
def eqTransportLemmas : List Name :=
  [`lt_of_lt_of_eq, `lt_of_eq_of_lt]

/-- Curated "basic-manipulation" bridge lemmas (Milestone 4.2, mechanism #3): the
logical/membership/structure plumbing observed across the implication-witness
corpus. All are Eq/Iff-conclusioned (so they'd pass the audit anyway); this list
exists to *drive* search and normalization, not merely to permit. Grouped by role;
expect one tuning pass against the witness corpus. -/
def plumbingLemmas : Array Name := #[
  -- logic / negation plumbing
  -- M4.7: `not_forall`/`not_not` were listed as bare names, but Mathlib only
  -- `export`s them from `Classical` — an export is a resolution alias, NOT a
  -- declaration, so `env.contains` was false and `normalizationContext`'s
  -- guard silently DROPPED both. Verified by running Lean:
  --   not_forall/not_not -> contains=false ;  Classical.* -> contains=true
  -- Consequence until now: `¬∀` and double negation were never normalized.
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

/-- **M4.4 master toggle — OFF.** Carrier lifting (zify/qify/rify), the
transport bridge layer, pair-local delta unfolding, the conditional-cast
discharger, and the deep finisher phase stack. Verdict from the M4.4
validation: on the 14 catalogued transport pairs these produced **zero** new
closes (the survey's four "clean" targets each need one further mechanism —
numeral-case analysis for Imo2019P4, injection-term synthesis for
putnam_1965_b3/1971_a1), while costing ~3x runtime and ~2x peak memory on
failing directions, which dominate real batches. The code stays in the tree,
tested and documented, behind this flag; flip to `true` together with the
mechanisms in docs/ProofPatterns.md §M4.4 and re-run the gates.

Kept ON regardless (they are fixes, not features): capped-phase state
rollback, the loop-lemma exclusions, and the normal-form layering discipline
(the base normalize attempt never sees transport lemmas). -/
def enableM44Transport : Bool := false

/-- M4.4 carrier-transport bridges (from the transport-pair witness survey).
Kept OUT of `plumbingLemmas`: they change the normalization normal form, and
the base normalize attempt must stay bit-stable with the D4-era behavior — the
transport layer rides in SEPARATE ladder attempts (transport-normalize and the
carrier lifts). Known loop pairs excluded: `Finset.sum_Ico_eq_sum_range`
(loops with `range_eq_Ico`), `Int.natCast_pos` (inverts zify's `natCast_lt`). -/
def transportLemmas : Array Name := #[
  -- subtype ↔ bounded quantifier
  `Subtype.exists, `Subtype.forall, `SetCoe.exists, `SetCoe.forall,
  -- Set ↔ Finset / ncard ↔ card
  `Set.ncard_coe_finset, `Set.ncard_eq_toFinset_card, `Set.Finite.mem_toFinset,
  `Set.Finite.coe_toFinset, `Finset.coe_nonempty, `Finset.mem_coe,
  -- Infinite encodings + set-literal membership
  `Set.infinite_coe_iff, `Set.mem_insert_iff,
  -- Finset index reindexing
  `Finset.Ico_add_one_right_eq_Icc, `Nat.add_sub_cancel,
  -- ℤ/ℕ pointwise inverses and coprimality
  `Int.toNat_of_nonneg, `Int.toNat_natCast,
  `Nat.isCoprime_iff_coprime, `Nat.coprime_comm,
  -- division packaging
  `one_div_mul_eq_div, `mul_one_div, `div_eq_iff
]

/-- Is `n` a theorem-like constant whose conclusion head is Eq/Iff-shaped? -/
def eqIffConclusioned (n : Name) : MetaM Bool := do
  let some info := (← getEnv).find? n | return false
  -- P2-0: check the PLAIN head first — `forallTelescopeReducing` unfolds
  -- `Ne a b` into `a = b → False` and telescopes the arrow, leaving head
  -- `False`, so the `` `Ne `` entry in `acceptedHeads` was dead code (measured:
  -- `ne_of_gt`, `Ne.symm`, and the `zero_ne_one` P2 extractor all rejected).
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
variables)? Concrete-pattern equations (`Real.sign 0 = 0`, `catalan 2 = 2`, …)
rewrite bare numerals/constants into decorated forms — numerology that floods
the discovery budget and can never be a packaging bridge. -/
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
    -- M4.7: a variable-free side is numerology ONLY when it is data-typed
    -- (`Real.sign 0 : ℝ`, `catalan 2 : ℕ`). A variable-free PROP side is logical
    -- plumbing — `Bool.false_eq_true : (false = true) = False` is the bridge for
    -- the Bool/Prop drift class (`… → false = true` vs `¬…`), and this filter was
    -- silently blocking it (measured: the Artin 6_4_12 quadruplet had NO closing
    -- arm at all). No flooding risk: the discrimination tree only surfaces a
    -- lemma when the probe CONTAINS its concrete side as a subterm, so
    -- `false = true`-style keys match drift statements and nothing else.
    return !(← isProp side)

/-- **(b) 2026-08-16 — categorical grading.** Core logical vocabulary for the
schematic test, ported from `ProofAudit.coreLogic` (whose doc marks it as
superseding `structuralWhitelist`). A constant whose TYPE is built solely from
sorts, variables and these heads is a tautology schema — it cannot carry
domain content. -/
def coreLogic : NameSet := .ofList
  [``Eq, ``HEq, ``Iff, ``And, ``Or, ``Not, ``Ne, ``Exists, ``True, ``False]

/-- Namespace closure (checker Plan A #2): `Exists.intro`, `Or.inl`,
`And.casesOn`, … belong to core logic by their ROOT, so constructor/eliminator
mentions inside a core-logic type do not break schematicity. -/
def coreLogicName (c : Name) : Bool :=
  coreLogic.contains c || coreLogic.contains c.getRoot

/-- Is this TYPE a pure logical schema? Allowed: sorts, bound/free variables,
Pi/lambda, and applications headed by a variable or a core-logic constant.
(Ported verbatim from `ProofAudit.schematicType`.) -/
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

/-- A genuine eliminator — a real recursor, or an elim-suffix-named constant
whose PLAIN conclusion is variable-headed (a motive). Ported from
`ProofAudit.isEliminatorConst`. -/
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

/-- Process-global admissibility memo for `auditProof`'s constant grading.
SOUND as a global: grading only ever runs on MODULE-level constants (env-local
constants are expanded, never judged), whose types and class-ness are fixed by
the import set — identical in every pair env of a batch. This is where (b)
buys its efficiency: the isProp + telescope grading used to be recomputed per
accepted candidate, per pair, with no memo at all. -/
initialize auditGradeCache : IO.Ref (Lean.NameMap Bool) ← IO.mkRef {}

/-- AUDIT v2 (strict tier). Walk the proof's used constants, expanding every
environment-local constant (tactics hide dependencies in `_proof_1`-style
auxiliaries). Accept iff the antecedent is reached, and every OTHER used
constant grades admissible — categorically since (b) 2026-08-16: non-Prop
(defs, instances, recursors) / eliminator / logically schematic / bridge
(Eq-Iff-HEq-Ne, class-headed, or variable-conclusioned — `Fact.out`) / the
retained ~18-name side-condition pack (adoption item (d) proposes retiring
it; still consulted). The
name-list whitelist (`structuralWhitelist` + plumbing/transport packs) is no
longer consulted here; categories over whitelists (checker blueprint). Returns
`none` on acceptance, or a rejection reason. -/
partial def auditProof (ante : Name) (proof : Expr) (assumed : NameSet := {})
    : MetaM (Option String) := do
  -- ABLATION A2 (2026-08-21): categorical proof audit off — accept any proof.
  if (← IO.getEnv "STATIC_EVAL_NO_PROOFAUDIT").isSome then return none
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
    -- P0 NOTE (2026-08-16): the `exFalsoConstants` ban used to live here as an
    -- unconditional reject. It moved into `constructsFalse?`, the polarity-aware
    -- term walk, where it fires only in positive position — this flat walk has
    -- no notion of polarity and rejected honest ¬-goal proofs that end in
    -- `absurd … hn` under their intro binder. Every acceptance site that runs
    -- `auditProof` must therefore also run `exFalsoVacuous?` (proveGoal's strict
    -- chain does; the streamed exact?/apply? sites below do too).
    -- M4.8 Fix 1 (STATIC_EVAL_TRUST_PREAMBLE): a user-named preamble theorem is
    -- an ASSUMED fact — like the antecedent, its sorry is sanctioned; do NOT
    -- look through it (its value reaches sorryAx by design). Internal-detail
    -- auxiliaries (`_simp_N`, `_proof_N`) are NEVER in this set — they must
    -- still be expanded, or the audit grows a laundering blind spot.
    if assumed.contains c then
      continue
    if (env.getModuleIdxFor? c).isNone then
      -- env-local auxiliary: look through it rather than judging it. The elab env
      -- may not carry its value (async/private outlining — e.g. simp's
      -- conditional-rewrite proofs land in `_private.….0._simp_n` auxiliaries with
      -- `value? = none`), so resolve through the kernel environment, exactly like
      -- `#print axioms` does; otherwise the walk dead-ends and both antecedent
      -- usage and sorry leakage hide behind the auxiliary.
      let info? := env.toKernelEnv.find? c <|> env.find? c
      if let some v := info?.bind (·.value?) then
        queue := v.getUsedConstantsAsSet.toList ++ queue
      continue
    -- (b) 2026-08-16: memoized categorical grading. Chain: non-Prop exemption →
    -- eliminator → schematic → plain-then-reducing bridge (P2-0: Ne survives
    -- the plain pass; variable-headed conclusions are bridge-grade — `Fact.out`,
    -- `Trans.trans` — matching `ProofAudit.bridgeGradeType`) → residual
    -- side-condition pack. Memo hit skips all of it.
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
            else do
              let plainOk ← forallTelescope info.type fun _ concl =>
                pure (match concl.getAppFn with
                  | .const head _ => acceptedHeads.contains head
                  | .fvar _ => true
                  | _ => false)
              if plainOk then pure true else do
                let red ← forallTelescopeReducing info.type fun _ concl => do
                  match concl.getAppFn with
                  | .const head _ =>
                    if acceptedHeads.contains head || isClass env head then return true
                    -- abbrev-wrapped class conclusions (`NoetherianSpace : Prop :=
                    -- WellFoundedGT (Opens α)`): the head is an abbrev, not the
                    -- class — `Meta.isClass?` unfolds reducibles and finds the
                    -- class underneath (audit FP, `Finite.to_noetherianSpace`)
                    return (← Meta.isClass? concl).isSome
                  | .fvar _ => return true
                  | _ => return false
                if red then pure true
                -- the ~18 Prop, non-schematic, non-Eq/Iff side-condition
                -- dischargers — the one residual name list ((d) proposes retiring it; still consulted)
                else pure (sideConditionLemmas.contains c
                  || eqTransportLemmas.contains c)
          else pure true
        auditGradeCache.modify (·.insert c b)
        pure b
    unless ok do
      return some s!"uses non-Eq/Iff library fact {c}"
  unless anteUsed do
    return some "antecedent unused"
  return none

/-- P0 (strict): does the proof CONSTRUCT a term of type `False`?

A faithful correspondence TRANSPORTS the antecedent's content into the goal. It
may transplant an existing negation — hand over a term of type `¬Q`, after
rewriting it into shape — but it never needs to REBUILD one by
`intro q; <derive False>`. Whenever two faithfully-equivalent statements differ
under a negation, their negated bodies are Iff-equivalent, and that Iff is
exactly a rewrite bridge, so the transport route always exists in principle.

Constructing a `False` is therefore the signature of logical RE-DERIVATION
rather than structural transport — and, when the antecedent is self-
contradictory, of ex-falso vacuity (a contradictory antecedent proves anything).
Henry's rule (2026-07-28): never accept a strict close that closes a goal from a
constructed `False`, wherever the `False` came from. This replaces the earlier
provenance-tracking version, whose bookkeeping mislabelled goal-introduced
hypotheses as antecedent-derived and rejected faithful proofs (finding F1).

**This does NOT reject negation GOALS.** `¬Q` unfolds to `Q → False`, so its
TYPE mentions `False`; but a term of type `¬Q` is not a term of type `False`.
Transplant-style closes carry no `False`-typed subterm and pass untouched — e.g.
`Exists.intro w ⟨right, left⟩` for the And-comm pair (verified equivalent), and
the rewrite-then-transplant proofs `normalize + structural` produces.

POLARITY REFINEMENT (2026-08-16, ported from the checker's `negBump` /
`checkFalseNode`, `ProofAudit.lean`): an honest proof of a ¬-shaped goal IS
`intro q; derive False` — that `False` is the goal's own content, not a
re-derivation, and the unconditional rule rejected it (measured cost: 4 PNV
pairs — t0010/t1448 Munkres 29.4, v0650/v2178 Putnam B3 — plus v1847's
single-arm fragility). The walk now carries a negation depth `neg`: entering a
lambda whose body proves `False` bumps it, and all rejections fire only at
`neg == 0` (positive position).

Binder-participation refinement: the bump requires the intro'd hypothesis to
actually OCCUR in the `False`-derivation (`hasLooseBVar 0`). An honest ¬-proof
consumes `q`; an ex-falso-vacuous proof (self-contradictory antecedent closing
an unrelated ¬-goal) ignores it — its body is then a `False`-typed node at
`neg = 0` and is rejected at the root of the derivation. This is the
contradictory-ante-vs-¬-goal trap (`trap:exfalso:contra_ante_neg_goal`).

The `exFalsoConstants` ban lives HERE now (moved 2026-08-16 out of
`auditProof`'s flat constant walk, where polarity does not exist): `absurd` /
`False.elim` & co. are rejected only in positive position — an honest ¬-proof
may legitimately end in `absurd (transported q) hn` under its binder. Env-local
auxiliaries (`_simp_N`, `_proof_N`) are expanded with the ambient polarity
carried down (kernel-env fallback, same discipline as `auditProof`) so an
`absurd` buried inside an auxiliary referenced at positive position is still
caught; expansion is deduplicated per (constant, polarity-class) via
`visited = (seen at neg 0, seen at neg > 0)`. -/
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
    if (env.getModuleIdxFor? c).isNone then
      let (seenPos, seenNeg) ← visited.get
      let seen := if neg == 0 then seenPos.contains c else seenNeg.contains c
      unless seen do
        visited.modify fun (p, n) =>
          if neg == 0 then (p.insert c, n) else (p, n.insert c)
        let info? := env.toKernelEnv.find? c <|> env.find? c
        if let some v := info?.bind (·.value?) then
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
    -- a lambda's own type is a Pi, never `False`; only its body can be one.
    -- negBump with binder participation: descend at `neg + 1` iff the body
    -- proves `False` AND the binder occurs in it (checked on the raw body,
    -- before instantiation).
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

/-- P0 (precision): reject a strict close that closes its goal from a
constructed `False` in positive position. Runs only on otherwise-accepted
strict closes. See `constructsFalse?`; the antecedent is not consulted
(deliberately — provenance tracking is what finding F1 broke). -/
def exFalsoVacuous? (_ante : Name) (proof : Expr) : MetaM (Option String) := do
  -- ABLATION A3 (2026-08-21): P0 polarity / ex-falso audit off.
  if (← IO.getEnv "STATIC_EVAL_NO_P0").isSome then return none
  let visited ← IO.mkRef (({} : NameSet), ({} : NameSet))
  let r ← constructsFalse? visited 0 proof
  if r.isSome then
    if (← IO.getEnv "STATIC_EVAL_P0_TRACE").isSome then
      IO.eprintln s!"[p0-trace] REJECTED proof term:\n{← Meta.ppExpr proof}"
  return r

/-- SET the heartbeat budget for `x` (option units), regardless of ambient — a
deliberate, bounded policy exception for the recursion-heavy closers whose
phase stack cannot fit the default per-attempt budget. -/
def withHeartbeatBudget (n : Nat) (x : MetaM α) : MetaM α := do
  let now ← IO.getNumHeartbeats
  withTheReader Core.Context
    (fun c => { c with initHeartbeats := now, maxHeartbeats := n * 1000 }) x

/-- Run `x` under a local heartbeat budget, in `maxHeartbeats`-option units
(1 unit = 1000 raw heartbeats; the ladder's per-attempt budget is 50000). A
search phase that detonates on a pathological unification then costs a bounded
slice of the attempt budget, not all of it. Runtime exceptions (deterministic
timeouts) are converted to `false`. -/

def withHeartbeatCap (n : Nat) (x : MetaM Bool) : MetaM Bool := do
  let now ← IO.getNumHeartbeats
  let ctx ← readThe Core.Context
  -- never EXTEND the ambient budget: the cap is min(requested, remaining)
  let remaining :=
    if ctx.maxHeartbeats == 0 then n * 1000
    else ctx.maxHeartbeats - (now - ctx.initHeartbeats)
  let budget := min (n * 1000) remaining
  tryCatchRuntimeEx
    (withTheReader Core.Context
      (fun c => { c with initHeartbeats := now, maxHeartbeats := budget }) x)
    (fun _ => pure false)

/-- Lemma set for the structural `solveByElim`. Deliberately narrow: the antecedent
plus extensionality bridges with `Eq`-shaped conclusions. Star-conclusioned
projections (`And.left`, `Iff.mp`, …) must NOT go here — their conclusions are bare
metavariables that unify with every goal, and backward search over them explodes
exponentially (observed: every attempt burning its full heartbeat budget).
Destructuring is done by hypothesis saturation instead; the antecedent's iff
directions are covered by the restricted search's `(ante, .mp/.mpr)` candidates. -/
def structuralSolveLemmas (ante : Name) : List Name :=
  [ante, ``Subtype.ext, ``Prod.ext] ++ sideConditionCore
    ++ (if enableM44Transport then sideConditionExtra ++ eqTransportLemmas else [])

/-- The wide-only additions: excluded from the deep (depth-16) `solveByElim`
phase, whose exponential branching cannot afford generic-headed lemmas. -/
def wideOnlyLemmas : List Name := sideConditionExtra ++ eqTransportLemmas

/-- The strict machinery's lemma list WITHOUT the antecedent: what the vacuity
probe and the counterfactual replays are allowed to use. -/
def noAnteLemmas : List Name :=
  [``Subtype.ext, ``Prod.ext] ++ sideConditionCore
    ++ (if enableM44Transport then sideConditionExtra ++ eqTransportLemmas else [])

/-- D4 replumbing variants: packaging-only transforms of a proof term, pushed
under its ∀-telescope — `Eq.symm`/`Iff.symm`/`Ne.symm` flips, `Iff.mp`/`Iff.mpr`
and `And.left`/`And.right` projections. `saturateHyps` destructures only at the
TOP level of a hypothesis; a quantified hypothesis (`∀ x, P x ∧ Q x`,
`∀ x, f x = g x`) hides its structure under the binders, which is exactly the
shape of the one-token `.symm`/`.1` witness proofs the strict tier missed.
Projections recurse (they strictly reduce structure); flips do not (symm∘symm
would loop). Everything is built from the term plus `Eq.symm`/`Iff.mp`-grade
logical plumbing, which the categorical audit grades schematic/eliminator, so
the variants are audit-safe by construction. -/
partial def plumbVariants (e : Expr) (maxOut : Nat := 12) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  let mut queue : Array Expr := #[e]
  while !queue.isEmpty && out.size < maxOut do
    let cur := queue.back!
    queue := queue.pop
    let ty ← inferType cur
    let (flips, projs) ← forallTelescope ty fun xs body => do
      let app := mkAppN cur xs
      let mut flips : Array Expr := #[]
      let mut projs : Array Expr := #[]
      match body.getAppFn.constName?.getD .anonymous with
      | ``Eq =>
        flips := flips.push (← mkAppM ``Eq.symm #[app])
        -- Eq of sets / of functions: expose the pointwise content via the
        -- Iff-conclusioned plumbing bridges (recursion then gives the .mp/.mpr
        -- of the pointwise iff under the new binder)
        let args := body.getAppArgs
        if args.size == 3 then
          let bridge? : Option Name :=
            if args[0]!.getAppFn.constName?.getD .anonymous == `Set then
              some `Set.ext_iff
            else if args[0]!.isForall then
              some `funext_iff
            else none
          if let some bridge := bridge? then
            if (← getEnv).contains bridge then
              try
                projs := projs.push
                  (← mkAppM ``Iff.mp #[← mkConstWithFreshMVarLevels bridge, app])
              catch _ => pure ()
      | ``Ne => flips := flips.push (← mkAppM ``Ne.symm #[app])
      | ``Iff =>
        flips := flips.push (← mkAppM ``Iff.symm #[app])
        projs := projs.push (← mkAppM ``Iff.mp #[app])
        projs := projs.push (← mkAppM ``Iff.mpr #[app])
      | ``And =>
        projs := projs.push (← mkAppM ``And.left #[app])
        projs := projs.push (← mkAppM ``And.right #[app])
      | _ => pure ()
      let flipTerms ← flips.mapM (mkLambdaFVars xs ·)
      let projTerms ← projs.mapM (mkLambdaFVars xs ·)
      return (flipTerms, projTerms)
    out := out ++ flips ++ projs
    queue := queue ++ projs
  return out.shrink maxOut

/-- Assert the replumbing variants of every Prop hypothesis into the goal's
context (capped), so saturation and `solveByElim` see the under-binder structure.
Hypotheses produced here are consequences of existing ones — no new content. -/
def assertVariants (g : MVarId) (cap : Nat := 24) : MetaM MVarId := do
  -- most recent hypotheses first: the asserted antecedent sits at the end of the
  -- context and must not lose its variant budget to the goal's own hypotheses
  let hyps := (← g.getNondepPropHyps).reverse
  let mut g := g
  let mut n := 0
  for fv in hyps do
    if n ≥ cap then break
    let vs ← try g.withContext (plumbVariants (mkFVar fv)) catch _ => pure #[]
    for v in vs do
      if n < cap then
        try
          let ty ← g.withContext (inferType v)
          g ← g.assert ((`h_plumb).appendIndexAfter n) ty v
          let (_, g') ← g.intro1P
          g := g'
          n := n + 1
        catch _ => pure ()
  return g


/-- Saturate the local context: destructure every hypothesis whose head is
`And`/`Exists`/`Iff`/`Or` (the `obtain`/`rcases` shapes of the witness corpus).
`Or` branches multiply the goals; everything else just enriches the context. -/
partial def saturateHyps (g : MVarId) (fuel : Nat := 12) : MetaM (List MVarId) := do
  if fuel == 0 then
    return [g]
  let target? ← g.withContext do
    for h in ← getLCtx do
      unless h.isImplementationDetail do
        let head := (← whnfR h.type).getAppFn.constName?.getD .anonymous
        if head == ``And || head == ``Exists || head == ``Iff || head == ``Or then
          return some h.fvarId
    return none
  match target? with
  | none => return [g]
  | some fvarId =>
    let subs ← g.cases fvarId
    let mut acc := []
    for s in subs do
      acc := acc ++ (← saturateHyps s.mvarId (fuel - 1))
    return acc

/-- Run `solveByElim` restricted to an explicit lemma list (+ local hypotheses and
the harmless defaults `rfl`/`trivial`/`congrFun`/`congrArg`). Restricted by
construction: no library search happens here. Returns the remaining goals. -/
def structuralSolve (lemmaNames : List Name) (goals : List MVarId)
    (maxDepth : Nat := 16) (transparency? : Option TransparencyMode := none)
    (constructor : Bool := true) : MetaM (List MVarId) := do
  let cfg : SolveByElim.SolveByElimConfig :=
    { maxDepth, exfalso := false, symm := true, commitIndependentGoals := true,
      transparency := transparency?.getD (← getTransparency), constructor }
  let adds : List Term := lemmaNames.map fun n => mkIdent n
  let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet false false adds [] #[]
  SolveByElim.solveByElim cfg lemmas ctx goals

/-- **R8' (2026-08-19) — delayed-instance ante application.** The defeq-through-
packaging class (t1354: `[(H.subgroupOf K).Characteristic]` in context vs the
ante's `[(comap K.subtype H).Characteristic]` binder — `subgroupOf` IS that
comap by definition) fails on one fixed point: `synthInstance` matches at
reducible transparency and never unfolds a plain `def`, so apply-side instance
synthesis cannot see the repackaged local instance. Core `ApplyConfig`'s
`allowSynthFailures := true` turns failed instance binders into GOALS, and the
ordinary structural finisher — which unifies at default transparency — closes
them from the context (`assumption`-grade for the instances; reassembly for
Prop arguments; side goals exactly like the rw arms' `r.mvarIds`). Probe- and
harness-verified on t1354's open direction. Audit surface: none — the proof
term is the ante applied to context material; the strict chain (auditProof,
P0, essential-use) applies unchanged. -/
def applyDelayedInstance (goalType : Expr) (ante : Name) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let (_, g) ← root.mvarId!.intros
    let f ← mkConstWithFreshMVarLevels ante
    let goals ← g.apply f (cfg := { allowSynthFailures := true })
    let rem ← structuralSolve (structuralSolveLemmas ante) goals
    unless rem.isEmpty do
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- **P2 (M4.9).** Curated instance-plumbing moves, PACK column: constructors
that BUILD an instance of the keyed class from hypotheses/instances in scope.
Two names per row, nothing more; the table grows only when a measured miss
demands a row. Every constructor is class-headed, so AUDIT v2's class escape
admits it with no whitelist change (measured). Single-backtick names: Mathlib
constants, this file imports core only — an absent constant simply never
elaborates and the move fails closed. -/
def instancePackMoves : List (Name × Name) := [
  (`Nontrivial,          `nontrivial_of_ne),
  (`Fintype,             `Fintype.ofFinite),
  (`Fact,                `Fact.mk),
  (`MulDistribMulAction, `MulDistribMulAction.compHom)
]

/-- P2 UNPACK column: extractors producing a PROP fact from ambient instances,
keyed by the fact's head. `Fact.out` is not listed — its conclusion is a bare
variable, so it is attempted generically (it self-guards via `[Fact _]`
synthesis). `zero_ne_one` needs the P2-0 plain-head fix to pass the audit. -/
def propUnpackMoves : List (Name × Name) := [
  (`Ne, `zero_ne_one),
  (`Ne, `one_ne_zero)
]

/-- **R1 (2026-08-18) — generated packaging index.** The environment's PACKAGING
LEMMAS: theorems/defs whose conclusion head is a class but which are NOT
registered instances (`Fintype.ofFinite`, `nontrivial_of_ne`,
`MulDistribMulAction.compHom`, …) — the converters between hypothesis-form and
instance-form facts, which rewrite discovery cannot see (implication-
conclusioned) and `synthInstance` never consults. Generalizes the 4-row
`instancePackMoves` table to the whole import. Keyed by conclusion class head.

Admissibility (grind's `checkCoverage` idea as an index-admission test):
≤ 6 binders, and every non-instance binder either OCCURS in the conclusion
(so unification determines it) or is a Prop (fillable from locals by
`tryCuratedMove`'s pass 1). Built once per process on first use — class-heads
and binder shapes are fixed by the import set, so a global cache is sound
(same argument as `auditGradeCache`). -/
initialize packIndexCache : IO.Ref (Option (Lean.NameMap (Array Name))) ← IO.mkRef none

def buildPackIndex : MetaM (Lean.NameMap (Array Name)) := do
  let env ← getEnv
  -- BASE-ONLY (Henry, 2026-08-18 — measured decision): the coverage check is
  -- dropped. The three gates are: class-headed conclusion, not a registered
  -- instance, ≤ 6 NON-INSTANCE binders (instance binders are synthesized, not
  -- searched — counting them excluded `compHom`, 8 binders / 4 real).
  -- Constructors are admitted (`Fact.mk` is `ctorInfo`); monster class
  -- constructors (`Group.mk`) fall to the binder cap. The ~110 unpinnable-
  -- binder lemmas coverage would trim are defused at use time by the per-head
  -- try cap and the R1(b) failure memo. Measured scan cost: ~2s once per
  -- process (pass 1 sweep ~1.95s; the rest ~150ms).
  let pre ← IO.mkRef (#[] : Array (Name × Name))
  env.constants.forM fun c info => do
    if c.isInternal then return ()
    if (env.getModuleIdxFor? c).isNone then return ()
    match info with
    | .thmInfo _ | .defnInfo _ | .ctorInfo _ =>
      -- count leading NON-INSTANCE binders; grab the conclusion head — all
      -- syntactic, no Meta
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

def getPackIndex : MetaM (Lean.NameMap (Array Name)) := do
  match ← packIndexCache.get with
  | some idx => return idx
  | none =>
    let idx ← try buildPackIndex catch _ => pure {}
    packIndexCache.set (some idx)
    return idx

/-- **R1(b) (2026-08-18) — pack memos.** Keys are `head|pp(classType)` strings:
binder user-names are stable across an arm's rebuilds (every arm intros the
same statement), so the pp of a demanded class type (`Fintype G`) identifies
the demand across all arms of a pair. NOT sound across pairs — `Driver`
clears both refs per pair. `packFailCache`: demands where every mover failed —
skip the whole construction next time (the measured +10-20% was this exact
lookup re-running per arm on failing directions). `packRecipeCache`: demand →
the mover that worked — replayed first, one application instead of a search.
Known accepted risk: a failure memo'd in one arm suppresses retries in arms
whose REWRITTEN hypotheses might have enabled the pack; pack material (raw
`Finite G` / `φ` hypotheses) is rarely what arms rewrite. -/
initialize packFailCache : IO.Ref (List String) ← IO.mkRef []
initialize packRecipeCache : IO.Ref (List (String × Name)) ← IO.mkRef []
/-- Per-`forwardInstantiate`-call collection of pack-constructed instances
(type × value, valid in that goal's context) for assert-based sharing. -/
initialize packBuiltRef : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

def packKey (mTy : Expr) : MetaM String := do
  let head := mTy.getAppFn.constName?.getD .anonymous
  return s!"{head}|{← ppExpr mTy}"

/-- R1 pack-construction depth: maximum converter-NESTING levels
(`STATIC_EVAL_PACK_DEPTH`, default 2 — level 2 is `compHom` needing
`ofFinite` for its own instance binder). Each extra level multiplies worst-case
attempts by the per-head cap (8), so raise only with a measured pair in hand.
Read once per process. -/
initialize packDepthRef : IO.Ref (Option Nat) ← IO.mkRef none

def packDepthMax : MetaM Nat := do
  match ← packDepthRef.get with
  | some n => return n
  | none => do
    let n := match ← IO.getEnv "STATIC_EVAL_PACK_DEPTH" with
      | some s => s.toNat?.getD 2
      | none => 2
    packDepthRef.set (some n)
    return n

/-- **P2.** Try ONE curated move to construct a term of type `ty`: elaborate the
mover, unify its conclusion with `ty`, then fill its arguments — PROP arguments
FIRST from `locals` (their types usually determine the data arguments:
`nontrivial_of_ne`'s `h : x ≠ y` fixes `x` and `y` by unification), then
instance arguments by synthesis, then remaining data arguments from `locals`.
R1 (2026-08-18): depth 2 — a mover's own failed INSTANCE argument may recurse
ONCE into the packaging index (`Fintype.ofFinite` feeding `compHom`'s
`[Fintype G]`, the cw:02 nesting); `depth` guards the recursion. -/
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
              let hit ← try isDefEq a l catch _ => pure false
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
            -- R1: synthesis failed for a mover's own instance binder — recurse
            -- into the packaging machinery (curated rows first, then the
            -- generated index), up to `packDepthMax` nesting levels (default 2).
            let mut filled := false
            if depth + 1 < (← packDepthMax) then
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
              let hit ← try isDefEq a l catch _ => pure false
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
metavariable binder from the local candidates (instances by synthesis), DFS with
a shared defeq budget. -/
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
      -- **P2-1 (M4.9).** Synthesis failed; the blocked binder selects itself
      -- and its type is already concrete (earlier binders are unified).
      -- (a) HYPOTHESIS PROMOTION: a local whose type IS the needed class
      -- instance, written as a plain hypothesis (`(h : Nontrivial R) → …`) —
      -- invisible to `trySynthInstance`, which consults instance-marked locals
      -- only. Same backtracking discipline as the data loop below.
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
      -- (b) CURATED CONSTRUCTION: build the instance from context material
      -- (`nontrivial_of_ne 0 1 hR`, `Fintype.ofFinite`, `compHom G φ`, …).
      let head := mTy.getAppFn.constName?.getD .anonymous
      let key ← packKey mTy
      -- R1(b): a demand every mover already failed — skip the whole search
      if (← packFailCache.get).contains key then
        return false
      let record (mover : Name) (v : Expr) : MetaM Unit := do
        packRecipeCache.modify ((key, mover) :: ·)
        packBuiltRef.modify (·.push (mTy, v))
      -- R1(b): recipe replay — the mover that worked for this demand before
      if let some (_, mover) := (← packRecipeCache.get).find? (·.1 == key) then
        if let some v ← tryCuratedMove budget locals mover mTy then
          if ← isDefEq m v then
            packBuiltRef.modify (·.push (mTy, v))
            return ← fillFromLocals budget locals ms infos (i + 1)
      for (h, mover) in instancePackMoves do
        if h == head then
          if let some v ← tryCuratedMove budget locals mover mTy then
            if ← isDefEq m v then
              record mover v
              return ← fillFromLocals budget locals ms infos (i + 1)
      -- R1 (2026-08-18): the generated packaging index — same move, every
      -- admissible Mathlib packaging lemma for this class head (curated rows
      -- above keep first shot; per-head try cap bounds the cost).
      if let some cands := (← getPackIndex).find? head then
        for j in [0:min 8 cands.size] do
          if let some v ← tryCuratedMove budget locals cands[j]! mTy then
            if ← isDefEq m v then
              record cands[j]! v
              return ← fillFromLocals budget locals ms infos (i + 1)
      packFailCache.modify (key :: ·)
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
  -- **P2-2 (M4.9).** No local supplies this argument. If it is a PROP, try the
  -- unpack extractors: the fact may be derivable from an ambient INSTANCE the
  -- goal side carries in the other packaging (`0 ≠ 1` from `[Nontrivial R]`
  -- via `zero_ne_one`; any `p` from `[Fact p]` via `Fact.out`, which
  -- self-guards through its own instance synthesis).
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

/-- **R3 (2026-08-19) — e-match forward instantiation (adapter).**
Replaces `forwardInstantiate`'s flat locals-loop with grind's e-matcher, used
STRICTLY as a matching subroutine: internalize the goal (local ∀-Prop
hypotheses — the ante above all — auto-promote to e-match theorems), register
the top-K pool bridges as Eq theorems (demand-driven equality injection:
round 1 instantiates a bridge into the e-graph, round 2 matches the ante
THROUGH the merged classes), run bounded `ematch'` rounds, and harvest the
instantiations from the goal's `newRawFacts` queue as (prop, proof) pairs.
Grind's own engine (`solve`, splits, `byContradiction`) is never entered; its
state is discarded.

v1 extraction split: a harvested proof that mentions `Lean.Grind`-namespace
plumbing (grind-internal casts — the Prop-slot-transport "case 2") is DROPPED
and counted (`ematchCase2Drops`); everything else is re-checked in OUR MetaM
and asserted by the caller with ordinary terms. Bridges therefore never enter
an asserted proof silently: case-1 facts are ante-applied-to-context terms;
case-2 facts wait for the v2 explicit-transport step, gated on this counter. -/
initialize ematchCase2Drops : IO.Ref Nat ← IO.mkRef 0
/-- R3: the current direction's ante DECL name. Local-hypothesis auto-promotion
in grind silently skips type-polymorphic hypotheses (measured: `∀ {S : Type*}
[CommRing S] …` never gets a pattern), which is the typical PNV ante shape —
so the adapter registers the ante's top-level declaration as an explicit
e-match theorem (kind `.default`, same as `grind [decl]`), where polymorphic
patterns work. -/
initialize ematchAnteRef : IO.Ref (Option Name) ← IO.mkRef none
/-- R3 diagnostics: e-match theorem registrations that failed (was a silent
`catch` — a failure here means the ante/bridge contributes nothing). -/
initialize ematchThmFails : IO.Ref Nat ← IO.mkRef 0


open Lean.Meta.Grind in
def ematchInstantiate (g : MVarId) (bridges : Array (Name × Bool))
    (rounds : Nat := 2) (maxFacts : Nat := 8) : MetaM (Array (Expr × Expr)) := do
  let config : Grind.Config := { revert := false }
  let params ← Grind.mkOnlyParams config
  let prios ← getGlobalSymbolPriorities
  let mut extra : Array EMatchTheorem := #[]
  -- Ante registration, fvar-first: the `h_ante` HYPOTHESIS carries the
  -- canonicalized statement (goal-side vocabulary — pair preambles are
  -- namespaced per side, so the ante DECL's constants can differ from the
  -- goal's and its patterns would never match), fixed universes (dodges the
  -- promotion refusal on polymorphic hyps), and proofs that reference the
  -- fvar instead of the sorried decl. Decl registration is the fallback.
  let mut anteRegistered := false
  match (← g.withContext do
      let lctx ← getLCtx
      pure (lctx.findFromUserName? `h_ante |>.map (·.fvarId))) with
  | some fv =>
    try
      if let some thm ← g.withContext do
          mkEMatchTheoremWithKind? (.fvar fv) #[] (mkFVar fv) (.default false) prios then
        extra := extra.push thm
        anteRegistered := true
    catch _ => ematchThmFails.modify (· + 1)
  | none => pure ()
  if !anteRegistered then
    if let some ante ← ematchAnteRef.get then
      try extra := extra.push (← mkEMatchTheoremForDecl ante (.default false) prios)
      catch _ => ematchThmFails.modify (· + 1)
  for (lem, symm) in bridges do
    try
      let k : EMatchTheoremKind := if symm then .eqRhs false else .eqLhs false
      extra := extra.push (← mkEMatchTheoremForDecl lem k prios)
    catch _ => ematchThmFails.modify (· + 1)
  let extraThms := extra
  -- side-effect-free: grind may otherwise assign the goal mvar during
  -- internalization; harvested facts are plain exprs over the (unchanged)
  -- local context, so a full state rollback keeps them valid
  withoutModifyingState do
  GrindM.runAtGoal g params fun goal => do
    let (facts, _) ← GoalM.run goal do
      -- Goal-directed anchor: `runAtGoal` internalizes only the HYPOTHESES
      -- (the by-contradiction step that puts the target into the e-graph
      -- lives in `solve`, which we skip). Without this, conclusion-side
      -- patterns (e.g. `IsUnit (1 - ?a * ?b)`) have no node to match and
      -- goal-directed instantiation silently never fires.
      let tgt ← instantiateMVars (← (← get).mvarId.getType)
      try internalize tgt 0 catch _ => pure ()
      -- flush internalization residue so every later queue entry is ours
      processNewFacts
      let mut out : Array (Expr × Expr) := #[]
      let mut seen : Std.HashSet String := {}
      for _ in [0:rounds] do
        discard <| ematch' extraThms
        let s ← get
        for f in s.newRawFacts.toArray do
          let key := toString f.prop
          if out.size < maxFacts && !seen.contains key then
            seen := seen.insert key
            -- case-2 proxy: grind-internal plumbing in the proof means the
            -- instantiation crossed a propositional equality inside an
            -- argument slot — v1 drops (and counts) it
            let bad := f.proof.getUsedConstantsAsSet.toList.any fun c =>
              (`Lean.Grind).isPrefixOf c || (`Grind).isPrefixOf c
            if bad then
              ematchCase2Drops.modify (· + 1)
            else
              out := out.push (f.prop, f.proof)
        processNewFacts   -- internalize this round's facts for the next round
      pure out
    return facts

/-- R3 flag: `enableEMatchForward` routes `structuralCore`'s enrichment through
the e-match adapter instead of `forwardInstantiate`. Bridge count from
`STATIC_EVAL_EMATCH_K` (default 8). OFF pending the Phase-3 head-to-head. -/
def enableEMatchForward : IO Bool := do
  return (← IO.getEnv "STATIC_EVAL_EMATCH_FWD").isSome

/-- **And-split** (`STATIC_EVAL_AND_SPLIT`, 2026-08-26, Henry's call). A conjunctive goal handed WHOLE to
`solveByElim` makes it search for one term proving all conjuncts at once — the
choice space is the product, so a five-fold conclusion is unreachable at any
budget (measured on synth:order:G1: 0/2 closes at 8x heartbeats, 25 min).
Splitting first turns one deep search into independent shallow ones, each
matching a hypothesis directly, each with its own rollback.

The M4.4/transport branch of `structuralCore` has always done this (its
comment: "a connective-headed goal cannot fall to blind search … split FIRST,
so the deep solvers only ever run on atoms") — but that branch is off, so the
D4 path has never had it. This toggle gives D4 the same move, restricted to
`And`: splitting an `↔` means proving two implications separately, which is
proof work rather than carrying one phrasing into another (Henry, 2026-08-26),
so `Iff` stays unsplit here even though the transport path splits it.

Default ON since 2026-08-26 (Henry): measured with the gate's rescue fix in
place — recall_fast 24/29 with ZERO verdict diffs and -5.6% summed pair time,
pollution 0 FP / 6-6 controls / 0 diffs, traps 0 FP / 0 diffs. Set
`STATIC_EVAL_AND_SPLIT=0` to restore the un-split D4 body.

NOTE for anyone measuring this again: the split also strengthens the ante-free
prober INSIDE the essential-use gate, which is a pollution detector defined by
what the prover can do. Before the rescue fix it therefore converted
`equiv:Compfiles:Imo1960P1` into a pollution refusal (the gate correctly
noticed a decidable conjunct). Prover improvements are not monotone in recall
while that coupling stands. -/
def enableAndSplit : IO Bool := do
  match ← IO.getEnv "STATIC_EVAL_AND_SPLIT" with
  | some "0" => return false
  | some _   => return true
  | none     => return true

def ematchK : IO Nat := do
  match ← IO.getEnv "STATIC_EVAL_EMATCH_K" with
  | some s => return s.toNat?.getD 8
  | none => return 8

/-- Top-K ranked pool bridges for the adapter (set by the discovery block once
per pair; direction-agnostic — a bridge is an equality either way round). -/
initialize ematchBridgesRef : IO.Ref (Array (Name × Bool)) ← IO.mkRef #[]


/-- R3 drop-in for `forwardInstantiate`: harvest e-match instantiations,
re-check each proof in OUR MetaM (grind state long gone), assert as `h_em_N`.
Proof terms are ante/bridge-free ante-applications (case-2 dropped upstream),
so the audit chain sees nothing new. -/
def ematchForward (g : MVarId) (maxAsserts : Nat := 6) : MetaM MVarId := do
  let bridges ← ematchBridgesRef.get
  let facts ← try ematchInstantiate g bridges catch e => do
    if (← IO.getEnv "STATIC_EVAL_EMATCH_TRACE").isSome then
      IO.eprintln s!"[em] adapter EXCEPTION: {← e.toMessageData.toString}"
    pure #[]
  if (← IO.getEnv "STATIC_EVAL_EMATCH_TRACE").isSome then
    IO.eprintln s!"[em] harvested {facts.size} facts:"
    for (prop, _) in facts do
      IO.eprintln s!"[em]   {(← ppExpr prop).pretty.take 120}"
  let mut g := g
  let mut n := 0
  for (prop, proof) in facts do
    if n < maxAsserts then
      let ok ← g.withContext do
        try
          Meta.check proof
          isDefEq (← inferType proof) prop
        catch _ => pure false
      if ok then
        try
          let g' ← g.assert ((`h_em).appendIndexAfter n) prop proof
          let (_, g'') ← g'.intro1P
          g := g''
          n := n + 1
        catch _ => pure ()
      else if (← IO.getEnv "STATIC_EVAL_EMATCH_TRACE").isSome then
        IO.eprintln s!"[em]   CHECK-FAIL: {(← ppExpr prop).pretty.take 100}"
  if (← IO.getEnv "STATIC_EVAL_EMATCH_TRACE").isSome then
    IO.eprintln s!"[em] asserted {n}/{facts.size}"
  return g

/-- D4 forward instantiation: specialize each ∀-headed Prop hypothesis (most
importantly the asserted antecedent) against the local context — every binder
filled by a local of defeq type (backtracking, bounded), instances synthesized —
and assert the instantiated body when its head is destructurable (∃/∧/↔/∨).
This is what unlocks the hypothesis-side witness: for `h_ante : ∀ x U …, ∃ V, …`
no goal-side `apply` can ever expose the `∃`; after intros the goal's locals
mirror the antecedent's binders one-to-one, so the specialization is usually
forced. Pure modus ponens over existing hypotheses — no new constants. -/
def forwardInstantiate (g : MVarId) (maxAsserts : Nat := 6) : MetaM MVarId := do
  packBuiltRef.set #[]   -- R1(b): fresh collection for this pass's constructions
  let hyps := (← g.getNondepPropHyps).reverse
  let mut g := g
  let mut n := 0
  for fv in hyps do
    if n ≥ maxAsserts then break
    let inst? ← g.withContext do
      try
        let ty ← instantiateMVars (← fv.getType)
        unless ty.isForall do return none
        let (ms, infos, body) ← forallMetaTelescope ty
        -- R1(b) (2026-08-18): cap 8 → 16. Research-level antes are bigger than
        -- the cap assumed — cw:02's Glauberman statement carries ~15 binders
        -- (3 types + 8 instance binders across A/G/Ω + 3 Props), so at 8 (and
        -- even at the first-tried 12) the ante was never specialized and the
        -- whole packaging machinery was unreachable. Cost stays bounded by
        -- `fillFromLocals`' defeq budget (300), not by the binder count.
        if ms.isEmpty || ms.size > 16 then return none
        unless (← isProp body) do return none
        let head := (← whnfR body).getAppFn.constName?.getD .anonymous
        let destructurable :=
          head == ``Exists || head == ``And || head == ``Iff || head == ``Or
        -- **P2-1(c) (M4.9).** An ATOMIC body may still be exactly the goal —
        -- the pure modus-ponens shape (`… → IsUnit (1 - a*b)` vs goal
        -- `IsUnit (1 - a*b)`). Unify the body (mvars still open) against the
        -- goal FIRST, so the GOAL determines the data arguments (`?b := b` —
        -- a locals-first fill can pick wrong and there is no backtracking
        -- across this gate), then let the filler + P2 moves discharge the
        -- rest. Without this, a successful curated instance construction was
        -- built and then DISCARDED because the body head was not ∃/∧/↔/∨ —
        -- measured on the t1128 triplet.
        if !destructurable then
          unless ← isDefEq body (← g.getType) do
            return none
        let mut locals : Array Expr := #[]
        for h in ← getLCtx do
          unless h.isImplementationDetail || h.fvarId == fv do
            locals := locals.push (mkFVar h.fvarId)
        let budget ← IO.mkRef (300 : Nat)
        unless (← fillFromLocals budget locals ms infos 0) do return none
        let args ← ms.mapM instantiateMVars
        if args.any (·.hasExprMVar) then return none
        let body ← instantiateMVars body
        if body.hasExprMVar then return none
        return some (body, mkAppN (mkFVar fv) args)
      catch _ => return none
    if let some (ty, val) := inst? then
      try
        g ← g.assert ((`h_fwd).appendIndexAfter n) ty val
        let (_, g') ← g.intro1P
        g := g'
        n := n + 1
      catch _ => pure ()
  -- **R1(b) assert-based sharing (2026-08-18).** Every instance the pack pass
  -- constructed is asserted into the goal context: `assert`/`intro1P` route
  -- through `withNewLocalInstances`, so each becomes a REAL local instance
  -- that everything downstream — the structural close, `solveByElim`'s
  -- apply-side synthesis, later `trySynthInstance` calls — finds natively
  -- instead of re-deriving (or failing to). Values were built in this goal's
  -- context, so the fvars they mention remain valid under extension. Audit:
  -- unchanged — the constructions are class-typed data, and the middleman
  -- channel is the confiscated reproof's jurisdiction.
  let mut seenTy : List String := []
  let mut k := 0
  for (ty, v) in ← packBuiltRef.get do
    let key ← try packKey ty catch _ => pure ""
    unless key.isEmpty || seenTy.contains key do
      seenTy := key :: seenTy
      try
        g ← g.assert ((`h_inst).appendIndexAfter k) ty v
        let (_, g') ← g.intro1P
        g := g'
        k := k + 1
      catch _ => pure ()
  return g

/-- Substitute local equations whose side is a free variable (`hf : f = X^3 + …`
⊢ `Irreducible f` — the witness corpus's `rw [hf]` shape): pure `Eq.subst`
plumbing, applied hypothesis-side. One failed substitution stops the pass (the
context indices shift after each success). -/
def substEqHyps (g : MVarId) : MetaM MVarId := do
  let mut g := g
  for _ in [0:8] do
    match ← try substSomeVar? g catch _ => pure none with
    | some g' => g := g'
    | none => break
  return g

/-- Rewrite the goal's target with the local Eq/Iff Prop hypotheses as rules
(the `simp only [*]` shape, hypotheses-as-rewrites only — no library set).
Returns the simplified goal when simp made progress. -/
def simpWithLocalEqs (g : MVarId) : MetaM (Option MVarId) := do
  g.withContext do
    let mut st : SimpTheorems := {}
    let mut any := false
    for h in ← getLCtx do
      unless h.isImplementationDetail do
        if (← isProp h.type) then
          let head := (← instantiateMVars h.type).getAppFn.constName?.getD .anonymous
          if head == ``Eq || head == ``Iff then
            try
              st ← st.add (.fvar h.fvarId) #[] (mkFVar h.fvarId)
              any := true
            catch _ => pure ()
    unless any do return none
    let ctx ← Simp.mkContext {} (simpTheorems := #[st])
      (congrTheorems := ← getSimpCongrTheorems)
    let (res, _) ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := #[])
    match res with
    | none => return none  -- fully closed is handled by the caller's retry
    | some (_, g') => return some g'

mutual

/-- The shared D4 tail of every structural closer, over an explicit lemma list:
substitute variable equations, enrich the context with replumbing variants,
forward-instantiate quantified hypotheses against the locals, saturate
(destructure ∧/∃/↔/∨ hypotheses), then `solveByElim` over the lemmas +
hypotheses per goal. Goals that survive get the apply-hypothesis-and-recurse
round (`applyHypRecurseCore`). Returns the remaining goals. -/
partial def structuralCore (lemmas : List Name) (g : MVarId) (depth : Nat := 1)
    (enrich : Bool := true) : MetaM (List MVarId) := do
  let g ← substEqHyps g
  -- variants + forward instantiation are asserted into the context and thus
  -- PERSIST into recursive rounds — regenerating them per recursion level
  -- multiplies cost for nothing (M4.4 only; the D4 path always enriches, as
  -- the committed body did)
  let enrich := enrich || !enableM44Transport
  let g ← if enrich then assertVariants g else pure g
  let g ← if enrich then
      -- R3 additive: e-match runs ON TOP of forwardInstantiate (substituting
      -- it lost its P2-1(c) goal-unification and packing closes — the 5
      -- casualties of the first K-sweep were all substitution artifacts)
      (do let g ← forwardInstantiate g
          if ← enableEMatchForward then ematchForward g else pure g)
    else pure g
  let goals ← saturateHyps g (fuel := 24)
  -- per-goal: `solveByElim` THROWS on failure (it never returns partial
  -- leftovers), and one hard sibling must not doom the rest
  unless enableM44Transport do
    -- D4 path: byte-for-byte the committed 35d4a3b body — one `solveByElim`
    -- per goal (ambient transparency, constructor on, no cap), then
    -- apply-hypothesis-and-recurse. This is what the M4.3 recall/precision
    -- numbers were measured against; do not "improve" it without re-measuring.
    let mut d4out := []
    let andSplit ← enableAndSplit
    for gg in goals do
      -- And-split FIRST when enabled (see `enableAndSplit`): the deep solvers
      -- then only ever run on atoms. Rolls back wholesale on failure, so the
      -- ordinary path below is reached with the goal untouched.
      if andSplit then
        let isAnd ← try
            pure ((← whnfR (← gg.getType)).getAppFn.constName?.getD .anonymous == ``And)
          catch _ => pure false
        if isAnd then
          if ← andSplitThenRecurse lemmas gg depth then continue
      let closed ← try
        pure (← structuralSolve lemmas [gg]).isEmpty
      catch _ => pure false
      if closed then continue
      if depth > 0 then
        if ← applyHypRecurseCore lemmas gg depth then continue
      d4out := d4out ++ [gg]
    return d4out
  let mut out := []
  for gg in goals do
    -- a connective-headed goal cannot fall to blind search (iff sides need
    -- intros + saturation; conjunctions explode the search) — split FIRST,
    -- so the deep solvers only ever run on atoms
    let splitHead ← try
      let h := (← whnfR (← gg.getType)).getAppFn.constName?.getD .anonymous
      pure (h == ``Iff || h == ``And)
    catch _ => pure false
    if splitHead && depth > 0 then
      if ← splitThenRecurse lemmas gg depth then continue
    -- two-phase solve, each under a heartbeat cap (a pathological unification
    -- against big stuck arithmetic terms must cost a slice, not the attempt):
    -- wide-and-shallow (full lemma set, leaf arithmetic — reducible + no
    -- constructor: `Eq.refl`-as-constructor forces full-transparency
    -- unification), then narrow-and-deep (original small set, re-tuple chains)
    -- every capped phase must roll back on failure: `commitIndependentGoals`
    -- assigns goals mid-search, and an aborted run otherwise leaves the goal
    -- poisoned — assigned to a proof referencing dead metavariables
    let narrow := lemmas.filter fun n => !wideOnlyLemmas.contains n
    let s0 ← saveState
    -- wide phase, two capped rounds: constructor-off first (cannot detonate —
    -- `Eq.refl`-as-constructor forces full unification of huge stuck terms),
    -- then constructor-on (needed to re-assemble ∧/∃ after variant application)
    let closed ← try
      withHeartbeatCap 10000 do
        pure (← structuralSolve lemmas [gg] (maxDepth := 8)
          (transparency? := some .reducible) (constructor := false)).isEmpty
    catch _ => pure false
    unless closed do restoreState s0
    if closed then continue
    let s1 ← saveState
    let closed ← try
      withHeartbeatCap 30000 do
        pure (← structuralSolve narrow [gg] (maxDepth := 16)).isEmpty
    catch _ => pure false
    unless closed do restoreState s1
    if closed then continue
    -- rewrite the target with the LOCAL Eq/Iff hypotheses (a case analysis
    -- leaves `↑n = 1`-style facts that `subst` cannot use), then retry —
    -- hypotheses carry no library constants, so this stays audit-clean
    let s2 ← saveState
    let closed ← try
      withHeartbeatCap 10000 do
        match ← simpWithLocalEqs gg with
        | some gg' => pure (← structuralSolve lemmas [gg'] (maxDepth := 6)
            (transparency? := some .reducible) (constructor := false)).isEmpty
        | none => pure false
    catch _ => pure false
    unless closed do restoreState s2
    if closed then continue
    if depth > 0 then
      let s3 ← saveState
      let ok ← try withHeartbeatCap 30000 (applyHypRecurseCore lemmas gg depth)
        catch _ => pure false
      unless ok do restoreState s3
      if ok then continue
    -- constructor-on wide round LAST: it greedily closes intermediate goals in
    -- dead-end ways (shared metavariables, no cross-goal backtracking), so it
    -- must not preempt the narrow/applyHyp paths; capped — its `Eq.refl`
    -- detonations on huge stuck terms cost a slice, not the attempt
    let s4 ← saveState
    let closed ← try
      withHeartbeatCap 15000 do
        pure (← structuralSolve lemmas [gg] (maxDepth := 8)
          (transparency? := some .reducible)).isEmpty
    catch _ => pure false
    unless closed do restoreState s4
    if closed then continue
    out := out ++ [gg]
  return out

/-- And-only split for the D4 path (`enableAndSplit`). Unlike
`splitThenRecurse` this passes the SAME `depth` to the recursive
`structuralCore`: `And.intro` strictly decreases goal size, so nesting
terminates on the conjunction's own structure and must not consume the
apply-hypothesis recursion budget — otherwise a 5-fold conclusion at the
shipped `depth := 1` would split once and hand the 4-fold remainder back to
blind search, which is the very failure this fixes. `enrich := false`: the
variants/instantiations were asserted into the context by the top-level call
and persist, so leaves must not regenerate them. All-or-nothing rollback. -/
partial def andSplitThenRecurse (lemmas : List Name) (g : MVarId) (depth : Nat)
    : MetaM Bool := do
  unless (← whnfR (← g.getType)).getAppFn.constName?.getD .anonymous == ``And do
    return false
  let trace := (← IO.getEnv "STATIC_EVAL_TRACE").isSome
  let st ← saveState
  let ok ← try
    let subs ← g.applyConst ``And.intro
    if trace then
      IO.eprintln s!"[and-split] fired on: {← Meta.ppExpr (← instantiateMVars (← g.getType))}"
    let mut all := true
    let mut idx := 0
    for sub in subs do
      let (_, sub') ← sub.intros
      idx := idx + 1
      let left ← structuralCore lemmas sub' depth (enrich := false)
      if trace then
        IO.eprintln s!"[and-split]   subgoal {idx}: {if left.isEmpty then "closed" else "OPEN"}"
        if !left.isEmpty then
          for lg in left.take 1 do
            IO.eprintln s!"[and-split]     residual: {← Meta.ppExpr (← instantiateMVars (← lg.getType))}"
      unless left.isEmpty do
        all := false
        break
    pure all
  catch _ => pure false
  if ok then return true
  restoreState st
  return false

/-- Constructor-split an `Iff`/`And`-headed target and recursively finish each
side after `intros` — the sides of an iff are implication goals whose
hypotheses need introduction and saturation (case analysis on a disjunctive
antecedent), which `solveByElim`'s internal search can never do. -/
partial def splitThenRecurse (lemmas : List Name) (g : MVarId) (depth : Nat)
    : MetaM Bool := do
  let head := (← whnfR (← g.getType)).getAppFn.constName?.getD .anonymous
  unless head == ``Iff || head == ``And do
    return false
  let ctor := if head == ``Iff then ``Iff.intro else ``And.intro
  let st ← saveState
  let ok ← try
    let subs ← g.applyConst ctor
    let mut all := true
    for sub in subs do
      let (_, sub') ← sub.intros
      unless (← structuralCore lemmas sub' (depth - 1) (enrich := false)).isEmpty do
        all := false
        break
    pure all
  catch _ => pure false
  if ok then
    return true
  restoreState st
  return false

/-- Apply a quantified Prop hypothesis (the asserted antecedent first — the
context is scanned most-recent-first) to the goal and recursively finish each
side goal. This is the `refine ante (fun … => ?_) h` witness shape: the
antecedent's ∀-hypothesis argument is itself a replumbing problem (reshuffle the
corresponding local hypothesis under its binders), unreachable by `solveByElim`
alone. -/
partial def applyHypRecurseCore (lemmas : List Name) (g : MVarId) (depth : Nat)
    : MetaM Bool := do
  let hyps := (← g.getNondepPropHyps).reverse
  for fv in hyps.toList.take 6 do
    let s ← saveState
    let ok ← try
      let subs ← g.apply (mkFVar fv)
      let mut all := true
      for sub in subs do
        let (_, sub') ← sub.intros
        unless (← structuralCore lemmas sub' (depth - 1)).isEmpty do
          all := false
          break
      pure all
    catch _ => pure false
    if ok then
      return true
    restoreState s
  return false

end

/- ### R2 (2026-08-19) — statement-directed instance saturation (push mode)

R1(b) packs on DEMAND (a failing instance-fill triggers construction at the
failure site). This pass packs PROACTIVELY: before the structural machinery
runs, assert every instance the catalog can build from the context for the
CLASS HEADS THE PAIR'S OWN STATEMENTS MENTION — so consumers the demand hook
cannot reach (solveByElim's apply-time synthesis, simp dischargers,
`forwardInstantiate`'s fills) find them as real local instances.

Design (Henry, 2026-08-19 — discover once, replay): the RULE-SET SCAN runs
once per direction; the successful rule names are memoized (`satRuleCache`,
keyed by ante, cleared per pair by the Driver) and every later arm merely
REPLAYS those rules (one match + assert each, microseconds; a replay that no
longer applies in a rewritten context skips harmlessly). Flood controls:
heads limited to classes mentioned by the statements; per-head rule cap;
`maxAsserts` cap; explicit denylist (`Fact.mk` fires on every Prop — it stays
demand-only, as it always has); and a rule whose conclusion is ALREADY
ambiently synthesizable is skipped (no duplicate instances — duplicates both
slow synthesis and burn `fillFromLocals`' shared defeq budget on junk). -/
initialize satRuleCache : IO.Ref (List (Name × Array Name)) ← IO.mkRef []

/-- **MEASURED OFF (2026-08-19).** Full comparison battery vs the pull-only
baseline (traps/pollution/recall_fast/theywin/coworker, 118 pairs): ZERO
verdict changes at 1.19-1.29x runtime on the failing-heavy suites. Everything
push can assert, the demand-driven R1(b) path (plus the R8' delayed-instance
arm) already supplies when asked. Kept behind this flag for the capability
study's knob ladder; flip only with a measured pair in hand. -/
def enablePushSaturation : Bool := false

def pushDenylist : NameSet := .ofList [`Fact.mk]

/-- Try one catalog rule in PUSH mode: no conclusion anchor — every argument
must be pinned by matching a LOCAL (Prop, data, or instance hypothesis) or by
instance synthesis once its type is ground. Two passes so later matches pin
earlier type variables. Returns (conclusion type, value). -/
def tryPushRule (budget : IO.Ref Nat) (locals : Array Expr) (rule : Name)
    : MetaM (Option (Expr × Expr)) := do
  if (← budget.get) == 0 then return none
  budget.modify (· - 1)
  let s ← saveState
  try
    let f ← mkConstWithFreshMVarLevels rule
    let (args, binfos, concl) ← forallMetaTelescope (← inferType f)
    for _ in [0:2] do
      for h : i in [0:args.size] do
        let a := args[i]
        unless ← a.mvarId!.isAssigned do
          let mut done := false
          for l in locals do
            unless done do
              let s2 ← saveState
              let hit ← try isDefEq a l catch _ => pure false
              if hit then done := true else restoreState s2
          unless done do
            if binfos[i]! == .instImplicit then
              let aTy ← instantiateMVars (← a.mvarId!.getType)
              unless aTy.hasExprMVar do
                match ← trySynthInstance aTy with
                | .some v => discard <| isDefEq a v
                | _ => pure ()
    for a in args do
      unless ← a.mvarId!.isAssigned do
        restoreState s
        return none
    let v ← instantiateMVars (mkAppN f args)
    let cTy ← instantiateMVars concl
    if v.hasExprMVar || v.hasSorry || cTy.hasExprMVar then
      restoreState s
      return none
    -- dedup vs ambient synthesis: only assert what synthesis CANNOT already see
    match ← (try trySynthInstance cTy catch _ => pure .undef) with
    | .some _ => restoreState s; return none
    | _ => return some (cTy, v)
  catch _ =>
    restoreState s
    return none

/-- Class heads the direction's statements mention: the ante's instance-binder
heads (from its type, syntactically) plus class-headed local hypothesis types. -/
def pushHeads (ante : Name) (g : MVarId) : MetaM (Array Name) := do
  let env ← getEnv
  let mut hs : Array Name := #[]
  let addTy (hs : Array Name) (ty : Expr) : Array Name := Id.run do
    let mut hs := hs
    let mut t := ty
    while t.isForall do
      if t.bindingInfo! == .instImplicit then
        if let .const h _ := t.bindingDomain!.getAppFn then
          unless hs.contains h do hs := hs.push h
      t := t.bindingBody!
    hs
  if let some info := env.find? ante then
    hs := addTy hs info.type
  let localHeads ← g.withContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if let .const h _ := d.type.getAppFn then
          if isClass env h then out := out.push h
    pure out
  for h in localHeads do
    unless hs.contains h do hs := hs.push h
  return hs[0:8].toArray

/-- The push pass: discovery once per direction (rule scan memoized by ante),
cheap replay afterwards. Asserted results register as real local instances
(`assert`/`intro1P` route through `withNewLocalInstances`). -/
def saturatePush (ante : Name) (g : MVarId) (maxAsserts : Nat := 6) : MetaM MVarId := do
  let cached := (← satRuleCache.get).find? (·.1 == ante) |>.map (·.2)
  let rules ← match cached with
    | some rs => pure rs
    | none => do
      let heads ← try pushHeads ante g catch _ => pure #[]
      let idx ← getPackIndex
      let mut rs : Array Name := #[]
      for h in heads do
        for (hh, mover) in instancePackMoves do
          if hh == h && !rs.contains mover then rs := rs.push mover
        if let some cands := idx.find? h then
          for j in [0:min 8 cands.size] do
            unless rs.contains cands[j]! || pushDenylist.contains cands[j]! do
              rs := rs.push cands[j]!
      pure rs
  if rules.isEmpty then
    if cached.isNone then satRuleCache.modify ((ante, #[]) :: ·)
    return g
  let budget ← IO.mkRef (100 : Nat)
  let mut g := g
  let mut fired : Array Name := #[]
  let mut n := 0
  -- two rounds: round-2 rules may consume round-1 asserts
  for _ in [0:2] do
    for rule in rules do
      if n < maxAsserts && !fired.contains rule then
        let hit ← g.withContext do
          let mut locals : Array Expr := #[]
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              locals := locals.push (mkFVar d.fvarId)
          try tryPushRule budget locals rule catch _ => pure none
        if let some (cTy, v) := hit then
          try
            let g' ← g.assert ((`h_sat).appendIndexAfter n) cTy v
            let (_, g'') ← g'.intro1P
            g := g''
            fired := fired.push rule
            n := n + 1
          catch _ => pure ()
  if cached.isNone then
    satRuleCache.modify ((ante, fired) :: ·)
  return g

/-- `structuralCore` keyed by the antecedent (the strict closers' entry point). -/
def finishStructurally (ante : Name) (g : MVarId)
    (depth : Nat := if enableM44Transport then 3 else 1)
    : MetaM (List MVarId) := do
  -- R2: proactive instance saturation — MEASURED OFF (see `enablePushSaturation`)
  let g ← if enablePushSaturation then (try saturatePush ante g catch _ => pure g) else pure g
  structuralCore (structuralSolveLemmas ante) g depth

/-- Try to fully close `goal` with the structural strategy: intro, bring the
antecedent INTO the context (so saturation and replumbing variants apply to it —
D4: as a mere `solveByElim` lemma it could never be destructured or flipped),
assert replumbing variants, saturate (the `obtain` shapes), then `solveByElim`
with goal-constructor splitting. Returns the proof. -/
def structuralClose (ante : Name) (goal : MVarId) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root := goal
    let (_, goal) ← goal.intros
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let goal ← goal.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, goal) ← goal.intro1P
    let remaining ← finishStructurally ante goal
    if remaining.isEmpty then
      return some (← instantiateMVars (mkMVar root))
    restoreState s
    return none
  catch _ =>
    restoreState s
    return none

/-- Probe: is the goal definitionally true (`rfl`-closable after intros)? A pure
triviality signal — never a closer: `1 = 1` and `2 = 2` are both rfl-true and
utterly unrelated. -/
def goalDefeqTrue (goalType : Expr) : MetaM Bool := do
  let s ← saveState
  try
    let g := (← mkFreshExprMVar goalType).mvarId!
    let (_, g) ← g.intros
    g.refl
    restoreState s
    return true
  catch _ =>
    restoreState s
    return false

/-- Probe (BEq+ guard, enforced as a gate): is the goal provable from its own
hypotheses alone? MUST wield exactly the strict closer's machinery minus the
antecedent — any power asymmetry lets a self-provable goal slip the gate while
the strict tier closes it with the destructured antecedent laundered into the
proof term (observed: `7 ∣ 49` via `⟨7, rfl⟩` at depth 16 with the depth-6
probe blind to it). -/
def provableFromOwnHyps (goalType : Expr) : MetaM Bool := do
  let s ← saveState
  try
    let g := (← mkFreshExprMVar goalType).mvarId!
    let (_, g) ← g.intros
    let remaining ← structuralCore noAnteLemmas g
    restoreState s
    return remaining.isEmpty
  catch _ =>
    restoreState s
    return false

/-- One obligation extracted for the essential-use gate (M4.5 v2). `expr` is
CLOSED: re-generalized over every binder in scope at its extraction site —
including ∃-binders for binder-dependent parts, so a part `Q x` inside
`∃ x, P x ∧ Q x` becomes the obligation `∀ x, Q x` (if THAT is provable
ante-free, the part adds no relational content for any witness; v1 dropped
dependent parts entirely — a verified escape). `decoration` marks Prop binder
domains (P4 `q → p` wrappers, now caught at ANY depth) as opposed to asserted
∧/↔/∃ parts — the two kinds rescue against different antecedent pools. -/
structure GateObl where
  expr : Expr
  decoration : Bool
  deriving Inhabited

/-- Recursive obligation decomposer for the essential-use gate. Walks the goal
through `∧`/`↔` (both sides), `∃` (body decomposed under the binder — parts are
re-generalized, so x-free parts lift out unchanged modulo a vacuous binder and
x-dependent parts become `∀ x, part`), and `∀`/`→` (a Prop domain is a
decoration obligation — at any depth, closing the nested-P4 laundering where
`(q → p) ∧ r` hid the decoration inside a conjunct — and the body is decomposed
under the binder, so hypothesis binders are KEPT in part obligations: the part
`3 ∣ n` of `∀ n, 6 ∣ n → … ∧ 3 ∣ n` is the obligation `∀ n, 6 ∣ n → 3 ∣ n`).
When a side of `∧`/`↔` itself split, the side is ALSO emitted as a whole
obligation: a nested `Even n ↔ n % 2 = 0` is library-provable as a unit while
neither side is (the verified `even_iff` self-rewrite pollution), so leaves
alone are not enough. Returns (obligations, didSplit); an atom that never
split is returned as a single part so enclosing `∧`s can claim it, and the
top-level wrapper discards non-decoration parts when nothing split (the
whole-goal case belongs to the vacuity probes, not this gate). -/
partial def decomposeObls (xs : Array Expr) (e : Expr) (fuel : Nat)
    (directional : Bool := false) : MetaM (Array GateObl × Bool) := do
  let e ← instantiateMVars e
  let closed (t : Expr) (deco : Bool) : MetaM GateObl := do
    return { expr := ← mkForallFVars xs t, decoration := deco }
  let atom : MetaM (Array GateObl × Bool) := do return (#[← closed e false], false)
  if fuel == 0 then atom
  else match e.getAppFn.constName?.getD .anonymous, e.getAppArgs with
  | ``And, #[a, b] =>
    let (pa, sa) ← decomposeObls xs a (fuel - 1) directional
    let (pb, sb) ← decomposeObls xs b (fuel - 1) directional
    let mut out := pa ++ pb
    -- sides that split are also obligations as a whole (see docstring); an
    -- unsplit side already IS its own single part
    if sa then out := out.push (← closed a false)
    if sb then out := out.push (← closed b false)
    return (out, true)
  | ``Iff, #[a, b] =>
    let (pa, sa) ← decomposeObls xs a (fuel - 1) directional
    let (pb, sb) ← decomposeObls xs b (fuel - 1) directional
    let mut out := pa ++ pb
    if sa then out := out.push (← closed a false)
    if sb then out := out.push (← closed b false)
    if directional then
      -- ante-side rescue patterns only: an ante asserting `A ↔ B` licenses a
      -- candidate part `A → B` or `B → A` (m42-iff-split's split form) — the
      -- directions are shared content, not pollution. Never emitted for goal
      -- obligations (they would just add probe work).
      for arr in [← mkArrow a b, ← mkArrow b a] do
        out := out.push (← closed arr false)
        -- 2026-08-26: DECOMPOSE the synthesized arrow too, don't stop at the
        -- atom. The GOAL side's `isForall` branch below distributes a
        -- hypothesis over its consequent's `∧` (emitting `∀ xs, A → cᵢ` per
        -- conjunct); an iff-spelled ANTE stopped at the closed arrow, so the
        -- pool held `∀ xs, cᵢ` (hypothesis-free) and `∀ xs, A → c₁ ∧ c₂ ∧ c₃`
        -- (whole consequent) but never `∀ xs, A → cᵢ` — and
        -- `openNonPropBinders` may not bridge that gap (stripping a Prop
        -- domain is the nested-P4 laundering). Faithful "iff restated as two
        -- implications" pairs therefore lost their rescue purely by SPELLING:
        -- measured on equiv:Compfiles:Imo1960P1, where the same content is
        -- rescued in the direction whose ante is implication-spelled and not
        -- in the one whose ante is iff-spelled.
        -- Risk direction (per this function's docstring): more patterns =>
        -- rescue MORE => reject FEWER — recall-positive, precision-exposed,
        -- so pollution + traps are mandatory for this change.
        let (ps, _) ← decomposeObls xs arr (fuel - 1) directional
        out := out ++ ps
    return (out, true)
  | ``Exists, #[_, lam] =>
    if lam.isLambda then
      withLocalDecl lam.bindingName! lam.binderInfo lam.bindingDomain! fun x => do
        let (parts, split) ← decomposeObls (xs.push x) (lam.bindingBody!.instantiate1 x)
          (fuel - 1) directional
        -- an ∃ whose body does not split is an atom, not an obligation
        if split then return (parts, true) else atom
    else atom
  | _, _ =>
    if e.isForall then
      let d := e.bindingDomain!
      let dProp ← try isProp d catch _ => pure false
      withLocalDecl e.bindingName! e.binderInfo d fun x => do
        let (parts, split) ← decomposeObls (xs.push x) (e.bindingBody!.instantiate1 x)
          (fuel - 1) directional
        if dProp then
          let dec ← closed d true
          return (parts.push dec, split)
        else
          return (parts, split)
    else atom

/-- Open an obligation's leading NON-Prop binders as fresh metavariables and
stop at the first Prop domain: stripping a Prop domain is exactly the nested-P4
laundering the review caught (`(q → p)` unified with a bare `p` after
`forallTelescope`, rescuing the polluted part). Fresh mvars let
binder-dependent shared content unify across binder order/naming. -/
partial def openNonPropBinders (e : Expr) : MetaM Expr := do
  if e.isForall then
    let d := e.bindingDomain!
    let dProp ← try isProp d catch _ => pure false
    if dProp then return e
    let m ← mkFreshExprMVar d
    openNonPropBinders (e.bindingBody!.instantiate1 m)
  else return e

/-- Counterpart rescue: does the (closed) obligation unify with any (closed)
antecedent pattern? Both sides open their non-Prop binders as fresh mvars in
the SAME metavariable context — v1 minted pattern mvars in one `MetaM.run'`
and matched them in another, hitting the unknown-metavariable panic path: the
rescue was silently dead for every quantified antecedent (and three pollution
pairs were "gated" only by that bug). Flex-headed sides never match (a
Prop-quantified antecedent's bare `?P` would rescue everything). Every try is
rolled back and heartbeat-capped. -/
def matchesAntePattern (obl : Expr) (pats : Array Expr) : MetaM Bool := do
  for p in pats do
    let hit ← withoutModifyingState do
      withHeartbeatCap 2000 do
        try
          let b ← openNonPropBinders obl
          let q ← openNonPropBinders p
          if b.getAppFn.isMVar || q.getAppFn.isMVar then pure false
          else isDefEq b q
        catch _ => pure false
    if hit then return true
  return false

/-- Restricted normalization simp set (Milestone 4.2, plan mechanism #1 realized):
the `push_cast` extension (exclusively Eq/Iff-conclusioned by construction — its
attribute handler rejects anything else; conditional lemmas' side conditions are
discharged only from local hypotheses), the curated plumbing lemmas, and the
antecedent itself as a rewrite rule. -/
def normalizationContext (ante? : Option Name) (extraExts : List Name := [])
    (unfoldLocals : Array Name := #[]) (transport : Bool := false)
    : MetaM Simp.Context := do
  let mut st ← NormCast.pushCastExt.getTheorems
  let env ← getEnv
  for n in plumbingLemmas do
    if env.contains n then
      try st ← st.addConst n catch _ => pure ()
  if transport then
    for n in transportLemmas do
      if env.contains n then
        try st ← st.addConst n catch _ => pure ()
  -- pair-local definitions (solution sets &c.): the two statements name the
  -- same object through DIFFERENT local constants; only delta can meet them
  for n in unfoldLocals do
    try st ← st.addDeclToUnfold n catch _ => pure ()
  if let some ante := ante? then
    try st ← st.addConst ante catch _ => pure ()
  let mut sets := #[st]
  -- carrier-lift extensions (M4.4): `zify_simps`/`qify_simps`/`rify_simps` are
  -- exclusively Iff-conclusioned carrier bridges (a ≤ b ↔ ↑a ≤ ↑b, …) — the
  -- audit accepts them on conclusion shape alone
  for extName in extraExts do
    if let some ext ← getSimpExtension? extName then
      sets := sets.push (← ext.getTheorems)
  Simp.mkContext {} (simpTheorems := sets) (congrTheorems := ← getSimpCongrTheorems)

/-- Side-condition discharger for conditional bridges (M4.4). Default simp
discharging first (preserves all pre-M4.4 behavior), then the structural
solver over local hypotheses + the numeric side-condition pack — the
`Nat.cast_sub`-style monotonicity goals (`2^i ≤ 2^n` from `i < n`) that the
default discharger cannot reach. No antecedent involved: side-condition proofs
carry no relational content, and every pack lemma is audit-accepted. -/
def dischargeSideCondition (e : Expr) : MetaM (Option Expr) := do
  unless (← isProp e) do return none
  let s ← saveState
  try
    let m ← mkFreshExprMVar e
    let mut g := m.mvarId!
    -- forward-normalize ambient Prop hypotheses with the plumbing set and
    -- assert the transported copies: congruence-provided binder facts arrive
    -- as memberships (`i ∈ Finset.Ico 0 n`) that the arithmetic side goal
    -- (`2^i ≤ 2^n`) needs as inequalities
    let ctx ← normalizationContext none
    let mut nAdded := 0
    for h in ← getLCtx do
      if nAdded ≥ 6 then break
      unless h.isImplementationDetail do
        -- only small, unquantified facts (congruence binder hypotheses like
        -- `i ∈ Ico 0 n`) — normalizing a large ∀-hypothesis on every
        -- side-condition call is a heartbeat sink
        if !h.type.isForall && h.type.approxDepth ≤ 16 && (← isProp h.type) then
          let (r, _) ← simp h.type ctx
          unless r.expr == h.type do
            let proof ← match r.proof? with
              | some pf => mkAppM ``Eq.mp #[pf, mkFVar h.fvarId]
              | none => pure (mkFVar h.fvarId)
            g ← g.assert (h.userName.appendAfter "✱") r.expr proof
            let (_, g') ← g.intro1P
            g := g'
            nAdded := nAdded + 1
    let goals ← saturateHyps g (fuel := 8)
    let remaining ← structuralSolve sideConditionLemmas goals (maxDepth := 8)
      (transparency? := some .instances)
    if remaining.isEmpty then
      let proof ← instantiateMVars m
      if proof.hasExprMVar || proof.hasSorry then
        restoreState s
        return none
      return some proof
    restoreState s
    return none
  catch _ =>
    restoreState s
    return none

/-- See `dischargeSideCondition`. Deliberately does NOT call
`Simp.dischargeDefault?` itself: invoking it from inside a custom discharge
closure bypasses simp's discharge-depth guard and loops
(discharge → simp → discharge → …). Instead the METHODS wrapper falls back:
simp calls the custom discharger only after its own default discharging has
been tried — so composing here is unnecessary as well as unsafe. -/
def dischargeStructural : Simp.Discharge := fun e =>
  if enableM44Transport then liftM (dischargeSideCondition e) else pure none


/-- Env-local, non-proposition, value-bearing definitions referenced by an
expression — the pair's own auxiliary constants (solution sets, helper defs).
These are unfold targets for normalization. -/
def localDefsOf (env : Environment) (es : Array Expr) : MetaM (Array Name) := do
  let mut out : Array Name := #[]
  let mut seen : NameSet := {}
  for e in es do
    for c in e.getUsedConstants do
      unless seen.contains c do
        seen := seen.insert c
        if (env.getModuleIdxFor? c).isNone then
          if let some (.defnInfo info) := env.find? c then
            unless (← isProp info.type) do
              out := out.push c
  return out

/-- The simpa-generalization: bring a fully-general instance of the antecedent into
the local context, normalize BOTH it and the target with the restricted simp set
(cast placement, membership unfolding, negation pushing — both ends meet in the
middle), then close structurally. Covers the witness corpus's
`simpa [bridges] using ante`, `push Not at h`, and cast-placement shapes. -/
def normalizeThenSolve (goalType : Expr) (ante : Name) (extraExts : List Name := [])
    (transport : Bool := false) (bridges : Array (Name × Bool) := #[])
    : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let (_, g) ← root.mvarId!.intros
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let anteType ← inferType anteExpr
    let g ← g.assert `h_ante anteType anteExpr
    let (anteFVar, g) ← g.intro1P
    -- the base attempt is normal-form-stable with D4: no local-def unfolding,
    -- no transport layer, no custom discharger; the transport/lift attempts
    -- carry the full M4.4 machinery
    let locals ← if transport then localDefsOf (← getEnv) #[goalType, anteType]
                 else pure #[]
    let ctx ← normalizationContext (some ante) extraExts locals transport
    -- normalize EVERY Prop hypothesis (the goal's own hypotheses may carry the
    -- bridge shape, e.g. `x ∈ Set.Ioo 0 1` needing `mem_Ioo`), plus the target
    let hyps ← g.getNondepPropHyps
    let (res, _) ← simpGoal g ctx
      (discharge? := if transport then some dischargeStructural else none)
      (simplifyTarget := true) (fvarIdsToSimp := hyps.push anteFVar)
    let finished ← do
      match res with
      | none => pure true  -- simp closed the goal
      | some (_, g') => do
        -- M4.7: when the plumbing normalization FIRED but the structural tail
        -- fails, the normalized goal is exactly the right starting point for the
        -- discovered bridges — a bridge that only matches the normalized shape is
        -- unreachable from the raw goal (RecallPlan P1(d)). Applying them here
        -- costs one extra simp pass on an already-normalized goal.
        let step ← if bridges.isEmpty then pure (some g') else
          try
            let mut bst : SimpTheorems := {}
            for (lem, symm) in bridges do
              try bst ← bst.addConst lem (inv := symm) catch _ => pure ()
            let bctx ← Simp.mkContext {} (simpTheorems := #[bst])
              (congrTheorems := ← getSimpCongrTheorems)
            match ← simpGoal g' bctx (simplifyTarget := true)
                     (fvarIdsToSimp := ← g'.getNondepPropHyps) with
            | (none, _)         => pure (none : Option MVarId)
            | (some (_, g2), _) => pure (some g2)
          catch _ => pure (some g')
        match step with
        | none    => pure true
        | some gg => pure (← finishStructurally ante gg).isEmpty
    unless finished do
      restoreState s
      return none
    -- counterfactual replay (vacuity guard): same normalization, no antecedent
    let vacuous ← if (← IO.getEnv "STATIC_EVAL_NO_REPLAY").isSome then pure false else
      withoutModifyingState do
      withHeartbeatCap 20000 do
        let root2 ← mkFreshExprMVar goalType
        let (_, g2) ← root2.mvarId!.intros
        let locals2 ← if transport then localDefsOf (← getEnv) #[goalType]
                      else pure #[]
        let ctx2 ← normalizationContext none extraExts locals2 transport
        let (res2, _) ← simpGoal g2 ctx2
          (discharge? := if transport then some dischargeStructural else none)
          (simplifyTarget := true) (fvarIdsToSimp := ← g2.getNondepPropHyps)
        match res2 with
        | none => pure true
        | some (_, g2') => pure (← structuralCore noAnteLemmas g2').isEmpty
    if vacuous then
      if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
        IO.eprintln "[static_eval]       normalize: rejected as vacuous"
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
        IO.eprintln s!"[static_eval]       normalize: hygiene reject (sorry={proof.hasSorry} mvar={proof.hasExprMVar})"
        let mvars := (proof.collectMVars {}).result
        for m in mvars do
          IO.eprintln s!"[static_eval]         unassigned ?goal : {← ppExpr (← m.getType)}"
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- Intro binders up to (excluding) the first ORDINARY Prop hypothesis — the
arm-side mirror of the S3b probe-0 stop rule. Data and instance binders are
opened; the implication structure a transplant-style close needs stays in the
goal. -/
partial def introsToFirstPropHyp (g : MVarId) : MetaM MVarId := do
  match ← g.getType with
  | .forallE _ d _ bi =>
    if (← isProp d) && bi != .instImplicit then return g
    let (_, g') ← g.intro1P
    introsToFirstPropHyp g'
  | _ => return g

/-- Dedup key for a search state: printed target + sorted non-dependent Prop
hypothesis types. Collapses `ℓ` then `←ℓ` cycles and convergent step orders. -/
def ppState (g : MVarId) : MetaM String := do
  g.withContext do
    let tgt := toString (← ppExpr (← g.getType))
    let mut hs : Array String := #[]
    for h in (← g.getNondepPropHyps) do
      hs := hs.push (toString (← ppExpr (← h.getType)))
    return tgt ++ "||" ++ String.intercalate ";" (hs.qsort (· < ·)).toList

/-- **M4.8-D2v2.** One level-1 harvest record: a single-lemma arm whose TRANSFORM
fired, captured as a printed state key plus the tag needed to re-execute it.
Strings and names only — goal states (mvars) cannot cross elaboration sessions,
so the state itself is reconstructed later from this tag. Recorded BEFORE the
close attempt (Henry: states must be collected before knowing whether level 1
succeeds), and discarded for free when a close lands. -/
structure HarvestEntry where
  key     : String
  lem     : Name
  symm    : Bool
  viaSimp : Bool
  shallow : Bool

/-- D4 bridge application (`rw [lem] at h ⊢`, done right): assert the
antecedent, rewrite ALL Prop hypotheses — including it — AND the target with a
SINGLE discovered Eq/Iff lemma via simp (simp rewrites under binders, where
`rw`'s motive fails on quantified hypotheses/goals), then finish structurally.
One attempt per discovered lemma keeps the rewrite auditable and the search
stepwise. -/
def bridgeAtHyps (goalType : Expr) (ante : Name) (lemmas : Array (Name × Bool))
    (shallow : Bool := false)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let g ← if shallow then introsToFirstPropHyp root.mvarId!
            else do let (_, gg) ← root.mvarId!.intros; pure gg
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let g ← g.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, g) ← g.intro1P
    -- M4.7-F0: the simp set may hold ONE bridge (the per-lemma fallback arms) or
    -- ALL discovered bridges at once (the packed arm). Packing is sound here in a
    -- way it is NOT on the goal side: these arms already run `simp only` to
    -- fixpoint over hypotheses + target, so adding rules changes how far the
    -- normal form travels, not the kind of step taken. The goal-side equivalent
    -- (the old aggregate `simp only [<all rules>, <ante>]` chain, deleted with
    -- the rw-discovery cluster) is not reinstated — 24 `rw` rules are not confluent
    -- w.r.t. the one useful rewrite. `addConst` can reject a lemma (non-rewrite
    -- shape); skip those rather than losing the whole arm.
    let mut st : SimpTheorems := {}
    for (lem, symm) in lemmas do
      try st ← st.addConst lem (inv := symm) catch _ => pure ()
    let ctx ← Simp.mkContext {} (simpTheorems := #[st])
      (congrTheorems := ← getSimpCongrTheorems)
    let hyps ← g.getNondepPropHyps
    -- discharge?: `none` means simp uses its OWN default discharger. Passing a
    -- custom closure REPLACES it — so when M4.4 is off we must pass `none`,
    -- not a no-op closure, or conditional rewrites lose side-condition
    -- discharging entirely (silently weaker than D4).
    let disch := if enableM44Transport then some dischargeStructural else none
    let (res, _) ← simpGoal g ctx (discharge? := disch)
      (simplifyTarget := true) (fvarIdsToSimp := hyps)
    let finished ← do
      match res with
      | none => pure true  -- a hypothesis simplified to False
      | some (_, g') => do
        -- M4.8-D2v2: harvest the fired state (single-lemma arms only), captured
        -- BEFORE the `simp only [ante]` pass — the deep search's step function
        -- has no ante pass, so a post-pass state would not be reconstructible.
        if let some ref := harvest? then
          if h : lemmas.size = 1 then
            let (lem, symm) := lemmas[0]
            let key ← ppState g'
            ref.modify (·.push { key, lem, symm, viaSimp := true, shallow })
        -- M4.7: after the bridges have reshaped hypotheses + target, use the
        -- ANTECEDENT as a rewrite rule on the target — `simp only [bridges];
        -- simp only [ante]`. Deliberately a SECOND pass, and deliberately NOT
        -- over `h_ante`: making the antecedent a rule in the same set that
        -- rewrites `h_ante` lets simp collapse `h_ante` to `True`, destroying the
        -- hypothesis the arm exists to reshape. Optional — if it fires nothing,
        -- `simpGoal` throws under `failIfUnchanged` and we keep the goal as-is.
        let step ← try
          let mut ast : SimpTheorems := {}
          ast ← ast.addConst ante
          let actx ← Simp.mkContext {} (simpTheorems := #[ast])
            (congrTheorems := ← getSimpCongrTheorems)
          match ← simpGoal g' actx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
          | (none, _)         => pure (none : Option MVarId)   -- ante alone closed it
          | (some (_, g2), _) => pure (some g2)
        catch _ => pure (some g')
        match step with
        | none    => pure true
        | some gg => pure (← finishStructurally ante gg).isEmpty
    unless finished do
      restoreState s
      return none
    -- counterfactual replay (vacuity guard): the same bridge WITHOUT the
    -- antecedent must not close the goal. A bridge can transform the target
    -- into defeq-trivial territory (`7 ∣ 49` ↝ `49 % 7 = 0 % 7` ≡ `0 = 0`)
    -- AFTER the pre-transformation probes ran; the transformed antecedent then
    -- "closes" it while doing no semantic work.
    let vacuous ← if (← IO.getEnv "STATIC_EVAL_NO_REPLAY").isSome then pure false else
      withoutModifyingState do
      try
        let root2 ← mkFreshExprMVar goalType
        -- parity: replay at the SAME intros depth as the attempt
        let g2 ← if shallow then introsToFirstPropHyp root2.mvarId!
                 else do let (_, gg) ← root2.mvarId!.intros; pure gg
        let hyps2 ← g2.getNondepPropHyps
        let (res2, _) ← simpGoal g2 ctx (discharge? := disch)
          (simplifyTarget := true) (fvarIdsToSimp := hyps2)
        match res2 with
        | none => pure true
        | some (_, g2') => pure (← structuralCore noAnteLemmas g2').isEmpty
      catch _ => pure false
    if vacuous then
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- **M4.7 arm conversion.** `rw [±lem] at *` — one-shot rewrite of the TARGET and
every non-dependent Prop hypothesis (`h_ante` included), then structural close.
The `rw` counterpart of `bridgeAtHyps`: it applies the permutative rules `simp`
structurally refuses (AC-increasing direction, `acLt` — 32–36 % of `rw`'s
measured win volume on pnv), and cannot cross binders where simp descends —
each strategy covers the other's refusals. Subsumed and replaced the
target-only / hyps-only split arms (`rwThenStructural` / `rwAtHyps`, deleted
M4.10-E1). Side goals of a conditional TARGET rewrite are discharged
structurally; a conditional HYPOTHESIS rewrite is skipped
(`replaceLocalDecl` would leave its side goals dangling). Same counterfactual
replay as every arm: the identical transform WITHOUT the antecedent must not
close the goal. -/
def rwStar (goalType : Expr) (ante : Name) (lem : Name) (symm : Bool)
    (shallow : Bool := false)
    (harvest? : Option (IO.Ref (Array HarvestEntry)) := none)
    (proofOverride? : Option Expr := none) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let root ← mkFreshExprMVar goalType
    let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
             else do let (_, g) ← root.mvarId!.intros; pure g
    let anteExpr ← mkConstWithFreshMVarLevels ante
    let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
    let (_, g1) ← g1.intro1P
    -- R6: transport entries rewrite with their fully-instantiated application
    -- (the bare constant would re-face the underdetermined second carrier)
    let lemExpr : MetaM Expr := match proofOverride? with
      | some p => pure p
      | none => mkConstWithFreshMVarLevels lem
    -- the shared transform: rewrite the target (side goals collected), then each
    -- non-dependent Prop hypothesis; succeeds if ANY site rewrote (rw-at-* rule)
    let rewriteStar (gIn : MVarId) : MetaM (Option (MVarId × List MVarId)) := do
      let mut gg := gIn
      let mut side : List MVarId := []
      let mut any := false
      let tgtRes ← try
          let tgt ← gg.getType
          let r ← gg.rewrite tgt (← lemExpr) symm
          pure (some (← gg.replaceTargetEq r.eNew r.eqProof, r.mvarIds))
        catch _ => pure none
      if let some (g', ms) := tgtRes then
        gg := g'; side := side ++ ms; any := true
      for h in (← gg.getNondepPropHyps) do
        let ok ← try
            let hty ← gg.withContext do instantiateMVars (← h.getType)
            let r ← gg.rewrite hty (← lemExpr) symm
            if !r.mvarIds.isEmpty then pure none
            else pure (some (← gg.replaceLocalDecl h r.eNew r.eqProof))
          catch _ => pure none
        match ok with
        | some res => gg := res.mvarId; any := true
        | none => pure ()
      return if any then some (gg, side) else none
    let some (g2, side) ← rewriteStar g1 | (do restoreState s; return none)
    -- M4.8-D2v2: harvest the fired state. CONDITIONAL target rewrites (side
    -- goals pending) are NOT harvested — the deep step function cannot
    -- reproduce a state with an open side obligation.
    if let some ref := harvest? then
      if side.isEmpty then
        let key ← ppState g2
        ref.modify (·.push { key, lem, symm, viaSimp := false, shallow })
    let remaining ← finishStructurally ante g2
    let remSide ← structuralSolve (structuralSolveLemmas ante) side
    unless (remaining ++ remSide).isEmpty do
      restoreState s
      return none
    let vacuous ← if (← IO.getEnv "STATIC_EVAL_NO_REPLAY").isSome then pure false else
      withoutModifyingState do
      try
        let root2 ← mkFreshExprMVar goalType
        -- parity: the replay MUST open binders to the same depth as the attempt
        let gr ← if shallow then introsToFirstPropHyp root2.mvarId!
                 else do let (_, g) ← root2.mvarId!.intros; pure g
        match ← rewriteStar gr with
        | none => pure false
        | some (gg, side2) =>
          let rem2 ← structuralCore noAnteLemmas gg
          let remSide2 ← structuralSolve noAnteLemmas side2
          pure (rem2 ++ remSide2).isEmpty
      catch _ => pure false
    if vacuous then
      restoreState s
      return none
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasExprMVar then
      restoreState s
      return none
    return some proof
  catch _ =>
    restoreState s
    return none

/-- **M4.8-D2.** One SEQUENCE STEP for the deep search: a single lemma applied by
one strategy over hypotheses + target. Returns the residual goal, or `none` when
the step did not fire (simp unchanged / rw matched nowhere) or closed the goal
outright (single-step closes are the depth-1 arms' business, already tried).
Conditional rewrites are disallowed in steps — threading their side goals through
a sequence is deferred until something demands it. -/
def simpStepOnce (g : MVarId) (lem : Name) (symm : Bool) : MetaM (Option MVarId) := do
  try
    let mut st : SimpTheorems := {}
    st ← st.addConst lem (inv := symm)
    let ctx ← Simp.mkContext {} (simpTheorems := #[st])
      (congrTheorems := ← getSimpCongrTheorems)
    let hyps ← g.getNondepPropHyps
    match (← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps)).1 with
    | none => return none
    | some (_, g') => return some g'
  catch _ => return none

/-- See `simpStepOnce` — the `rw` strategy: one-shot rewrite of target + each
non-dependent Prop hypothesis, ≥1 site must fire. -/
def rwStepOnce (g : MVarId) (lem : Name) (symm : Bool) : MetaM (Option MVarId) := do
  try
    let mut gg := g
    let mut any := false
    let t ← try
        let tgt ← gg.getType
        let r ← gg.rewrite tgt (← mkConstWithFreshMVarLevels lem) symm
        if r.mvarIds.isEmpty then pure (some (← gg.replaceTargetEq r.eNew r.eqProof))
        else pure none
      catch _ => pure none
    if let some g' := t then
      gg := g'; any := true
    for h in (← gg.getNondepPropHyps) do
      let o ← try
          let hty ← gg.withContext do instantiateMVars (← h.getType)
          let r ← gg.rewrite hty (← mkConstWithFreshMVarLevels lem) symm
          if r.mvarIds.isEmpty then pure (some (← gg.replaceLocalDecl h r.eNew r.eqProof))
          else pure none
        catch _ => pure none
      if let some res := o then
        gg := res.mvarId; any := true
    return if any then some gg else none
  catch _ => return none

/-- Runtime-safe single step: `catch` does not intercept runtime exceptions
(deterministic timeouts, `maxRecDepth`, simp's nested errors) — only
`tryCatchRuntimeEx` does, and inside a search over many candidate steps a single
detonating candidate must cost that step, not the whole arm. -/
def stepSafe (viaSimp : Bool) (g : MVarId) (lem : Name) (symm : Bool)
    : MetaM (Option MVarId) :=
  tryCatchRuntimeEx
    (if viaSimp then simpStepOnce g lem symm else rwStepOnce g lem symm)
    (fun _ => return none)

/-- **M4.8-D2.** Run one PATH of the deep search: fresh root, staged intros,
assert the antecedent, apply the steps in order, close structurally. The
counterfactual replays the ENTIRE sequence without the antecedent at the SAME
intros depth. -/
def runDeepPath (goalType : Expr) (ante : Name)
    (path : List (Name × Bool × Bool)) (shallow : Bool) : MetaM (Option Expr) := do
  let s ← saveState
  let r ← tryCatchRuntimeEx (do
      let root ← mkFreshExprMVar goalType
      let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
               else do let (_, g) ← root.mvarId!.intros; pure g
      let anteExpr ← mkConstWithFreshMVarLevels ante
      let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
      let (_, g1) ← g1.intro1P
      let mut gg := g1
      let mut ok := true
      for (lem, symm, viaSimp) in path do
        match ← stepSafe viaSimp gg lem symm with
        | some g' => gg := g'
        | none => ok := false; break
      if !ok then pure none
      else do
      -- M4.8-D2v2 (Henry): after the sequence, the ANTECEDENT as a rewrite rule
      -- on the target — the same optional second pass the single bridge arms
      -- have, restoring close parity between depth 1 and depth ≥ 2. The
      -- counterfactual below deliberately OMITS it (it is ante-dependent).
      let afterAnte ← (do
        try
          let mut ast : SimpTheorems := {}
          ast ← ast.addConst ante
          let actx ← Simp.mkContext {} (simpTheorems := #[ast])
            (congrTheorems := ← getSimpCongrTheorems)
          match ← simpGoal gg actx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
          | (none, _)         => pure (none : Option MVarId)   -- ante pass closed it
          | (some (_, g2), _) => pure (some g2)
        catch _ => pure (some gg))
      let closedByStructural ← match afterAnte with
        | none => pure true
        | some gg2 => pure (← finishStructurally ante gg2).isEmpty
      if !closedByStructural then do
        if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
          let show1 := fun (t : Name × Bool × Bool) =>
            let (l, sy, v) := t
            (if v then "simp " else "rw ") ++ (if sy then "← " else "") ++ toString l
          IO.eprintln s!"[deep]   fired-but-unclosed: {path.map show1}"
        pure none
      else do
        let vac ← if (← IO.getEnv "STATIC_EVAL_NO_REPLAY").isSome then pure false else
          tryCatchRuntimeEx (withoutModifyingState do
            let r2 ← mkFreshExprMVar goalType
            let g2init ← if shallow then introsToFirstPropHyp r2.mvarId!
                         else do let (_, g) ← r2.mvarId!.intros; pure g
            let mut g2 := g2init
            let mut ok2 := true
            for (lem, symm, viaSimp) in path do
              match ← stepSafe viaSimp g2 lem symm with
              | some g' => g2 := g'
              | none => ok2 := false; break
            if !ok2 then pure false
            else pure (← structuralCore noAnteLemmas g2).isEmpty)
            (fun _ => pure false)
        if vac then pure none
        else do
          let proof ← instantiateMVars root
          if proof.hasSorry || proof.hasExprMVar then pure none
          else pure (some proof))
    (fun _ => pure none)
  if r.isNone then restoreState s
  return r

/-- **M4.8-D2v2 deep search** — the general WHILE-LOOP form (Henry, 2026-07-31).

Level 1 is the ordinary ladder: its single-lemma arms HARVEST their fired states
(via `HarvestEntry` side-channel) as they run, interleaved with their own closes;
if any single arm closes, the direction ends and the harvest is discarded. This
function runs only after the full ladder failed. Levels are then uniform:

* frontier := first `nStateCap` DISTINCT harvested states, first-come-first-served
  in arm (rank) order — level 1 has NO lemma cap, it uses whatever the ladder ran;
* per level (≤ `levelBudget` heartbeats, absolute): for each frontier state
  (reconstructed from its path — mvars cannot cross sessions), apply the top
  `nLemmaCap` candidates × both strategies; every transform landing on a state
  never seen before (GLOBAL dedup, base states included — kills `ℓ`/`←ℓ` cycles)
  gets the `simp only [ante]` pass + structural close IMMEDIATELY; survivors fill
  the next frontier up to `nStateCap`;
* budget death mid-level keeps partial results (side-channel refs survive the
  exception) and simply ends the level — truncation is best-first by rank.

Returns the closing proof and the DEPTH USED (= path length), for `bridgeDepth`. -/
def deepSearchLoop (goalType : Expr) (ante : Name)
    (harvest : Array HarvestEntry) (step2Entries : Array (Name × Bool))
    (nLemmaCap nStateCap levelBudget maxDepth : Nat)
    (rdForbid : NameSet := {})
    : MetaM (Option (Expr × Nat)) := do
  let trace := (← IO.getEnv "STATIC_EVAL_TRACE").isSome
  -- RD (2026-08-24, STATIC_EVAL_REDISCOVER=1): mid-path lemma re-discovery.
  -- Endpoint-only discovery freezes the step vocabulary (the measured
  -- `tendsto` echo chamber); RD re-probes each frontier STATE's goal (one
  -- bounded findRewrites, cap 16, shared module tree, same forbid set as
  -- discovery) and merges fresh Eq/Iff hits into that state's step set. Same
  -- audit posture: rd lemmas land in the recorded path, so `runDeepPath`'s
  -- ante-free replay covers them; the categorical audit grades the proof.
  let rdOn := (← IO.getEnv "STATIC_EVAL_REDISCOVER").isSome
  let rdTree? ← if rdOn then some <$> Meta.Rewrites.createModuleTreeRef else pure none
  let rdProbe (st : MVarId) : MetaM (List (Name × Bool)) := do
    match rdTree? with
    | none => pure []
    | some tree =>
      tryCatchRuntimeEx (st.withContext do
          -- IN the state's context: the goal type mentions the state's fvars
          let tgt ← instantiateMVars (← st.getType)
          let results ← Meta.Rewrites.findRewrites #[] tree st tgt
            (forbidden := rdForbid) (side := .none)
            (stopAtRfl := false) (max := 16) (leavePercentHeartbeats := 10)
          let known : NameSet := step2Entries.foldl (fun a (n, _) => a.insert n) {}
          let mut out : List (Name × Bool) := []
          for r in results do
            if let some lem := r.expr.getAppFn.constName? then
              unless known.contains lem || rdForbid.contains lem do
                out := (lem, r.symm) :: out
          pure out.reverse)
        (fun e => do
          if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
            IO.eprintln s!"[deep-rd] probe ERROR: {← e.toMessageData.toString}"
          pure [])
  -- rebuild a frontier state from its path; none if any step no longer fires
  let rebuild (path : List (Name × Bool × Bool)) (shallow : Bool)
      : MetaM (Option MVarId) := do
    tryCatchRuntimeEx (do
        let root ← mkFreshExprMVar goalType
        let g0 ← if shallow then introsToFirstPropHyp root.mvarId!
                 else do let (_, g) ← root.mvarId!.intros; pure g
        let anteExpr ← mkConstWithFreshMVarLevels ante
        let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
        let (_, g1) ← g1.intro1P
        let mut gg := g1
        let mut ok := true
        for (lem, symm, viaSimp) in path do
          match ← stepSafe viaSimp gg lem symm with
          | some g' => gg := g'
          | none => ok := false; break
        pure (if ok then some gg else none))
      (fun _ => pure none)
  -- global seen: the two base states + every harvested key
  let seenRef ← IO.mkRef (#[] : Array String)
  for sh in [true, false] do
    let k? ← tryCatchRuntimeEx (withoutModifyingState do
        let root ← mkFreshExprMVar goalType
        let g0 ← if sh then introsToFirstPropHyp root.mvarId!
                 else do let (_, g) ← root.mvarId!.intros; pure g
        let anteExpr ← mkConstWithFreshMVarLevels ante
        let g1 ← g0.assert `h_ante (← inferType anteExpr) anteExpr
        let (_, g1) ← g1.intro1P
        some <$> ppState g1)
      (fun _ => pure none)
    if let some k := k? then seenRef.modify (·.push k)
  -- frontier from the harvest: FCFS in arm order = rank order, dedup, cap
  let mut frontier : Array (List (Name × Bool × Bool) × Bool) := #[]
  for h in harvest do
    if frontier.size ≥ nStateCap then break
    unless (← seenRef.get).contains h.key do
      seenRef.modify (·.push h.key)
      frontier := frontier.push ([(h.lem, h.symm, h.viaSimp)], h.shallow)
  if trace then
    IO.eprintln s!"[deep] harvest {harvest.size} fired arms → frontier       {frontier.size} (cap {nStateCap})"
  let winnerRef ← IO.mkRef (none : Option (Expr × Nat))
  let mut level := 2
  while level ≤ maxDepth && !frontier.isEmpty do
    let nextRef ← IO.mkRef (#[] : Array (List (Name × Bool × Bool) × Bool))
    let frontierNow := frontier
    -- side-channel refs carry results OUT of the budget scope: heartbeat death
    -- mid-level keeps everything committed so far
    let _ ← tryCatchRuntimeEx (withHeartbeatBudget levelBudget do
        for (path, shallow) in frontierNow do
          if (← winnerRef.get).isSome then break
          let some st ← rebuild path shallow | continue
          let last := path.getLast!
          let rdExtra ← if rdOn then rdProbe st else pure []
          if trace && rdOn then
            IO.eprintln s!"[deep-rd] probed state (path len {path.length}): {rdExtra.length} fresh"
          if trace && !rdExtra.isEmpty then
            IO.eprintln s!"[deep-rd] +{rdExtra.length} fresh step lemmas at path len {path.length}: {(rdExtra.take 4).map (·.1)}"
          for (l2, s2) in step2Entries.toList.take nLemmaCap ++ rdExtra do
            if (← winnerRef.get).isSome then break
            unless l2 == last.1 && s2 != last.2.1 do
              for v2 in [true, false] do
                if (← winnerRef.get).isSome then break
                let key? ← tryCatchRuntimeEx (withoutModifyingState do
                    match ← stepSafe v2 st l2 s2 with
                    | some g' => some <$> ppState g'
                    | none => pure none)
                  (fun _ => pure none)
                if let some key := key? then
                  unless (← seenRef.get).contains key do
                    seenRef.modify (·.push key)
                    let newPath := path ++ [(l2, s2, v2)]
                    -- CLOSE on every unseen state (Henry decision 2)
                    match ← runDeepPath goalType ante newPath shallow with
                    | some prf => winnerRef.set (some (prf, newPath.length))
                    | none =>
                      if (← nextRef.get).size < nStateCap then
                        nextRef.modify (·.push (newPath, shallow))
        pure true)
      (fun _ => pure true)
    if let some w ← winnerRef.get then
      if trace then
        IO.eprintln s!"[deep] closed at depth {w.2}"
      return some w
    frontier ← nextRef.get
    if trace then
      IO.eprintln s!"[deep] level {level} done, next frontier {frontier.size}"
    level := level + 1
  return none

/-- The numeric-carrier ladder ℕ < ℤ < ℚ < ℝ, with the simp extensions that
lift statements INTO each carrier (the `zify`/`qify`/`rify` simp sets — pure
Iff-conclusioned bridges; `push_cast` is always added separately). -/
def carrierLadder : List (Name × List Name) :=
  [ (`Int,  [`zify_simps])
  , (`Rat,  [`zify_simps, `qify_simps])
  , (`Real, [`zify_simps, `qify_simps, `rify_simps]) ]

/-- Collect which ladder carriers (ℕ/ℤ/ℚ/ℝ) a statement mentions. -/
def carriersOf (e : Expr) : NameSet :=
  e.foldConsts {} fun n acc =>
    if n == ``Nat || n == ``Int || n == `Rat || n == `Real then acc.insert n else acc

/-- Carrier-lift targets worth trying for a goal/antecedent pair (M4.4): when
the two statements mention DIFFERENT ladder carriers, normalizing both ends
into a common larger carrier can make them meet (`∀ n : ℕ, …` vs casts in ℝ).
Returns the extension lists for every ladder carrier ≥ the pair's maximum,
starting at the smallest adequate one — at most two attempts. -/
def carrierLiftTargets (goalType anteType : Expr) : List (Name × List Name) :=
  let gs := carriersOf goalType
  let as := carriersOf anteType
  if gs.isEmpty || as.isEmpty then []
  else if (gs.toList.all as.contains) && (as.toList.all gs.contains) then []
  else
    let union := gs.toList ++ as.toList
    let rank : Name → Nat := fun n =>
      if n == ``Nat then 0 else if n == ``Int then 1 else if n == `Rat then 2 else 3
    let maxRank := union.foldl (fun m n => max m (rank n)) 0
    (carrierLadder.filter fun (c, _) => rank c ≥ maxRank).take 2

open LibrarySearch in
/-- The restricted candidate finder: the default discrimination-tree matches,
filtered — during search, before any application — to the antecedent, structural
constants, and Eq/Iff-conclusioned lemmas. The antecedent (an env-local constant
the imported-modules tree does not index) is prepended explicitly, so "apply the
antecedent, discharging its arguments structurally" is always the first candidate
tried. -/
def restrictedFinder (ante : Name) (ty : Expr) : MetaM (Array (Name × DeclMod)) := do
  let cands ← libSearchFindDecls ty
  let cands ← cands.filterM fun (n, _) => do
    if n == ante || structuralWhitelist.contains n || plumbingLemmas.contains n then
      return true
    eqIffConclusioned n
  let anteFirst : Array (Name × DeclMod) := #[(ante, .none), (ante, .mp), (ante, .mpr)]
  return anteFirst ++ cands

open LibrarySearch in
/-- Restricted library search (the strict tier's `exact?`/`apply?`).

Re-composition of `librarySearch'` with our finder: collect ALL candidate proofs
(`collectAll`), audit each one as it streams out, and accept the first that
passes — so a plausible-but-unauditable first candidate does not discard the
direction. In `exactMode` only fully-closed candidates count; otherwise
(apply?-mode) candidates with remaining side goals are accepted when the
structural solver closes those goals.

Returns `(proof, description)` of the accepted candidate. -/
def restrictedSearch (goalType : Expr) (ante : Name) (exactMode : Bool)
    (leavePercentHeartbeats : Nat := 10) : MetaM (Option (Expr × String)) := do
  let s ← saveState
  try
    let root := (← mkFreshExprMVar goalType).mvarId!
    let (_, goal) ← root.intros
    let cfg : ApplyConfig := { allowSynthFailures := true }
    if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
      let ctx ← readThe Core.Context
      let now ← IO.getNumHeartbeats
      IO.eprintln s!"[exact?] scope: init={ctx.initHeartbeats} max={ctx.maxHeartbeats} now={now} spent={now - ctx.initHeartbeats}"
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    -- goal.withContext is LOAD-BEARING: after `root.intros` the binders live in
    -- the goal's local context, and candidate collection inspects the goal type
    -- (DiscrTree keying can need an intro'd fvar's type, e.g. a projection of a
    -- bound hypothesis like `hσ.measurableSpace`). Without it the search threw
    -- `unknown free variable` on exactly the heavy-binder statements — swallowed
    -- by the catch below, so the arm 0ms-failed silently (measured: every cw
    -- pair; simple goals key without fvar lookups, which hid the bug).
    let candidates ← goal.withContext <| librarySearchSymm (restrictedFinder ante) goal
    if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
      IO.eprintln s!"[exact?] candidates collected: {candidates.size}"
    -- VANILLA-MECHANICS streaming loop (2026-08-25, probe-validated: the
    -- previous interior — structuralSolve as the per-candidate side-solver +
    -- a collectAll sweep of every candidate before any audit — burned the
    -- whole heartbeat scope where the stock `exact?` machinery needs
    -- milliseconds; probe: lib version timeout @100k vs 8ms for this shape).
    -- Per candidate: apply, fill side goals with the SAME cheap solver stock
    -- `exact?` uses (local assumptions, maxDepth 6, no exfalso), and on a full
    -- close audit IMMEDIATELY — first candidate that passes wins; an
    -- unauditable close just continues the scan (the original streaming
    -- intent, now with vanilla's early exit). Restriction stays where it
    -- belongs: the finder's vocabulary and the audit at acceptance.
    for c in candidates do
      if ← shouldAbort then break
      let rem? ← tryCatch (do
          let ((goal, mctx), (name, mod)) := c
          setMCtx mctx
          let lem ← mkLibrarySearchLemma name mod
          let newGoals ← goal.apply lem cfg
          let rem ← try
              LibrarySearch.solveByElim [] (exfalso := false) newGoals (maxDepth := 6)
            catch _ => pure newGoals
          pure (some rem))
        (fun _ => pure none)
      match rem? with
      | some [] =>
        let proof ← instantiateMVars (mkMVar root)
        -- P0 must run here too: with the ex-falso ban moved into the
        -- polarity walk, `auditProof` alone no longer covers `absurd` & co.
        if (← auditProof ante proof).isNone
            && (← exFalsoVacuous? ante proof).isNone then
          restoreState s
          return some (proof, "restricted exact?")
        restoreState s
      | some remaining =>
        if !exactMode && !remaining.isEmpty then
          -- apply?-mode: try to close the leftovers structurally
          let leftover ← structuralSolve (structuralSolveLemmas ante) remaining
          if leftover.isEmpty then
            let proof ← instantiateMVars (mkMVar root)
            if (← auditProof ante proof).isNone
                && (← exFalsoVacuous? ante proof).isNone then
              restoreState s
              return some (proof, "restricted apply? + structural side goals")
          restoreState s
        else
          restoreState s
      | none => restoreState s
    restoreState s
    return none
  catch e =>
    if (← IO.getEnv "STATIC_EVAL_TRACE").isSome then
      IO.eprintln s!"[exact?] swallowed exception: {← e.toMessageData.toString}"
    restoreState s
    return none
/-- Ante-free provability, core arms (mirrors the strict ladder minus the
antecedent — same probe-parity principle as `provableFromOwnHyps`): defeq/rfl,
structural close, restricted normalization. The discovery-rewrite arm lives in
`Search.lean` (needs the rw?-index). -/
def antefreeProvableCore (obl : Expr) : MetaM Bool := do
  if ← goalDefeqTrue obl then return true
  let s ← saveState
  let ok ← try
    let g := (← mkFreshExprMVar obl).mvarId!
    let (_, g) ← g.intros
    pure (← structuralCore noAnteLemmas g).isEmpty
  catch _ => pure false
  restoreState s
  if ok then return true
  let s ← saveState
  let ok ← try
    let g := (← mkFreshExprMVar obl).mvarId!
    let (_, g) ← g.intros
    let ctx ← normalizationContext none
    let hyps ← g.getNondepPropHyps
    let (res, _) ← simpGoal g ctx (simplifyTarget := true) (fvarIdsToSimp := hyps)
    match res with
    | none => pure true
    | some (_, g') => pure (← structuralCore noAnteLemmas g').isEmpty
  catch _ => pure false
  restoreState s
  return ok

/-- Gate-side term normalization: the restricted normalization simp set
(plumbing + push_cast, NO antecedent) applied to a statement as a term. The
ladder proves *through* this normalization, so the gate must decompose the
normalized form too — a pollutant behind one plumbing-removable wrapper
(`¬(A ∨ ¬q)` via `not_or`/`not_not`, `a ∈ {x | P x ∧ q}` via
`Set.mem_setOf_eq`) is invisible on the raw term (verified escape shapes). -/
def gateNormalize (t : Expr) : MetaM Expr := do
  try
    let ctx ← normalizationContext none
    let (r, _) ← Meta.simp t ctx
    pure r.expr
  catch _ => pure t

/-- All essential-use obligations of a goal: decompose the RAW goal and its
gate-normalized form, dedup structurally. Conjunct obligations only count when
a genuine split occurred somewhere (an un-split conclusion is the whole goal —
the vacuity probes own that case); decoration obligations always count.
Normalization is belt-and-braces in BOTH directions: it can EXPOSE a wrapped
pollutant, and if a simproc normalizes a ground pollutant away (`2+2=4` ↦
`True`), the raw decomposition still carries it. -/
def gateObligations (goalType : Expr) : MetaM (Array GateObl) := do
  let collect (t : Expr) : MetaM (Array GateObl) := do
    let (obls, split) ← decomposeObls #[] t 6
    return if split then obls else obls.filter (·.decoration)
  let mut out ← collect goalType
  for o in ← collect (← gateNormalize goalType) do
    unless out.any (·.expr == o.expr) do out := out.push o
  return out

/-- The antecedent's own content, decomposed EXACTLY like a goal (raw +
normalized, same generalization over inner binders — symmetry is what lets a
shared `∀ n, 6 ∣ n → 3 ∣ n` part match shape-for-shape), split into the two
rescue pools:

* `concl` — what the antecedent ASSERTS (conclusion parts, sub-nodes, and the
  whole statement). Rescues conjunct obligations.
* `hyps` — what the antecedent merely ASSUMES (decoration obligations = its
  hypothesis domains at any depth). Rescues ONLY decoration obligations: an
  antecedent that assumes `q` never licenses a candidate that asserts `q` —
  the verified sentinel is pol:div_2v3, whose pollutant `3 ∣ n` matches an
  ante hypothesis and must NOT be rescued (v1 pooled both, and only the
  cross-mctx bug kept it gated).

All patterns are closed terms: matching opens binders per-try in the ambient
mctx, so nothing here can dangle. -/
structure AntePatterns where
  concl : Array Expr := #[]
  hyps : Array Expr := #[]

/-- **M4.7-S3d-2.** `anteCanon?` is the antecedent's canonical δ-unfolded,
instance-canonicalized form — the form the GOAL side is decomposed on. Without it
the rescue patterns came from the RAW declaration type while `gateObligations`
decomposed the canonical goal, so a pattern could fail to match an obligation purely
because one side had a side-local definition folded and the other did not; the
obligation then fell through to the ante-free probe and could be rejected as
decoration, costing a faithful pair.

DIRECTION OF RISK, stated plainly: patterns are match TARGETS for the *rescue*
step, so adding forms can only rescue MORE obligations, hence reject FEWER. That is
recall-positive and **precision-exposed** — the opposite direction from most gate
changes — so pollution and traps are mandatory here, not optional. Both forms are
kept rather than substituting the canonical one, because a raw-form pattern that
matches today must keep matching. -/
def anteGatePatterns (ante : Name) (anteCanon? : Option Expr := none)
    : MetaM AntePatterns := do
  let some info := (← getEnv).find? ante | return {}
  let add (arr : Array Expr) (e : Expr) : Array Expr :=
    if arr.contains e then arr else arr.push e
  let mut concl : Array Expr := #[]
  let mut hyps : Array Expr := #[]
  let baseForms := match anteCanon? with
    | some c => [info.type, c]
    | none   => [info.type]
  let mut forms : List Expr := []
  for b in baseForms do
    forms := forms ++ [b, ← gateNormalize b]
  for t in forms do
    concl := add concl t
    -- no split-gating on the ante side: patterns are match TARGETS, and the
    -- unsplit atom body ("the whole assertion") is a legitimate counterpart;
    -- directional := iff nodes also license their two implications
    let (obls, _) ← decomposeObls #[] t 6 (directional := true)
    for o in obls do
      if o.decoration then hyps := add hyps o.expr
      else concl := add concl o.expr
  return { concl, hyps }

end StaticEval
