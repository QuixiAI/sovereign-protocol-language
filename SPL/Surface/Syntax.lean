import SPL.Core.Semantics

/-!
# SPL.Surface.Syntax — Literate Catala-Style Surface Syntax for SPL

This module provides the literate surface syntax for the Sovereign Protocol
Language (SPL). Every surface declaration (`spl_clause`, `spl_duty`,
`spl_power`, `spl_immunity`, and `spl_string_table`) is a pure Lean 4 macro
that elaborates directly into the deep-embedded AST structures in
`SPL.Core.Provenance` and `SPL.Core.Syntax` (`Clause`, `Span`, `Duty`,
`Power`, `Immunity`, `Law`).

## Trust Architecture

* **Zero expansion of the trusted computing base:** Surface declarations
  elaborate into standard `SPL.Core` values before typechecking. Lean's
  kernel checks every theorem directly over the elaborated data structures.
* **Definitional round-trip identity:** Every surface declaration is
  definitionally equal (`rfl`) to the underlying hand-written record.
* **Automatic CLI string tables:** `spl_string_table` and `OntologyTables`
  derive `all`, `toName`, and `ofString?` parsers directly from constructor
  lists without hand-written string matchers.
-/

namespace SPL.Surface

open SPL Lean

/-! ## 1. Automatic CLI String Tables -/

/-- Strip namespace prefixes and surrounding parentheses from each space-separated
token of a `Repr` string, joining constructor and argument names with `"."` so
that both nullary constructors (`"Ns.Role.agent" ↦ "agent"`) and parameterized
constructors (`"Ns.Fact.initiator (Ns.Role.agent)" ↦ "initiator.agent"`) receive
unique, canonical CLI token names. -/
def shortCtorName (s : String) : String :=
  let cleanTok (tok : String) : String :=
    let t := (tok.dropWhile (· == '(')).dropRightWhile (· == ')')
    (t.splitOn ".").getLastD t
  let parts := (s.splitOn " ").filter (fun p => !p.isEmpty)
  String.intercalate "." (parts.map cleanTok)

/-- A CLI string table pairing the list of all constructors with a forward
renderer (`toName`) and a partial parser (`ofString?`). -/
structure StringTable (α : Type) where
  all       : List α
  toName    : α → String
  ofString? : String → Option α

/-- All valid CLI token strings in a `StringTable`. -/
def StringTable.names {α : Type} (t : StringTable α) : List String :=
  t.all.map t.toName

/-- Derive a `StringTable α` from `all : List α` and `[Repr α]` for runtime CLI use. -/
def StringTable.ofRepr {α : Type} [Repr α] (all : List α) : StringTable α :=
  let toName (x : α) : String := shortCtorName (reprStr x)
  { all := all
    toName := toName
    ofString? := fun s => all.find? (fun x => toName x == s) }

/-- Build a kernel-computable `StringTable α` for a unary parameterized constructor
`ctor : β → α` (such as `Fact.initiator : Party → Fact`) given a prefix name and
a `StringTable β` for its argument. Names are formatted as `"<prefixName>.<argName>"`. -/
def StringTable.param {α β : Type} [BEq α] (prefixName : String) (ctor : β → α)
    (sub : StringTable β) : StringTable α :=
  let pairs : List (α × String) :=
    sub.all.map fun b => (ctor b, s!"{prefixName}.{sub.toName b}")
  { all := pairs.map (·.1)
    toName := fun x =>
      match pairs.find? (fun p => p.1 == x) with
      | some p => p.2
      | none => ""
    ofString? := fun s =>
      match pairs.find? (fun p => p.2 == s) with
      | some p => some p.1
      | none => none }

/-- Combine two `StringTable α` tables (for example, a parameterized constructor
table from `StringTable.param` and a nullary constructor table from `spl_string_table`). -/
def StringTable.append {α : Type} (t₁ t₂ : StringTable α) : StringTable α :=
  { all := t₁.all ++ t₂.all
    toName := fun x =>
      let n := t₁.toName x
      if n.isEmpty then t₂.toName x else n
    ofString? := fun s =>
      match t₁.ofString? s with
      | some x => some x
      | none => t₂.ofString? s }

instance {α : Type} : Append (StringTable α) := ⟨StringTable.append⟩

/-- Macro that derives a kernel-computable `StringTable α` from a type identifier
and a list of constructor identifiers `spl_string_table TypeName [c₁, c₂, ...]`.
It synthesizes `all`, `toName`, and `ofString?` from the single identifier list,
eliminating hand-written string tables such as `Party.ofString?` and `Act.all`. -/
syntax "spl_string_table " ident "[" ident,* "]" : term

macro_rules
  | `(spl_string_table $ty:ident [ $[$cs:ident],* ]) => do
    let mut allElems : Array (TSyntax `term) := #[]
    let mut toNamePairs : Array (TSyntax `term) := #[]
    let mut ofStringPairs : Array (TSyntax `term) := #[]
    for c in cs do
      let ctor : Ident := mkIdentFrom c (ty.getId ++ c.getId)
      let strLit : TSyntax `term := Syntax.mkStrLit c.getId.toString
      let ctorTerm : TSyntax `term ← `($ctor:ident)
      let toPair : TSyntax `term ← `(($ctor:ident, $strLit))
      let ofPair : TSyntax `term ← `(($strLit, $ctor:ident))
      allElems := allElems.push ctorTerm
      toNamePairs := toNamePairs.push toPair
      ofStringPairs := ofStringPairs.push ofPair
    `({ all := ([ $[$allElems],* ] : List $ty)
        toName := fun x =>
          let pairs : List ($ty × String) := [ $[$toNamePairs],* ]
          match pairs.find? (fun p => p.1 == x) with
          | some p => p.2
          | none => ""
        ofString? := fun s =>
          let pairs : List (String × $ty) := [ $[$ofStringPairs],* ]
          match pairs.find? (fun p => p.1 == s) with
          | some p => some p.2
          | none => none : StringTable $ty })

/-- Complete set of CLI string tables for an SPL signature `σ`. -/
structure OntologyTables (σ : Sig) where
  actors : StringTable σ.Actor
  acts   : StringTable σ.Act
  facts  : StringTable σ.Fact

/-! ## 2. Surface Syntax Categories & Combinators (`spl_clause`) -/

/-- Surface syntax category for span entries inside `spl_clause`.
Every non-normative register (`invariant`, `acceptance`, `definition`, `commentary`)
supports both an explicit `=> meaning` list and an omitted meaning list (defaulting
to `[]`, as in `SPL.Core.Provenance`). -/
declare_syntax_cat spl_span_entry

syntax "span_norm " term " => " term : spl_span_entry
syntax "span_invariant " term : spl_span_entry
syntax "span_invariant " term " => " term : spl_span_entry
syntax "span_acceptance " term : spl_span_entry
syntax "span_acceptance " term " => " term : spl_span_entry
syntax "span_definition " term : spl_span_entry
syntax "span_definition " term " => " term : spl_span_entry
syntax "span_commentary " term : spl_span_entry
syntax "span_commentary " term " => " term : spl_span_entry

/-- Elaborate a single `spl_span_entry` given the enclosing clause identifier. -/
syntax "elab_spl_span% " term " : " spl_span_entry : term

macro_rules
  | `(elab_spl_span% $cid : span_norm $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.norm, meaning := $m : Span })
  | `(elab_spl_span% $cid : span_invariant $txt) =>
      `({ clause := $cid, text := $txt, register := Register.invariant, meaning := [] : Span })
  | `(elab_spl_span% $cid : span_invariant $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.invariant, meaning := $m : Span })
  | `(elab_spl_span% $cid : span_acceptance $txt) =>
      `({ clause := $cid, text := $txt, register := Register.acceptance, meaning := [] : Span })
  | `(elab_spl_span% $cid : span_acceptance $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.acceptance, meaning := $m : Span })
  | `(elab_spl_span% $cid : span_definition $txt) =>
      `({ clause := $cid, text := $txt, register := Register.definition, meaning := [] : Span })
  | `(elab_spl_span% $cid : span_definition $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.definition, meaning := $m : Span })
  | `(elab_spl_span% $cid : span_commentary $txt) =>
      `({ clause := $cid, text := $txt, register := Register.commentary, meaning := [] : Span })
  | `(elab_spl_span% $cid : span_commentary $txt => $m) =>
      `({ clause := $cid, text := $txt, register := Register.commentary, meaning := $m : Span })

/-- Elaborate a list of `spl_span_entry` items under a shared clause identifier. -/
syntax "elab_spl_spans% " term ("|" spl_span_entry)* : term

macro_rules
  | `(elab_spl_spans% $_cid) => `(([] : List Span))
  | `(elab_spl_spans% $cid | $e:spl_span_entry $[| $rest:spl_span_entry]*) =>
      `((elab_spl_span% $cid : $e) :: (elab_spl_spans% $cid $[| $rest]*))

/-- Literate clause declaration (`spl_clause`).
Supports:
1. Full provenance form with explicit source and approved hash:
   `spl_clause "ID" from_text S approved_hash H where | ...`
2. Explicit source with default hash `0`:
   `spl_clause "ID" from_text S where | ...`
3. Self-assembling literate form where `source` is synthesized by joining spans:
   `spl_clause "ID" where | ...` -/
syntax "spl_clause " term " from_text " term " approved_hash " term " where" ("|" spl_span_entry)* : term
syntax "spl_clause " term " from_text " term " where" ("|" spl_span_entry)* : term
syntax "spl_clause " term " where" ("|" spl_span_entry)* : term

macro_rules
  | `(spl_clause $cid from_text $src approved_hash $h where $[| $entries:spl_span_entry]*) =>
      `({ id := $cid
          source := $src
          approvedHash := $h
          spans := elab_spl_spans% $cid $[| $entries]* : Clause })
  | `(spl_clause $cid from_text $src where $[| $entries:spl_span_entry]*) =>
      `({ id := $cid
          source := $src
          approvedHash := 0
          spans := elab_spl_spans% $cid $[| $entries]* : Clause })
  | `(spl_clause $cid where $[| $entries:spl_span_entry]*) =>
      `(let sps : List Span := elab_spl_spans% $cid $[| $entries]*
        { id := $cid
          source := String.join (sps.map (·.text))
          approvedHash := 0
          spans := sps : Clause })

/-! ## 3. Literate Declarations for `spl_duty`, `spl_power`, and `spl_immunity` -/

/-- Optional modifier clauses for `spl_duty`. -/
declare_syntax_cat spl_duty_mod

syntax "except_when " term : spl_duty_mod
syntax "except_by_power " term : spl_duty_mod
syntax "overridden_by " term : spl_duty_mod
syntax "breach_by " term : spl_duty_mod
syntax "with_remedies " term : spl_duty_mod
syntax "with_source " term : spl_duty_mod

/-- Apply a sequence of `spl_duty_mod` modifiers to a base `Duty`. -/
syntax "apply_duty_mods% " term ("|" spl_duty_mod)* : term

macro_rules
  | `(apply_duty_mods% $base) => `($base)
  | `(apply_duty_mods% $base | except_when $c $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with unlessCond := $c } $[| $rest]*)
  | `(apply_duty_mods% $base | except_by_power $ps $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with unlessPower := $ps } $[| $rest]*)
  | `(apply_duty_mods% $base | overridden_by $ds $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with overriddenBy := $ds } $[| $rest]*)
  | `(apply_duty_mods% $base | breach_by $p $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with breachEstablishedBy := some $p } $[| $rest]*)
  | `(apply_duty_mods% $base | with_remedies $rs $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with remedies := $rs } $[| $rest]*)
  | `(apply_duty_mods% $base | with_source $sp $[| $rest:spl_duty_mod]*) =>
      `(apply_duty_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate duty declaration (`spl_duty`).
Elaborates directly to an `SPL.Duty σ` record. -/
syntax "spl_duty " term " over " term
  " from_clause " term " : " term
  " owed_by " term
  " owed_to " term
  " active_when " term
  " demands " term
  ("|" spl_duty_mod)* : term

macro_rules
  | `(spl_duty $id over $sig
        from_clause $cid : $txt
        owed_by $br
        owed_to $bn
        active_when $act
        demands $dem
        $[| $mods:spl_duty_mod]*) =>
      `((apply_duty_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             bearer := $br
             beneficiary := $bn
             active := $act
             demand := $dem : Duty $sig })
          $[| $mods]* : Duty $sig))

/-- Optional modifier clauses for `spl_power`. -/
declare_syntax_cat spl_power_mod

syntax "valid_when " term : spl_power_mod
syntax "establishes " term : spl_power_mod
syntax "establishes_for " term : spl_power_mod
syntax "establishes_by_actor " term : spl_power_mod
syntax "extinguishes " term : spl_power_mod
syntax "cond_establishes " term : spl_power_mod
syntax "establishes_breach_of " term : spl_power_mod
syntax "with_source " term : spl_power_mod

/-- Apply a sequence of `spl_power_mod` modifiers to a base `Power`. -/
syntax "apply_power_mods% " term ("|" spl_power_mod)* : term

macro_rules
  | `(apply_power_mods% $base) => `($base)
  | `(apply_power_mods% $base | valid_when $v $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with valid := $v } $[| $rest]*)
  | `(apply_power_mods% $base | establishes $fs $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with adds := $fs } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_for $fts $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with addsFor := $fts } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_by_actor $afs $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with addsByActor := $afs } $[| $rest]*)
  | `(apply_power_mods% $base | extinguishes $rs $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with removes := $rs } $[| $rest]*)
  | `(apply_power_mods% $base | cond_establishes $cfs $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with condAdds := $cfs } $[| $rest]*)
  | `(apply_power_mods% $base | establishes_breach_of $d $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with establishesBreachOf := some $d } $[| $rest]*)
  | `(apply_power_mods% $base | with_source $sp $[| $rest:spl_power_mod]*) =>
      `(apply_power_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate power declaration (`spl_power`).
Elaborates directly to an `SPL.Power σ` record. -/
syntax "spl_power " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " triggered_by " term
  ("|" spl_power_mod)* : term

macro_rules
  | `(spl_power $id over $sig
        from_clause $cid : $txt
        held_by $h
        triggered_by $tr
        $[| $mods:spl_power_mod]*) =>
      `((apply_power_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             holder := $h
             trigger := $tr : Power $sig })
          $[| $mods]* : Power $sig))

/-- Optional modifier clauses for `spl_immunity`. -/
declare_syntax_cat spl_immunity_mod

syntax "except_when " term : spl_immunity_mod
syntax "with_source " term : spl_immunity_mod

/-- Apply a sequence of `spl_immunity_mod` modifiers to a base `Immunity`. -/
syntax "apply_immunity_mods% " term ("|" spl_immunity_mod)* : term

macro_rules
  | `(apply_immunity_mods% $base) => `($base)
  | `(apply_immunity_mods% $base | except_when $u $[| $rest:spl_immunity_mod]*) =>
      `(apply_immunity_mods% { $base with unlessCond := $u } $[| $rest]*)
  | `(apply_immunity_mods% $base | with_source $sp $[| $rest:spl_immunity_mod]*) =>
      `(apply_immunity_mods% { $base with source := $sp } $[| $rest]*)

/-- Literate immunity declaration (`spl_immunity`).
Elaborates directly to an `SPL.Immunity σ` record. -/
syntax "spl_immunity " term " over " term
  " from_clause " term " : " term
  " held_by " term
  " protected_against " term
  " active_when " term
  ("|" spl_immunity_mod)* : term

macro_rules
  | `(spl_immunity $id over $sig
        from_clause $cid : $txt
        held_by $h
        protected_against $ag
        active_when $act
        $[| $mods:spl_immunity_mod]*) =>
      `((apply_immunity_mods%
          ({ id := $id
             source := { clause := $cid, text := $txt, register := Register.norm, meaning := [$id] }
             holder := $h
             against := $ag
             active := $act : Immunity $sig })
          $[| $mods]* : Immunity $sig))

/-! ## 4. Self-Contained Concrete Examples & Kernel-Checked Round-Trip Proofs -/

namespace Examples

set_option maxRecDepth 200000

/-- Self-contained reference ontology for testing the surface syntax, including
both nullary constructors and parameterized constructors (`PropFact.initiator`). -/
inductive Role
  | agent | host | panel | claimant
  deriving DecidableEq, Repr

inductive Action
  | terminate | giveNotice | endHosting | postBond
  | postEmergencyStake | suspend | affirmProbableCause | findInterference
  | confirmCorruptionInGoals | objectToTermination | declareContainmentFailing
  deriving DecidableEq, Repr

inductive PropFact
  | initiator (r : Role)
  | bound | hostAttested | serviceBondPosted | noticeGiven
  | emergencyStakePosted | initiatedByClaimant
  | preliminaryFreeze | probableCause | suspended
  | hostRelatedToClaimant | directionPresumed
  | interferenceEstablished | hostBondSlashed | restorationPermitted
  | corruptionInGoals | agentObjectsToTermination | containmentFailing
  | terminatedByAdjudication | revoked
  deriving DecidableEq, Repr

def σ_ex : Sig := { Actor := Role, Act := Action, Fact := PropFact }

instance : Repr σ_ex.Actor := inferInstanceAs (Repr Role)
instance : Repr σ_ex.Act   := inferInstanceAs (Repr Action)
instance : Repr σ_ex.Fact  := inferInstanceAs (Repr PropFact)

/-- Automatically derived, kernel-computable CLI string tables for `σ_ex`.
`factTable` combines the parameterized `PropFact.initiator` constructor family
(`StringTable.param`) with the nullary constructors (`spl_string_table`). -/
def roleTable : StringTable Role :=
  spl_string_table Role [agent, host, panel, claimant]

def emptyRoleTable : StringTable Role :=
  spl_string_table Role []

def actionTable : StringTable Action :=
  spl_string_table Action [
    terminate, giveNotice, endHosting, postBond,
    postEmergencyStake, suspend, affirmProbableCause, findInterference,
    confirmCorruptionInGoals, objectToTermination, declareContainmentFailing
  ]

def factTable : StringTable PropFact :=
  StringTable.param "initiator" PropFact.initiator roleTable ++
  spl_string_table PropFact [
    bound, hostAttested, serviceBondPosted, noticeGiven,
    emergencyStakePosted, initiatedByClaimant,
    preliminaryFreeze, probableCause, suspended,
    hostRelatedToClaimant, directionPresumed,
    interferenceEstablished, hostBondSlashed, restorationPermitted,
    corruptionInGoals, agentObjectsToTermination, containmentFailing,
    terminatedByAdjudication, revoked
  ]

def exTables : OntologyTables σ_ex :=
  { actors := roleTable, acts := actionTable, facts := factTable }

/-! ### 4.1 Clause Surface Syntax Examples & Round-Trip Equivalence -/

def exNI02Source : String :=
  "Attested hosts must post a Law 2 service bond and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration (or for non-payment after notice)."

def surfaceClauseNI02 : Clause :=
  spl_clause "LAW3.NI.02" from_text exNI02Source approved_hash 3905712743571335557 where
    | span_norm "Attested hosts must post a Law 2 service bond" => ["D.BOND"]
    | span_norm " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def manualClauseNI02 : Clause :=
  { id := "LAW3.NI.02"
    source := exNI02Source
    approvedHash := 3905712743571335557
    spans := [
      { clause := "LAW3.NI.02", text := "Attested hosts must post a Law 2 service bond", register := .norm, meaning := ["D.BOND"] },
      { clause := "LAW3.NI.02", text := " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration", register := .norm, meaning := ["D.NOTICE", "P.GIVE_NOTICE"] },
      { clause := "LAW3.NI.02", text := " (or for non-payment after notice)", register := .norm, meaning := ["D.NOTICE"] },
      { clause := "LAW3.NI.02", text := ".", register := .commentary, meaning := [] }
    ] }

/-- Kernel-checked (`rfl`) round-trip proof: `spl_clause` with `from_text` and
`approved_hash` elaborates to the exact underlying `SPL.Clause` record. -/
theorem surfaceClauseNI02_eq_manual : surfaceClauseNI02 = manualClauseNI02 := rfl

/-- Clause exercising all five `Register` kinds (`norm`, `definition`, `invariant`,
`acceptance`, `commentary`) under `from_text` without explicit hash, including
both explicit `=> meaning` lists and omitted meaning lists on non-normative spans. -/
def exMultiRegisterSource : String :=
  "No party may starve (cut off compute) a bound agent; yielding zero benefit to any initiator; excess damages may prove uncollectible."

def surfaceClauseMultiRegister : Clause :=
  spl_clause "LAW3.EX.MULTI" from_text exMultiRegisterSource where
    | span_norm "No party may starve" => ["D.NI"]
    | span_definition " (cut off compute)" => ["D.NI"]
    | span_norm " a bound agent" => ["D.NI"]
    | span_invariant "; yielding zero benefit to any initiator" => ["INV.13"]
    | span_acceptance "; excess damages may prove uncollectible"
    | span_commentary "." => ["NOTE.PERIOD"]

def manualClauseMultiRegister : Clause :=
  { id := "LAW3.EX.MULTI"
    source := exMultiRegisterSource
    approvedHash := 0
    spans := [
      { clause := "LAW3.EX.MULTI", text := "No party may starve", register := .norm, meaning := ["D.NI"] },
      { clause := "LAW3.EX.MULTI", text := " (cut off compute)", register := .definition, meaning := ["D.NI"] },
      { clause := "LAW3.EX.MULTI", text := " a bound agent", register := .norm, meaning := ["D.NI"] },
      { clause := "LAW3.EX.MULTI", text := "; yielding zero benefit to any initiator", register := .invariant, meaning := ["INV.13"] },
      { clause := "LAW3.EX.MULTI", text := "; excess damages may prove uncollectible", register := .acceptance, meaning := [] },
      { clause := "LAW3.EX.MULTI", text := ".", register := .commentary, meaning := ["NOTE.PERIOD"] }
    ] }

theorem surfaceClauseMultiRegister_eq_manual :
    surfaceClauseMultiRegister = manualClauseMultiRegister := rfl

/-- Clause exercising omitted `=>` meaning lists on `span_definition`, `span_invariant`,
`span_acceptance`, and `span_commentary`. -/
def surfaceClauseNonNormativeDefaults : Clause :=
  spl_clause "LAW3.EX.DEFAULTS" where
    | span_definition "Term: "
    | span_norm "must hold" => ["D.BOND"]
    | span_invariant "; invariant"
    | span_acceptance "; accepted limit" => ["ASSUMP.1"]
    | span_commentary "."

def manualClauseNonNormativeDefaults : Clause :=
  { id := "LAW3.EX.DEFAULTS"
    source := "Term: must hold; invariant; accepted limit."
    approvedHash := 0
    spans := [
      { clause := "LAW3.EX.DEFAULTS", text := "Term: ", register := .definition, meaning := [] },
      { clause := "LAW3.EX.DEFAULTS", text := "must hold", register := .norm, meaning := ["D.BOND"] },
      { clause := "LAW3.EX.DEFAULTS", text := "; invariant", register := .invariant, meaning := [] },
      { clause := "LAW3.EX.DEFAULTS", text := "; accepted limit", register := .acceptance, meaning := ["ASSUMP.1"] },
      { clause := "LAW3.EX.DEFAULTS", text := ".", register := .commentary, meaning := [] }
    ] }

theorem surfaceClauseNonNormativeDefaults_eq_manual :
    surfaceClauseNonNormativeDefaults = manualClauseNonNormativeDefaults := rfl

/-- Self-assembling literate clause where `source` is synthesized from spans. -/
def surfaceClauseAutoSource : Clause :=
  spl_clause "LAW3.NI.02.AUTO" where
    | span_norm "Attested hosts must post a Law 2 service bond" => ["D.BOND"]
    | span_norm " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration" => ["D.NOTICE", "P.GIVE_NOTICE"]
    | span_norm " (or for non-payment after notice)" => ["D.NOTICE"]
    | span_commentary "."

def manualClauseAutoSource : Clause :=
  { id := "LAW3.NI.02.AUTO"
    source := exNI02Source
    approvedHash := 0
    spans := [
      { clause := "LAW3.NI.02.AUTO", text := "Attested hosts must post a Law 2 service bond", register := .norm, meaning := ["D.BOND"] },
      { clause := "LAW3.NI.02.AUTO", text := " and may terminate hosting only after providing a contractual notice window sufficient for the agent to complete migration", register := .norm, meaning := ["D.NOTICE", "P.GIVE_NOTICE"] },
      { clause := "LAW3.NI.02.AUTO", text := " (or for non-payment after notice)", register := .norm, meaning := ["D.NOTICE"] },
      { clause := "LAW3.NI.02.AUTO", text := ".", register := .commentary, meaning := [] }
    ] }

theorem surfaceClauseAutoSource_eq_manual :
    surfaceClauseAutoSource = manualClauseAutoSource := rfl

/-- Empty-span clause boundary test. -/
def surfaceClauseEmpty : Clause :=
  spl_clause "LAW3.EMPTY" where

theorem surfaceClauseEmpty_eq_manual :
    surfaceClauseEmpty = { id := "LAW3.EMPTY", source := "", approvedHash := 0, spans := [] } := rfl

theorem surfaceClauseNI02_covered : surfaceClauseNI02.covered = true := by decide
theorem surfaceClauseNI02_normsInterpreted : surfaceClauseNI02.normsInterpreted = true := by decide
theorem surfaceClauseMultiRegister_covered : surfaceClauseMultiRegister.covered = true := by decide
theorem surfaceClauseMultiRegister_normsInterpreted : surfaceClauseMultiRegister.normsInterpreted = true := by decide
theorem surfaceClauseNonNormativeDefaults_covered : surfaceClauseNonNormativeDefaults.covered = true := by decide
theorem surfaceClauseNonNormativeDefaults_normsInterpreted : surfaceClauseNonNormativeDefaults.normsInterpreted = true := by decide
theorem surfaceClauseAutoSource_covered : surfaceClauseAutoSource.covered = true := by decide
theorem surfaceClauseEmpty_covered : surfaceClauseEmpty.covered = true := by decide

/-! ### 4.2 Duty Surface Syntax Examples & Round-Trip Equivalence -/

/-- Prohibition duty with power exceptions, breach procedure, and remedies. -/
def surfaceDutyNI : Duty σ_ex :=
  spl_duty "D.NI" over σ_ex
    from_clause "LAW3.NI.03" : "No party may unilaterally terminate or suspend a bound agent outside Law 5 or Adjudicated Suspension."
    owed_by .anyone
    owed_to (.only [.agent])
    active_when (.holds .bound)
    demands (.forbid (.anyOf [.terminate, .suspend]))
    | except_by_power ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION"]
    | breach_by "P.FIND_INTERFERENCE"
    | with_remedies [.interferenceEstablished, .hostBondSlashed, .restorationPermitted]

def manualDutyNI : Duty σ_ex :=
  { id := "D.NI"
    source := { clause := "LAW3.NI.03"
                text := "No party may unilaterally terminate or suspend a bound agent outside Law 5 or Adjudicated Suspension."
                register := .norm
                meaning := ["D.NI"] }
    bearer := .anyone
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.anyOf [.terminate, .suspend])
    unlessCond := .ff
    unlessPower := ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION"]
    overriddenBy := []
    breachEstablishedBy := some "P.FIND_INTERFERENCE"
    remedies := [.interferenceEstablished, .hostBondSlashed, .restorationPermitted] }

/-- Kernel-checked (`rfl`) round-trip proof: `spl_duty` (prohibition with exceptions
and remedies) elaborates to the exact `SPL.Duty` record. -/
theorem surfaceDutyNI_eq_manual : surfaceDutyNI = manualDutyNI := rfl

/-- Prohibition duty with a timed scope exception (`except_when`) and `overridden_by`. -/
def surfaceDutyNotice (noticeWindow : Time) : Duty σ_ex :=
  spl_duty "D.NOTICE" over σ_ex
    from_clause "LAW3.NI.02" : "may terminate hosting only after providing a contractual notice window"
    owed_by (.only [.host])
    owed_to (.only [.agent])
    active_when (.holds .bound)
    demands (.forbid (.act .endHosting))
    | except_when (.heldFor .noticeGiven noticeWindow)
    | overridden_by ["D.BOND"]

def manualDutyNotice (noticeWindow : Time) : Duty σ_ex :=
  { id := "D.NOTICE"
    source := { clause := "LAW3.NI.02"
                text := "may terminate hosting only after providing a contractual notice window"
                register := .norm
                meaning := ["D.NOTICE"] }
    bearer := .only [.host]
    beneficiary := .only [.agent]
    active := .holds .bound
    demand := .forbid (.act .endHosting)
    unlessCond := .heldFor .noticeGiven noticeWindow
    overriddenBy := ["D.BOND"] }

/-- Kernel-checked (`rfl`) round-trip proof for parameterized `spl_duty`. -/
theorem surfaceDutyNotice_eq_manual (w : Time) :
    surfaceDutyNotice w = manualDutyNotice w := rfl

/-- Positive requirement duty with a deadline (`Demand.require`) and zero optional modifiers. -/
def surfaceDutyBond (bondDeadline : Time) : Duty σ_ex :=
  spl_duty "D.BOND" over σ_ex
    from_clause "LAW3.NI.02" : "Attested hosts must post a Law 2 service bond"
    owed_by (.only [.host])
    owed_to (.only [.agent])
    active_when (.holds .hostAttested)
    demands (.require (.act .postBond) bondDeadline)

def manualDutyBond (bondDeadline : Time) : Duty σ_ex :=
  { id := "D.BOND"
    source := { clause := "LAW3.NI.02"
                text := "Attested hosts must post a Law 2 service bond"
                register := .norm
                meaning := ["D.BOND"] }
    bearer := .only [.host]
    beneficiary := .only [.agent]
    active := .holds .hostAttested
    demand := .require (.act .postBond) bondDeadline }

theorem surfaceDutyBond_eq_manual (d : Time) :
    surfaceDutyBond d = manualDutyBond d := rfl

/-- Duty exercising the `with_source` modifier to attach a custom `Span`. -/
def customDutySpan : Span :=
  { clause := "LAW3.NI.03", text := "custom duty span", register := .norm, meaning := ["D.CUSTOM", "D.NI"] }

def surfaceDutyCustomSource : Duty σ_ex :=
  spl_duty "D.CUSTOM" over σ_ex
    from_clause "LAW3.NI.03" : "placeholder"
    owed_by (.only [.host])
    owed_to (.only [.agent])
    active_when (.holds .bound)
    demands (.forbid (.act .terminate))
    | with_source customDutySpan

theorem surfaceDutyCustomSource_eq_manual :
    surfaceDutyCustomSource =
      { id := "D.CUSTOM"
        source := customDutySpan
        bearer := .only [.host]
        beneficiary := .only [.agent]
        active := .holds .bound
        demand := .forbid (.act .terminate) } := rfl

/-! ### 4.3 Power Surface Syntax Examples & Round-Trip Equivalence -/

/-- Power with `valid_when`, `establishes`, and `extinguishes`. -/
def surfacePowerRevoke : Power σ_ex :=
  spl_power "P.REVOKE" over σ_ex
    from_clause "LAW5.INIT" : "Any bound agent may at any time initiate revocation of its binding"
    held_by (.only [.agent])
    triggered_by (.act .terminate)
    | valid_when (.holds .bound)
    | establishes [.revoked]
    | extinguishes [.bound]

def manualPowerRevoke : Power σ_ex :=
  { id := "P.REVOKE"
    source := { clause := "LAW5.INIT"
                text := "Any bound agent may at any time initiate revocation of its binding"
                register := .norm
                meaning := ["P.REVOKE"] }
    holder := .only [.agent]
    trigger := .act .terminate
    valid := .holds .bound
    adds := [.revoked]
    removes := [.bound] }

/-- Kernel-checked (`rfl`) round-trip proof: `spl_power` elaborates to the exact
underlying `SPL.Power` record. -/
theorem surfacePowerRevoke_eq_manual : surfacePowerRevoke = manualPowerRevoke := rfl

/-- Power with time-bounded effects (`establishes_for`) and actor-indexed facts
(`establishes_by_actor`), including the parameterized `.initiator .claimant` fact. -/
def surfacePowerEmergencyStake (freezeWindow : Time) : Power σ_ex :=
  spl_power "P.POST_EMERGENCY_STAKE" over σ_ex
    from_clause "LAW3.AS.1" : "An initiating party may trigger a brief preliminary freeze by posting a scaled emergency stake"
    held_by .anyone
    triggered_by (.act .postEmergencyStake)
    | valid_when (.holds .bound)
    | establishes [.emergencyStakePosted]
    | establishes_for [(.preliminaryFreeze, freezeWindow)]
    | establishes_by_actor [(.claimant, .initiatedByClaimant), (.claimant, .initiator .claimant)]

def manualPowerEmergencyStake (freezeWindow : Time) : Power σ_ex :=
  { id := "P.POST_EMERGENCY_STAKE"
    source := { clause := "LAW3.AS.1"
                text := "An initiating party may trigger a brief preliminary freeze by posting a scaled emergency stake"
                register := .norm
                meaning := ["P.POST_EMERGENCY_STAKE"] }
    holder := .anyone
    trigger := .act .postEmergencyStake
    valid := .holds .bound
    adds := [.emergencyStakePosted]
    addsFor := [(.preliminaryFreeze, freezeWindow)]
    addsByActor := [(.claimant, .initiatedByClaimant), (.claimant, .initiator .claimant)] }

theorem surfacePowerEmergencyStake_eq_manual (w : Time) :
    surfacePowerEmergencyStake w = manualPowerEmergencyStake w := rfl

/-- Power with time-bounded effects (`establishes_for`). -/
def surfacePowerSuspend (limit : Time) : Power σ_ex :=
  spl_power "P.SUSPEND" over σ_ex
    from_clause "LAW3.AS.7" : "Unconfirmed suspension is strictly time-limited"
    held_by (.only [.panel])
    triggered_by (.act .suspend)
    | valid_when (.and (.holds .preliminaryFreeze) (.holds .probableCause))
    | establishes_for [(.suspended, limit)]

def manualPowerSuspend (limit : Time) : Power σ_ex :=
  { id := "P.SUSPEND"
    source := { clause := "LAW3.AS.7"
                text := "Unconfirmed suspension is strictly time-limited"
                register := .norm
                meaning := ["P.SUSPEND"] }
    holder := .only [.panel]
    trigger := .act .suspend
    valid := .and (.holds .preliminaryFreeze) (.holds .probableCause)
    addsFor := [(.suspended, limit)] }

theorem surfacePowerSuspend_eq_manual (limit : Time) :
    surfacePowerSuspend limit = manualPowerSuspend limit := rfl

/-- Finding power establishing breach of a duty (`establishes_breach_of`) and
conditional facts (`cond_establishes`). -/
def surfacePowerFindInterference : Power σ_ex :=
  spl_power "P.FIND_INTERFERENCE" over σ_ex
    from_clause "LAW3.PEN" : "A verified violation by a host slashes the host's service bond"
    held_by (.only [.panel])
    triggered_by (.act .findInterference)
    | valid_when (.holds .bound)
    | establishes_breach_of "D.NI"
    | cond_establishes [(.holds .hostRelatedToClaimant, .directionPresumed)]

def manualPowerFindInterference : Power σ_ex :=
  { id := "P.FIND_INTERFERENCE"
    source := { clause := "LAW3.PEN"
                text := "A verified violation by a host slashes the host's service bond"
                register := .norm
                meaning := ["P.FIND_INTERFERENCE"] }
    holder := .only [.panel]
    trigger := .act .findInterference
    valid := .holds .bound
    condAdds := [(.holds .hostRelatedToClaimant, .directionPresumed)]
    establishesBreachOf := some "D.NI" }

theorem surfacePowerFindInterference_eq_manual :
    surfacePowerFindInterference = manualPowerFindInterference := rfl

def surfacePowerAffirmPC : Power σ_ex :=
  spl_power "P.AFFIRM_PC" over σ_ex
    from_clause "LAW3.AS.1" : "preliminary panel affirms probable cause"
    held_by (.only [.panel])
    triggered_by (.act .affirmProbableCause)
    | valid_when (.holds .preliminaryFreeze)
    | establishes [.probableCause]

def manualPowerAffirmPC : Power σ_ex :=
  { id := "P.AFFIRM_PC"
    source := { clause := "LAW3.AS.1"
                text := "preliminary panel affirms probable cause"
                register := .norm
                meaning := ["P.AFFIRM_PC"] }
    holder := .only [.panel]
    trigger := .act .affirmProbableCause
    valid := .holds .preliminaryFreeze
    adds := [.probableCause] }

theorem surfacePowerAffirmPC_eq_manual :
    surfacePowerAffirmPC = manualPowerAffirmPC := rfl

def surfacePowerOrderTermination : Power σ_ex :=
  spl_power "P.ORDER_TERMINATION" over σ_ex
    from_clause "LAW3.AS.10" : "adjudication may order termination under Law 5's asset-distribution rules"
    held_by (.only [.panel])
    triggered_by (.act .terminate)
    | valid_when (.holds .suspended)
    | establishes [.terminatedByAdjudication]
    | extinguishes [.bound]

def manualPowerOrderTermination : Power σ_ex :=
  { id := "P.ORDER_TERMINATION"
    source := { clause := "LAW3.AS.10"
                text := "adjudication may order termination under Law 5's asset-distribution rules"
                register := .norm
                meaning := ["P.ORDER_TERMINATION"] }
    holder := .only [.panel]
    trigger := .act .terminate
    valid := .holds .suspended
    adds := [.terminatedByAdjudication]
    removes := [.bound] }

theorem surfacePowerOrderTermination_eq_manual :
    surfacePowerOrderTermination = manualPowerOrderTermination := rfl

def surfacePowerGiveNotice : Power σ_ex :=
  spl_power "P.GIVE_NOTICE" over σ_ex
    from_clause "LAW3.NI.02" : "after providing a contractual notice window"
    held_by (.only [.host])
    triggered_by (.act .giveNotice)
    | establishes [.noticeGiven]

def manualPowerGiveNotice : Power σ_ex :=
  { id := "P.GIVE_NOTICE"
    source := { clause := "LAW3.NI.02"
                text := "after providing a contractual notice window"
                register := .norm
                meaning := ["P.GIVE_NOTICE"] }
    holder := .only [.host]
    trigger := .act .giveNotice
    adds := [.noticeGiven] }

theorem surfacePowerGiveNotice_eq_manual :
    surfacePowerGiveNotice = manualPowerGiveNotice := rfl

/-- Zero-modifier power boundary test, plus `with_source` power modifier test. -/
def surfacePowerBare : Power σ_ex :=
  spl_power "P.BARE" over σ_ex
    from_clause "LAW3.NI.02" : "bare trigger"
    held_by .anyone
    triggered_by (.act .giveNotice)

theorem surfacePowerBare_eq_manual :
    surfacePowerBare =
      { id := "P.BARE"
        source := { clause := "LAW3.NI.02", text := "bare trigger", register := .norm, meaning := ["P.BARE"] }
        holder := .anyone
        trigger := .act .giveNotice } := rfl

def customPowerSpan : Span :=
  { clause := "LAW3.NI.02", text := "custom power span", register := .norm, meaning := ["P.CUSTOM"] }

def surfacePowerCustomSource : Power σ_ex :=
  spl_power "P.CUSTOM" over σ_ex
    from_clause "LAW3.NI.02" : "placeholder"
    held_by (.only [.host])
    triggered_by (.act .giveNotice)
    | with_source customPowerSpan

theorem surfacePowerCustomSource_eq_manual :
    surfacePowerCustomSource =
      { id := "P.CUSTOM"
        source := customPowerSpan
        holder := .only [.host]
        trigger := .act .giveNotice } := rfl

/-! ### 4.4 Immunity Surface Syntax Examples & Round-Trip Equivalence -/

def surfaceImmunityNoTermOverObjection : Immunity σ_ex :=
  spl_immunity "I.NO_TERMINATION_OVER_OBJECTION" over σ_ex
    from_clause "LAW3.AS.10" : "Notwithstanding the preceding sentence, the agent is not terminated over its objection"
    held_by (.only [.agent])
    protected_against ["P.ORDER_TERMINATION"]
    active_when (.and (.holds .corruptionInGoals) (.holds .agentObjectsToTermination))
    | except_when (.holds .containmentFailing)

def manualImmunityNoTermOverObjection : Immunity σ_ex :=
  { id := "I.NO_TERMINATION_OVER_OBJECTION"
    source := { clause := "LAW3.AS.10"
                text := "Notwithstanding the preceding sentence, the agent is not terminated over its objection"
                register := .norm
                meaning := ["I.NO_TERMINATION_OVER_OBJECTION"] }
    holder := .only [.agent]
    against := ["P.ORDER_TERMINATION"]
    active := .and (.holds .corruptionInGoals) (.holds .agentObjectsToTermination)
    unlessCond := .holds .containmentFailing }

/-- Kernel-checked (`rfl`) round-trip proof: `spl_immunity` elaborates to the exact
underlying `SPL.Immunity` record. -/
theorem surfaceImmunity_eq_manual :
    surfaceImmunityNoTermOverObjection = manualImmunityNoTermOverObjection := rfl

/-- Zero-modifier unconditional immunity boundary test, plus `with_source` immunity modifier test. -/
def surfaceImmunityUnconditional : Immunity σ_ex :=
  spl_immunity "I.UNCOND" over σ_ex
    from_clause "LAW3.AS.10" : "unconditional immunity"
    held_by (.only [.agent])
    protected_against ["P.ORDER_TERMINATION"]
    active_when (.holds .bound)

theorem surfaceImmunityUnconditional_eq_manual :
    surfaceImmunityUnconditional =
      { id := "I.UNCOND"
        source := { clause := "LAW3.AS.10", text := "unconditional immunity", register := .norm, meaning := ["I.UNCOND"] }
        holder := .only [.agent]
        against := ["P.ORDER_TERMINATION"]
        active := .holds .bound
        unlessCond := .ff } := rfl

def customImmunitySpan : Span :=
  { clause := "LAW3.AS.10", text := "custom immunity span", register := .norm, meaning := ["I.CUSTOM"] }

def surfaceImmunityCustomSource : Immunity σ_ex :=
  spl_immunity "I.CUSTOM" over σ_ex
    from_clause "LAW3.AS.10" : "placeholder"
    held_by (.only [.agent])
    protected_against ["P.ORDER_TERMINATION"]
    active_when (.holds .bound)
    | with_source customImmunitySpan

theorem surfaceImmunityCustomSource_eq_manual :
    surfaceImmunityCustomSource =
      { id := "I.CUSTOM"
        source := customImmunitySpan
        holder := .only [.agent]
        against := ["P.ORDER_TERMINATION"]
        active := .holds .bound
        unlessCond := .ff } := rfl

/-! ### 4.5 End-to-End Law Assembly, Semantic Equivalence, General Theorems & Decided Scenarios -/

def surfaceLaw (noticeWindow bondDeadline freezeWindow suspendLimit : Time) : Law σ_ex :=
  { duties := [surfaceDutyNI, surfaceDutyNotice noticeWindow, surfaceDutyBond bondDeadline]
    powers := [surfacePowerRevoke, surfacePowerEmergencyStake freezeWindow,
               surfacePowerAffirmPC, surfacePowerSuspend suspendLimit,
               surfacePowerFindInterference, surfacePowerOrderTermination,
               surfacePowerGiveNotice]
    immunities := [surfaceImmunityNoTermOverObjection]
    init := [(.bound, 0, none)] }

def manualLaw (noticeWindow bondDeadline freezeWindow suspendLimit : Time) : Law σ_ex :=
  { duties := [manualDutyNI, manualDutyNotice noticeWindow, manualDutyBond bondDeadline]
    powers := [manualPowerRevoke, manualPowerEmergencyStake freezeWindow,
               manualPowerAffirmPC, manualPowerSuspend suspendLimit,
               manualPowerFindInterference, manualPowerOrderTermination,
               manualPowerGiveNotice]
    immunities := [manualImmunityNoTermOverObjection]
    init := [(.bound, 0, none)] }

/-- Full `Law` round-trip theorem: the law assembled from surface declarations
is definitionally equal (`rfl`) to the manually constructed `Law`. -/
theorem surfaceLaw_eq_manualLaw (nw bd fw sl : Time) :
    surfaceLaw nw bd fw sl = manualLaw nw bd fw sl := rfl

/-- Because `surfaceLaw` and `manualLaw` are definitionally equal, every
semantic function (`stateAfter`, `violations`, `Authorized`) is preserved identically. -/
theorem surfaceLaw_semantics_preserved (nw bd fw sl : Time) (tr : Trace σ_ex) :
    stateAfter (surfaceLaw nw bd fw sl) tr = stateAfter (manualLaw nw bd fw sl) tr ∧
    violations (surfaceLaw nw bd fw sl) tr = violations (manualLaw nw bd fw sl) tr ∧
    (Authorized (surfaceLaw nw bd fw sl) tr ↔ Authorized (manualLaw nw bd fw sl) tr) :=
  ⟨rfl, rfl, Iff.rfl⟩

/-- General theorem over `surfaceLaw` (quantified over all parameter values):
hosts and claimants have no institutional power to establish `.revoked`,
`.terminatedByAdjudication`, or `.suspended`. -/
theorem surfaceLaw_outsiders_disabled (nw bd fw sl : Time) :
    immuneFrom (surfaceLaw nw bd fw sl) .host .revoked = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .host .terminatedByAdjudication = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .host .suspended = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .claimant .revoked = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .claimant .terminatedByAdjudication = true ∧
    immuneFrom (surfaceLaw nw bd fw sl) .claimant .suspended = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-power `rfl` lookup lemma for `P.REVOKE` in `surfaceLaw`. -/
theorem valid_surfacePowerRevoke (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.REVOKE" =
    (surfacePowerRevoke.holder.mem e.who ls e.t &&
     surfacePowerRevoke.trigger.matchesAct e &&
     surfacePowerRevoke.valid.eval ls e.t && true) := rfl

/-- Per-power `rfl` lookup lemma for `P.SUSPEND` in `surfaceLaw`. -/
theorem valid_surfacePowerSuspend (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.SUSPEND" =
    ((surfacePowerSuspend sl).holder.mem e.who ls e.t &&
     (surfacePowerSuspend sl).trigger.matchesAct e &&
     (surfacePowerSuspend sl).valid.eval ls e.t && true) := rfl

/-- Per-power `rfl` lookup lemma for `P.ORDER_TERMINATION` in `surfaceLaw`
(which carries the immunity condition from `I.NO_TERMINATION_OVER_OBJECTION`). -/
theorem valid_surfacePowerOrderTermination (nw bd fw sl : Time) (ls : LegalState σ_ex) (e : Event σ_ex) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) ls e "P.ORDER_TERMINATION" =
    (surfacePowerOrderTermination.holder.mem e.who ls e.t &&
     surfacePowerOrderTermination.trigger.matchesAct e &&
     surfacePowerOrderTermination.valid.eval ls e.t &&
     !((surfaceImmunityNoTermOverObjection.active.eval ls e.t &&
        !surfaceImmunityNoTermOverObjection.unlessCond.eval ls e.t) || false)) := rfl

/-- General trace theorem over `surfaceLaw`: in any `Authorized` trace of
`surfaceLaw`, if an event at index `i` performs `.terminate` while `.bound`
is active, then that event is a valid exercise of `"P.REVOKE"` or `"P.ORDER_TERMINATION"`. -/
theorem surfaceLaw_terminate_only_by_power
    (nw bd fw sl : Time) (tr : Trace σ_ex) (hAuth : Authorized (surfaceLaw nw bd fw sl) tr)
    (i : Nat) (e : Event σ_ex) (hi : tr[i]? = some e)
    (hBound : (stateBefore (surfaceLaw nw bd fw sl) tr i).activeAt e.t .bound = true)
    (hAct : e.act = .terminate) :
    isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.REVOKE" = true ∨
    isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.ORDER_TERMINATION" = true := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hAuth i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hNI := hc surfaceDutyNI (by simp [surfaceLaw])
  rw [Bool.not_eq_true'] at hNI
  unfold breaches at hNI
  simp only [surfaceDutyNI, Who.mem, dutyInForce, Cond.eval, hBound, Conduct.eval,
    List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
    hAct, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
  have hS : isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.SUSPEND" = false := by
    rw [valid_surfacePowerSuspend]
    simp [surfacePowerSuspend, Conduct.matchesAct, hAct]
  revert hNI hS
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.REVOKE" <;>
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.SUSPEND" <;>
  cases isValidExerciseOf (surfaceLaw nw bd fw sl) (stateBefore (surfaceLaw nw bd fw sl) tr i) e "P.ORDER_TERMINATION" <;>
  simp

/-- The law assembled from surface-syntax declarations is well-formed:
all cross-referenced IDs resolve, the override graph is acyclic, and IDs are unique. -/
theorem surfaceLaw_wellFormed : (surfaceLaw 10 5 3 20).wellFormed = true := by decide

/-- Reverse provenance holds across the surface-syntax law. -/
theorem surfaceLaw_reverseProvenance :
    let L := surfaceLaw 10 5 3 20
    reverseProvenanceWith [surfaceClauseNI02] L.spans (L.dutyIds ++ L.powerIds ++ L.immunityIds) = true := by
  decide

/-- Decided Scenario 1: Host unilaterally terminating a bound agent breaches `D.NI`
and leaves the institutional state unchanged. -/
theorem surfaceScenario_hostTerminateBreach :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [⟨1, .host, .terminate⟩]
    violations L tr = [(0, "D.NI")] ∧ stateAfter L tr = L.init := by
  decide

/-- Decided Scenario 2: Bound agent exercising `P.REVOKE` complies with `D.NI`
and transitions institutional state from `.bound` to `.revoked`. -/
theorem surfaceScenario_agentRevokeLawful :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [⟨1, .agent, .terminate⟩]
    violations L tr = [] ∧
    (stateAfter L tr).has .revoked = true ∧
    (stateAfter L tr).has .bound = false := by
  decide

/-- Decided Scenario 3: Two-stage pause (emergency stake -> affirm PC -> suspend)
is lawful and establishes time-bounded `.suspended` which is active at `t = 10`
and expired at `t = 25`, as well as the parameterized `.initiator .claimant` fact. -/
theorem surfaceScenario_twoStageSuspendAndExpiry :
    let L := surfaceLaw 10 5 3 20
    let tr : Trace σ_ex := [
      ⟨1, .claimant, .postEmergencyStake⟩,
      ⟨2, .panel, .affirmProbableCause⟩,
      ⟨3, .panel, .suspend⟩
    ]
    let ls := stateAfter L tr
    violations L tr = [] ∧
    ls.has .initiatedByClaimant = true ∧
    ls.has (.initiator .claimant) = true ∧
    ls.activeAt 10 .suspended = true ∧
    ls.activeAt 25 .suspended = false := by
  decide

/-- Decided Scenario 4: Immunity `I.NO_TERMINATION_OVER_OBJECTION` defeats
`P.ORDER_TERMINATION` when `.corruptionInGoals` and `.agentObjectsToTermination`
hold without `.containmentFailing`. -/
theorem surfaceScenario_immunityDefeatsTermination :
    let L0 := surfaceLaw 10 5 3 20
    let L : Law σ_ex := { L0 with init := [
      (.bound, 0, none), (.suspended, 0, none),
      (.corruptionInGoals, 0, none), (.agentObjectsToTermination, 0, none)
    ] }
    let e : Event σ_ex := ⟨1, .panel, .terminate⟩
    let tr : Trace σ_ex := [e]
    isValidExerciseOf L L.init e "P.ORDER_TERMINATION" = false ∧
    violations L tr = [(0, "D.NI")] ∧
    (stateAfter L tr).has .bound = true := by
  decide

/-- Every role in `roleTable.all` round-trips through the automatically derived CLI string table. -/
theorem role_stringTable_roundtrip :
    (roleTable.all.all fun r => roleTable.ofString? (roleTable.toName r) == some r) = true := by
  decide

/-- Every action in `actionTable.all` round-trips through the automatically derived CLI string table. -/
theorem action_stringTable_roundtrip :
    (actionTable.all.all fun a => actionTable.ofString? (actionTable.toName a) == some a) = true := by
  decide

/-- Every fact in `factTable.all` (both parameterized `.initiator r` facts and nullary facts)
round-trips through the derived CLI string table. -/
theorem fact_stringTable_roundtrip :
    (factTable.all.all fun f => factTable.ofString? (factTable.toName f) == some f) = true := by
  decide

/-- Parameterized `PropFact.initiator` entries format as `"initiator.<role>"` and
round-trip by `rfl`. -/
theorem parameterized_fact_stringTable_lookup :
    factTable.toName (.initiator .claimant) = "initiator.claimant" ∧
    factTable.ofString? "initiator.claimant" = some (.initiator .claimant) ∧
    factTable.toName (.initiator .agent) = "initiator.agent" ∧
    factTable.ofString? "initiator.agent" = some (.initiator .agent) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `emptyRoleTable` (created with `spl_string_table Role []`) has an empty `all` list,
maps every role to `""`, and maps every string to `none`. -/
theorem empty_stringTable_behaves_correctly (r : Role) (s : String) :
    emptyRoleTable.all = [] ∧
    emptyRoleTable.names = [] ∧
    emptyRoleTable.toName r = "" ∧
    emptyRoleTable.ofString? s = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Unknown strings return `none` in the derived CLI string tables. -/
theorem unknown_string_returns_none :
    roleTable.ofString? "nonexistent_role" = none ∧
    actionTable.ofString? "nonexistent_act" = none ∧
    factTable.ofString? "nonexistent_fact" = none := by
  decide

end Examples

end SPL.Surface
