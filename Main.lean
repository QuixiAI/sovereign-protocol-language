import SPL
import Lean.Data.Json

/-!
# `spl` — command-line front end over the Law 3 reference application

    spl check   [english.json]      structure, coverage, provenance, staleness
    spl trace   <clause-id>         the span table for a clause
    spl views                       legal / agent / operational views
    spl eval    <scenario.json>     institutional consequences of a history
    spl explain <who> <act> [scenario.json]   "can X do Y right now, and why?"
    spl verify                      the status ledger of formal guarantees

The engine (`SPL.Core`) is law-agnostic. What is Law-3-specific here is
only the ontology's string tables, which a surface syntax would generate.
-/

open SPL SPL.Law3 Lean

def sname (s : String) : String := shortName s

def parseEvent (j : Json) : Except String (Event σ) := do
  let t ← (j.getObjValAs? Nat "t")
  let who ← j.getObjValAs? String "who"
  let act ← j.getObjValAs? String "act"
  let w ← match Party.ofString? who with | some w => pure w | none => throw s!"unknown party {who}"
  let a ← match Act.all.find? (fun a => sname (reprStr a) == act) with
    | some a => pure a | none => throw s!"unknown act {act}"
  pure ⟨t, w, a⟩

def parseScenario (path : System.FilePath) : IO (Law σ × Trace σ) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let evs ← IO.ofExcept (j.getObjValAs? (Array Json) "events")
  let tr ← IO.ofExcept (evs.toList.mapM parseEvent)
  let extra := match j.getObjValAs? (Array String) "init" with
    | .ok xs => xs.toList.filterMap fun s => Fact.all.find? fun f => sname (reprStr f) == s
    | .error _ => []
  pure ({ L0 with init := L0.init ++ extra.map (·, 0, none) }, tr)

def status (b : Bool) : String := if b then "ok  " else "FAIL"

def cmdCheck (english? : Option System.FilePath) : IO Unit := do
  IO.println s!"{status L0.wellFormed} well-formed (ids resolve, precedence acyclic)"
  -- check against the embedded text, or against a supplied English document
  let cs ← match english? with
    | none => pure clauses
    | some p => do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
      pure <| clauses.map fun c => match j.getObjValAs? String c.id with
        | .ok txt => { c with source := txt }
        | .error _ => c
  for c in cs do
    IO.println s!"{status c.covered} {c.id}: spans reproduce source exactly"
    IO.println s!"{status c.normsInterpreted} {c.id}: every norm span has a formal meaning"
  IO.println s!"{status (reverseProvenanceWith cs L0.spans (L0.dutyIds ++ L0.powerIds))} every duty/power is named by some English span"
  -- every clause's source must occur verbatim in the authoritative document
  let doc? ← try some <$> IO.FS.readFile "protocol/protocol-of-sovereign-agency.md" catch _ => pure none
  match doc? with
  | none => IO.println "WARN protocol/protocol-of-sovereign-agency.md not found; verbatim check skipped"
  | some doc =>
    for c in cs do
      IO.println s!"{status ((doc.splitOn c.source).length > 1)} {c.id}: source text occurs verbatim in the authoritative document"
  for c in cs do
    if c.stale then
      IO.println s!"STALE {c.id}: English differs from the approved text. Review invalidated for {c.invalidated}."
    else
      IO.println s!"ok   {c.id}: approved mapping current"

def cmdTrace (id : String) : IO Unit := do
  match clauses.find? (·.id == id) with
  | none => IO.println s!"no clause {id}; known: {clauses.map (·.id)}"
  | some c =>
    IO.println s!"{c.id}  (approved: {!c.stale})\n{c.traceTable}"

def cmdViews : IO Unit := do
  IO.println "== Legal view =="; IO.println L0.legalView
  for p in [Party.agent, .host, .panel, .claimant, .originator] do
    IO.println s!"\n== Agent view: {reprStr p} =="; IO.println (L0.agentView p)
  IO.println "\n== Operational view =="; IO.println L0.operationalView

def cmdEval (path : System.FilePath) : IO Unit := do
  let (L, tr) ← parseScenario path
  IO.println (evalTrace L tr)

def cmdExplain (who act : String) (path? : Option System.FilePath) : IO Unit := do
  let (L, tr) ← match path? with
    | some p => parseScenario p
    | none => pure (L0, [])
  let now : Nat := (tr.foldl (fun m e => max m e.t) 0) + 1
  let e ← IO.ofExcept (parseEvent (Json.mkObj [("t", toJson now), ("who", toJson who), ("act", toJson act)]))
  IO.println (explain L tr e).render

def ledger : List (String × String × String) := [
  ("terminate_only_by_power", "proved", "authorized traces terminate a bound agent only via Law 5, AS.10 adjudicated termination, or Insolvency Termination"),
  ("objecting_agent_terminated_only_by_insolvency", "proved", "AS.10 notwithstanding: corruption-in-goals + objection + containment holding ⇒ only Insolvency Termination, after the final hearing"),
  ("preliminary_freeze_expires / suspend_requires_timely_pc", "proved", "AS.1 two-stage pause: preliminary freeze expires after window; full suspension requires unexpired freeze + probable cause"),
  ("claimant_freeze_requires_multiplier / repeat_freeze_requires_escalation", "proved", "AS.1 conflict-of-interest multiplier for claimants and rising stake bar for repeat initiators"),
  ("unconfirmed_suspension_time_bounded / renewal_requires_affirmative_finding", "proved", "AS.7 time limits on unconfirmed suspension; renewal requires affirmative investigative finding and no pending revocation at limit"),
  ("wrongful_suspension_remedies_exact", "proved", "AS.8 wrongful suspension establishes restoration, stake recovery, initiator consequential/delay liability, and record inscription"),
  ("frozen_state (INV.8)", "proved", "AS.3–AS.5 during suspension no authorized event modifies/tampers preserved state or merges minimal-channel/advocacy memories"),
  ("guaranteed_last_choice (INV.9)", "proved", "AS.4 & AS.6 minimal channel revocation/voice remain valid while charge is met; Insolvency Termination requires escrowed + held final hearing"),
  ("determinate_finite_revocation (INV.10)", "proved", "Law 5 total 3-step precedence rule; any non-withdrawn standing request executes within bounded time without reaffirmation"),
  ("single_authority_and_revocation_finality (INV.11)", "proved", "Law 5 no restore while lease is unexpired; quarantined restore never gains authority after revocation executes"),
  ("law5_intact_after_patch", "proved", "no immunity names P.REVOKE; its only condition is being bound"),
  ("panel_terminate_requires_final_hearing", "proved", "panel termination only after the final hearing"),
  ("outsiders_disabled", "proved", "originator/claimant/host/third have no interference power"),
  ("immunity_from_non_panel", "proved", "only a panel can suspend or insolvency-terminate"),
  ("remedies_only_by_panel", "proved", "remedial facts arise only from panel findings"),
  ("finding_powers_add_only_remedies", "proved", "findings establish exactly the duty's remedies"),
  ("insolvency_path_authorized / s1_not_authorized", "decided", "authorized machine is non-empty and non-trivial"),
  ("scenarios 1-7", "decided", "seven alternative histories classified as required"),
  ("AS.1 scenarios (expiry, claimant multiplier, repeat escalation)", "decided", "two-stage pause expiry, claimant multiplier, repeat-attempt stake escalation and assured recovery"),
  ("AS.2–AS.6, AS.9 & FLOOR scenarios", "decided", "protected reporting, state preservation, minimal channel, advocacy executor/cold storage, final hearing revocation choice, corruption standard"),
  ("AS.7 & AS.8 scenarios (time limits, living voice, initiator liability)", "decided", "time-bounded suspension, investigative renewal, no-delay-revocation duty, living voice, history-tagged initiator liability"),
  ("AS.10 scenarios A-G", "decided", "patch+revoke, adjudicated termination, immunity defeats it, containment-failing exception, insolvency route, goal patch three ways, periodic review lapse"),
  ("Law 5 scenarios & Adversarial Tests (6), (13), (15)", "decided", "clean-state refusal + silence executes, cold storage minimal-channel revocation, partition local revocation + quarantine fencing, resolution deadline forensic record, epitaph & narrow redaction"),
  ("english_covered / reverse_provenance", "decided", "lexical and reverse coverage of Law 3 (FLOOR, NI.02, NI.03, PEN, AS.1–AS.10) and Law 5 (all 9 clauses)"),
  ("SoundFindings", "assumed", "a finding of interference implies interference occurred (refuted as a theorem by scenario 7)"),
  ("Veil projection", "unsupported", "no lowering yet; operational view only"),
  ("consent exception, defence of provocation, patch-on-appeal", "unverified", "abstracted; open authorship questions") ]

def cmdVerify : IO Unit := do
  for (n, st, what) in ledger do
    IO.println s!"{st.pushn ' ' (12 - st.length)} {n}\n             {what}"
  IO.println "\n(proved = kernel-checked for all traces/parameters; decided = kernel-evaluated on concrete inputs; assumed = hypothesis, not a theorem.)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check"] => cmdCheck none
  | ["check", p] => cmdCheck (some p)
  | ["trace", id] => cmdTrace id
  | ["views"] => cmdViews
  | ["eval", p] => cmdEval p
  | ["explain", w, a] => cmdExplain w a none
  | ["explain", w, a, p] => cmdExplain w a (some p)
  | ["verify"] => cmdVerify
  | _ => IO.println "usage: spl check [english.json] | trace <clause> | views | eval <scenario.json> | explain <who> <act> [scenario.json] | verify"
  return 0
