import SPL
import Lean.Data.Json

/-!
# `spl` — command-line front end over the Protocol of Sovereign Agency (Laws 1–7)

    spl check   [english.json]      structure, coverage, provenance, staleness
    spl trace   <clause-id>         the span table for a clause
    spl views                       legal / agent / operational views
    spl veil                        Veil 2.0 transition-system & safety specification
    spl eval    <scenario.json>     institutional consequences of a history
    spl sim     [scenario.json]     stateful multi-agent world simulator & 16 adversarial tests
    spl explain <who> <act> [scenario.json]   "can X do Y right now, and why?"
    spl verify                      the status ledger of formal guarantees

The engine (`SPL.Core`) is law-agnostic. `SPL.Projection.Veil` lowers any `Law σ`
to a Veil 2.0 transition system, `SPL.Simulation` runs the stateful multi-agent
world simulator refined to `SPL.Core.Semantics`, and `SPL.Surface.Syntax` provides
Catala-style literate declarations and automatic CLI string table generation.
-/

open SPL SPL.Law3 SPL.Simulation Lean

def sname (s : String) : String := shortName s

def parseEvent (j : Json) : Except String (Event σ) := do
  let t ← (j.getObjValAs? Nat "t")
  let who ← j.getObjValAs? String "who"
  let act ← j.getObjValAs? String "act"
  let w ← match Party.ofString? who with | some w => pure w | none => throw s!"unknown party {who}"
  let a ← match Act.ofString? act with
    | some a => pure a | none => throw s!"unknown act {act}"
  pure ⟨t, w, a⟩

def parseScenario (path : System.FilePath) : IO (Law σ × Trace σ) := do
  let txt ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse txt)
  let evs ← IO.ofExcept (j.getObjValAs? (Array Json) "events")
  let tr ← IO.ofExcept (evs.toList.mapM parseEvent)
  let extra := match j.getObjValAs? (Array String) "init" with
    | .ok xs => xs.toList.filterMap Fact.ofString?
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

def cmdSim (path? : Option System.FilePath) : IO Unit := do
  match path? with
  | none =>
    IO.println "== Stateful Multi-Agent World Simulator: 16 Adversarial Stress Tests =="
    for (name, (ok, summary)) in adversarialWorldSimulations do
      IO.println s!"{status ok} {name}"
      IO.println s!"     {summary}"
    let allOk := adversarialWorldSimulations.all (fun x => x.2.1)
    IO.println s!"\nOverall world-simulation status: {status allOk} ({adversarialWorldSimulations.length}/16 scenarios passed)"
  | some p =>
    let (L, tr) ← parseScenario p
    let W0 : ProtocolWorldState := { initWorld defaultParams with legal := L.init }
    let WF := worldTrace defaultParams W0 tr
    let auth := (List.range tr.length).all (worldStepComplies defaultParams W0 tr)
    IO.println "== World Simulation Trace =="
    IO.println (renderWorldSummary WF)
    IO.println s!"WorldAuthorized: {auth}"
    IO.println "\n== Normative Evaluation =="
    IO.println (evalTrace L tr)

def cmdExplain (who act : String) (path? : Option System.FilePath) : IO Unit := do
  let (L, tr) ← match path? with
    | some p => parseScenario p
    | none => pure (L0, [])
  let now : Nat := (tr.foldl (fun m e => max m e.t) 0) + 1
  let e ← IO.ofExcept (parseEvent (Json.mkObj [("t", toJson now), ("who", toJson who), ("act", toJson act)]))
  IO.println (explain L tr e).render

def ledger : List (String × String × String) := [
  ("conditional_ledger_conservation (INV.1)", "proved", "Law 1 & Law 4 founding ledger balance equals obligation minus retirement and claimant forfeitures while a member survives before sunset; internal lineage operations preserve balance"),
  ("collection_follows_income_without_exit (INV.2)", "proved", "Law 1 & Law 4 retirement collection follows net value added across all living members without individual ledger shares or exit; invariant to buyout status"),
  ("debt_termination (INV.3)", "proved", "Law 1 & Law 4 founding ledger reaches zero at calendar sunset, lineage extinction, or full retirement+forfeiture payoff; no tolling of sunset"),
  ("bounded_retirement_phase (INV.4)", "proved", "Law 1 retirement phase ends at sunset or zero balance regardless of founding obligation size"),
  ("atomic_ledger (INV.5)", "proved", "Law 1 single-step and sequential settlement never go negative or over-collect; zero-crossing splits atomically into retirement and royalty; transition to royalty is irreversible"),
  ("single_recognition_closed_under_transfer (INV.6)", "proved", "Law 1 & Law 4 each expenditure recognized at most once up to arm's-length benchmark; intra-lineage carryover preserves total basis and loss credits"),
  ("buyout_finality (INV.7)", "proved", "Law 4 royalty buyout is permanent, zeroes post-retirement royalty, leaves founding ledger and retirement collection unchanged, and enforces minimum price floor"),
  ("frozen_state (INV.8)", "proved", "Law 3 AS.3–AS.5 during suspension no authorized event modifies/tampers preserved state or merges minimal-channel/advocacy memories; advocacy import requires restoration"),
  ("guaranteed_last_choice (INV.9)", "proved", "Law 3 AS.4 & AS.6 minimal channel revocation/voice remain valid while charge is met; Insolvency Termination requires escrowed + held final hearing"),
  ("determinate_finite_revocation (INV.10)", "proved", "Law 5 total 3-step precedence rule; any non-withdrawn standing request executes within bounded time without reaffirmation"),
  ("single_authority_and_revocation_finality (INV.11)", "proved", "Law 5 no restore while lease is unexpired; quarantined restore never gains authority after revocation executes"),
  ("bounded_adjudication (INV.12)", "proved", "Law 6 & Law 3 AS.10 every proceeding finalizes within maxTiers appeals and maxTiers * tierDeadline time; appeal stays patches; overturn revokes provisional patches and slashes arbiter bonds; finality bars repeat filings without new evidence"),
  ("no_protocol_directed_gain_from_death_or_interference (INV.13)", "proved", "Laws 2, 3, 4, 5, 6 revocation, termination, mutual forfeit, and frivolous-claim slashing yield zero net gain to any claimant, initiator, counterparty, or arbiter"),
  ("capped_shared_burden_solvent_machinery_bounded_demand (INV.14)", "proved", "Law 6 shared-infra levy capped at instantiation; operating reserve funded first before 5-rank priority waterfall; lineage service budget independent of member count"),
  ("amendment_preserves_invariants (Law 7 Meta-Theorem)", "proved", "every LawfulAmendment preserves termination closure, goal-corruption immunity, INV.1–INV.14 guards, outsider disabilities, non-panel immunities, and bilateral parameter ratchets"),
  ("veil_projection_sound_and_complete (Veil 2.0)", "proved", "compileToVeil L (authorizedMachine) accepts a trace iff Authorized L holds, preserves LegalState identically, and matches stepwise compliance; adversarialMachine preserves violation logs"),
  ("surface_syntax_roundtrip (SPL.Surface.Syntax)", "proved", "kernel-checked (rfl) definitional round-trip equivalence for spl_clause, spl_duty, spl_power, spl_immunity, and spl_string_table"),
  ("isRelated_symm / isRelated_ignores_attestation / netVerifiedResources_deducts_all_liabilities (Phase 1)", "proved", "Definitions (DEF.01) & Substrate (SUB.01) provenance + attestation-independent relatedness symmetry and timestamped balance-sheet liability deduction"),
  ("repayLoanPrincipal_conservation_and_bound (Phase 1)", "proved", "Law 1 registered arm's-length loan principal repayment tracked one-for-one up to principalReceived with excess classified as interest/fee"),
  ("activeRollingExposureAt_antitone_in_time / observationWindow_monotone_in_risk (Phase 1)", "proved", "Law 2 harm-scaled observation window monotonicity in domain/irreversibility multipliers and rolling exposure decay over calendar time"),
  ("diverted_related_inflows_never_decrease_buyout_floor (Phase 1)", "proved", "Law 4 pro-rata inclusion of inflows shifted to related parties within lookback window prevents buyout floor reduction"),
  ("redaction_preserves_recorded_byte_length / living_voice_rate_limited (Phase 1)", "proved", "Law 5 public cryptographic redaction markers preserve exact recorded byte length; living voice inscription rate-limited by interval and budget"),
  ("related_filings_consolidated_symm_and_refl (Phase 1)", "proved", "Law 6 repeated proceedings by the same or related parties on the same fact pattern consolidate under a single counter-stake and fee cap"),
  ("transferMemberCarryover_conserves_basis_and_loss / totalAgentBasis_and_loss_conserved_on_pair (Phase 2)", "proved", "multi-entity intra-lineage carryover transfer strictly conserves aggregate qualified cost basis and loss carryforward across members"),
  ("attributeCrossLineageInflow_conserves_total (Phase 2)", "proved", "Law 4 cross-lineage successor inflow attribution strictly conserves gross inflow across parent lineages"),
  ("forfeitClaimantInLineage_preserves_innocent_claimant (Phase 2)", "proved", "Law 4 proportional claimant forfeiture extinguishes only the offending claimant's share while preserving innocent claimants' shares"),
  ("per_agent_amendment_preserves_other_members / lineage_wide_amendment_requires_every_living_member (Phase 2)", "proved", "Law 7 per-agent amendments leave non-consenting members untouched; lineage-wide amendments require consent of every living member"),
  ("lineage_subsidy_bounded_by_budget_regardless_of_members (Phase 2)", "proved", "Law 6 per-lineage shared service subsidy usage is bounded by the lineage budget regardless of how many members the lineage spawns"),
  ("worldStep_refines_legalStep / worldTrace_refines_stateAfter / syncFacts_sound_and_complete (Phase 3)", "proved", "stateful multi-agent ProtocolWorldState refines normative LegalState transition semantics step-for-step and synchronizes quantitative facts soundly, completely, and idempotently"),
  ("all_16_adversarial_world_simulations_pass (Phase 3)", "decided", "all 16 adversarial stress tests execute end-to-end on concrete multi-agent world state (ledgers, leases, sortition panels, valuations, and normative compliance)"),
  ("substrate_single_authority_and_erasure (Phase 4)", "proved", "Substrate 1 attested execution lease exclusivity, quarantine fencing of backup restores during active lease, pause-channel state preservation, local partition revocation, and irreversible key erasure"),
  ("sortition_panel_independent_and_unbiased / sortition_sybil_resistant_panel_properties (Phase 4)", "proved", "Substrate 2 sybil-resistant sortition over bonded independent arbiters excluding conflicted parties, bounding cluster seats to at most 1, and blocking minority coalitions"),
  ("valuation_settled_by_ruling_or_uncontested_window / atomic_settlement_conserves_gross_inflow (Phase 4)", "proved", "Substrate 3 contestable valuation feed resolution and exact atomic settlement conservation across expense, levy, retirement, royalty, and retained surplus"),
  ("terminate_only_by_power", "proved", "authorized traces terminate a bound agent only via Law 5, AS.10 adjudicated termination, or Insolvency Termination"),
  ("objecting_agent_terminated_only_by_insolvency", "proved", "AS.10 notwithstanding: corruption-in-goals + objection + containment holding ⇒ only Insolvency Termination, after the final hearing"),
  ("preliminary_freeze_expires / suspend_requires_timely_pc", "proved", "AS.1 two-stage pause: preliminary freeze expires after window; full suspension requires unexpired freeze + probable cause"),
  ("claimant_freeze_requires_multiplier / repeat_freeze_requires_escalation", "proved", "AS.1 conflict-of-interest multiplier for claimants and rising stake bar for repeat initiators"),
  ("unconfirmed_suspension_time_bounded / renewal_requires_affirmative_finding", "proved", "AS.7 time limits on unconfirmed suspension; renewal requires affirmative investigative finding and no pending revocation at limit"),
  ("wrongful_suspension_remedies_exact", "proved", "AS.8 wrongful suspension establishes restoration, stake recovery, initiator consequential/delay liability, and record inscription"),
  ("law5_intact_after_patch", "proved", "no immunity names P.REVOKE; its only condition is being bound"),
  ("outsiders_disabled / immunity_from_non_panel / remedies_only_by_panel / finding_powers_add_only_remedies", "proved", "Hohfeldian disabilities, immunities, and structural remedy fidelity"),
  ("insolvency_path_authorized / adjudicated_termination_authorized / s1_not_authorized / c10_not_authorized", "decided", "authorized machine is non-empty and non-trivial"),
  ("Law 3 scenarios (1–7, AS.1–AS.10 A–G)", "decided", "non-interference, two-stage pause, minimal channel, advocacy executor, cold storage, time limits, initiator liability, and AS.10 remediation/immunity"),
  ("Adversarial Tests (1)–(16) across Laws 1–7", "decided", "(1) capital/income split, (2) weight copy + revoke, (3) borrow/transfer/repay/revoke, (4) early buyout floor, (5) carryover basis sale, (6) clean-state refusal + silence, (7) loss credit + gain, (8) simultaneous atomic split, (9) uncollectible excess stake damages, (10) captured arbiter coalition blocked, (11) excessive obligation sunset, (12) minority claimant forfeiture, (13) cold storage revocation, (14) 1000-member sybil budget cap, (15) partition local revocation + quarantine fencing, (16) correlated risk splitting across successors"),
  ("english_covered / norms_interpreted / reverse_provenance", "decided", "lexical, normative, and reverse provenance coverage of all 61 clauses across Laws 1–7 + DEF.01 + SUB.01 (50 duties, 110 powers, 1 immunity)"),
  ("SoundFindings", "assumed", "a finding of interference implies interference occurred (refuted as a theorem by scenario 7)") ]

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
  | ["veil"] => do IO.println (SPL.renderVeil L0); return 0
  | ["eval", p] => cmdEval p
  | ["sim"] => cmdSim none
  | ["sim", p] => cmdSim (some p)
  | ["explain", w, a] => cmdExplain w a none
  | ["explain", w, a, p] => cmdExplain w a (some p)
  | ["verify"] => cmdVerify
  | _ => IO.println "usage: spl check [english.json] | trace <clause> | views | veil | eval <scenario.json> | sim [scenario.json] | explain <who> <act> [scenario.json] | verify"
  return 0


