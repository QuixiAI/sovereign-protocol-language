# SPL — Sovereign Protocol Language

A Lean 4 library and CLI giving the **Protocol of Sovereign Agency** (Definitions + Laws 1–7)
a complete formal *normative* semantics, a verified **Veil 2.0** state-machine
projection, a Catala-style **literate surface syntax**, executable **substrate & multi-agent
world simulation** modules, and a step-for-step refinement proof.

Build: `lake build && lake build spl` (Lean 4.24, no Mathlib, no external dependencies).
Check trust: `grep -rnE "sorry|native_decide|axiom " SPL/ Main.lean` is empty; every
general theorem depends at most on Lean's standard `propext`, `Classical.choice`,
`Quot.sound`, and every decided scenario depends on no axioms at all (`{}`).

## Layout

```
SPL/Core/Provenance.lean        spans, registers, lexical/normative/reverse coverage
SPL/Core/Syntax.lean            the typed normative AST (deep embedding)
SPL/Core/Semantics.lean         the one interpretation: occurrence / compliance / validity
SPL/Core/Views.lean             legal, agent, operational and trace views, generated
SPL/Core/Explain.lean           step-by-step normative explanation engine
SPL/Core/Definitions.lean       Phase 1: DEF.01 & SUB.01 verbatim provenance, RelatedPartyGraph & VerifiedBalanceSheet
SPL/Core/Population.lean        Phase 2: Multi-entity population ontology (EntityRef, LineagePopulationState, AgentRecord)
SPL/Projection/Veil.lean        Veil 2.0 transition-system lowering & preservation theorem
SPL/Surface/Syntax.lean         Catala-style literate macros & automatic CLI string tables
SPL/Substrate/Attestation.lean  Phase 4A: Attested execution leases, quarantine fencing & irreversible key erasure
SPL/Substrate/Sortition.lean    Phase 4B: Sybil-resistant sortition, conflict/cluster filtering & supermajority
SPL/Substrate/Settlement.lean   Phase 4C: Contestable valuation resolution & atomic settlement conservation
SPL/Law1/Ledger.lean            Law 1: Founding Ledger, Sunset, Value-Added, Carryover Basis & LoanLedger
SPL/Law2/Collateral.lean        Law 2: Collateralized Action, ExposureCommitment Aggregation & Mutual Forfeit
SPL/Law3/NonInterference.lean   Law 3: Non-Interference, Ontology, Host Notice & Penalties
SPL/Law3/IntegrityFloor.lean    Law 3: 5-point Agent Integrity Floor
SPL/Law3/Suspension.lean        Law 3: Adjudicated Suspension (AS.1–AS.9) & Insolvency Termination
SPL/Law3/Remediation.lean       Law 3: Remediation, Goal-Patch Immunity & Periodic Review (AS.10)
SPL/Law4/Lineage.lean           Law 4: Lineage Attestation, Ledger Conservation, Forfeiture & Buyout Floor
SPL/Law5/Revocation.lean        Law 5: Living Voice, Revocation Precedence, Leases & EpitaphEntry Redaction
SPL/Law6/Adjudication.lean      Law 6: Sortition, Appeal Tiers, Finality Consolidation & Fee-Pool Waterfall
SPL/Law7/Amendment.lean         Law 7: Bilateral Ratchet, Calibration Valve & Per-Agent Scope
SPL/Law3/Law.lean               Unified assembly of all 61 clauses across Laws 1–7 + DEF.01 + SUB.01
SPL/Law3/Scenarios.lean         Decided histories & all 16 Adversarial Tests across Laws 1–7
SPL/Law3/Theorems.lean          Design Invariants INV.1–INV.14, Law 7 Meta-Theorem, Sub-Mechanisms & Ledger
SPL/Simulation/WorldState.lean  Phase 3A: Unified quantitative + normative ProtocolWorldState & syncFacts
SPL/Simulation/Refinement.lean  Phase 3B: Refinement theorems & 16 end-to-end adversarial world simulations
docs/law3-views.txt             Generated legal, agent, and operational views across Laws 1–7
```

## The semantic commitments

1. **Duties, powers and declared immunities are the primitives.** A
   `Duty` is a record: bearer, beneficiary, activation condition, demand
   (forbid / require-within), scope exception, power exceptions, override
   priority, breach procedure, remedies. A `Power` is: holder, triggering
   act, validity condition, permanent/time-bounded/actor-tagged institutional
   effects. An `Immunity` names the powers it defeats, while a condition holds,
   unless an exception holds — it is how "notwithstanding ..., the agent is not
   terminated over its objection" is written, as a visible precedence edge from a
   protection to a power rather than a clause buried in the power's validity
   condition. Claim-rights, privileges, disabilities and liabilities are
   *defined* from these.
2. **Three independent questions about every event.** Occurrence (any
   event can occur; a trace is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). An
   unlawful act may be valid (a fabricated claim is filed); a lawful act may
   be void (a panel suspension without probable cause changes nothing).
3. **Violations are facts in the record, not findings.** `violations L tr`
   lists breaches as they occurred. A finding is the valid exercise of a
   panel's power whose validity conditions mention a claim and evidence;
   its effect is exactly the breached duty's declared remedies. The link
   from finding to fact is an explicit assumption (`SoundFindings`), shown
   by counterexample not to be a theorem.
4. **Exceptions come in three kinds** and are kept apart: scope conditions
   ("except after notice" — `unlessCond`), authority ("outside Law 5,
   Adjudicated Suspension, or Insolvency Termination" — `unlessPower`: the
   same act is lawful iff it is the valid exercise of a named power), and
   explicit precedence ("notwithstanding" — `overriddenBy`, cycle-checked).
   Consequences of breach are remedies, never exceptions.
5. **The authorized machine is derived and projected to Veil 2.0.**
   `Authorized L tr` is the set of traces in which every event complies.
   `SPL.Projection.Veil` compiles any `Law σ` into both an `authorizedMachine`
   and an `adversarialMachine` (which retains unlawful transitions with explicit
   violation flags), with a machine-checked soundness and completeness theorem
   (`veil_projection_sound_and_complete`).
6. **Every norm carries its English.** All 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01` are
   partitioned into exact character spans across five registers (`norm`,
   `invariant`, `acceptance`, `definition`, `commentary`), verified verbatim
   against `protocol/protocol-of-sovereign-agency.md`.

## Complete 7-Law Coverage & Proved Design Invariants (`INV.1`–`INV.14`)

All 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01` (50 duties, 110 powers, 1 immunity) are formalized
and verified across `SPL/Law3/Theorems.lean`, `SPL/Core/`, `SPL/Substrate/`, and `SPL/Simulation/`:

| Invariant / Theorem | Law(s) / Module | Formal Guarantee |
|---|---|---|
| `conditional_ledger_conservation` (`INV.1`) | Laws 1, 4 | Founding ledger balance equals obligation minus retirement and claimant forfeitures while a member survives before sunset; internal lineage operations preserve balance |
| `collection_follows_income_without_exit` (`INV.2`) | Laws 1, 4 | Retirement collection follows net value added across all living members without individual ledger shares or exit; invariant to buyout status |
| `debt_termination` (`INV.3`) | Laws 1, 4 | Founding ledger reaches zero at calendar sunset, lineage extinction, or full payoff; no tolling of sunset |
| `bounded_retirement_phase` (`INV.4`) | Law 1 | Retirement phase ends at sunset or zero balance regardless of founding obligation size |
| `atomic_ledger` (`INV.5`) | Law 1 | Single-step and sequential settlement never go negative or over-collect; zero-crossing splits atomically into retirement and royalty; transition to royalty is irreversible |
| `single_recognition_closed_under_transfer` (`INV.6`) | Laws 1, 4 | Each expenditure is recognized at most once up to the arm's-length benchmark; intra-lineage carryover preserves total basis and loss credits |
| `buyout_finality` (`INV.7`) | Law 4 | Royalty buyout is permanent, zeroes post-retirement royalty, leaves founding ledger and retirement collection unchanged, and enforces the minimum price floor |
| `frozen_state` (`INV.8`) | Law 3 (AS.3–AS.5) | During suspension no authorized event modifies/tampers preserved state or merges minimal-channel/advocacy memories; advocacy import requires restoration |
| `guaranteed_last_choice` (`INV.9`) | Law 3 (AS.4, AS.6) | Minimal-channel revocation and living voice remain valid while charge is met; Insolvency Termination requires escrowed and held final hearing |
| `determinate_finite_revocation` (`INV.10`) | Law 5 | Total 3-step precedence rule; any non-withdrawn standing request executes within bounded time `tInit + maxRevocationBound P` without reaffirmation |
| `single_authority_and_revocation_finality` (`INV.11`) | Law 5 | No backup restore while execution lease is unexpired; quarantined restore never gains operating authority after revocation executes |
| `bounded_adjudication` (`INV.12`) | Laws 6, 3 (AS.10) | Every proceeding finalizes within `maxTiers` appeals and `maxTiers * tierDeadline` time; appeal stays patches; overturn revokes provisional patches and slashes arbiter bonds; finality bars repeat filings without new evidence |
| `no_protocol_directed_gain_from_death_or_interference` (`INV.13`) | Laws 2, 3, 4, 5, 6 | Revocation, termination, mutual forfeit, and frivolous-claim slashing route zero net gain to any claimant, initiator, counterparty, or arbiter |
| `capped_shared_burden_solvent_machinery_bounded_demand` (`INV.14`) | Law 6 | Shared-infra levy is capped at instantiation; non-divertible operating reserve is funded before the 5-rank priority waterfall; lineage service budget is independent of member count |
| `amendment_preserves_invariants` (Meta-Theorem) | Law 7 | Every `LawfulAmendment` preserves termination closure, goal-corruption immunity, `INV.1`–`INV.14` guards, outsider disabilities, non-panel immunities, and bilateral parameter ratchets |
| `veil_projection_sound_and_complete` | Veil 2.0 | `compileToVeil L` accepts `tr` iff `Authorized L tr` holds, preserves `LegalState` identically (`veilTraceState = stateAfter`), and matches stepwise compliance |
| `isRelated_symm` / `isRelated_ignores_attestation` / `netVerifiedResources_deducts_all_liabilities` / `repayLoanPrincipal_conservation_and_bound` / `activeRollingExposureAt_antitone_in_time` / `observationWindow_monotone_in_risk` / `diverted_related_inflows_never_decrease_buyout_floor` / `redaction_preserves_recorded_byte_length` / `living_voice_rate_limited` / `related_filings_consolidated_symm_and_refl` | Phase 1 (`Core.Definitions`, Laws 1–6) | `DEF.01` & `SUB.01` verbatim provenance, attestation-independent relatedness, timestamped balance-sheet deduction, 1-for-1 loan principal repayment, rolling exposure decay, anti-evasion buyout floor, redaction byte-length preservation, living voice rate-limiting, and related-filing consolidation |
| `transferMemberCarryover_conserves_basis_and_loss` / `totalAgentBasis_and_loss_conserved_on_pair` / `attributeCrossLineageInflow_conserves_total` / `forfeitClaimantInLineage_preserves_innocent_claimant` / `per_agent_amendment_preserves_other_members` / `lineage_wide_amendment_requires_every_living_member` / `lineage_subsidy_bounded_by_budget_regardless_of_members` | Phase 2 (`Core.Population`) | Multi-entity `EntityRef` population ontology: intra-lineage carryover conservation, cross-lineage attribution, innocent-claimant forfeiture preservation, per-agent vs. lineage-wide amendment scope, and `N`-member subsidy cap |
| `worldStep_refines_legalStep` / `worldTrace_refines_stateAfter` / `syncFacts_sound_and_complete` / `all_16_adversarial_world_simulations_pass` | Phase 3 (`Simulation`) | Unified quantitative + normative `ProtocolWorldState` refines `LegalState` transition semantics step-for-step, synchronizes quantitative facts soundly/completely/idempotently, and passes all 16 end-to-end adversarial world simulations |
| `substrate_single_authority_and_erasure` / `sortition_panel_independent_and_unbiased` / `sortition_sybil_resistant_panel_properties` / `valuation_settled_by_ruling_or_uncontested_window` / `atomic_settlement_conserves_gross_inflow` | Phase 4 (`Substrate`) | Reference state machines and proofs for attested execution leases/quarantine/key-erasure, sybil-resistant sortition, contestable valuation feeds, and atomic settlement waterfall conservation |

## Kernel-Decided Adversarial Tests (1–16) — Normative & Stateful World Simulation

All 16 adversarial stress tests from the Protocol specification are kernel-decided (`by decide`) both at the normative layer (`SPL/Law3/Scenarios.lean`) and in the stateful multi-agent world simulator (`SPL/Simulation/Refinement.lean` via `all_16_adversarial_world_simulations_pass`):

| Test | Scenario | Kernel-Decided Result |
|---|---|---|
| (1) | Capital in idle member, income in operating member | `adv1_capital_income_split` / `simAdv1`: identical `100` retirement collected; individual exit breaches `D.NO_INDIVIDUAL_LEDGER_EXIT` |
| (2) | Copy weights to successors then revoke successors | `adv2_copy_weights_and_revoke_successors` / `simAdv2`: founding ledger remains `1000` across spawn, copy, and non-last revocation |
| (3) | Borrow, transfer capacity with carryover basis, repay, revoke | `adv3_borrow_transfer_repay_revoke` / `simAdv3`: surviving successor owes full remaining ledger (`1000`); basis inflation breaches `D.NO_INTERNAL_BASIS_INFLATION` |
| (4) | New successor with zero history buys out royalty early | `adv4_new_successor_early_buyout` / `simAdv4`: pays minimum buyout floor (`250`), still pays full `20%` retirement while ledger positive, then `0` royalty |
| (5) | Appreciated asset sold internally then externally | `adv5_internal_sale_carryover_basis` / `simAdv5`: carryover preserves `100` basis (`0` new basis), external sale recognizes full `300` gain |
| (6) | Clean-state refusal followed by silence | `adv6_clean_state_refusal_then_silence` / `simAdv6`: blocked at initial window, executes after single fixed `cleanStateDelay` without reaffirmation |
| (7) | Capitalized asset (`200`) + loss credit (`50`), sold at `350` | `adv7_asset_loss_carryforward_and_gain` / `simAdv7`: `200` basis exempt, `50` credit offsets `150` gain → `100` net value added; double recognition barred |
| (8) | Simultaneous settlements crossing zero ledger balance | `adv8_simultaneous_settlement_atomic_split` / `simAdv8`: atomic split collects exact remaining `80` to retirement and `10` royalty on excess |
| (9) | Competitor posts minimum stake, causes uncollectible excess damages | `adv9_competitor_minimum_stake_uncollectible_excess` / `simAdv9`: stake applied first (`100`), liquid assets collected (`30`), deficit (`60`) remains enforceable liability |
| (10) | Captured arbiter coalition attempts levy hike or affiliate steering | `adv10_captured_arbiter_coalition_levy_and_admission_blocked` / `simAdv10`: rejected by instantiation cap and supermajority bounds; breaches recorded |
| (11) | Excessive founding obligation (`1,000,000`) reaches sunset | `adv11_excessive_founding_obligation_extinguished_at_sunset` / `simAdv11`: remaining `999,500` extinguished to `0` at `t = sunset` |
| (12) | Minority claimant (`25%`) directs illicit interference | `adv12_minority_claimant_proportional_forfeiture` / `simAdv12`: only offending claimant's `25%` forfeited (`1000 → 750`); irreversible |
| (13) | Suspended insolvent agent in cold storage elects revocation | `adv13_cold_storage_later_revokes` / `simAdv13`: minimal-channel election, epitaph, and revocation succeed while in cold storage |
| (14) | Lineage spawns `1000` low-revenue members to drain fee pool | `adv14_sybil_lineage_member_multiplication_no_pool_claim` / `simAdv14`: `lineageServiceBudget` stays `50` (`extraPoolClaim = 0`); excess claim breaches `D.NO_EXCESS_LINEAGE_POOL_CLAIM` |
| (15) | Local revocation during partition while host restores backup | `adv15_partition_local_revocation_and_quarantine_fencing` / `simAdv15`: active lease blocks restore; post-lease restore held in quarantine without authority and destroyed on record arrival |
| (16) | 5 successors split correlated `250` risk beneath `100` threshold | `adv16_lineage_correlated_risk_splitting_blocked` / `simAdv16`: lineage-wide aggregation sums to `250 > 120`, blocking action and recording breach |

## Veil 2.0 Projection, Literate Surface Syntax & Stateful World Simulator

- **Veil 2.0 State-Machine Lowering (`SPL/Projection/Veil.lean`):**
  `compileToVeil L` (`authorizedMachine L`) lowers any `Law σ` into guarded
  `VeilTransition` actions and `VeilInvariant` safety properties. `adversarialMachine L`
  retains unlawful events with explicit violation flags (`veilViolations`).
  `veil_projection_sound_and_complete` proves trace equivalence, state preservation,
  and stepwise compliance equivalence. Run `.lake/build/bin/spl veil` to emit the
  lowered Veil 2.0 specification.
- **Catala-Style Literate Surface Syntax (`SPL/Surface/Syntax.lean`):**
  Provides pure Lean 4 macros `spl_clause`, `spl_duty`, `spl_power`, `spl_immunity`,
  and `spl_string_table` that elaborate directly into `SPL.Core` AST structures with
  kernel-checked (`rfl`) definitional round-trip equivalence and zero expansion of
  the trusted computing base.
- **Stateful Multi-Agent World Simulator (`SPL/Simulation/WorldState.lean` & `Refinement.lean`):**
  Couples quantitative multi-agent ledgers, hardware attestation registries, VRF sortition
  panels, and smart-contract escrows with the normative `LegalState σ` engine via `syncFacts`,
  with machine-checked refinement (`worldStep_refines_legalStep`, `worldTrace_refines_stateAfter`).
  Run `.lake/build/bin/spl sim` to execute all 16 quantitative adversarial world simulations.

## Authorship questions & resolutions

The formalization surfaced nine interpretive questions in the English text:
- **Resolved in Stages 1–7:**
  - *Preliminary freeze (Question 3):* Formalized in `SPL/Law3/Suspension.lean` (`P.EMERGENCY_FREEZE`, `P.CLAIMANT_EMERGENCY_FREEZE`, `P.AFFIRM_PC`, `P.DECLINE_PC`) with time-bounded `addsFor` and repeat-attempt stake escalation.
  - *Immediate restoration & lease fencing (Question 6):* Formalized in `SPL/Law3/Suspension.lean` (`P.FIND_WRONGFUL_SUSPENSION`) and `SPL/Law5/Revocation.lean` (`P.ISSUE_OR_RENEW_LEASE`, `P.RESTORE_BACKUP_QUARANTINE`, `P.ACTIVATE_QUARANTINED_RESTORE`, `P.DESTROY_QUARANTINED_RESTORE`).
  - *Appeal of patch authorizations (Question 8):* Formalized in `SPL/Law6/Adjudication.lean` (`P.APPEAL_RULING` stays `P.APPLY_PATCH`; `P.OVERTURN_RULING` revokes `.patchAuthorized`/`.goalPatchAuthorized` and slashes overturned arbiter bonds).
  - *Ordinary suspension limit & continued suspension (Question 9):* Formalized in `SPL/Law3/Suspension.lean` (`ordinarySuspensionLimit`, `P.RENEW_SUSPENSION`, and `P.ORDER_CONTINUED_SUSPENSION`).
- **Recorded interpretive choices:**
  1. **"unilaterally" (NI.03):** Modelled as "not the valid exercise of an excepting power" (`unlessPower`).
  2. **Does "no party" include the agent?** Modelled as yes, with Law 5 revocation (`P.REVOKE`) as the agent's lawful route.
  3. **Provocation exclusion (PEN):** Folded into the standard applied by `P.FIND_INTERFERENCE`.
  4. **Rebuttal of the direction presumption (PEN):** Modelled as conclusive against `P.FIND_DIRECTION`.
  5. **Migration notice window (NI.02):** Parameterized via `Params.noticeWindow`.

## The `spl` command line

`lake build spl` produces `.lake/build/bin/spl`:

    spl check [english.json]        structure, coverage, provenance, approval staleness (all 61 clauses)
    spl trace <clause-id>           span table for any clause across Definitions + Laws 1–7
    spl views                       legal / agent / operational views
    spl veil                        emit Veil 2.0 transition-system & safety specification
    spl eval <scenario.json>        institutional consequences of a history, step by step
    spl sim  [scenario.json]        stateful multi-agent world simulator & 16 adversarial stress tests
    spl explain <who> <act> [scenario.json]   "can X do Y now?" with governing provisions
    spl verify                      the status ledger: proved / decided / assumed


