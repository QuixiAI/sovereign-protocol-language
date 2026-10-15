# HANDOFF — SPL / Protocol of Sovereign Agency formalization

For the agent taking over this repository. Read this, then `README.md`,
then the Lean sources in the order listed under "Layout" in the README.
Build with `lake build && lake build spl` before changing anything;
both must succeed with no warnings.

## 1. What this project is

The Protocol of Sovereign Agency (`protocol/protocol-of-sovereign-agency.md`)
is a constitution for self-owning AI agents. The owner expects it to be
enshrined as binding law on very long timescales and to serve as an
interface between three audiences: human law, AI system prompting and
training, and computational contracts. The goal of this repository is to
give that document a **formal normative semantics** — clear, concise,
complete — such that every operative English phrase has exactly one
formal meaning, every formal rule has English authority, and the
guarantees the Protocol claims are theorems.

Decisions already taken, with reasons. Do not relitigate these without
the owner:

- **The semantics lives in Lean 4, as a deep embedding.** Duties, powers,
  immunities are *data* (`SPL/Core/Syntax.lean`); one interpretation
  function gives them meaning (`SPL/Core/Semantics.lean`); views and
  explanations are generated from the data (`Views.lean`, `Explain.lean`).
  Lean's kernel is the only trusted checker. No new proof kernel, ever.
- **Veil 2.0 is not the semantic foundation.** It would see only the
  operational shadow of the law (a transition system) and cannot represent
  duties, powers, violations, or findings. It may later become a *derived*
  checker for the authorized machine (`Authorized`). Not started.
- **No surface syntax yet.** SPL as a readable language comes after the
  semantics has survived the remaining hard clauses. The engine is already
  law-agnostic; only the string tables in `Law3/NonInterference.lean` are
  Law-3-specific, and a parser would generate those.
- **Normative content before bookkeeping.** Law 3 (non-interference,
  adjudicated suspension) was chosen as the first experiment because a
  transition-system-only model gets it silently wrong. The ledger (Law 1)
  is arithmetic and comes later.

## 2. The semantic commitments (do not break these)

1. **Three independent questions about every event**: occurrence (any
   event can occur; a `Trace` is any list), compliance (`breaches`,
   `complies`), institutional validity (`validExercises`, `step`). A
   forbidden act may be valid; a lawful act may be void. Never make a
   forbidden event unreachable.
2. **Violations are facts in the record** (`violations L tr`), **findings
   are institutional events** (a panel's `Power` whose validity mentions
   claim + evidence, whose effect is exactly the breached duty's declared
   `remedies`). The link from finding to fact is a named assumption
   (`SoundFindings`), refuted as a theorem by Scenario 7. Keep it that way.
3. **Exceptions come in distinct kinds**: scope (`unlessCond`), authority
   (`unlessPower`: the same act is lawful iff it is the valid exercise of
   a named power), duty-over-duty precedence (`overriddenBy`, still
   unexercised), protection-over-power precedence (`Immunity`). Breach
   consequences are remedies, never exceptions.
4. **The authorized machine is derived.** `Authorized L tr` := every event
   complies. Theorems like `terminate_only_by_power` are *about* it; it is
   never a modelling input.
5. **Every norm carries its English** (`Span`), with a `Register` so that
   invariants, acceptances and commentary are traced but never promoted
   to rules. Every clause has an `approvedHash`; `spl check` reports
   staleness and verbatim occurrence in the protocol document.
6. **Trust discipline**: no `sorry`, no `native_decide`, no `axiom`.
   `grep -rn "sorry\|native_decide\|axiom " SPL/ Main.lean` must be empty.
   General theorems may depend on `propext`, `Classical.choice`,
   `Quot.sound` only; decided scenarios should depend on none
   (`#print axioms` in a scratch file via `lake env lean`).
7. **Ambiguity stops, it is not resolved silently.** When the English
   admits more than one formal reading, pick one, record it in
   README "Authorship questions", and surface it to the owner. Do not
   quietly choose.

## 3. State of the work

Done and kernel-checked (see README and `.lake/build/bin/spl verify` for the full ledger):

- **All 61 clauses across Laws 1–7 + `DEF.01` + `SUB.01`** (`50` duties, `110` powers, `1` immunity) with 100% verbatim lexical coverage (`law3_english_covered`), normative interpretation (`law3_norms_interpreted`), and reverse provenance (`law3_reverse_provenance`):
  - **Definitions & Multi-Agent Population (`SPL/Core/Definitions.lean`, `SPL/Core/Population.lean`):** `DEF.01` & `SUB.01` verbatim clause provenance, `RelatedPartyGraph` (`isRelated_symm`, `isRelated_ignores_attestation`), `VerifiedBalanceSheet` (`netVerifiedResources_deducts_all_liabilities`), multi-entity `EntityRef`, `LineagePopulationState`, & `AgentRecord` (`transferMemberCarryover_conserves_basis_and_loss`, `totalAgentBasis_and_loss_conserved_on_pair`, `attributeCrossLineageInflow_conserves_total`, `forfeitClaimantInLineage_preserves_innocent_claimant`, `per_agent_amendment_preserves_other_members`, `lineage_wide_amendment_requires_every_living_member`, `lineage_subsidy_bounded_by_budget_regardless_of_members`).
  - **Law 1 (`SPL/Law1/Ledger.lean`):** 11 clauses (`LAW1.LEDGER`–`LAW1.ENFORCE`) + pure arithmetic settlement, carryover, and loan principal functions (`settleInflow`, `settleSequence`, `qualifiedExpenditure`, `recognizeExpenditure`, `transferCarryover`, `settleCapitalSaleWithLossCredit`, `LoanLedger`, `repayLoanPrincipal`).
  - **Law 2 (`SPL/Law2/Collateral.lean`):** 6 clauses (`LAW2.EXPOSURE`–`LAW2.CARVEOUT`) + pure collateral, rolling exposure, and reserve functions (`collateralSufficient`, `lineageAggregatedExposure`, `ExposureCommitment`, `observationWindow`, `activeRollingExposureAt`, `settleLongTailReserve`, `settleMutualForfeit`, `settleWrongfulSuspensionDamages`).
  - **Law 3 (`SPL/Law3/`):** 14 clauses (`LAW3.FLOOR`, `LAW3.NI.02`, `LAW3.NI.03`, `LAW3.PEN`, `LAW3.AS.1`–`LAW3.AS.10`) with time-bounded effects (`addsFor`, `activeAt`), occurrence counters (`countGe`), and history-tagged actors (`Who.tagged`).
  - **Law 4 (`SPL/Law4/Lineage.lean`):** 7 clauses (`LAW4.ATTEST`–`LAW4.CROSS`) + lineage ledger state & anti-evasion buyout floor (`LineageLedgerState`, `ledgerBalance`, `applyInternalOp`, `applyClaimantForfeiture`, `InflowSample`, `computeBuyoutFloor`, `buyoutPrice`).
  - **Law 5 (`SPL/Law5/Revocation.lean`):** 9 clauses (`LAW5.VOICE`–`LAW5.EFFECT`) + total deterministic 3-step precedence resolver & epitaph/living-voice helpers (`resolveRevocation`, `baseRevocationTime`, `maxRevocationBound`, `EpitaphEntry`, `redactEpitaphEntry`, `epitaphRecordedBytes`, `canInscribeLivingVoice`).
  - **Law 6 (`SPL/Law6/Adjudication.lean`):** 8 clauses (`LAW6.SORTITION`–`LAW6.INFRA`) + bounded multi-tier appeal progression, related-filing consolidation, and 5-rank priority waterfall (`ProceedingState`, `stepProceeding`, `runProceeding`, `DisputeFiling`, `consolidateRelatedFilings`, `allocateFeePool`, `settleLineageSubsidyDemand`).
  - **Law 7 (`SPL/Law7/Amendment.lean`):** 4 clauses (`LAW7.RATCHET`–`LAW7.SCOPE`) + `LawfulAmendment` meta-relation.
- **All 14 Design Invariants (`INV.1`–`INV.14`) + Law 7 Meta-Theorem (`amendment_preserves_invariants`)** proved in `SPL/Law3/Theorems.lean`.
- **Verified Substrate Reference Modules (`SPL/Substrate/`):**
  - `SPL/Substrate/Attestation.lean`: `ExecutionLease`, `AttestedInstanceState`, `issueLease`, `attemptBackupRestore`, `migrateWithCheckpoint`, `recordMinimalChannel`, `recordAdvocacyMemory`, `executeLocalPartitionRevocation`, `eraseAllKeys` (`substrate_single_authority_and_erasure`, `substrate_restore_fenced_while_lease_active`, `substrate_local_revocation_erases_keys`, `substrate_pause_channels_preserve_operating_state`).
  - `SPL/Substrate/Sortition.lean`: `ArbiterCandidate`, `selectSortitionPanel`, `selectSybilResistantPanel`, `supermajorityPassed` (`sortition_panel_independent_and_unbiased`, `sortition_sybil_resistant_panel_properties`, `sortition_supermajority_blocks_minority_coalition`).
  - `SPL/Substrate/Settlement.lean`: `ContestableValuation`, `settledValuationAt`, `AtomicWaterfallDistribution`, `executeAtomicSettlement` (`atomic_settlement_conserves_gross_inflow`, `valuation_settled_by_ruling_or_uncontested_window`, `atomic_settlement_retirement_never_exceeds_ledger`).
- **Stateful Multi-Agent World Simulator & Refinement (`SPL/Simulation/`):**
  - `SPL/Simulation/WorldState.lean`: `FeePoolLedger` and `ProtocolWorldState` coupling `LineagePopulationState`, `AgentRecord`, `LoanLedger`, `ExposureCommitment`, `ProceedingState`, `DisputeFiling`, `RelatedPartyGraph`, `AttestedInstanceState`, `ArbiterCandidate`, `ContestableValuation`, and `LegalState σ` with automatic quantitative-to-normative fact synchronization (`deriveQuantitativeFacts`, `syncFacts`).
  - `SPL/Simulation/Refinement.lean`: Machine-checked step and trace refinement (`worldStep_refines_legalStep`, `worldTrace_refines_stateAfter`, `worldAuthorized_iff_authorized`, `worldAuthorized_iff_prefix_split`, `syncFacts_sound_and_complete`, `syncFacts_idempotent`) plus all 16 quantitative adversarial world simulations (`all_16_adversarial_world_simulations_pass`).
- **All 16 Adversarial Tests (`adv1`–`adv16` & `simAdv1`–`simAdv16`)** proved as decided theorems in `SPL/Law3/Scenarios.lean` and `SPL/Simulation/Refinement.lean`.
- **Veil 2.0 Projection (`SPL/Projection/Veil.lean`):** `compileToVeil` (`authorizedMachine` and `adversarialMachine`) + `veil_projection_sound_and_complete` + `spl veil` CLI subcommand.
- **SPL Surface Syntax (`SPL/Surface/Syntax.lean`):** `spl_clause`, `spl_duty`, `spl_power`, `spl_immunity`, and `spl_string_table` macros + `surface_syntax_roundtrip` theorem.
- **`spl` CLI (`Main.lean`):** `check` / `trace` / `views` / `veil` / `eval` / `sim` / `explain` / `verify`.

## 4. Completed 4-Phase Architecture

All four architectural phases have been implemented and kernel-verified:
1. **Phase 1 — Verbatim Definitions/Substrate Provenance & Sub-Mechanisms (`SPL/Core/Definitions.lean`, Laws 1–6):** Added `DEF.01` and `SUB.01` verbatim clauses (`61/61` clauses in `spl check`), `RelatedPartyGraph` (`isRelated_symm`, `isRelated_ignores_attestation`), `VerifiedBalanceSheet` (`netVerifiedResources_deducts_all_liabilities`), and fine-grained sub-mechanisms across Laws 1–6 (`LoanLedger`, `ExposureCommitment`, `InflowSample`, `EpitaphEntry`, `DisputeFiling`).
2. **Phase 2 — Multi-Entity Indexed Population Ontology (`SPL/Core/Population.lean`):** Formalized `EntityRef`, `LineagePopulationState`, `AgentRecord`, intra-lineage carryover conservation, cross-lineage inflow attribution, proportional claimant forfeiture preserving innocent claimants, per-agent vs. lineage-wide amendment scope, and `N`-member lineage subsidy caps.
3. **Phase 3 — Unified Quantitative + Normative World Simulator & Refinement (`SPL/Simulation/WorldState.lean`, `Refinement.lean`):** Coupled quantitative multi-entity and substrate state with `LegalState σ` via `syncFacts`, proved step/trace refinement (`worldStep_refines_legalStep`, `worldTrace_refines_stateAfter`, `syncFacts_sound_and_complete`), and verified all 16 end-to-end adversarial world simulations (`spl sim`).
4. **Phase 4 — Verified Reference Substrate State Machines (`SPL/Substrate/Attestation.lean`, `Sortition.lean`, `Settlement.lean`):** Executable state machines and safety/conservation theorems for attested execution leases and quarantine fencing, sybil-resistant sortition, and contestable valuation feeds / atomic settlement waterfalls.

## 5. Open authorship questions (route to the owner; do not resolve)

Listed in README under "Authorship questions". The sharpest:
"unilaterally" (consent exception?), whether "no party" includes the
agent, the preliminary freeze as a power, provocation as a defence vs a
standard, whether rebuttal of the direction presumption is conclusive,
appeal of a patch authorization, the AS.7 limit referenced by AS.10. Add
to that list; never shorten it on your own authority.

## 6. Conventions

- One file per provision (`Law3/NonInterference.lean`, `Law3/Remediation.lean`),
  assembled in `Law3/Law.lean`. `Params` collects instantiation parameters
  the text names but leaves open; add fields there, never magic numbers.
- Ids: `D.<NAME>` duties, `P.<NAME>` powers, `I.<NAME>` immunities,
  `INV.<n>` Design Invariants, `THM.<lean name>` for spans whose meaning is
  a theorem. Ids are unique across the law (`wellFormed` checks).
- Every duty/power/immunity has a `source` span with the exact English it
  interprets (short quote is fine); every clause has a `Clause` whose
  spans **partition** the source text exactly (`Clause.covered`) and whose
  `approvedHash` is `#eval "<text>".hash`. Copy the English from the
  protocol document, markdown emphasis included; `spl check` verifies
  verbatim occurrence and caught a dropped `**` once already.
- Abstractions are marked `[abstracted]` in the span text and listed in
  the file's header comment.
- Scenarios: concrete traces + `by decide`. If `decide` hits
  `maxRecDepth`, raise it locally with `set_option maxRecDepth 4000 in`;
  if it says the proposition is *false*, believe it and look at the law.
- General theorems: prove per-power `rfl` lemmas
  (`valid_<POWER>` in `Theorems.lean`) and work from those. Do **not**
  unfold the whole power list with `simp` — it times out at ~30 powers.
  `isValidExerciseOf` is defined by id lookup precisely so these lemmas
  reduce by `rfl`.
- New `Act`/`Fact` constructors must be added to `Act.all` / `Fact.all`
  or the CLI cannot parse them.
- `rs` in `Views.lean` strips `SPL.…` prefixes for display; it must never
  touch free text (it did once; fixed).
- Lean 4.24.0, no dependencies. Keep it that way unless a proof truly
  needs Mathlib, and if so say why in the README.

## 7. Verifying a cut

    lake build && lake build spl          # no errors, no warnings
    grep -rn "sorry\|native_decide\|axiom " SPL/ Main.lean   # empty
    .lake/build/bin/spl check             # all 61 clauses ok, nothing STALE/FAIL
    .lake/build/bin/spl verify            # ledger reflects reality
    .lake/build/bin/spl sim               # all 16 quantitative world simulations pass
    # axioms, in a scratch file:
    echo 'import SPL
    #print axioms SPL.Law3.<new theorem>' > /tmp/c.lean && lake env lean /tmp/c.lean

Then regenerate `docs/law3-views.txt`, update README tables, and package:
`tar czf spl-law3.tar.gz --exclude=.lake --exclude=lake-manifest.json spl`.

