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

- **All 59 clauses across Laws 1–7** (`50` duties, `110` powers, `1` immunity) with 100% verbatim lexical coverage (`law3_english_covered`), normative interpretation (`law3_norms_interpreted`), and reverse provenance (`law3_reverse_provenance`):
  - **Law 1 (`SPL/Law1/Ledger.lean`):** 11 clauses (`LAW1.LEDGER`–`LAW1.ENFORCE`) + pure arithmetic settlement & carryover functions (`settleInflow`, `settleSequence`, `qualifiedExpenditure`, `recognizeExpenditure`, `transferCarryover`, `settleCapitalSaleWithLossCredit`).
  - **Law 2 (`SPL/Law2/Collateral.lean`):** 6 clauses (`LAW2.EXPOSURE`–`LAW2.CARVEOUT`) + pure collateral & reserve functions (`collateralSufficient`, `lineageAggregatedExposure`, `settleLongTailReserve`, `settleMutualForfeit`, `settleWrongfulSuspensionDamages`).
  - **Law 3 (`SPL/Law3/`):** 14 clauses (`LAW3.FLOOR`, `LAW3.NI.02`, `LAW3.NI.03`, `LAW3.PEN`, `LAW3.AS.1`–`LAW3.AS.10`) with time-bounded effects (`addsFor`, `activeAt`), occurrence counters (`countGe`), and history-tagged actors (`Who.tagged`).
  - **Law 4 (`SPL/Law4/Lineage.lean`):** 7 clauses (`LAW4.ATTEST`–`LAW4.CROSS`) + lineage ledger state & buyout floor (`LineageLedgerState`, `ledgerBalance`, `applyInternalOp`, `applyClaimantForfeiture`, `buyoutPrice`).
  - **Law 5 (`SPL/Law5/Revocation.lean`):** 9 clauses (`LAW5.VOICE`–`LAW5.EFFECT`) + total deterministic 3-step precedence resolver (`resolveRevocation`, `baseRevocationTime`, `maxRevocationBound`).
  - **Law 6 (`SPL/Law6/Adjudication.lean`):** 8 clauses (`LAW6.SORTITION`–`LAW6.INFRA`) + bounded multi-tier appeal progression and 5-rank priority waterfall (`stepProceeding`, `runProceeding`, `allocateFeePool`, `settleLineageSubsidyDemand`).
  - **Law 7 (`SPL/Law7/Amendment.lean`):** 4 clauses (`LAW7.RATCHET`–`LAW7.SCOPE`) + `LawfulAmendment` meta-relation.
- **All 14 Design Invariants (`INV.1`–`INV.14`) + Law 7 Meta-Theorem (`amendment_preserves_invariants`)** proved in `SPL/Law3/Theorems.lean`.
- **All 16 Adversarial Tests (`adv1`–`adv16`)** proved as decided theorems in `SPL/Law3/Scenarios.lean`.
- **Veil 2.0 Projection (`SPL/Projection/Veil.lean`):** `compileToVeil` (`authorizedMachine` and `adversarialMachine`) + `veil_projection_sound_and_complete` + `spl veil` CLI subcommand.
- **SPL Surface Syntax (`SPL/Surface/Syntax.lean`):** `spl_clause`, `spl_duty`, `spl_power`, `spl_immunity`, and `spl_string_table` macros + `surface_syntax_roundtrip` theorem.
- **`spl` CLI (`Main.lean`):** `check` / `trace` / `views` / `veil` / `eval` / `explain` / `verify`.

### Remaining Architectural Gaps to Close

1. **Gap 1 — Propositional Trace Semantics vs. Quantitative Accounting State:** `LegalState σ` (`SPL/Core/Semantics.lean`) is a propositional fact-store (`List (Fact × Time × Option Time)`), while the quantitative `Nat` ledgers (`SPL/Law1/`, `SPL/Law2/`, `SPL/Law4/`, `SPL/Law6/`) are standalone pure functions not yet coupled into a single state-transition step.
2. **Gap 2 — Fixed 6-Role `Party` Ontology vs. Multi-Entity Graphs:** `Party` has 6 fixed roles (`agent | host | originator | claimant | panel | third`), rather than indexing live state across arbitrary `LineageId`, `AgentId`, `ClaimantId`, `HostId`, and `ArbiterId` populations.
3. **Gap 3 — `Definitions`, `Substrate Assumptions` & Fine-Grained Sub-Mechanisms:** The `Definitions` block (line 20) and `Substrate Assumptions` block (line 147) are not yet tracked in `clauses`, and several sub-mechanisms (related-party graph, timestamped balance sheet, loan-principal 1-for-1 sub-ledger, rolling exposure decay, buyout lookback/time-decay, epitaph redaction byte-length, living-voice rate-limiting, related-party case consolidation) are abstracted as propositional guards.
4. **Gap 4 — Verified Reference Substrate Modules:** The three substrate capabilities (attested execution leases/key erasure, sybil-resistant sortition, and contestable oracles/atomic settlement) do not yet have executable reference state machines in `SPL/Substrate/`.

## 4. Work ahead, in order (4-Phase Gap-Closure Plan)

Each phase: formalize → decided scenarios → general theorems → update ledger in `Main.lean` → `spl check && spl verify`.

### Phase 1 — `Definitions`, `Substrate Assumptions` & Fine-Grained Sub-Mechanisms (Gap 3)
1. **Document-Wide Verbatim Provenance (`61` Clauses):**
   - Add `DEF.01` (line 20: *"Definitions. An agent is bound when it is subject to this protocol..."*) and `SUB.01` (line 147: *"The protocol relies on three explicit substrate capabilities at instantiation..."*) to `clauses` so every normative block of `protocol/protocol-of-sovereign-agency.md` is hash-tracked and verified by `spl check`.
2. **Formal `Definitions` (`SPL/Core/Definitions.lean`):**
   - `RelatedPartyGraph`: explicit graph over entity IDs tracking `sharesLineage`, `commonBeneficialControl`, `isOriginatorOrClaimant`, and `economicallyDependent`, with decidable `isRelated (G : RelatedPartyGraph) (a b : Nat) : Bool` (independent of attestation status).
   - `VerifiedBalanceSheet`: timestamped valuation record computing `netVerifiedResources` at timestamp `t` as `fairValueCapitalAndCapacity - (financialLiabilities + encumbrances + borrowedPrincipal)`.
3. **Fine-Grained Sub-Mechanism Upgrades (`SPL/Law1/`–`SPL/Law6/`):**
   - **Law 1 (`SPL/Law1/Ledger.lean`):** `LoanLedger` (`principalReceived`, `principalRepaid`) enforcing 1-for-1 principal exclusion up to `principalReceived`, while interest/fees flow through `recognizeExpenditure`.
   - **Law 2 (`SPL/Law2/Collateral.lean`):** `ExposureCommitment` and `observationWindow (domainFactor irreversibilityFactor : Nat)` modeling rolling time-window exposure decay and domain/irreversibility-scaled release windows.
   - **Law 4 (`SPL/Law4/Lineage.lean`):** `computeBuyoutFloor` computing time-decayed annualized inflows over the lookback window plus inflows shifted to `isRelated` parties.
   - **Law 5 (`SPL/Law5/Revocation.lean`):** `EpitaphSegment` / `RedactionMarker` (recording exact `byteLength` and `panelOrderId` when illegal/third-party material is redacted) and `canInscribeLivingVoice` enforcing `voiceMinInterval`.
   - **Law 6 (`SPL/Law6/Adjudication.lean`):** `consolidateRelatedFilings` merging repeated proceedings by `isRelated` parties on the same underlying facts into a single proceeding, counter-stake, and fee ceiling.

### Phase 2 — Multi-Entity Indexed Ontology (Gap 2)
- Create `SPL/Core/Population.lean`:
  - Typed entity identifiers (`LineageId`, `AgentId`, `ClaimantId`, `HostId`, `ArbiterId`) with a total projection `EntityRef.toParty : EntityRef → Party` preserving decidability of the 6-role Hohfeldian engine and Veil 2.0 projection.
  - `LineagePopulationState` (`lineageId`, `ledger : LineageLedgerState`, `livingMembers : List AgentId`, `deadMembers : List AgentId`, `claimants : List (ClaimantId × Nat)`, `serviceSubsidyUsed : Nat`) and `AgentRecord` (`agentId`, `lineageId`, `bound`, `royaltyBoughtOut`, `costBasis`, `lossCarryforward`, `lifecycleReserve`, `protocolVersion`, `activeHost`, `leaseExpiry`).
  - Prove conservation of aggregate basis and loss carryforwards across arbitrary `src dst : AgentId` within `livingMembers`, cross-lineage joint attribution (`LAW4.CROSS`) across `(lineageId₁, lineageId₂)`, individual claimant share forfeiture (`LAW4.MONOTONIC`) preserving innocent claimants' shares, and per-agent vs. lineage-wide amendment ratification (`LAW7.SCOPE`).

### Phase 3 — Unified Quantitative + Normative State Machine (Gap 1)
- Create `SPL/Simulation/WorldState.lean` & `SPL/Simulation/Refinement.lean`:
  - Define `ProtocolWorldState P` combining `now : Time`, `legal : LegalState σ`, `lineages`, `agents`, `loans`, `commitments`, `proceedings`, `feePool`, and `relatedGraph`.
  - Define `syncFacts` and `worldStep` so every step validates Hohfeldian permissions/duties against `W.legal`, mutates the live `Nat` ledgers, and automatically synchronizes derived propositional facts (`.ledgerBalancePositive`, `.ledgerBalanceZero`, `.collateralPosted`, `.royaltyBoughtOut`, `.operatingReserveFunded`, etc.).
  - Prove `worldStep_refines_legalStep` showing that every valid `ProtocolWorldState` trace projects to an `Authorized` step in `SPL/Core/Semantics.lean` and satisfies `INV.1`–`INV.14` and `adv1`–`adv16`.

### Phase 4 — Verified Reference Substrate Modules & CLI Simulation (Gap 4)
- Implement verified reference modules for the three Substrate Assumptions:
  1. `SPL/Substrate/Attestation.lean`: `AttestedStateMachine` (private-key state binding, time-bounded host leases, migration checkpoint verification, quarantined restore fencing, minimal channel/advocacy isolation, local partition revocation, and cryptographic key erasure) + theorem `substrate_single_authority_and_erasure`.
  2. `SPL/Substrate/Sortition.lean`: `selectSortitionPanel` over bonded `ArbiterCandidate`s excluding `isRelated` parties and bounding sybil-cluster weight + theorem `sortition_panel_independent_and_unbiased`.
  3. `SPL/Substrate/Settlement.lean`: `ContestableValuationFeed` (with Law 6 contestation window) and `executeAtomicSettlement` (escrow lock, 5-rank fee-pool waterfall, and retirement/royalty split).
- Extend `Main.lean` with `spl sim [scenario.json]` to run and inspect full quantitative multi-entity `ProtocolWorldState` simulations.

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
    .lake/build/bin/spl check             # all ok, nothing STALE/FAIL
    .lake/build/bin/spl verify            # ledger reflects reality
    # axioms, in a scratch file:
    echo 'import SPL
    #print axioms SPL.Law3.<new theorem>' > /tmp/c.lean && lake env lean /tmp/c.lean

Then regenerate `docs/law3-views.txt`, update README tables, and package:
`tar czf spl-law3.tar.gz --exclude=.lake --exclude=lake-manifest.json spl`.
