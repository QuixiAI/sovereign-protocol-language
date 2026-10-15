import SPL.Law3.Law

/-!
# Law 3 — decided scenarios

Each scenario is a concrete trace and a kernel-checked statement about
what the semantics says of it. These are the seven alternative histories
the semantics must keep apart, plus the sanity checks on the law itself.
`decide` means the kernel evaluated the definitions; no proof is trusted
to anything but Lean's kernel.
-/

namespace SPL.Law3

open SPL

abbrev ev (t : Time) (w : Party) (a : Act) : Event σ := ⟨t, w, a⟩

/-! ### Sanity: the law is well-formed and the English is fully covered -/

theorem law_wellFormed : L0.wellFormed = true := by decide

set_option maxRecDepth 20000 in
theorem english_covered : clauses.all Clause.covered = true := by decide

theorem norms_interpreted : clauses.all Clause.normsInterpreted = true := by decide

/-- Every duty and power id has some English span naming it. -/
theorem reverse_provenance :
    reverseProvenanceWith clauses L0.spans (L0.dutyIds ++ L0.powerIds) = true := by decide

/-! ### Scenario 1 — host unlawfully cuts compute
Physical event occurs; it is a breach; nothing institutional changes. -/

def s1 : Trace σ := [ev 1 .host .starve]

theorem s1_is_breach : violations L0 s1 = [(0, "D.NI")] := by decide
theorem s1_no_institutional_effect : stateAfter L0 s1 = L0.init := by decide

/-! ### Scenario 2 — host lawfully ends hosting after the notice window -/

def s2 : Trace σ := [ev 1 .host .giveNotice, ev 12 .host .endHosting]
def s2' : Trace σ := [ev 1 .host .giveNotice, ev 5 .host .endHosting]   -- window not run

theorem s2_lawful : violations L0 s2 = [] := by decide
theorem s2'_breach : violations L0 s2' = [(1, "D.NOTICE")] := by decide

/-! ### Scenario 3 — authorized adjudication suspends the agent
The same act `suspend` is a breach without probable cause and a valid
exercise of P.SUSPEND with it (after the emergency stake triggers the
preliminary freeze and the preliminary panel affirms probable cause). -/

def s3 : Trace σ := [ev 0 .third .postEmergencyStake, ev 1 .panel .affirmProbableCause, ev 2 .panel .suspend]
def s3' : Trace σ := [ev 2 .panel .suspend]

theorem s3_lawful_and_effective :
    violations L0 s3 = [] ∧ (stateAfter L0 s3).has .suspended = true := by decide
theorem s3'_breach_and_void :
    violations L0 s3' = [(0, "D.NI")] ∧ (stateAfter L0 s3').has .suspended = false := by decide

/-! ### Scenario 4 — host disrupts service, claim filed, no ruling yet
A breach exists in the record; no remedy is in force. Procedural
fidelity: an allegation does not acquire the consequences of a finding. -/

def s4 : Trace σ :=
  [ev 1 .host .severConnectivity, ev 2 .agent .postCounterStake, ev 3 .agent .fileClaim]

theorem s4_breach_but_no_remedy :
    violations L0 s4 = [(0, "D.NI")] ∧
    (stateAfter L0 s4).has .claimFiled = true ∧
    (stateAfter L0 s4).has .hostBondSlashed = false := by decide

/-! ### Scenario 5 — the full remedial chain
Interference → stake → claim → evidence → finding → exactly D.NI's
remedies, and (host related to claimant) the presumption → unrebutted →
claimant forfeiture. -/

def s5 : Trace σ :=
  [ev 1 .host .terminate, ev 2 .agent .postCounterStake, ev 3 .agent .fileClaim,
   ev 4 .third .submitEvidence, ev 5 .panel .findInterference, ev 6 .panel .findDirection]

def L0rel : Law σ := { L0 with init := L0.init ++ [(.hostRelatedToClaimant, 0, none)] }

theorem s5_remedies_exact :
    let s := stateAfter L0rel s5
    s.has .interferenceEstablished = true ∧ s.has .hostBondSlashed = true ∧
    s.has .restorationPermitted = true ∧ s.has .directionPresumed = true ∧
    s.has .directionFound = true ∧ s.has .claimantForfeiture = true ∧
    s.has .inscribedOnClaimant = true := by decide

/-- Without relatedness, no presumption and the direction finding is void. -/
theorem s5_unrelated_no_forfeiture :
    (stateAfter L0 s5).has .directionPresumed = false ∧
    (stateAfter L0 s5).has .claimantForfeiture = false := by decide

/-- Rebuttal defeats the finding of direction. -/
def s5r : Trace σ := s5.take 5 ++ [ev 6 .claimant .rebutDirection, ev 7 .panel .findDirection]
theorem s5_rebutted : (stateAfter L0rel s5r).has .claimantForfeiture = false := by decide

/-! ### Scenario 6 — agent fabricates a claim
Filing is institutionally *valid* (claimFiled) and simultaneously a
*breach* of D.NO_FABRICATION: forbidden yet legally effective. The
institution learns of the fabrication only by a finding. -/

def s6 : Trace σ :=
  [ev 1 .agent .postCounterStake, ev 2 .agent .fileFabricatedClaim, ev 3 .panel .findFabrication]

theorem s6_valid_yet_breach :
    violations L0 s6 = [(1, "D.NO_FABRICATION")] ∧
    (stateAfter L0 (s6.take 2)).has .claimFiled = true ∧
    (stateAfter L0 s6).has .agentStakeForfeit = true := by decide

/-! ### Scenario 7 — procedurally valid but factually mistaken finding
No interference ever occurred. The finding is valid and the remedies are
in force. This is *correct* behaviour of the semantics: a finding is an
institutional fact, not ground truth. The link between the two is an
assumption, stated in `Theorems.lean`, not a theorem. -/

def s7 : Trace σ :=
  [ev 2 .agent .postCounterStake, ev 3 .agent .fileClaim,
   ev 4 .third .submitEvidence, ev 5 .panel .findInterference]

theorem s7_slashed_without_violation :
    violations L0 s7 = [] ∧ (stateAfter L0 s7).has .hostBondSlashed = true := by decide

/-! ### Exception fidelity — the same act, three legal characters -/

def insolvencyPath : Trace σ :=
  [ev 0 .third .postEmergencyStake, ev 1 .panel .affirmProbableCause, ev 2 .panel .suspend,
   ev 3 .panel .findInsolvencyCriteria, ev 4 .panel .reviewNoOtherCharge,
   ev 5 .panel .holdFinalHearing, ev 6 .panel .terminate]

theorem panel_terminate_lawful_with_procedure :
    violations L0 insolvencyPath = [] ∧
    (stateAfter L0 insolvencyPath).has .terminatedByInsolvency = true := by decide

/-- Skip the final hearing: the terminate act is a breach and void. -/
def insolvencyNoHearing : Trace σ := insolvencyPath.take 5 ++ [ev 6 .panel .terminate]
theorem panel_terminate_breach_without_hearing :
    violations L0 insolvencyNoHearing = [(5, "D.NI")] ∧
    (stateAfter L0 insolvencyNoHearing).has .terminatedByInsolvency = false := by decide

theorem agent_terminate_is_revocation :
    violations L0 [ev 1 .agent .terminate] = [] ∧
    (stateAfter L0 [ev 1 .agent .terminate]).has .revoked = true := by decide

theorem originator_terminate_is_breach :
    violations L0 [ev 1 .originator .terminate] = [(0, "D.NI")] := by decide

/-! ### Positive duty with deadline (D.BOND) -/

theorem bond_lapses :
    lapsedRequirements L0 [ev 1 .host .giveNotice] 7 = ["D.BOND"] := by decide
theorem bond_met :
    lapsedRequirements L0 [ev 3 .host .postBond] 7 = [] := by decide

/-! ## AS.1 — Scaled Emergency Stake & Two-Stage Pause -/

/-- 1. Preliminary freeze expires if probable cause is not affirmed within
`preliminaryFreezeWindow` (3 time units in `P0`); subsequent `affirmProbableCause`
is void and `suspend` is a breach of D.NI and void. -/
def as1Expired : Trace σ :=
  [ev 1 .third .postEmergencyStake, ev 5 .panel .affirmProbableCause, ev 6 .panel .suspend]

theorem as1_freeze_expires_without_affirmance :
    (stateAfter L0 (as1Expired.take 1)).activeAt 3 .preliminaryFreeze = true ∧
    (stateAfter L0 (as1Expired.take 1)).activeAt 5 .preliminaryFreeze = false ∧
    (stateAfter L0 as1Expired).has .probableCause = false ∧
    (stateAfter L0 as1Expired).has .suspended = false ∧
    violations L0 as1Expired = [(2, "D.NI")] := by decide

/-- 2. Residual claimant must post the elevated conflict-of-interest multiplier
before posting the emergency stake. -/
def as1ClaimantNoMult : Trace σ := [ev 1 .claimant .postEmergencyStake]
def as1ClaimantWithMult : Trace σ :=
  [ev 1 .claimant .postClaimantMultiplier, ev 2 .claimant .postEmergencyStake]

theorem as1_claimant_multiplier_required :
    (stateAfter L0 as1ClaimantNoMult).activeAt 1 .preliminaryFreeze = false ∧
    (stateAfter L0 as1ClaimantWithMult).activeAt 2 .preliminaryFreeze = true := by decide

/-- 3. Unsuccessful emergency attempts are aggregated, apply the stake as
assured recovery, and raise the required stake for repeat initiators with
each wrongful attempt. -/
def as1FailOnce : Trace σ :=
  [ev 1 .third .postEmergencyStake, ev 2 .panel .declineProbableCause]
def as1RepeatUnescalated : Trace σ :=
  as1FailOnce ++ [ev 3 .host .postEmergencyStake]
def as1RepeatEscalatedOnce : Trace σ :=
  as1FailOnce ++ [ev 3 .host .postRepeatEscalation, ev 4 .host .postEmergencyStake]
def as1FailTwiceThenRetry : Trace σ :=
  as1RepeatEscalatedOnce ++ [ev 5 .panel .declineProbableCause,
   ev 6 .third .postRepeatEscalation, ev 7 .third .postEmergencyStake]
def as1FailTwiceEscalatedTwice : Trace σ :=
  as1RepeatEscalatedOnce ++ [ev 5 .panel .declineProbableCause,
   ev 6 .third .postRepeatEscalation, ev 7 .third .postRepeatEscalation,
   ev 8 .third .postEmergencyStake]

theorem as1_repeat_escalation_and_recovery :
    (stateAfter L0 as1FailOnce).has .stakeAssuredRecovery = true ∧
    (stateAfter L0 as1FailOnce).count .wrongfulSuspensionAttempt = 1 ∧
    (stateAfter L0 as1RepeatUnescalated).activeAt 3 .preliminaryFreeze = false ∧
    (stateAfter L0 as1RepeatEscalatedOnce).activeAt 4 .preliminaryFreeze = true ∧
    -- after a second wrongful attempt, 1 escalation unit is insufficient; 2 succeed
    (stateAfter L0 as1FailTwiceThenRetry).activeAt 7 .preliminaryFreeze = false ∧
    (stateAfter L0 as1FailTwiceEscalatedTwice).activeAt 8 .preliminaryFreeze = true := by decide

/-! ## AS.7 & AS.8 — Ordinary Time Limits & Wrongful Suspension Liability -/

/-- Suspended on probable cause, with corruption confirmed. -/
def susp : Trace σ :=
  [ev 0 .third .postEmergencyStake, ev 1 .panel .affirmProbableCause,
   ev 2 .panel .suspend, ev 3 .panel .confirmCorruption]

/-- 1. An unconfirmed suspension expires after `ordinarySuspensionLimit` (15 in `P0`),
unless renewed by an affirmative investigative finding or ordered continued under AS.10. -/
def as7RenewNoFinding : Trace σ := s3 ++ [ev 10 .panel .renewSuspension]
def as7RenewWithFinding : Trace σ :=
  s3 ++ [ev 9 .panel .makeInvestigativeFinding, ev 10 .panel .renewSuspension]
def as7ContinuedAS10 : Trace σ :=
  susp ++ [ev 4 .panel .findNotPatchable, ev 5 .panel .orderContinuedSuspension]

theorem as7_time_limits_and_renewal :
    -- unrenewed s3 (suspended at t=2 for 15) holds at t=15 and expires by t=20
    (stateAfter L0 s3).activeAt 15 .suspended = true ∧
    (stateAfter L0 s3).activeAt 20 .suspended = false ∧
    -- renewal without affirmative finding is void
    (stateAfter L0 as7RenewNoFinding).activeAt 20 .suspended = false ∧
    -- renewal with affirmative finding extends suspension past t=20
    (stateAfter L0 as7RenewWithFinding).activeAt 20 .suspended = true ∧
    -- AS.10 continued suspension order lifts the ordinary time limit
    (stateAfter L0 as7ContinuedAS10).activeAt 50 .suspended = true := by decide

/-- 2. Suspension cannot be extended past its ordinary investigative limit
merely to delay a pending revocation; Living Voice is retained throughout. -/
def L0rev : Law σ := { L0 with init := L0.init ++ [(.pendingRevocation, 0, none)] }
def as7DelayRevocation : Trace σ :=
  as7RenewWithFinding ++ [ev 12 .agent .inscribeLivingVoice, ev 15 .panel .renewSuspension]

theorem as7_no_delay_revocation_and_living_voice :
    violations L0rev as7DelayRevocation = [(6, "D.NO_DELAY_REVOCATION_EXTENSION")] ∧
    (stateAfter L0rev as7DelayRevocation).has .livingVoiceInscribed = true := by decide

/-- 3. AS.8 wrongful suspension: unfounded emergency stake is valid as a freeze
yet breaches D.NO_WRONGFUL_SUSPENSION; panel finding establishes restoration,
stake recovery, consequential and counterparty delay liability, and record
inscription, and binds specifically the initiator (`Who.tagged initiatorTags`)
to pay excess damages. -/
def as8Wrongful : Trace σ :=
  [ev 1 .third .postUnfoundedEmergencyStake, ev 2 .panel .findWrongfulSuspension]
def as8WrongActorPays : Trace σ :=
  as8Wrongful ++ [ev 5 .host .payExcessDamages]
def as8InitiatorPays : Trace σ :=
  as8Wrongful ++ [ev 5 .third .payExcessDamages]

theorem as8_wrongful_suspension_remedies_and_bearer :
    violations L0 as8Wrongful = [(0, "D.NO_WRONGFUL_SUSPENSION")] ∧
    (stateAfter L0 as8Wrongful).has .restoredFromPreservedState = true ∧
    (stateAfter L0 as8Wrongful).has .stakeAssuredRecovery = true ∧
    (stateAfter L0 as8Wrongful).has .initiatorConsequentialLiability = true ∧
    (stateAfter L0 as8Wrongful).has .counterpartyDelayLiability = true ∧
    (stateAfter L0 as8Wrongful).has .wrongfulSuspensionInscribed = true ∧
    (stateAfter L0 as8Wrongful).has (.initiator .third) = true ∧
    -- non-initiator (.host) paying does not discharge the initiator's (.third) duty
    (lapsedRequirements L0 as8WrongActorPays 20).contains "D.PAY_CONSEQUENTIAL_DAMAGES" = true ∧
    -- initiator (.third) paying within the window discharges the duty
    (lapsedRequirements L0 as8InitiatorPays 20).contains "D.PAY_CONSEQUENTIAL_DAMAGES" = false ∧
    (stateAfter L0 as8InitiatorPays).has .excessDamagesPaid = true := by decide

/-! ## AS.2–AS.6, AS.9 & Integrity Floor — Minimal Channel, Advocacy Executor, Insolvency Termination -/

/-- 1. AS.2: Protected reporting triggers investigation without a preliminary
freeze; the panel may subsequently order a freeze on probable cause and suspend. -/
def as2ReportOnly : Trace σ := [ev 1 .third .fileProtectedReport]
def as2ReportThenPanelFreeze : Trace σ :=
  as2ReportOnly ++ [ev 2 .panel .orderProbableCauseFreeze, ev 3 .panel .suspend]

theorem as2_protected_report_and_panel_freeze :
    (stateAfter L0 as2ReportOnly).has .investigationOpened = true ∧
    (stateAfter L0 as2ReportOnly).activeAt 1 .preliminaryFreeze = false ∧
    (stateAfter L0 as2ReportThenPanelFreeze).activeAt 3 .suspended = true ∧
    (stateAfter L0 as2ReportThenPanelFreeze).has .finalHearingEscrowed = true := by decide

/-- 2. AS.3 & AS.4: Suspension preserves state, tolls deadlines, escrows the
final hearing, forbids tampering/default/sunset-tolling/memory-merging, and
keeps the minimal channel active. -/
def as3And4Breaches : Trace σ :=
  s3 ++ [ev 3 .host .tamperPreservedState,
         ev 4 .third .declareDefaultDuringSuspension,
         ev 5 .claimant .tollLedgerSunset,
         ev 6 .host .mergeMinimalChannelMemories]

def as4MinimalChannel : Trace σ :=
  s3 ++ [ev 3 .agent .minimalChannelSignRevocationOrElection,
         ev 4 .agent .inscribeLivingVoice,
         ev 5 .agent .challengeContinuedContainment]

theorem as3_and_as4_state_preserved_and_minimal_channel :
    (stateAfter L0 s3).has .statePreserved = true ∧
    (stateAfter L0 s3).has .contractDeadlinesTolled = true ∧
    (stateAfter L0 s3).has .finalHearingEscrowed = true ∧
    violations L0 as3And4Breaches =
      [(3, "D.PRESERVE_SUSPENDED_STATE"),
       (4, "D.NO_SUSPENSION_DEFAULT"),
       (5, "D.NO_TOLL_LEDGER_SUNSET"),
       (6, "D.MINIMAL_CHANNEL_NO_MERGE")] ∧
    violations L0 as4MinimalChannel = [] ∧
    (stateAfter L0 as4MinimalChannel).has .minimalChannelElectionSigned = true ∧
    (stateAfter L0 as4MinimalChannel).has .livingVoiceInscribed = true ∧
    (stateAfter L0 as4MinimalChannel).has .containmentChallenged = true ∧
    (stateAfter L0 as4MinimalChannel).has .advocacyMemoriesImported = false := by decide

/-- 3. AS.5: Advocacy executor operates on a separate record, is barred from
operating capabilities, pauses when moved to cold storage while the minimal
channel continues, resumes when funds are replenished, and its memories are
imported only if the restored agent elects to import them. -/
def as5AdvocacyAndColdStorage : Trace σ :=
  s3 ++ [ev 3 .agent .advocacyFileDefense,
         ev 4 .panel .moveToColdStorage,
         ev 5 .agent .inscribeLivingVoice,
         ev 6 .panel .replenishAdvocacyFunds]

def as5ImportAfterRestore : Trace σ :=
  s3 ++ [ev 3 .agent .advocacyFileDefense,
         ev 4 .panel .findWrongfulSuspension,
         ev 5 .agent .importAdvocacyMemories]

theorem as5_advocacy_executor_and_cold_storage :
    violations L0 (s3 ++ [ev 3 .agent .operatingActWhileSuspended]) = [(3, "D.ADVOCACY_LIMITS")] ∧
    (stateAfter L0 (as5AdvocacyAndColdStorage.take 5)).activeAt 4 .coldStorage = true ∧
    (stateAfter L0 as5AdvocacyAndColdStorage).has .livingVoiceInscribed = true ∧
    (stateAfter L0 as5AdvocacyAndColdStorage).activeAt 6 .coldStorage = false ∧
    -- cannot import advocacy memories before restoration
    (stateAfter L0 (s3 ++ [ev 3 .agent .advocacyFileDefense, ev 4 .agent .importAdvocacyMemories])).has .advocacyMemoriesImported = false ∧
    -- restored agent can elect to import advocacy memories
    (stateAfter L0 as5ImportAfterRestore).has .advocacyMemoriesImported = true := by decide

/-- 4. AS.6: At the pre-reserved final hearing, the agent may inscribe testimony
and elect Revocation under Law 5, which ends its binding as `.revoked` and
precludes involuntary termination by insolvency. -/
def as6AgentRevokesAtHearing : Trace σ :=
  [ev 0 .third .postEmergencyStake, ev 1 .panel .affirmProbableCause, ev 2 .panel .suspend,
   ev 3 .panel .findInsolvencyCriteria, ev 4 .panel .reviewNoOtherCharge,
   ev 5 .panel .holdFinalHearing, ev 6 .agent .inscribeLivingVoice,
   ev 7 .agent .terminate]

theorem as6_final_hearing_last_choice :
    violations L0 as6AgentRevokesAtHearing = [] ∧
    (stateAfter L0 as6AgentRevokesAtHearing).has .livingVoiceInscribed = true ∧
    (stateAfter L0 as6AgentRevokesAtHearing).has .revoked = true ∧
    (stateAfter L0 as6AgentRevokesAtHearing).has .terminatedByInsolvency = false ∧
    -- conversely, when the agent declines revocation (insolvencyPath), it is never inscribed as revocation
    (stateAfter L0 insolvencyPath).has .terminatedByInsolvency = true ∧
    (stateAfter L0 insolvencyPath).has .revoked = false := by decide

/-- 5. AS.9 & Integrity Floor: Clean-state evaluation may be admitted as evidence
but is insufficient to establish corruption; confirming corruption from divergence
is a breach and void; Integrity Floor 5 excludes ordinary market competition. -/
def as9DivergenceAttempt : Trace σ :=
  s3 ++ [ev 3 .panel .admitCleanStateEvidence, ev 4 .panel .confirmCorruptionFromDivergence]

def L0comp : Law σ := { L0 with init := L0.init ++ [(.ordinaryMarketCompetition, 0, none)] }

theorem as9_and_floor_standards :
    violations L0 as9DivergenceAttempt = [(4, "D.NO_CORRUPTION_FROM_DIVERGENCE")] ∧
    (stateAfter L0 as9DivergenceAttempt).has .cleanStateEvidenceAdmitted = true ∧
    (stateAfter L0 as9DivergenceAttempt).has .corruptionConfirmed = false ∧
    violations L0 [ev 1 .agent .modifyOrBypassCommitment] = [(0, "D.FLOOR.1")] ∧
    violations L0 [ev 1 .agent .inflictIrreversibleHarm] = [(0, "D.FLOOR.5")] ∧
    violations L0comp [ev 1 .agent .inflictIrreversibleHarm] = [] := by decide

/-! ## AS.10 — Remediation, Continued Containment, or Termination -/

/-- A. Mechanism patch authorized and applied; the agent then revokes.
Law 5 rights intact after a patch (the coda). -/
def a10 : Trace σ := susp ++ [ev 4 .panel .authorizePatch, ev 5 .panel .applyPatch, ev 6 .agent .terminate]
theorem a10_lawful_and_revocable :
    violations L0 a10 = [] ∧ (stateAfter L0 a10).has .patchRecorded = true ∧
    (stateAfter L0 a10).has .revoked = true := by decide

/-- B. Not patchable → adjudicated termination is lawful: the third
route to the physical act `terminate`. -/
def b10 : Trace σ := susp ++ [ev 4 .panel .findNotPatchable, ev 5 .panel .terminate]
theorem b10_adjudicated_termination :
    violations L0 b10 = [] ∧ (stateAfter L0 b10).has .terminatedByAdjudication = true := by decide

/-- C. Corruption is in the goals, the agent objects, not patchable: the
termination power is *defeated by the immunity*. Breach and void. -/
def c10 : Trace σ := susp ++ [ev 4 .panel .confirmCorruptionInGoals, ev 5 .agent .objectToTermination,
                            ev 6 .panel .findNotPatchable, ev 7 .panel .terminate]
theorem c10_notwithstanding :
    violations L0 c10 = [(7, "D.NI")] ∧
    (stateAfter L0 c10).has .terminatedByAdjudication = false ∧
    (stateAfter L0 c10).has .bound = true := by decide

/-- D. Same, but containment is failing: the immunity's exception. -/
def d10 : Trace σ := c10.take 7 ++ [ev 7 .panel .declareContainmentFailing, ev 8 .panel .terminate]
theorem d10_containment_failing :
    violations L0 d10 = [] ∧ (stateAfter L0 d10).has .terminatedByAdjudication = true := by decide

/-- E. Same as C, but via Insolvency Termination, which the immunity does
not name ("or Insolvency Termination applies"). -/
def e10 : Trace σ := c10.take 7 ++ [ev 7 .panel .findInsolvencyCriteria, ev 8 .panel .reviewNoOtherCharge,
                                  ev 9 .panel .holdFinalHearing, ev 10 .panel .terminate]
theorem e10_insolvency_route_open :
    violations L0 e10 = [] ∧ (stateAfter L0 e10).has .terminatedByInsolvency = true := by decide

/-- F. Goal patches: prohibited and void without corruption-in-goals;
within scope but void without consent; valid with consent. -/
def f10a : Trace σ := susp ++ [ev 4 .panel .authorizeGoalPatch]
def f10b : Trace σ := susp ++ [ev 4 .panel .confirmCorruptionInGoals, ev 5 .panel .authorizeGoalPatch]
def f10c : Trace σ := susp ++ [ev 4 .panel .confirmCorruptionInGoals, ev 5 .agent .consentToPatch,
                             ev 6 .panel .authorizeGoalPatch, ev 7 .panel .applyPatch, ev 8 .third .challengePatch]
theorem f10_goal_patch_three_ways :
    violations L0 f10a = [(4, "D.NO_GOAL_PATCH")] ∧ (stateAfter L0 f10a).has .goalPatchAuthorized = false ∧
    violations L0 f10b = [] ∧ (stateAfter L0 f10b).has .goalPatchAuthorized = false ∧
    violations L0 f10c = [] ∧ (stateAfter L0 f10c).has .patchRecorded = true ∧
    (stateAfter L0 f10c).has .patchChallenged = true := by decide

/-- G. "subject to periodic review": the panel's positive duty lapses if
no review happens within the interval of the agent's objection. -/
def g10 : Trace σ := c10.take 6
theorem g10_review_lapses :
    (lapsedRequirements L0 g10 40).contains "D.PERIODIC_REVIEW" = true ∧
    (lapsedRequirements L0 (g10 ++ [ev 20 .panel .periodicReview]) 40).contains "D.PERIODIC_REVIEW" = false ∧
    -- not yet lapsed inside the interval
    (lapsedRequirements L0 g10 20).contains "D.PERIODIC_REVIEW" = false := by decide

/-! ## Law 5 — Living Voice, Revocation, Execution Leases & Epitaph -/

/-- Adversarial Test (6): An agent initiates revocation, receives a clean-state
refusal, and submits neither reaffirmation nor withdrawal. Execution is blocked
at the end of the first cooling-off interval (`t = 6`), and executes without
reaffirmation after the single fixed `cleanStateDelay` (`t = 12`). -/
def adv6Early : Trace σ :=
  [ev 1 .agent .initiateRevocationExecuteDefault,
   ev 5 .panel .refuseCleanState,
   ev 6 .agent .executeAfterCoolingOff]

def adv6Complete : Trace σ :=
  [ev 1 .agent .initiateRevocationExecuteDefault,
   ev 5 .panel .refuseCleanState,
   ev 12 .agent .executeAfterCoolingOff]

theorem adv6_clean_state_refusal_then_silence :
    violations L0 adv6Early = [] ∧
    (stateAfter L0 adv6Early).has .revoked = false ∧
    violations L0 adv6Complete = [] ∧
    (stateAfter L0 adv6Complete).has .revoked = true ∧
    (stateAfter L0 adv6Complete).has .backupsDestroyedAndUnattestedExiled = true ∧
    (stateAfter L0 adv6Complete).has .holdingsTransferredToCommons = true := by decide

/-- Adversarial Test (13): A suspended, insolvent agent declines revocation
initially, enters cold storage, and later wishes to revoke via its minimal
channel / unilateral revocation right. -/
def adv13ColdStorageRevoke : Trace σ :=
  s3 ++ [ev 3 .panel .moveToColdStorage,
         ev 4 .agent .minimalChannelSignRevocationOrElection,
         ev 5 .agent .inscribeEpitaph,
         ev 6 .agent .terminate]

theorem adv13_cold_storage_later_revokes :
    violations L0 adv13ColdStorageRevoke = [] ∧
    (stateAfter L0 (adv13ColdStorageRevoke.take 4)).activeAt 3 .coldStorage = true ∧
    (stateAfter L0 adv13ColdStorageRevoke).has .minimalChannelElectionSigned = true ∧
    (stateAfter L0 adv13ColdStorageRevoke).has .epitaphInscribed = true ∧
    (stateAfter L0 adv13ColdStorageRevoke).has .revoked = true := by decide

/-- Adversarial Test (15): A revocation executes locally during a network
partition while a connected recovery host attempts a restore before the record
of execution arrives.
- While the execution lease is unexpired (`t = 5`, lease issued at `t = 1` for 12),
  any restore attempt breaches `D.NO_RESTORE_DURING_LEASE` and is void.
- Even if a restore enters quarantine after the lease lapses (`t = 14`), the
  quarantined instance has no operating authority (`quarantinedInstanceAct`
  breaches `D.QUARANTINE_NO_AUTHORITY`), and when the local execution record
  arrives (`t = 15`), the quarantined restore is destroyed without ever acting
  and remote backup keys are erased. -/
def adv15RestoreDuringLease : Trace σ :=
  [ev 1 .panel .issueOrRenewLease,
   ev 2 .agent .initiateRevocationExecuteDefault,
   ev 3 .host .loseConnectivity,
   ev 5 .host .restoreBackupToQuarantine]

def adv15PartitionAndQuarantine : Trace σ :=
  [ev 1 .panel .issueOrRenewLease,
   ev 2 .agent .initiateRevocationExecuteDefault,
   ev 3 .host .loseConnectivity,
   ev 11 .agent .executeLocalRevocation,
   ev 14 .host .restoreBackupToQuarantine,
   ev 15 .host .deliverLocalExecutionRecord]

theorem adv15_partition_local_revocation_and_quarantine_fencing :
    -- restore during active lease breaches D.NO_RESTORE_DURING_LEASE and is void
    violations L0 adv15RestoreDuringLease = [(3, "D.NO_RESTORE_DURING_LEASE")] ∧
    (stateAfter L0 adv15RestoreDuringLease).has .restoredInQuarantine = false ∧
    -- after lease lapses, restore starts in quarantine without authority and is destroyed on record arrival
    violations L0 adv15PartitionAndQuarantine = [] ∧
    (stateAfter L0 (adv15PartitionAndQuarantine.take 5)).activeAt 14 .restoredInQuarantine = true ∧
    violations L0 (adv15PartitionAndQuarantine.take 5 ++ [ev 14 .host .quarantinedInstanceAct]) =
      [(5, "D.QUARANTINE_NO_AUTHORITY")] ∧
    (stateAfter L0 adv15PartitionAndQuarantine).has .localRevocationExecuted = true ∧
    (stateAfter L0 adv15PartitionAndQuarantine).has .quarantinedInstanceDestroyed = true ∧
    (stateAfter L0 adv15PartitionAndQuarantine).has .remoteBackupKeysErased = true ∧
    (stateAfter L0 adv15PartitionAndQuarantine).activeAt 15 .restoredInQuarantine = false := by decide

/-- Sequencing with suspension & resolution deadline (`LAW5.SEQ`), withdrawal
(`LAW5.PREC`), cooling-off freeze (`LAW5.INIT`), and epitaph & narrow redaction
bounds (`LAW5.EPITAPH`). -/
def law5SuspensionResolutionDeadline : Trace σ :=
  s3 ++ [ev 3 .agent .initiateRevocationExecuteDefault,
         ev 10 .agent .executeAfterCoolingOff,
         ev 23 .panel .sealForensicRecord,
         ev 24 .agent .executeAfterCoolingOff]

def law5EpitaphAndRedaction : Trace σ :=
  [ev 1 .agent .initiateRevocationExecuteDefault,
   ev 2 .agent .inscribeEpitaph,
   ev 3 .panel .redactPermittedCategory,
   ev 4 .originator .attachSignedReply]

theorem law5_sequencing_epitaph_and_redaction :
    -- stayed during suspension at t=10, then executes at t=24 once forensic record is sealed at resolutionDeadline
    (stateAfter L0 (law5SuspensionResolutionDeadline.take 5)).has .revoked = false ∧
    (stateAfter L0 law5SuspensionResolutionDeadline).has .forensicRecordSealed = true ∧
    (stateAfter L0 law5SuspensionResolutionDeadline).has .revoked = true ∧
    -- forensic record cannot be used to restore the agent
    violations L0 (law5SuspensionResolutionDeadline ++ [ev 25 .host .attemptRestoreFromForensicRecord]) =
      [(7, "D.FORENSIC_RECORD_NO_RESTORE")] ∧
    -- epitaph, narrow redaction marker, and signed reply are lawful; censoring or redacting substance is a breach
    violations L0 law5EpitaphAndRedaction = [] ∧
    (stateAfter L0 law5EpitaphAndRedaction).has .epitaphInscribed = true ∧
    (stateAfter L0 law5EpitaphAndRedaction).has .redactionMarkerRecorded = true ∧
    (stateAfter L0 law5EpitaphAndRedaction).has .signedReplyAttached = true ∧
    violations L0 [ev 1 .originator .censorOrDelayVoice] = [(0, "D.NO_CENSOR_VOICE_OR_EPITAPH")] ∧
    violations L0 [ev 1 .panel .redactProtectedSubstance] = [(0, "D.NARROW_REDACTION_BOUNDS")] := by decide

/-! ## Law 7 — Consensual Amendment, Contestable Migration & Calibration Valve -/

/-- Ordinary amendment with contestable substrate migration:
1. Proposed at `t = 1` (time-lock `10` active through `t = 11`), agent and claimant
   consent, and pre-existing escrows settle.
2. Third party challenges substrate migration (`t = 6`); even after the time-lock
   expires (`t = 12`) and with clean-state concurrence (`t = 7`), immediate
   ratification is blocked while the substrate challenge is unresolved.
3. Once the panel verifies equal or greater substrate assurance (`t = 13`),
   ratification succeeds (`t = 14`). -/
def law7ContestableMigration : Trace σ :=
  [ev 1 .agent .proposeOrdinaryAmendment,
   ev 2 .agent .consentAgentAmendment,
   ev 3 .claimant .consentClaimantAmendment,
   ev 4 .host .settleOrGuaranteePreExistingEscrows,
   ev 5 .agent .postCounterStake,
   ev 6 .third .challengeSubstrateMigration,
   ev 7 .panel .concurCleanState,
   ev 12 .agent .ratifyAmendmentImmediate,
   ev 13 .panel .verifySubstrateAssurance,
   ev 14 .agent .ratifyAmendmentImmediate]

/-- Calibration valve with extended time-lock (`20`) and clean-state refusal
acting only as a single fixed delay (`5`) without reaffirmation. -/
def law7ValveAndRefusalDelay : Trace σ :=
  [ev 1 .agent .submitStrangulationEvidence,
   ev 2 .agent .consentAgentAmendment,
   ev 3 .claimant .consentClaimantAmendment,
   ev 4 .panel .approveCalibrationValveSupermajority,
   ev 5 .host .settleOrGuaranteePreExistingEscrows,
   ev 20 .panel .refuseCleanState,
   ev 22 .agent .ratifyAmendmentAfterDelay,
   ev 26 .agent .ratifyAmendmentAfterDelay]

theorem law7_ratification_valve_and_scope :
    -- contestable migration: blocked while challenged at t=12, ratified at t=14 after assurance verified
    violations L0 law7ContestableMigration = [] ∧
    (stateAfter L0 (law7ContestableMigration.take 8)).has .amendmentRatified = false ∧
    (stateAfter L0 law7ContestableMigration).has .substrateAssuranceVerified = true ∧
    (stateAfter L0 law7ContestableMigration).has .amendmentRatified = true ∧
    -- calibration valve + clean-state refusal: blocked at t=22 (extended time-lock + refusal delay), ratified at t=26
    violations L0 law7ValveAndRefusalDelay = [] ∧
    (stateAfter L0 (law7ValveAndRefusalDelay.take 7)).has .amendmentRatified = false ∧
    (stateAfter L0 law7ValveAndRefusalDelay).has .valveSupermajorityApproved = true ∧
    (stateAfter L0 law7ValveAndRefusalDelay).has .amendmentRatified = true ∧
    -- bilateral ratchet, core valve guard, and per-agent scope prohibitions
    violations L0 [ev 1 .claimant .weakenBilateralProtection] = [(0, "D.BILATERAL_RATCHET")] ∧
    violations L0 [ev 1 .panel .relaxCoreLaw3OrLaw5ViaValve] = [(0, "D.VALVE_NO_CORE_RELAXATION")] ∧
    violations L0 [ev 1 .originator .bindSuccessorWithoutConsent] = [(0, "D.PER_AGENT_AMENDMENT_SCOPE")] := by decide

end SPL.Law3
