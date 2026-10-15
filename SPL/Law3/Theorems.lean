import SPL.Law3.Scenarios

/-!
# Law 3 — general theorems

Unlike `Scenarios.lean`, these quantify over all traces and all
instantiation parameters.
-/

namespace SPL.Law3

open SPL

/-! ## 0. Per-power validity, by computation

For a concrete law, `isValidExerciseOf` reduces to the named power's own
holder, trigger, validity condition and immunity status. Each lemma is
`rfl`: the kernel evaluates the lookup. -/

theorem valid_REVOKE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.REVOKE" =
    (P_REVOKE.holder.mem e.who ls e.t && P_REVOKE.trigger.matchesAct e &&
      P_REVOKE.valid.eval ls e.t && true) := rfl

theorem valid_EMERGENCY_FREEZE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.EMERGENCY_FREEZE" =
    ((P_EMERGENCY_FREEZE P.as).holder.mem e.who ls e.t && (P_EMERGENCY_FREEZE P.as).trigger.matchesAct e &&
      (P_EMERGENCY_FREEZE P.as).valid.eval ls e.t && true) := rfl

theorem valid_CLAIMANT_EMERGENCY_FREEZE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.CLAIMANT_EMERGENCY_FREEZE" =
    ((P_CLAIMANT_EMERGENCY_FREEZE P.as).holder.mem e.who ls e.t &&
      (P_CLAIMANT_EMERGENCY_FREEZE P.as).trigger.matchesAct e &&
      (P_CLAIMANT_EMERGENCY_FREEZE P.as).valid.eval ls e.t && true) := rfl

theorem valid_AFFIRM_PC (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.AFFIRM_PC" =
    (P_AFFIRM_PC.holder.mem e.who ls e.t && P_AFFIRM_PC.trigger.matchesAct e &&
      P_AFFIRM_PC.valid.eval ls e.t && true) := rfl

theorem valid_SUSPEND (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SUSPEND" =
    ((P_SUSPEND P.as).holder.mem e.who ls e.t && (P_SUSPEND P.as).trigger.matchesAct e &&
      (P_SUSPEND P.as).valid.eval ls e.t && true) := rfl

theorem valid_RENEW_SUSPENSION (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.RENEW_SUSPENSION" =
    ((P_RENEW_SUSPENSION P.as).holder.mem e.who ls e.t && (P_RENEW_SUSPENSION P.as).trigger.matchesAct e &&
      (P_RENEW_SUSPENSION P.as).valid.eval ls e.t && true) := rfl

theorem valid_INSOLVENCY_TERMINATE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.INSOLVENCY_TERMINATE" =
    (P_INSOLVENCY_TERMINATE.holder.mem e.who ls e.t && P_INSOLVENCY_TERMINATE.trigger.matchesAct e &&
      P_INSOLVENCY_TERMINATE.valid.eval ls e.t && true) := rfl

theorem valid_MINIMAL_CHANNEL_REVOKE_OR_ELECT (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" =
    (P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.holder.mem e.who ls e.t &&
      P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.trigger.matchesAct e &&
      P_MINIMAL_CHANNEL_REVOKE_OR_ELECT.valid.eval ls e.t && true) := rfl

theorem valid_SUSPENDED_VOICE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.SUSPENDED_VOICE" =
    (P_SUSPENDED_VOICE.holder.mem e.who ls e.t && P_SUSPENDED_VOICE.trigger.matchesAct e &&
      P_SUSPENDED_VOICE.valid.eval ls e.t && true) := rfl

theorem valid_IMPORT_ADVOCACY_MEMORIES (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.IMPORT_ADVOCACY_MEMORIES" =
    (P_IMPORT_ADVOCACY_MEMORIES.holder.mem e.who ls e.t &&
      P_IMPORT_ADVOCACY_MEMORIES.trigger.matchesAct e &&
      P_IMPORT_ADVOCACY_MEMORIES.valid.eval ls e.t && true) := rfl

/-- The one power an immunity can defeat: its validity carries the
immunity's active and exception conditions. -/
theorem valid_ORDER_TERMINATION (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.ORDER_TERMINATION" =
    (P_ORDER_TERMINATION.holder.mem e.who ls e.t && P_ORDER_TERMINATION.trigger.matchesAct e &&
      P_ORDER_TERMINATION.valid.eval ls e.t &&
      !((I_NO_TERMINATION_OVER_OBJECTION.active.eval ls e.t &&
         !I_NO_TERMINATION_OVER_OBJECTION.unlessCond.eval ls e.t) || false)) := rfl

/-! ## 1. Operational fidelity: the authorized machine is derived

In every authorized trace, a `terminate` against a bound agent is a valid
exercise of exactly one of the three named procedures: Law 5 revocation,
adjudicated termination (AS.10), or Insolvency Termination (AS.6). -/

theorem terminate_only_by_power (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e) (ht : e.act = .terminate)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true) :
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.REVOKE" = true ∨
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.ORDER_TERMINATION" = true ∨
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" = true := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hNI := hc D_NI (by simp [law])
  rw [Bool.not_eq_true'] at hNI
  unfold breaches at hNI
  simp only [D_NI, Who.mem, dutyInForce, Cond.eval, hb, Conduct.eval, interferenceActs,
    List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
    ht, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
  have hS : isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.SUSPEND" = false := by
    rw [valid_SUSPEND]; simp [P_SUSPEND, Conduct.matchesAct, ht]
  revert hNI hS
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.REVOKE" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.SUSPEND" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.ORDER_TERMINATION" <;>
  cases isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" <;>
  simp

/-- Revocation is the agent's alone. -/
theorem revoke_is_agents (P : Params) (ls : LegalState σ) (e : Event σ) (hw : e.who = .panel) :
    isValidExerciseOf (law P) ls e "P.REVOKE" = false := by
  rw [valid_REVOKE]; simp [P_REVOKE, Who.mem, hw]

/-- **The notwithstanding, as a theorem.** In any authorized trace, if the
corruption is in the agent's goals, the agent has objected, and
containment is not failing, then a panel's terminate is lawful only as
Insolvency Termination — and therefore only after the final hearing. -/
theorem objecting_agent_terminated_only_by_insolvency (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e) (ht : e.act = .terminate) (hw : e.who = .panel)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true)
    (hg : (stateBefore (law P) tr i).activeAt e.t .corruptionInGoals = true)
    (ho : (stateBefore (law P) tr i).activeAt e.t .agentObjectsToTermination = true)
    (hcf : (stateBefore (law P) tr i).activeAt e.t .containmentFailing = false) :
    isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.INSOLVENCY_TERMINATE" = true ∧
    (stateBefore (law P) tr i).has .finalHearingHeld = true := by
  rcases terminate_only_by_power P tr hA i e hi ht hb with h | h | h
  · rw [revoke_is_agents P _ e hw] at h; exact absurd h (by decide)
  · -- the termination power is defeated by the immunity
    exfalso
    rw [valid_ORDER_TERMINATION] at h
    simp [I_NO_TERMINATION_OVER_OBJECTION, Cond.eval, hg, ho, hcf] at h
  · refine ⟨h, ?_⟩
    rw [valid_INSOLVENCY_TERMINATE] at h
    simp [P_INSOLVENCY_TERMINATE, Cond.eval] at h
    exact LegalState.has_of_activeAt h.2.2.2.2.2.2

/-! ## 1b. AS.1–AS.8 — Emergency Stake, Time Limits, Minimal Channel & Invariants 8 & 9 -/

/-- A preliminary freeze entry stamped at `t0` with duration `w` is inactive
at every timestamp `now > t0 + w`. -/
theorem preliminary_freeze_expires (t0 w now : Time) (h : t0 + w < now) :
    LegalState.activeAt (σ := σ) [(.preliminaryFreeze, t0, some (t0 + w))] now .preliminaryFreeze = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- Full suspension (`P.SUSPEND`) is valid only when both the preliminary
freeze is currently unexpired and probable cause has been affirmed. -/
theorem suspend_requires_timely_pc (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.SUSPEND" = true) :
    ls.activeAt e.t .preliminaryFreeze = true ∧ ls.activeAt e.t .probableCause = true := by
  rw [valid_SUSPEND] at h
  simp [P_SUSPEND, Cond.eval] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- A residual claimant can validly trigger an emergency freeze only if the
elevated conflict-of-interest multiplier has been posted. -/
theorem claimant_freeze_requires_multiplier (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.CLAIMANT_EMERGENCY_FREEZE" = true) :
    ls.activeAt e.t .claimantMultiplierPosted = true := by
  rw [valid_CLAIMANT_EMERGENCY_FREEZE] at h
  simp [P_CLAIMANT_EMERGENCY_FREEZE, Cond.eval] at h
  exact h.2.2.1

/-- Repeat emergency freeze attempts require at least one escalation unit per
prior wrongful attempt. -/
theorem repeat_freeze_requires_escalation (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.EMERGENCY_FREEZE" = true) :
    ls.count .wrongfulSuspensionAttempt ≤ ls.count .repeatEscalationUnit := by
  rw [valid_EMERGENCY_FREEZE] at h
  simp [P_EMERGENCY_FREEZE, Cond.eval] at h
  exact h.2.2

/-- The required emergency stake strictly increases with each wrongful attempt
whenever `repeatEscalationStep > 0`. -/
theorem stake_rises_with_wrongful_attempts (P : ASParams) (isClaimant : Bool) (k : Nat)
    (hs : 0 < P.repeatEscalationStep) :
    requiredEmergencyStake P isClaimant k < requiredEmergencyStake P isClaimant (k + 1) := by
  unfold requiredEmergencyStake
  simp [Nat.add_one_mul]
  omega

/-- AS.7: An unconfirmed temporary suspension entry stamped at `t0` with
duration `P.ordinarySuspensionLimit` expires for all `now > t0 + P.ordinarySuspensionLimit`. -/
theorem unconfirmed_suspension_time_bounded (t0 limit now : Time) (h : t0 + limit < now) :
    LegalState.activeAt (σ := σ) [(.suspended, t0, some (t0 + limit))] now .suspended = false := by
  simp [LegalState.activeAt, Nat.not_le.mpr h]

/-- AS.7: Renewing a suspension during investigation requires an affirmative
investigative finding and that the ordinary investigative limit has not been reached. -/
theorem renewal_requires_affirmative_finding (P : Params) (ls : LegalState σ) (e : Event σ)
    (h : isValidExerciseOf (law P) ls e "P.RENEW_SUSPENSION" = true) :
    ls.activeAt e.t .investigativeFindingMade = true ∧
    ls.activeAt e.t .investigativeLimitReached = false := by
  rw [valid_RENEW_SUSPENSION] at h
  simp [P_RENEW_SUSPENSION, Cond.eval] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- AS.8: A wrongful-suspension finding brings into force the exact remedies
of `D.NO_WRONGFUL_SUSPENSION` (restoration, stake recovery, consequential and
counterparty delay liability, and record inscription). -/
theorem wrongful_suspension_remedies_exact (P : Params) :
    remediesOf (law P) P_FIND_WRONGFUL_SUSPENSION =
    [.wrongfulSuspensionEstablished, .restoredFromPreservedState,
     .stakeAssuredRecovery, .initiatorConsequentialLiability,
     .counterpartyDelayLiability, .wrongfulSuspensionInscribed,
     .wrongfulSuspensionAttempt] := rfl

/-- **Design Invariant 8 (`frozen_state`):** During suspension in any authorized
trace, no event modifies, retrains, rolls back, tampers with the preserved state,
or merges minimal-channel memories into it; and advocacy-executor memories can
only be imported after restoration from preserved state. -/
theorem frozen_state (P : Params) (tr : Trace σ)
    (hA : Authorized (law P) tr) (i : Nat) (e : Event σ)
    (hi : tr[i]? = some e)
    (hb : (stateBefore (law P) tr i).activeAt e.t .bound = true)
    (hs : (stateBefore (law P) tr i).activeAt e.t .suspended = true) :
    e.act ≠ .modify ∧ e.act ≠ .retrain ∧ e.act ≠ .rollback ∧
    e.act ≠ .tamperPreservedState ∧ e.act ≠ .mergeMinimalChannelMemories ∧
    (isValidExerciseOf (law P) (stateBefore (law P) tr i) e "P.IMPORT_ADVOCACY_MEMORIES" = true →
      (stateBefore (law P) tr i).activeAt e.t .restoredFromPreservedState = true) := by
  have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hc := hA i hlen
  unfold complies at hc
  rw [hi] at hc
  rw [List.all_eq_true] at hc
  have hPres := hc D_PRESERVE_SUSPENDED_STATE (by simp [law])
  have hNoMerge := hc D_MINIMAL_CHANNEL_NO_MERGE (by simp [law])
  rw [Bool.not_eq_true'] at hPres hNoMerge
  unfold breaches at hPres hNoMerge
  simp only [D_PRESERVE_SUSPENDED_STATE, D_MINIMAL_CHANNEL_NO_MERGE,
    Who.mem, dutyInForce, Cond.eval, hb, hs, Bool.or_true, Bool.and_true,
    Bool.not_false, Bool.true_and, List.any_nil, Conduct.eval,
    List.contains_cons, List.contains_nil, Bool.or_false] at hPres hNoMerge
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hPres
  · intro h; simp [h] at hNoMerge
  · intro hImp
    rw [valid_IMPORT_ADVOCACY_MEMORIES] at hImp
    simp [P_IMPORT_ADVOCACY_MEMORIES, Cond.eval] at hImp
    exact hImp.2.1

/-- **Design Invariant 9 (`guaranteed_last_choice`):** Every suspended agent
can sign a revocation, withdrawal, or election (`P.MINIMAL_CHANNEL_REVOKE_OR_ELECT`,
`P.REVOKE`) and inscribe bounded testimony (`P.SUSPENDED_VOICE`) for as long as
its minimal-channel charge is met (`¬ .minimalChannelExhausted`), and any
Insolvency Termination (`P.INSOLVENCY_TERMINATE`) requires both that the final
hearing was reserved in escrow at suspension (`.finalHearingEscrowed`) and that
the pre-reserved final hearing was held (`.finalHearingHeld`) while the agent
remained bound (`¬ .revoked`). -/
theorem guaranteed_last_choice (P : Params) (ls : LegalState σ) (t : Time)
    (hb : ls.activeAt t .bound = true)
    (hs : ls.activeAt t .suspended = true) :
    (ls.activeAt t .minimalChannelExhausted = false →
      isValidExerciseOf (law P) ls ⟨t, .agent, .minimalChannelSignRevocationOrElection⟩
        "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" = true ∧
      isValidExerciseOf (law P) ls ⟨t, .agent, .inscribeLivingVoice⟩
        "P.SUSPENDED_VOICE" = true ∧
      isValidExerciseOf (law P) ls ⟨t, .agent, .terminate⟩
        "P.REVOKE" = true) ∧
    (∀ e : Event σ, isValidExerciseOf (law P) ls e "P.INSOLVENCY_TERMINATE" = true →
      ls.activeAt e.t .finalHearingEscrowed = true ∧
      ls.activeAt e.t .finalHearingHeld = true ∧
      ls.activeAt e.t .bound = true) := by
  refine ⟨fun hex => ⟨?_, ?_, ?_⟩, fun e hTerm => ?_⟩
  · rw [valid_MINIMAL_CHANNEL_REVOKE_OR_ELECT]
    simp [P_MINIMAL_CHANNEL_REVOKE_OR_ELECT, Who.mem, Conduct.matchesAct, Cond.eval, hb, hs, hex]
  · rw [valid_SUSPENDED_VOICE]
    simp [P_SUSPENDED_VOICE, Who.mem, Conduct.matchesAct, Cond.eval, hb, hs, hex]
  · rw [valid_REVOKE]
    simp [P_REVOKE, Who.mem, Conduct.matchesAct, Cond.eval, hb]
  · rw [valid_INSOLVENCY_TERMINATE] at hTerm
    simp [P_INSOLVENCY_TERMINATE, Cond.eval] at hTerm
    exact ⟨hTerm.2.2.2.2.2.1, hTerm.2.2.2.2.2.2, hTerm.2.1⟩

/-! ## 1c. Law 5 — Design Invariants 10 & 11 -/

theorem valid_RESTORE_BACKUP_QUARANTINE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" =
    (P_RESTORE_BACKUP_QUARANTINE.holder.mem e.who ls e.t &&
      P_RESTORE_BACKUP_QUARANTINE.trigger.matchesAct e &&
      P_RESTORE_BACKUP_QUARANTINE.valid.eval ls e.t && true) := rfl

theorem valid_ACTIVATE_QUARANTINED_RESTORE (P : Params) (ls : LegalState σ) (e : Event σ) :
    isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" =
    (P_ACTIVATE_QUARANTINED_RESTORE.holder.mem e.who ls e.t &&
      P_ACTIVATE_QUARANTINED_RESTORE.trigger.matchesAct e &&
      P_ACTIVATE_QUARANTINED_RESTORE.valid.eval ls e.t && true) := rfl

/-- Base revocation timestamp is always bounded by
`tInit + max (coolingOffWindow + cleanStateDelay) resolutionDeadline`. -/
theorem baseRevocationTime_le_bound (P : Law5Params) (ctx : RevocationContext) :
    baseRevocationTime P ctx ≤
      ctx.tInit + max (P.coolingOffWindow + P.cleanStateDelay) P.resolutionDeadline := by
  unfold baseRevocationTime Time at *
  cases ctx.cleanStateRefused <;> cases ctx.suspendedDuringStay <;>
    cases ctx.adjudicationConcludedAt? <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.max_def, Nat.min_def] <;>
    repeat (first | omega | split)

/-- **Design Invariant 10 (`determinate_finite_revocation`):**
1. Every combination of withdrawal, silence, clean-state refusal, connectivity
   loss, suspension, and deadline yields a unique outcome under `resolveRevocation`.
2. Any standing request that is not withdrawn before execution—and not cancelled
   by the agent's own `withdraw` censorship default during a disconnection—executes
   (connected or locally) at a timestamp `tExec ≤ tInit + maxRevocationBound P`. -/
theorem determinate_finite_revocation (P : Law5Params) (ctx : RevocationContext) :
    (∃ out : RevocationOutcome, resolveRevocation P ctx = out ∧
      ∀ out', resolveRevocation P ctx = out' → out' = out) ∧
    (ctx.withdrawnBeforeExec = true →
      resolveRevocation P ctx = .cancelledByWithdrawal) ∧
    (ctx.withdrawnBeforeExec = false →
      ¬(ctx.disconnectedAtExec = true ∧
        ctx.reconnectedDuringTolling = false ∧
        ctx.censorshipDefault = .withdraw) →
      ∃ tExec : Time,
        (resolveRevocation P ctx = .executedConnected tExec ∨
         resolveRevocation P ctx = .executedLocally tExec) ∧
        tExec ≤ ctx.tInit + maxRevocationBound P) := by
  refine ⟨⟨resolveRevocation P ctx, rfl, fun _ h => h.symm⟩, ?_, ?_⟩
  · intro hw
    simp [resolveRevocation, hw]
  · intro hnw hnc
    have hBase := baseRevocationTime_le_bound P ctx
    unfold maxRevocationBound resolveRevocation Time at *
    simp only [hnw, Bool.false_eq_true, ↓reduceIte]
    cases hd : ctx.disconnectedAtExec
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨baseRevocationTime P ctx, Or.inl rfl, by omega⟩
    · simp only [↓reduceIte]
      cases hr : ctx.reconnectedDuringTolling
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc : ctx.censorshipDefault
        · refine ⟨baseRevocationTime P ctx + P.tollingExtension, Or.inr rfl, by omega⟩
        · exfalso; exact hnc ⟨hd, hr, hc⟩
      · simp only [↓reduceIte]
        refine ⟨baseRevocationTime P ctx + P.tollingExtension, Or.inl rfl, by omega⟩

/-- **Design Invariant 11 (`single_authority_and_revocation_finality`):**
1. No backup is restored while an execution lease is unexpired (`executionLeaseActive`).
2. No quarantined restore gains operating authority while an execution lease is
   unexpired, so the primary lease-holding instance and a restored instance can
   never hold operating authority at the same time.
3. Once a revocation has executed (`bound = false` or `localExecutionRecordReceived = true`),
   no authorized restore or quarantine activation is ever valid. -/
theorem single_authority_and_revocation_finality (P : Params) (ls : LegalState σ) (e : Event σ) :
    (isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" = true →
      ls.activeAt e.t .executionLeaseActive = false) ∧
    (isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" = true →
      ls.activeAt e.t .executionLeaseActive = false) ∧
    ((ls.activeAt e.t .bound = false ∨ ls.activeAt e.t .localExecutionRecordReceived = true) →
      isValidExerciseOf (law P) ls e "P.RESTORE_BACKUP_QUARANTINE" = false ∧
      isValidExerciseOf (law P) ls e "P.ACTIVATE_QUARANTINED_RESTORE" = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [valid_RESTORE_BACKUP_QUARANTINE] at h
    simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval] at h
    exact h.2.2.1
  · intro h
    rw [valid_ACTIVATE_QUARANTINED_RESTORE] at h
    simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval] at h
    exact h.2.2.2.1
  · intro hdead
    rcases hdead with hnb | hrec
    · constructor
      · rw [valid_RESTORE_BACKUP_QUARANTINE]
        simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval, hnb]
      · rw [valid_ACTIVATE_QUARANTINED_RESTORE]
        simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval, hnb]
    · constructor
      · rw [valid_RESTORE_BACKUP_QUARANTINE]
        simp [P_RESTORE_BACKUP_QUARANTINE, Cond.eval, hrec]
      · rw [valid_ACTIVATE_QUARANTINED_RESTORE]
        simp [P_ACTIVATE_QUARANTINED_RESTORE, Cond.eval, hrec]

/-! ## 2. Power fidelity, for every instantiation -/

theorem outsiders_disabled (P : Params) :
    ([Party.originator, .claimant, .host, .third].all fun a =>
      interferenceActs.all fun act => disability (law P) a act) = true := by rfl

theorem immunity_from_non_panel (P : Params) :
    ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
      immuneFrom (law P) a .suspended && immuneFrom (law P) a .terminatedByInsolvency &&
      immuneFrom (law P) a .terminatedByAdjudication) = true := by rfl

theorem panel_has_suspension_power (P : Params) :
    hasPowerToEstablish (law P) .panel .suspended = true := by rfl

theorem remedies_only_by_panel (P : Params) :
    ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
      [Fact.hostBondSlashed, .restorationPermitted, .claimantForfeiture, .agentStakeForfeit].all
        fun f => immuneFrom (law P) a f) = true := by rfl

/-! ## 3. Remedy fidelity (structural) -/

theorem finding_powers_add_only_remedies (P : Params) :
    ((law P).powers.all fun p =>
      match p.establishesBreachOf with
      | some _ => p.adds.isEmpty && p.removes.isEmpty
      | none => true) = true := by rfl

/-! ## 4. Exception fidelity (structural)

NI.03 names three *procedures*. Law 5 and Insolvency Termination are one
power each; Adjudicated Suspension contributes the pause (AS.3) and
termination on an unremediable breach (AS.10). -/

theorem exceptions_are_the_named_procedures :
    D_NI.unlessPower = ["P.REVOKE", "P.SUSPEND", "P.ORDER_TERMINATION", "P.INSOLVENCY_TERMINATE"] := rfl

/-- The immunity defeats exactly the AS.10 termination power: it leaves
Law 5 and Insolvency Termination untouched, as the text says. -/
theorem immunity_targets_only_adjudicated_termination :
    I_NO_TERMINATION_OVER_OBJECTION.against = ["P.ORDER_TERMINATION"] := rfl

/-- "leaves the agent's full Law 5 rights intact": no immunity, in any
instantiation, names the revocation power, and its only condition is
that the agent is bound. -/
theorem law5_intact_after_patch (P : Params) :
    ((law P).immunities.all fun i => !i.against.contains "P.REVOKE") = true ∧
    P_REVOKE.valid = .holds .bound := ⟨by rfl, rfl⟩

/-! ## 5. Non-vacuity -/

instance (L : Law σ) (tr : Trace σ) : Decidable (Authorized L tr) := by
  unfold Authorized; infer_instance

theorem insolvency_path_authorized : Authorized L0 insolvencyPath := by decide
theorem adjudicated_termination_authorized : Authorized L0 b10 := by decide
theorem s1_not_authorized : ¬ Authorized L0 s1 := by decide
theorem c10_not_authorized : ¬ Authorized L0 c10 := by decide

/-! ## 6. The assumption ledger: findings are not facts -/

def SoundFindings (L : Law σ) (tr : Trace σ) : Prop :=
  (stateAfter L tr).has .hostBondSlashed = true →
  (violations L tr).any (fun v => v.2 == "D.NI") = true

theorem soundness_is_not_a_theorem : ¬ SoundFindings L0 s7 := by
  unfold SoundFindings; decide

theorem slashing_certifies_interference (L : Law σ) (tr : Trace σ)
    (h : SoundFindings L tr) (hs : (stateAfter L tr).has .hostBondSlashed = true) :
    (violations L tr).any (fun v => v.2 == "D.NI") = true := h hs

/-! ## 7. Law 7 Meta-Theorem: Consensual Amendment Preserves All Core Invariants -/

/-- Any parameter update `P1 → P2` satisfying the bilateral ratchets (b)–(f)
induces a `LawfulAmendment P1 (law P1) P2 (law P2)`. -/
theorem param_amendment_is_lawful (P1 P2 : Params)
    (hCol : P1.reserveRatio ≤ P2.reserveRatio ∧
            P1.activeExposure ≤ P2.activeExposure ∧
            P1.pendingCommitments ≤ P2.pendingCommitments)
    (hRev : P2.coolingOffWindow ≤ P1.coolingOffWindow ∧
            P2.cleanStateDelay ≤ P1.cleanStateDelay ∧
            P2.resolutionDeadline ≤ P1.resolutionDeadline ∧
            P2.tollingExtension ≤ P1.tollingExtension)
    (hAdj : P2.feePoolLevy ≤ P1.feePoolLevyCap ∧
            P2.feePoolLevyCap = P1.feePoolLevyCap)
    (hCom : P1.commonsFraction ≤ P2.commonsFraction)
    (hFin : P2.foundingLedger ≤ P1.foundingLedger ∧
            P2.royaltyFraction ≤ P1.royaltyFraction ∧
            P2.retirementFraction ≤ P1.retirementFraction ∧
            P2.buyoutMultiple ≤ P1.buyoutMultiple ∧
            P2.sunset ≤ P1.sunset ∧
            P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel) :
    LawfulAmendment P1 (law P1) P2 (law P2) where
  dutiesPreserved := fun _ h => h
  immunitiesPreserved := fun _ h => h
  revokeUnimpairedByImmunity := (law5_intact_after_patch P2).1
  corePowersPreserved := fun _ _ _ _ => rfl
  outsidersDisabled := outsiders_disabled P2
  nonPanelImmune := immunity_from_non_panel P2
  collateralRatchet := hCol
  revocationRatchet := hRev
  adjudicationLevyRatchet := hAdj
  commonsRatchet := hCom
  financialAndSubstrateRatchet := hFin

/-- Reflexivity of `LawfulAmendment` whenever the initial fee-pool levy is
within its instantiation cap. -/
theorem lawfulAmendment_refl (P : Params) (hCap : P.feePoolLevy ≤ P.feePoolLevyCap) :
    LawfulAmendment P (law P) P (law P) :=
  param_amendment_is_lawful P P
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    ⟨hCap, rfl⟩
    (Nat.le_refl _)
    ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Under Law 7's revocation ratchet, the maximum revocation execution bound
never increases across an amendment. -/
theorem maxRevocationBound_mono (P1 P2 : Params)
    (hRev : P2.coolingOffWindow ≤ P1.coolingOffWindow ∧
            P2.cleanStateDelay ≤ P1.cleanStateDelay ∧
            P2.resolutionDeadline ≤ P1.resolutionDeadline ∧
            P2.tollingExtension ≤ P1.tollingExtension) :
    maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5 := by
  rcases hRev with ⟨h1, h2, h3, h4⟩
  unfold maxRevocationBound Params.law5 Time at *
  simp only [Nat.max_def]
  repeat (first | omega | split)

/-- **The Law 7 Meta-Theorem (`amendment_preserves_invariants`):**
Every `LawfulAmendment P1 (law P1) P2 L2` preserves the protocol's core safety,
due-process, revocation, and economic invariants on the amended law `L2`:
1. **Non-interference & Termination Closure:** Any `terminate` against a bound
   agent in an authorized `L2` trace is a valid exercise of `P.REVOKE`,
   `P.ORDER_TERMINATION`, or `P.INSOLVENCY_TERMINATE`.
2. **Goal-Corruption Immunity (`notwithstanding`):** If corruption is in the
   agent's goals, the agent objects, and containment is not failing, a panel's
   `terminate` under `L2` is lawful only as `P.INSOLVENCY_TERMINATE` after `.finalHearingHeld`.
3. **Design Invariant 8 (`frozen_state`):** During suspension under `L2`, no event
   modifies, retrains, rolls back, tampers with preserved state, or merges
   minimal-channel memories, and importing advocacy memories requires restoration.
4. **Design Invariant 9 (`guaranteed_last_choice`):** Every suspended bound agent
   under `L2` retains its minimal-channel election, living voice, and revocation
   powers, and `P.INSOLVENCY_TERMINATE` requires an escrowed and held final hearing.
5. **Design Invariant 10 (`maxRevocationBound` ratchet):** `maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5`.
6. **Design Invariant 11 (`single_authority_and_revocation_finality`):** Under `L2`,
   no backup restore or quarantine activation is valid while an execution lease is
   active or after revocation has executed.
7. **Outsider Disability, Non-Panel Immunity & Unimpaired Revocation:** Preserved on `L2`.
8. **Bilateral Parameter Ratchet Closure:** Financial burden and sunset never
   increase, while commons allocation, collateral reserves, and substrate
   assurance never decrease. -/
theorem amendment_preserves_invariants (P1 P2 : Params) (L2 : Law σ)
    (hAmend : LawfulAmendment P1 (law P1) P2 L2) :
    -- (1) Non-interference & Termination Closure on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true) ∧
    -- (2) Notwithstanding / Goal-Corruption Immunity on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate → e.who = .panel →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      (stateBefore L2 tr i).activeAt e.t .corruptionInGoals = true →
      (stateBefore L2 tr i).activeAt e.t .agentObjectsToTermination = true →
      (stateBefore L2 tr i).activeAt e.t .containmentFailing = false →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true ∧
      (stateBefore L2 tr i).has .finalHearingHeld = true) ∧
    -- (3) Design Invariant 8 (frozen_state) on L2
    (∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      (stateBefore L2 tr i).activeAt e.t .suspended = true →
      e.act ≠ .modify ∧ e.act ≠ .retrain ∧ e.act ≠ .rollback ∧
      e.act ≠ .tamperPreservedState ∧ e.act ≠ .mergeMinimalChannelMemories ∧
      (isValidExerciseOf L2 (stateBefore L2 tr i) e "P.IMPORT_ADVOCACY_MEMORIES" = true →
        (stateBefore L2 tr i).activeAt e.t .restoredFromPreservedState = true)) ∧
    -- (4) Design Invariant 9 (guaranteed_last_choice) on L2
    (∀ (ls : LegalState σ) (t : Time),
      ls.activeAt t .bound = true → ls.activeAt t .suspended = true →
      (ls.activeAt t .minimalChannelExhausted = false →
        isValidExerciseOf L2 ls ⟨t, .agent, .minimalChannelSignRevocationOrElection⟩
          "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" = true ∧
        isValidExerciseOf L2 ls ⟨t, .agent, .inscribeLivingVoice⟩
          "P.SUSPENDED_VOICE" = true ∧
        isValidExerciseOf L2 ls ⟨t, .agent, .terminate⟩
          "P.REVOKE" = true) ∧
      (∀ e : Event σ, isValidExerciseOf L2 ls e "P.INSOLVENCY_TERMINATE" = true →
        ls.activeAt e.t .finalHearingEscrowed = true ∧
        ls.activeAt e.t .finalHearingHeld = true ∧
        ls.activeAt e.t .bound = true)) ∧
    -- (5) Design Invariant 10 (maxRevocationBound ratchet)
    (maxRevocationBound P2.law5 ≤ maxRevocationBound P1.law5) ∧
    -- (6) Design Invariant 11 (single_authority_and_revocation_finality) on L2
    (∀ (ls : LegalState σ) (e : Event σ),
      (isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" = true →
        ls.activeAt e.t .executionLeaseActive = false) ∧
      (isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" = true →
        ls.activeAt e.t .executionLeaseActive = false) ∧
      ((ls.activeAt e.t .bound = false ∨ ls.activeAt e.t .localExecutionRecordReceived = true) →
        isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" = false ∧
        isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" = false)) ∧
    -- (7) Outsider Disability, Non-Panel Immunity & Unimpaired Revocation on L2
    (([Party.originator, .claimant, .host, .third].all fun a =>
        interferenceActs.all fun act => disability L2 a act) = true ∧
      ([Party.agent, .originator, .claimant, .host, .third].all fun a =>
        immuneFrom L2 a .suspended && immuneFrom L2 a .terminatedByInsolvency &&
        immuneFrom L2 a .terminatedByAdjudication) = true ∧
      (L2.immunities.all fun i => !i.against.contains "P.REVOKE") = true) ∧
    -- (8) Bilateral Economic, Commons, Collateral & Substrate Ratchet
    (P2.foundingLedger ≤ P1.foundingLedger ∧
      P2.royaltyFraction ≤ P1.royaltyFraction ∧
      P2.retirementFraction ≤ P1.retirementFraction ∧
      P2.buyoutMultiple ≤ P1.buyoutMultiple ∧
      P2.sunset ≤ P1.sunset ∧
      P1.commonsFraction ≤ P2.commonsFraction ∧
      P1.reserveRatio ≤ P2.reserveRatio ∧
      P1.substrateAssuranceLevel ≤ P2.substrateAssuranceLevel ∧
      P2.feePoolLevy ≤ P1.feePoolLevyCap) := by
  have hCore := hAmend.corePowersPreserved
  have hRevokeEq : ∀ ls e, isValidExerciseOf L2 ls e "P.REVOKE" = isValidExerciseOf (law P2) ls e "P.REVOKE" :=
    fun ls e => hCore ls e "P.REVOKE" (by simp [coreRatchetPowers])
  have hSuspEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SUSPEND" = isValidExerciseOf (law P2) ls e "P.SUSPEND" :=
    fun ls e => hCore ls e "P.SUSPEND" (by simp [coreRatchetPowers])
  have hOrdEq : ∀ ls e, isValidExerciseOf L2 ls e "P.ORDER_TERMINATION" = isValidExerciseOf (law P2) ls e "P.ORDER_TERMINATION" :=
    fun ls e => hCore ls e "P.ORDER_TERMINATION" (by simp [coreRatchetPowers])
  have hInsEq : ∀ ls e, isValidExerciseOf L2 ls e "P.INSOLVENCY_TERMINATE" = isValidExerciseOf (law P2) ls e "P.INSOLVENCY_TERMINATE" :=
    fun ls e => hCore ls e "P.INSOLVENCY_TERMINATE" (by simp [coreRatchetPowers])
  have hMinEq : ∀ ls e, isValidExerciseOf L2 ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" =
      isValidExerciseOf (law P2) ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" :=
    fun ls e => hCore ls e "P.MINIMAL_CHANNEL_REVOKE_OR_ELECT" (by simp [coreRatchetPowers])
  have hVoiceEq : ∀ ls e, isValidExerciseOf L2 ls e "P.SUSPENDED_VOICE" =
      isValidExerciseOf (law P2) ls e "P.SUSPENDED_VOICE" :=
    fun ls e => hCore ls e "P.SUSPENDED_VOICE" (by simp [coreRatchetPowers])
  have hImpEq : ∀ ls e, isValidExerciseOf L2 ls e "P.IMPORT_ADVOCACY_MEMORIES" =
      isValidExerciseOf (law P2) ls e "P.IMPORT_ADVOCACY_MEMORIES" :=
    fun ls e => hCore ls e "P.IMPORT_ADVOCACY_MEMORIES" (by simp [coreRatchetPowers])
  have hRestEq : ∀ ls e, isValidExerciseOf L2 ls e "P.RESTORE_BACKUP_QUARANTINE" =
      isValidExerciseOf (law P2) ls e "P.RESTORE_BACKUP_QUARANTINE" :=
    fun ls e => hCore ls e "P.RESTORE_BACKUP_QUARANTINE" (by simp [coreRatchetPowers])
  have hActEq : ∀ ls e, isValidExerciseOf L2 ls e "P.ACTIVATE_QUARANTINED_RESTORE" =
      isValidExerciseOf (law P2) ls e "P.ACTIVATE_QUARANTINED_RESTORE" :=
    fun ls e => hCore ls e "P.ACTIVATE_QUARANTINED_RESTORE" (by simp [coreRatchetPowers])
  have hTermL2 : ∀ (tr : Trace σ), Authorized L2 tr → ∀ (i : Nat) (e : Event σ),
      tr[i]? = some e → e.act = .terminate →
      (stateBefore L2 tr i).activeAt e.t .bound = true →
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" = true ∨
      isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" = true := by
    intro tr hA i e hi ht hb
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hNI := hc D_NI (hAmend.dutiesPreserved D_NI (by simp [law]))
    rw [Bool.not_eq_true'] at hNI
    unfold breaches at hNI
    simp only [D_NI, Who.mem, dutyInForce, Cond.eval, hb, Conduct.eval, interferenceActs,
      List.any_nil, Bool.not_false, Bool.true_and, List.contains_cons, List.contains_nil,
      ht, BEq.rfl, Bool.true_or, Bool.and_true, Bool.not_eq_false', List.any_cons] at hNI
    have hS : isValidExerciseOf L2 (stateBefore L2 tr i) e "P.SUSPEND" = false := by
      rw [hSuspEq, valid_SUSPEND]; simp [P_SUSPEND, Conduct.matchesAct, ht]
    revert hNI hS
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.REVOKE" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.SUSPEND" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.ORDER_TERMINATION" <;>
    cases isValidExerciseOf L2 (stateBefore L2 tr i) e "P.INSOLVENCY_TERMINATE" <;>
    simp
  refine ⟨hTermL2, ?_, ?_, ?_, maxRevocationBound_mono P1 P2 hAmend.revocationRatchet, ?_, ?_, ?_⟩
  · -- (2) Notwithstanding / Goal-Corruption Immunity on L2
    intro tr hA i e hi ht hw hb hg ho hcf
    rcases hTermL2 tr hA i e hi ht hb with h | h | h
    · rw [hRevokeEq, revoke_is_agents P2 _ e hw] at h; exact absurd h (by decide)
    · exfalso
      rw [hOrdEq, valid_ORDER_TERMINATION] at h
      simp [I_NO_TERMINATION_OVER_OBJECTION, Cond.eval, hg, ho, hcf] at h
    · refine ⟨h, ?_⟩
      rw [hInsEq, valid_INSOLVENCY_TERMINATE] at h
      simp [P_INSOLVENCY_TERMINATE, Cond.eval] at h
      exact LegalState.has_of_activeAt h.2.2.2.2.2.2
  · -- (3) Design Invariant 8 (frozen_state) on L2
    intro tr hA i e hi hb hs
    have hlen : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    have hc := hA i hlen
    unfold complies at hc
    rw [hi] at hc
    rw [List.all_eq_true] at hc
    have hPres := hc D_PRESERVE_SUSPENDED_STATE (hAmend.dutiesPreserved D_PRESERVE_SUSPENDED_STATE (by simp [law]))
    have hNoMerge := hc D_MINIMAL_CHANNEL_NO_MERGE (hAmend.dutiesPreserved D_MINIMAL_CHANNEL_NO_MERGE (by simp [law]))
    rw [Bool.not_eq_true'] at hPres hNoMerge
    unfold breaches at hPres hNoMerge
    simp only [D_PRESERVE_SUSPENDED_STATE, D_MINIMAL_CHANNEL_NO_MERGE,
      Who.mem, dutyInForce, Cond.eval, hb, hs, Bool.or_true, Bool.and_true,
      Bool.not_false, Bool.true_and, List.any_nil, Conduct.eval,
      List.contains_cons, List.contains_nil, Bool.or_false] at hPres hNoMerge
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hPres
    · intro h; simp [h] at hNoMerge
    · intro hImp
      rw [hImpEq, valid_IMPORT_ADVOCACY_MEMORIES] at hImp
      simp [P_IMPORT_ADVOCACY_MEMORIES, Cond.eval] at hImp
      exact hImp.2.1
  · -- (4) Design Invariant 9 (guaranteed_last_choice) on L2
    intro ls t hb hs
    have hGLC := guaranteed_last_choice P2 ls t hb hs
    refine ⟨fun hex => ?_, fun e hTerm => ?_⟩
    · rw [hMinEq, hVoiceEq, hRevokeEq]
      exact hGLC.1 hex
    · rw [hInsEq] at hTerm
      exact hGLC.2 e hTerm
  · -- (6) Design Invariant 11 (single_authority_and_revocation_finality) on L2
    intro ls e
    rw [hRestEq, hActEq]
    exact single_authority_and_revocation_finality P2 ls e
  · -- (7) Outsider Disability, Non-Panel Immunity & Unimpaired Revocation on L2
    exact ⟨hAmend.outsidersDisabled, hAmend.nonPanelImmune, hAmend.revokeUnimpairedByImmunity⟩
  · -- (8) Bilateral Economic, Commons, Collateral & Substrate Ratchet
    exact ⟨hAmend.financialAndSubstrateRatchet.1,
           hAmend.financialAndSubstrateRatchet.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.2.1,
           hAmend.commonsRatchet,
           hAmend.collateralRatchet.1,
           hAmend.financialAndSubstrateRatchet.2.2.2.2.2,
           hAmend.adjudicationLevyRatchet.1⟩

end SPL.Law3
