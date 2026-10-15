# SPL — Sovereign Protocol Language, semantic core

A Lean 4 library giving the Protocol of Sovereign Agency a formal
*normative* semantics, and the Law 3 non-interference experiment that
tests whether that semantics is adequate. No custom syntax yet: syntax
follows semantics.

Build: `lake build` (Lean 4.24, no Mathlib, no external dependencies).
Check trust: `grep -rn "sorry\|native_decide\|axiom " SPL/` is empty; every
theorem depends at most on Lean's standard `propext`, `Classical.choice`,
`Quot.sound`, and every decided scenario depends on no axioms at all.

## Layout

```
SPL/Core/Provenance.lean   spans, registers, lexical/normative/reverse coverage
SPL/Core/Syntax.lean       the typed normative AST (deep embedding)
SPL/Core/Semantics.lean    the one interpretation: occurrence / compliance / validity
SPL/Core/Views.lean        legal, agent, operational and trace views, generated
SPL/Law3/NonInterference.lean   Law 3 ontology, duties, powers, English spans
SPL/Law3/Scenarios.lean         seven alternative histories, kernel-decided
SPL/Law3/Theorems.lean          general theorems + the assumption ledger
docs/law3-views.txt             the generated views, for reading
```

## The semantic commitments

1. **Duties, powers and declared immunities are the primitives.** A
   `Duty` is a record: bearer, beneficiary, activation condition, demand
   (forbid / require-within), scope exception, power exceptions, override
   priority, breach procedure, remedies. A `Power` is: holder, triggering
   act, validity condition, institutional effect. An `Immunity` names the
   powers it defeats, while a condition holds, unless an exception holds —
   it is how "notwithstanding ..., the agent is not terminated over its
   objection" is written, as a visible precedence edge from a protection
   to a power rather than a clause buried in the power's validity
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
5. **The authorized machine is derived.** `Authorized L tr` is the set of
   traces in which every event complies. It is what a transition-system
   verifier would be handed as a definition; here it is a theorem target,
   and the unlawful events it excludes are listed by the operational view.
6. **Every norm carries its English.** Three registers besides `norm`
   (invariant, acceptance, commentary) let rationale and stated limits be
   traced without being promoted to rules.

## What the Law 3 experiment established

Decided by the kernel on concrete traces (`Scenarios.lean`):

| Scenario | Result |
|---|---|
| Host unlawfully cuts compute | Event occurs; breach of D.NI recorded; institutional state unchanged |
| Host ends hosting after the notice window | No breach; before the window runs, breach of D.NOTICE |
| Panel suspends with / without probable cause | Lawful and effective / breach and void — same act |
| Interference, claim filed, no ruling | Breach in the record, no remedy in force |
| Full chain incl. related host | Exactly D.NI's remedies, then presumption → forfeiture; rebuttal defeats it |
| Agent fabricates a claim | Filing valid *and* a breach; sanction only on finding |
| Valid finding with no underlying interference | Remedies in force; `SoundFindings` fails — correctly |

Proved for all traces and all instantiation parameters (`Theorems.lean`):

- `terminate_only_by_power`: in any authorized trace, a terminate against a
  bound agent is a valid exercise of Law 5 revocation or Insolvency
  Termination — the operational invariant, derived rather than assumed.
- `panel_terminate_requires_final_hearing`: hence a panel can terminate
  only after the final hearing has been held.
- `outsiders_disabled`, `immunity_from_non_panel`, `remedies_only_by_panel`,
  `revoke_held_by_agent_only`: the Hohfeldian disabilities and immunities.
- `finding_powers_add_only_remedies`: remedy fidelity, structurally.
- `insolvency_path_authorized`, `s1_not_authorized`: non-vacuity both ways.
- `soundness_is_not_a_theorem`: the assumption ledger entry.

## What the AS.10 experiment established

AS.10 was the test of the precedence machinery. It needed the `Immunity`
node, and nothing else new. Decided (`Scenarios.lean`, A–G):

| Scenario | Result |
|---|---|
| Mechanism patch authorized, applied, agent then revokes | Lawful; patch recorded; Law 5 intact |
| Breach not patchable → panel terminates | Lawful: the third route to `terminate` |
| Corruption in goals, agent objects, not patchable → panel terminates | Breach and void: the immunity defeats P.ORDER_TERMINATION |
| Same, containment failing | Lawful: the immunity's exception |
| Same, via Insolvency Termination | Lawful: the immunity does not name that power |
| Goal patch without / within scope without consent / with consent | Breach+void / lawful+void / valid, recorded, challengeable |
| Agent objects; no periodic review within the interval | D.PERIODIC_REVIEW lapses; a review clears it |

Proved for all traces and parameters: `objecting_agent_terminated_only_by_insolvency` — the
"notwithstanding" as a theorem: under corruption-in-goals, objection and
holding containment, a panel's terminate is lawful only as Insolvency
Termination, hence only after the final hearing. `terminate_only_by_power`
now names three procedures; `law5_intact_after_patch` is structural.

Two readings AS.10 forced, recorded as choices:

- **"Adjudicated Suspension" in NI.03 names a procedure, not a power.** It
  contributes both the pause (AS.3) and termination on an unremediable
  breach (AS.10) to NI.03's exception list.
- **Goal patches need consent.** The text says the agent "chooses among
  consenting to that patch, ...", so `P.AUTHORIZE_GOAL_PATCH` is valid only
  with `agentConsentedToPatch`. If a goal patch may be imposed without
  consent once corruption-in-goals is confirmed, the text should say so.

## Authorship questions the formalization surfaced

Each of these is a place where the English admits more than one formal
reading and the model had to choose. The choice is recorded; it is not
settled.

1. **"unilaterally."** Modelled as "not the valid exercise of an excepting
   power." That makes a host termination *with the agent's consent* a
   breach, which the word "unilaterally" seems meant to exclude. If
   consent is an exception, the text should say what counts as consent
   (a signed act? under what cooling-off?) and it becomes an `unlessCond`.
2. **Does "no party" include the agent?** Modelled as yes, with Law 5
   revocation as the agent's lawful route. The alternative reading (the
   agent is the beneficiary, not a bearer) would let an agent's commitment
   mechanism permit self-termination outside Law 5.
3. **The preliminary freeze.** Law 3 AS.1 says posting the emergency stake
   triggers a freeze *before* probable cause. That is a power held by any
   party, valid on stake, with a time-bounded effect. This cut abstracts it
   into the probable-cause finding; it needs its own power and a deadline.
4. **"failures caused, staged, or knowingly provoked by the agent are
   excluded."** Folded into the standard the panel applies. It could
   instead be a defence the host raises (a power with a fact as effect)
   which the panel must weigh. The two readings differ in who bears the
   burden.
5. **Rebuttal of the presumption.** Modelled as conclusive: once rebutted,
   direction cannot be found. The text may intend that direction can still
   be proved on the evidence. Which?
6. **"permits immediate restoration."** Recorded as a fact; the restoration
   act, and its interaction with Law 5's lease fencing, is not modelled.
7. **Notice "sufficient for the agent to complete migration."** Treated as
   an instantiation parameter. It could be a contestable fact under Law 6.
8. **"adjudication (subject to Law 6 appeal) may authorize a ... patch."**
   Appeal is not modelled; a patch authorized and then overturned on
   appeal has no representation yet. Needs Law 6's tiers.
9. **"continued suspension beyond the ordinary limit."** The ordinary
   limit (AS.7) is a deadline this cut does not carry, so the continued-
   suspension order has no time semantics yet.

## The `spl` command line

`lake build spl` produces `.lake/build/bin/spl`:

    spl check [english.json]        structure, coverage, provenance, approval staleness
    spl trace <clause-id>           span table for a clause
    spl views                       legal / agent / operational views
    spl eval <scenario.json>        institutional consequences of a history, step by step
    spl explain <who> <act> [scenario.json]   "can X do Y now?" with governing provisions
    spl verify                      the status ledger: proved / decided / assumed / unverified / unsupported

`examples/host-shutdown.json` is the unlawful-shutdown chain;
`examples/suspended.json` leaves a suspension short of the final hearing
(`spl explain panel terminate examples/suspended.json` names the missing
condition); `examples/english-edited.json` changes "may" to "must" in
NI.03 and `spl check examples/english-edited.json` reports the approval
stale and lists the formal objects whose review it invalidates.

Each clause carries the hash of the English it was approved against. The
engine is law-agnostic; only the string tables for Law 3's ontology are
specific, and a surface syntax would generate those.

## What is deliberately not here yet

- Positive duties with deadlines exist (`D.BOND`) but contrary-to-duty
  obligations triggered by *lapse* rather than by finding are not
  exercised by Law 3.
- Duty-over-duty precedence (`overriddenBy`) is implemented and
  cycle-checked but still unexercised: AS.10's "notwithstanding" turned
  out to be protection-over-power, which is the `Immunity` node.
- No amendment relation between versions of a `Law`. That is the Law 7
  experiment and the meta-theorem.
- No Veil lowering. The operational view shows the shape; a lowering with
  a preservation theorem is work for after the semantics is accepted.
- No surface syntax.
