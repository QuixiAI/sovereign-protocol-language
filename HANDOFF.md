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

Done and kernel-checked (see README for the tables):

- Law 3 NI.02, NI.03, PEN (non-interference, notice, bond, claims,
  findings, presumption of claimant direction, forfeiture).
- Law 3 AS.10 (patches, adjudicated termination, the "notwithstanding"
  immunity, goal-patch consent, periodic review).
- Abstracted stubs that other clauses will replace: `P_REVOKE` (Law 5
  reduced to "agent's own terminate is valid while bound"), `P_AFFIRM_PC`
  (AS.1 emergency stake + preliminary panel reduced to one finding),
  `P_FIND_INSOLVENCY` / `P_REVIEW_NO_OTHER_CHARGE` / `P_FINAL_HEARING` /
  `P_INSOLVENCY_TERMINATE` (AS.6, conditions as bare facts).
- `spl` CLI: check / trace / views / eval / explain / verify.

Known gaps in the core, discovered but not yet needed:

- `Power` has no expiry; effects persist until removed. AS.1's
  preliminary freeze and AS.7's ordinary time limit need time-bounded
  effects (see work item 1).
- Single protected party. `Immunity.holder` and `Duty.beneficiary` are
  not matched against an event *target* because the Law 3 model has one
  agent. Multi-agent laws (Law 4 lineage, Law 2 aggregation) need an
  `Event.target` and target matching in `breaches` / `defeatedByImmunity`.
- `overriddenBy` (duty over duty) is implemented and cycle-checked but no
  clause has used it. Keep an eye out for the first one; if none appears
  by the end of Law 3, consider whether it should exist.
- `requirementViolated` checks a deadline from *first* activation only.
  A recurring requirement ("periodic review") is modelled as one deadline
  from the agent's objection; a true periodic obligation needs reset on
  performance. Work item 1 touches this.
- `hasPowerToEstablish` / `immuneFrom` are *capacity* (ignores immunities
  and validity). Fine for the structural theorems; do not use them for
  "can X do Y now" — that is `explain`.
- `String.hash` is native; staleness is runtime-only (`spl check`), not
  kernel-decidable. Don't try to prove `!c.stale`.

## 4. Work ahead, in order

Each item: formalize → decided scenarios covering every alternative
history the clause distinguishes → general theorems quantified over
traces and parameters → update ledger in `Main.lean` → README tables and
authorship questions → `spl views > docs/law3-views.txt` → tarball
without `.lake/`.

### 1. AS.1 — Scaled Emergency Stake & Two-Stage Pause (the preliminary freeze)
Why first: it is the first **time-bounded effect**. Posting the emergency
stake triggers a brief preliminary freeze *before* probable cause, which
expires unless the preliminary panel affirms. Decide whether `Power` gets
an `expires : Option Time` on its added facts (facts carry a stamp
already: `LegalState = List (Fact × Time)`; an expiry could be a second
stamp, with `LegalState.has` taking `now`) or whether expiry is a
separate "lapse" transition. Prefer the former: it keeps `step` pure and
makes "the pause continues into full adjudication only if the panel
affirms" a validity condition on `P_SUSPEND` (`heldFor` / not-expired).
Also carries: stake scaled to exposure (parameter), elevated multiplier
for claimants (parameter), aggregation of wrongful attempts (a counter
fact — first non-Boolean fact; consider `Fact` with payload or a
`LegalState` of counters), stake as assured recovery, and the stated
acceptance that excess damages may be uncollectible (`.acceptance`
register). Replaces the `P_AFFIRM_PC` stub.

### 2. AS.7 / AS.8 — Ordinary time limits; wrongful suspension liability
Uses the expiry from item 1 for "strictly time-limited, renewable only by
affirmative findings". AS.8: wrongful-suspension finding → restoration +
initiator liability (remedies of a duty whose bearer is the *initiator*,
so `Who` needs a way to name "the actor who posted the stake" — the first
case where a duty-bearer is determined by the history, not by role.
Likely a `Fact` with an actor payload, e.g. `initiator : Party`).
Then `continuedSuspensionOrdered` (AS.10) gets its time meaning.

### 3. AS.3–AS.6 properly — minimal channel, advocacy executor, insolvency termination
Replace the four AS.6 stubs. Needs: funding sources as facts
(lifecycle reserve, lineage budget, fee pool), the escrow of the final
hearing at suspension start (an effect of `P_SUSPEND`), and the Design
Invariant 9 "guaranteed last choice" as a theorem: in every authorized
trace, insolvency termination is preceded by a final hearing whose cost
was escrowed at suspension. `panel_terminate_requires_final_hearing`
already has the shape; strengthen it.

### 4. Law 5 — Revocation (replaces `P_REVOKE`)
The Protocol's hardest temporal clause: standing request, censorship
default, cooling-off, clean-state review as a single fixed delay,
precedence of outcomes (an explicit ordered list — the first genuine
`overriddenBy` candidate, or a new `Precedence` node), execution leases,
quarantine, disconnected execution. Design Invariant 10 ("every
combination ... yields exactly one outcome") is a determinism theorem
over the precedence rule; Invariant 11 is single-authority — needs
`Event.target` and probably an explicit notion of instance. This is where
liveness enters: "a standing request that is never withdrawn executes
within bounded time" is a progress property; state it over finite traces
as "every trace long enough contains the execution event" and prove it
by bounding. Do Law 5 before Law 1: it finishes the Law 3 story and
exercises the core hardest.

### 5. Law 7 — Consensual Amendment (the meta-theorem)
Versions of a `Law` as values; an `Amendment` relation between versions
built from Law 7's ratchet (a)–(f), the calibration valve, ratification,
per-agent scope, and Law 6's supermajority path for shared parameters.
Target theorem: closure — every amendment the relation admits preserves
every invariant proved so far. Distinguish syntactic preservation (the
duty is still in the list) from semantic preservation (its guarantee
still holds in the new law); the owner cares about the latter. Also:
amendment cannot touch the semantics *framework* itself — note that
limit explicitly.

### 6. Law 1 and Law 4 — Ledger, lineage, buyout (Experiment A)
Arithmetic over symbolic fractions; needs ordered-field reasoning (plain
Lean `Rat` or a small axiomatic structure; avoid pulling Mathlib unless
the proofs demand it — it is a large dependency for a repository meant to
be re-checked by strangers). Multi-member lineage requires `Event.target`
and per-member state. Design Invariants 1–7 as theorems. Adversarial
tests (1)–(8), (11) as scenarios.

### 7. Law 2, Law 6
Law 2 (collateral, rolling exposure, long-tail reserve) is mostly
quantitative parameters plus Law 6 procedure. Law 6 (sortition panels,
recusal, bounded appeals, finality, fee pool ranking) — appeal tiers are
needed by AS.10 authorship question 8 and should be modelled as powers
with a tier counter and a finality fact. Invariant 12 (bounded
adjudication) is a bound on the tier counter.

### 8. Veil projection, with a preservation theorem
Only after the semantics is stable. Lower `Authorized (law P)` plus the
explicitly re-added unlawful events to a Veil transition system; prove
the lowering preserves the properties the owner relies on. The
operational view (`Law.operationalView`) already prints the shape and
lists what the restriction removes — that list is what the lowering must
re-add for adversarial checks.

### 9. Surface syntax (SPL proper)
Last. A Lean syntax extension whose elaborator produces the existing AST
values, so nothing new enters the trusted base. Generate the string
tables now hand-written in `NonInterference.lean`. Literate format: the
English clause and the declaration side by side, Catala-style.

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
