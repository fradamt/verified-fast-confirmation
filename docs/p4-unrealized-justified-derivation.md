# P-4 — deriving `JustificationInterface.unrealized_justified` at the spec layer

> **OUTCOME: RESOLVED-BY-DELETION.** The field had **zero** projection sites left in the
> development, so it is deleted outright (`JustificationInterface` 13 → **12** fields) rather
> than derived. §5 records what landed. §§1-4 are the analysis that establishes both halves of
> the finding: that the field is dead (§1), and that the intended derivation would *not* have
> reproduced it as stated anyway (§3).

**Snapshot:** branch `centaur/weak-synchrony-202609150824`, working tree at 2026-09-17
(`git pull --ff-only` → already up to date at `0aade51`).
**Baseline before any edit:** `bash scripts/check_build.sh` green; `lake env lean
scripts/Audit.lean` → *project trust audit passed: 9963 declarations, 6222 theorems, 26
generated partials, 21 public witnesses*, sorry-free, axioms `[propext, Classical.choice,
Quot.sound]`.
**Pinned spec:** consensus-specs `30aa65fc21cf7f7c7dd1f7d6b686d0250462d04f`;
`fast-confirmation.md` / `fork-choice.md` line numbers as in `docs/plumbing-spec-citations.md`.

The flag under study is `docs/plumbing-spec-citations.md` §13 **P-4** (row 7 of §2), against
`FastConfirmation/Spec/TheoremStatements.lean:196-202` (pre-deletion):

```lean
  unrealized_justified : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg n → E.WithinHorizon cfg m →
    E.slot_at cfg n ≤ E.slot_at cfg m →
      JustifiedIn (E.store cfg ext w m)
        (E.store cfg ext v n).unrealized_justified_checkpoint ∧
      JustifiedIn (E.store cfg ext w m)
        ((E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint)
```

The owner's ruling is that this should be **derived**, not assumed, because the model's synchrony
already contains honest relay: `PaperSafetySynchrony.block_relay`
(`FastConfirmation/Spec/Model/Assumptions.lean:209-216`) relays any block root in an honest store
to every honest store, regardless of the block's producer, and the accepted FFG semantic
contracts then recompute the unrealized justification at the receiving store.

This document asks, adversarially, **who consumes it** (§1), **what `JustifiedIn` actually
demands** (§2), **whether the derivation closes** (§3), and **what the two conjuncts cost
separately** (§4).

---

## 0. Headline

1. **There are no consumers.** A repo-wide projection scan and a forward-closure computation
   over the compiled environment both return **zero** declarations mentioning
   `JustificationInterface.unrealized_justified` — not reachable ones, *zero mentions anywhere*.
   Its last and only consumer, `FinalWiring.prev_greatest_of_interface`, was deleted in the P-6
   orphan sweep (`096e51b`). §1.
2. The field therefore survived only as **unprojected weight on the premise surface** of the four
   weak headlines W20–W23, which carry `hji : JustificationInterface` as a binder. Deleting it is
   a strict premise weakening and changes no statement. §1.3.
3. The intended derivation is **most of the way there**: three of its four steps are already
   in-tree and load-bearing elsewhere. The origins record supplies the witnessing block, block
   relay carries it, and `accepted_unrealized_justification_eq` recomputes `GU` at the receiver,
   landing `JustifiedIn`'s fifth disjunct. The anchor disjunct closes too, via
   `genesis_unrealized_justification` + `get_forkchoice_store`'s literal
   `unrealized_justifications = {anchor_root: justified_checkpoint}`. §3.1-§3.3.
4. **But it does not reproduce the field as stated.** `block_relay` has a `+1`-slot gate
   (`slot_at n + 1 ≤ slot_at (m + 1)`); the field concluded from `slot_at n ≤ slot_at m`. The
   **same-slot cross-node corner** — `v` and `w` read in the same slot, `m` not the last second
   of that slot — is outside the block-relay guarantee. This limit is already recorded in-tree,
   for the structurally identical confirmed-block case, at `Proof/FinalWiring.lean:16-18`. §3.4.
5. So even on the "derive it" branch the honest outcome would have been a *weakened* field, not
   the field. Since nothing consumes either version, deletion dominates: it removes the whole
   proposition instead of narrowing it. §5.

---

## 1. Who consumes the field

### 1.1 Textual scan

`JustificationInterface` is **never constructed** in the repository: `rg` for
`JustificationInterface :=` / `.mk` finds only five `have hji : JustificationInterface cfg ext E
:= hSA.2.2.2.2.2.2.2.2` destructurings of `SpecAssumptions`
(`Proof/AnchorClose.lean:687`, `Proof/SameSlotProvenance.lean:808,861`,
`Proof/Knownness.lean:242`, `Proof/InterfaceRewire.lean:172`), all of which *select* the record,
none of which build one. So a field can only be load-bearing through a projection site.

A repo-wide `rg` for `unrealized_justified` not followed by `_checkpoint` /
`_justifications` / `_le_unrealized_justified` returns 30 hits, all of which are one of:

* the field's own declaration (`Spec/TheoremStatements.lean:196`);
* the **homonymous** field of the four store-global origins records —
  `FFGGlobalCheckpointOrigins.unrealized_justified`
  (`Proof/FFGGlobalCheckpointTrajectory.lean:57`) and
  `AcceptedFFGGlobalCheckpointOrigins.unrealized_justified`
  (`Proof/AcceptedFFGGlobalCheckpointTrajectory.lean:96`), projected at
  `FFGGlobalCheckpointTrajectory.lean:128,177,223,344,1516`,
  `AcceptedFFGGlobalCheckpointTrajectory.lean:124,177,225,347`,
  `CurrentTargetCertificateRealization.lean:596`,
  `NoConflictCertificatePinning.lean:709`, `AcceptedResetCheckpointRealization.lean:267`,
  `ActualResetCheckpointRealization.lean:286`,
  `AcceptedActualSelectedJustifiedOrientation.lean:63`,
  `AcceptedCandidateHistoryRecurrence.lean:553,581`, `WeakBankedJustification.lean:241`;
* `FFGCheckpointEpochOrder.unrealized_finalized_le_unrealized_justified`;
* `Identities.update_checkpoints_unrealized_justified`, the executable-rewrite lemma;
* the boolean `is_head_unrealized_justified_ok` of `get_latest_confirmed`
  (`Model/Confirmation.lean:221,226,254,261`, `Model/WeakSynchrony.lean:562,569`);
* prose in docstrings (`Proof/FinalWiring.lean:7,30`, `Proof/WeakBankedJustification.lean:234`,
  `Proof/NoConflictCertificatePinning.lean:183`, `Proof/WeakHistoricalA32CallSupplier.lean:491`).

**Exactly the same name-collision shape P-6 §1.3 found for `justified_descends`.** No site
projects the interface field.

### 1.2 Environment scan — the decisive check

The textual scan cannot see through `simpa`/`exact?`-generated terms, so it was repeated over the
**compiled environment**, by the §7.1 method of `docs/p6-justified-descends-derivation.md`: for
each of the 13 projections of `FastConfirmation.Spec.JustificationInterface`, scan every project
declaration's **type and proof term** (`ConstantInfo.value? (allowOpaque := true)` — note that
`value?` returns `none` for theorems unless `allowOpaque` is set, which silently zeroes the whole
computation otherwise), and intersect with the forward closure of the 21 `scripts/Audit.lean`
`publicWitnesses`. Throwaway script, not committed.

Closure size: **18728** constants, **5179** of them from `FastConfirmation.*` modules.

| field | project decls mentioning it | reachable from the 21 witnesses |
|---|---|---|
| `checkpoint_known` | 16 | **1** — `Execution.head_root_known` |
| `justified_ancestry` | 4 | 0 |
| `justified_cached` | 3 | 0 |
| `observed_checkpoint_known` | 3 | 0 |
| `finalized_justified_ancestry` | 2 | 0 |
| `justified_unique` | 1 | 0 |
| `observed_justified` | 1 | 0 |
| `finalized_descent` | 1 | 0 |
| `justified_block_boundary` | 1 | 0 |
| `observed_justified_cached` | 0 | 0 |
| `justified_requires_targets` | 0 | 0 |
| `greatest_unrealized_cached` | 0 | 0 |
| **`unrealized_justified`** | **0** | **0** |

The `checkpoint_known` row is the control that makes the pass decisive: the method still finds
the one field the audited witnesses genuinely project, and the one declaration
(`Execution.head_root_known`) through which they project it — reproducing
`p6-justified-descends-derivation.md` §7.1's control exactly. Against that control,
`unrealized_justified` is not merely unreachable: **no declaration in the project mentions it at
all.**

### 1.3 Where the consumer went

The one historical projection site was

```lean
/-! ## Section 1 — `prev_greatest` from `unrealized_justified` -/
```

`FinalWiring.prev_greatest_of_interface` (`Proof/FinalWiring.lean`), which turned the field into
one of the three E5 reset-anchor legs of the conditional `Spec_Safety` input records. It is
named in that module's own deletion note (`Proof/FinalWiring.lean:9-13`) as one of the six of
seven declarations that "went with them in the orphan sweep" — Wave B of the P-6 retirement,
commit `096e51b`, `refactor: garbage-collect the observed-anchor cone's orphans`. The section
header quoted above survived the sweep as stale prose; it is the only thing in the tree that
still pointed at the field.

So the field's status since `096e51b` has been: carried as one of 13 conjuncts of `hji` on the
premise surface of the four weak headline witnesses W20–W23
(`Proof/WeakTrajectorySafety.lean:424,506,613,654,686`;
`Proof/WeakObservedResetSeedSafety.lean`), and never projected by anything.

---

## 2. What `JustifiedIn` actually requires — the boundary subtlety

`JustifiedIn` (`Spec/TheoremStatements.lean:51-56`) is a five-way disjunction, and it is
**deliberately realized-and-unrealized**:

```lean
def JustifiedIn (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = store.justified_checkpoint ∨
  c = store.unrealized_justified_checkpoint ∨
  c = store.finalized_checkpoint ∨
  c = store.unrealized_finalized_checkpoint ∨
  ∃ r ∈ store.block_roots, store.unrealized_justifications r = c
```

Three consequences for the derivation:

1. **No realized-vs-unrealized mismatch.** The conclusion the deleted field asserted is not
   "`c` is `w`'s realized justified checkpoint"; disjuncts 2, 4 and 5 are all unrealized. So the
   worry that the premise is unrealized-shaped while the conclusion is realized-shaped does not
   arise — `JustifiedIn` is the weaker, union-shaped predicate on purpose.
2. **Disjunct 5 is the derivation's landing site**, and it is the only one that is reachable by
   relay: the first four pin `c` to one of `w`'s own four checkpoint fields, which is a fact
   about `w`'s epoch processing, not about what `w` has received. Disjunct 5 asks only that `w`
   knows *some* block whose unrealized justification is `c`. That is exactly what block relay
   plus a store-independent `GU` selector can deliver.
3. **The consumers that existed needed only `JustifiedIn`**, i.e. the disjunction —
   `prev_greatest_of_interface` fed it into the E5 reset legs, which consume `JustifiedIn`
   uniformly. No consumer ever needed a specific disjunct. (This is moot now, but it means the
   disjunct-5 route would have been adequate had a consumer survived.)

---

## 3. Does the derivation close?

Target, conjunct 1: honest `v`, in-horizon `n`; honest `w`, in-horizon `m`;
`slot_at n ≤ slot_at m` ⟹ `JustifiedIn (store w m) (store v n).unrealized_justified_checkpoint`.

Available on W20–W23 alongside `hji`: `B : ExactPrefixAcceptedFFGSemantics`,
`hanchor : B.anchor = E.genesis_store.justified_checkpoint`,
`hboundary : TrustedAnchorBoundaryAligned`, `hW.base.synchrony : PaperSafetySynchrony`,
`hT : ScheduledPrefixTrajectoryAssumptions` (derived from `hW.base`) — verified at
`Proof/WeakTrajectorySafety.lean:613-631, 654-671, 686-700`. **No new premise would be needed.**

### 3.1 Step 1 — the witnessing block. Available.

`AcceptedFFGGlobalCheckpointOrigins` (`Proof/AcceptedFFGGlobalCheckpointTrajectory.lean:91-101`)
carries, for each store,

```lean
  unrealized_justified : AcceptedGlobalUnrealizedJustifiedOrigin S store
    store.unrealized_justified_checkpoint
```

and (`:71-74`)

```lean
def AcceptedGlobalUnrealizedJustifiedOrigin
    (S : AcceptedChainFFGState cfg ext E anchor) (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = anchor ∨ ∃ r, E.AcceptedCarrierIn (cfg := cfg) (ext := ext) store r ∧ c = S.GU r
```

with `AcceptedCarrierIn store r` unfolding (`:35-38`) to `r ∈ store.block_roots ∧ ∃ b,
E.AcceptedBlockAt cfg ext r b`. So the checkpoint `v` holds is either the trusted anchor or
`S.GU r` for a block `r` **known in `v`'s store** — precisely the link the owner's step (1)
describes, and precisely the machinery
`AcceptedCurrentTargetLowerContracts.justifiedRootKnown_of_acceptedGlobalTrajectory`
(`Proof/AcceptedCurrentTargetLowerContracts.lean:36-106`) uses for the realized twin. Note `S.GU`
is **store-independent** — it is a selector on `B.state`, chosen before the store quantifier
(`AcceptedFFGGlobalCheckpointTrajectory.lean:6-8`).

### 3.2 Step 2 — relay. Available, with a gate (see §3.4).

`PaperSafetySynchrony.block_relay` (`Model/Assumptions.lean:209-216`):

```lean
  block_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n → r ∈ (E.store cfg ext v n).block_roots →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      r ∈ (E.store cfg ext w m).block_roots
```

Producer-agnostic, exactly as the owner says. Carried on W20–W23 as `hW.base.synchrony`.

### 3.3 Step 3 — recompute `GU` at `w`. Available, and exact.

`Execution.accepted_unrealized_justification_eq`
(`Proof/AcceptedFFGStateTrajectory.lean:572-577`):

```lean
theorem accepted_unrealized_justification_eq
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S) (w : ValidatorIndex) (n : ℕ)
    {r : Root} (hr : r ∈ (E.store cfg ext w n).block_roots) :
    (E.store cfg ext w n).unrealized_justifications r = S.GU r
```

This is the FFG contract "recomputing `JustifiedIn` at `w`" in its sharpest possible form: every
honest store's `unrealized_justifications` map **agrees with the global selector on every block
it knows**. Composing §3.1-§3.3 in the non-anchor case gives
`(store w m).unrealized_justifications r = S.GU r = (store v n).unrealized_justified_checkpoint`
with `r ∈ (store w m).block_roots` — `JustifiedIn` disjunct 5, done.

**The anchor disjunct closes too**, contrary to first appearance. If the checkpoint is `B.anchor`:
`get_forkchoice_store` (`Model/Handlers.lean:470-493`) literally sets
`unrealized_justifications := Function.update _ anchor_root justified_checkpoint` with
`justified_checkpoint = Checkpoint.mk anchor_epoch anchor_root` (`:474, 492-493`), so
`genesis_store.unrealized_justifications B.anchor.root = genesis_store.justified_checkpoint =
B.anchor` by `hanchor`; `AcceptedFFGSelectorCoherence.genesis_unrealized_justification`
(`Model/FFGStateSemantics.lean:872-874`) turns that into `S.GU B.anchor.root = B.anchor`; the
anchor root is known at every honest store by store monotonicity, the exact three lines used at
`Proof/AcceptedCurrentTargetLowerContracts.lean:55-60`; and §3.3 lands disjunct 5 again. No extra
premise — `genesis_unrealized_justification` is a field of `B.coherence`, already on the surface.

### 3.4 The obstruction — the same-slot corner

The field concluded from `E.slot_at cfg n ≤ E.slot_at cfg m`. `block_relay` demands
`E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1)`. Splitting:

* `slot_at n < slot_at m`: then `slot_at n + 1 ≤ slot_at m ≤ slot_at (m + 1)` by monotonicity.
  **Covered.**
* `slot_at n = slot_at m`: the gate reduces to `slot_at m + 1 ≤ slot_at (m + 1)`, i.e. second `m`
  must be the **last second of its slot**. Nothing in the field's hypotheses says so.
  **Not covered.**

This is not an artifact of how the derivation is arranged; it is the documented reach limit of
block relay in this model, recorded in-tree for the structurally identical confirmed-block case:

> What is delivered now is `hb_of_confirming`: the later-slot half of the confirmed block's
> endpoint knownness, from `Synchrony.block_relay` via `HeadStack.b_known_of_relay`. The
> **same-slot cross-node** membership stays outside the block-relay guarantee, because
> `block_relay` has a `+1`-slot gate.
> — `Proof/FinalWiring.lean:16-18`

And it is the difference between the deleted field and the one it was modelled on:
`observed_justified` (`Spec/TheoremStatements.lean:165-169`) carries the same
`slot_at n ≤ slot_at m` hypothesis, but that field transcribes fast-confirmation.md:94's
"observed by all honest nodes at the beginning of the current epoch", a claim the pinned spec
makes at same-slot granularity precisely because the *observed* rotation happens a full epoch
after the quantity is banked. The one-rotation-upstream quantity has not had that slack yet —
which is the same thing P-4 flags as a disclosure, arriving here as a concrete slot-arithmetic
gap.

**Verdict.** The derivation yields

```
slot_at n + 1 ≤ slot_at (m + 1) → JustifiedIn (store w m) (store v n).unrealized_justified_checkpoint
```

from premises already on W20–W23, with no new assumption. It does **not** yield the field.

---

## 4. The two conjuncts

They are not the same argument, but the second reduces to the first.

* **Conjunct 1** is about the store's own `unrealized_justified_checkpoint` — a *live* store-global
  running maximum, read at second `n`. §3 handles it.
* **Conjunct 2** is about `(E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint` — a
  *banked* value. `update_fast_confirmation_variables` (`Model/Confirmation.lean:36-59`) writes it
  only at an epoch's last slot, and writes exactly
  `fcr_store.previous_epoch_greatest_unrealized_checkpoint := store.unrealized_justified_checkpoint`
  (`:46-49`, transcribing fast-confirmation.md's
  `if is_start_slot_at_epoch(Slot(get_current_slot(store) + 1)):`). So at any second `n` the FCR's
  banked value is either the genesis FCR initialization or conjunct 1's quantity at some earlier
  second `n' ≤ n`, hence at a slot `slot_at n' ≤ slot_at n ≤ slot_at m`.

  Deriving conjunct 2 therefore needs, on top of §3: an induction over `fcrStep` recovering the
  banking second (the shape of `MicroSteps.fcrStep_observed_boundary`, cf.
  `Proof/MicroSteps.lean:134`'s note that both are greatest-unrealized rotations), plus the
  genesis base case. **Both are mechanical, and both inherit §3.4's slot gate** — indeed conjunct 2
  inherits it in a *milder* form, since the banking second `n'` is strictly earlier, so the
  same-slot corner only bites when the banking and the reading happen in the same slot as `w`'s
  read.

  Note this is the conjunct whose spec docstring says "according to a local view"
  (fast-confirmation.md:97) — the one P-4 names. It is also the conjunct the deleted field could
  not shed: as `docs/plumbing-spec-citations.md` P-4 records, "the field is consumed as a whole,
  so dropping either conjunct is not available as a weakening". That constraint is now void,
  because the field is consumed by nothing.

---

## 5. What landed

**Status:** landed on `centaur/weak-synchrony-202609150824`. `bash scripts/check_build.sh`
green; `lake env lean scripts/Audit.lean` → *project trust audit passed: **9962** declarations,
**6221** theorems, 26 generated partials, **21** public witnesses*, sorry-free, on
`[propext, Classical.choice, Quot.sound]` only; `python3 scripts/check_imports.py` → *import
architecture audit passed: 287 Spec, 54 Paper, 342 total modules*.
`JustificationInterface` is **13 → 12 fields**.

The declaration/theorem counts move by exactly **one** each (9963 → 9962, 6222 → 6221): the
deleted projection itself, and nothing else. That is the arithmetic signature of a field with no
consumers — contrast the P-6 deletion, which cascaded into two full orphan waves.

* **`Spec/TheoremStatements.lean`** — the field is deleted. A comment in its place records the
  P-4 disclosure it carried, that its sole projection site
  (`FinalWiring.prev_greatest_of_interface`) went with the P-6 observed-anchor cone leaving zero
  mentions, and §3's finding that the derivation reaches only the strictly-later-slot regime. The
  module header's list of deleted non-exports gains the field.
* **`Spec/Proof/FinalWiring.lean`** — the stale `/-! ## Section 1 — `prev_greatest` from
  `unrealized_justified` -/` header is retitled and the deletion note now records that
  `prev_greatest_of_interface` was the field's only projection site.
* **`docs/plumbing-spec-citations.md`** — row 7 of §2 and §13 P-4 now read
  RESOLVED-BY-DELETION.
* **`docs/witness-statement-audit.md`** — row C's field count 13 → 12.

### 5.1 Effect on the premise surface

`hji` shrinks from 13 to 12 fields on **every** witness carrying it — W20–W23, the four weak
trajectory headlines. This is a strict premise weakening: no witness gained anything, and no
witness statement changed. The accepted public theorem is unaffected: it is stated over
`AcceptedActualFCRNextSlotSafetyAssumptions`, which never mentioned `JustificationInterface`,
and `JustificationInterface` has no constructor, so a theorem that does not assume it cannot use
it.

### 5.2 What is deliberately *not* in the tree

The §3 derivation is **not** added. It closes only the strictly-later-slot regime, nothing
consumes either it or the field, and adding an unconsumed theorem would recreate exactly the
orphan the P-6 sweep spent two waves removing. §3 is recorded here instead, with file:line for
every step, so the content is reconstructible if a consumer ever appears — in which case the
honest statement to prove is the gated one at the end of §3.4, not the deleted field.
