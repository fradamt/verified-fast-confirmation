module
public import FastConfirmation.Spec.Proof.VoteLanding

@[expose] public section

/-!
# Spec / Proof / HeadStack: the head-stack knownness toolkit

This module packages the `get_head` and `get_checkpoint_block`
well-formedness inputs that `Delivery.vote_lands`/`vote_ubiquity` leave as their
two open hypotheses (`hhead_known`, `hhead_walk`) — packaged so the vote-landing
reductions can be *called*. This is the root blocker for the `hSmono`/`hXmono`/
`hsat` migration cruxes (`VoteLanding`'s enumerated residue): every one of them
routes a late voter's head through `vote_ubiquity`, whose only open inputs are the
two facts proved here.

Section 1 — **`hhead_known`, unconditional.** `Engine.get_head_root_mem_or` lands
`get_head` on a known block *or* the justified checkpoint root; the latter is a
known block by `JustificationInterface.checkpoint_known`. So `get_head` is known
with no side hypotheses (`head_root_known`).

Section 2 — **`hhead_walk`, reduced to the checkpoint-boundary bound.**
`AnchorFacade.store_walkKnownK` supplies the walk domain at every known target:
`WalkKnown store (blocks t).slot r` for known `t`, `r`. Taking `t :=`
`justified_checkpoint.root` and lifting the walk slot up to the FFG target epoch's
boundary (`AncestryRoots.WalkKnown.mono`) yields `hhead_walk` from the single store
invariant `(blocks justified.root).slot ≤ compute_start_slot_at_epoch cfg
target.epoch` (the justified block sits at or below the target epoch's boundary —
the genuine per-store residual; the honest target epoch is `≥` the source/justified
epoch and a checkpoint block never overshoots its own boundary).

Section 3 — the **closed vote-landing bundle** (`vote_lands_closed`,
`vote_ubiquity_closed`): `Delivery.vote_lands`/`vote_ubiquity` with `hhead_known`
discharged outright and `hhead_walk` reduced to the Section-2 bound. These are the
call sites `hSmono`/`hXmono`/`hsat` consume.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hhead_known`, unconditional -/

/-- **`get_head` lands on a known block, unconditionally.** The case split
of `Engine.get_head_root_mem_or` (known block, or the justified checkpoint root on an
empty filtered descent) closes against `JustificationInterface.checkpoint_known`
(the justified root is a known block at every honest store). No `store_domain` /
walk hypotheses. This is `hhead_known` (`= (honest_attestation …).data.beacon_block_root`
by `honest_attestation_data_beacon_block_root`). -/
theorem head_root_known (hji : JustificationInterface cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m) :
    (get_head cfg (E.store cfg ext w m)).root ∈ (E.store cfg ext w m).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext w m) with h | h
  · exact h
  · rw [h]; exact (hji.checkpoint_known w hw m hH).1

/-! ## Section 2 — `hhead_walk`, reduced to the checkpoint-boundary bound -/


/-! ## Section 3 — the closed vote-landing bundle -/



/-! ## Section 4 — `hJlb`: the saturated-regime `Jspec` lower bound

`VoteLanding.boost_dilution` (feeding `IHMechanize.hmaj_of_saturation`) consumes the
saturated-regime lower bound `2·(boost+1) ≤ Jspec lo σ'`. It is a pure `span_fraction`
consequence over the committee weight of the (saturated, `≥ 1`-epoch) window: with
`C := CONFIRMATION_BYZANTINE_THRESHOLD ≤ 25`, `span_fraction` gives byzantine weight
`≤ C·W/100 ≤ W/4`, so the honest weight `Jspec = W − byz ≥ 3W/4`. Hence any
`4·(boost+1) ≤ W` closes `2·(boost+1) ≤ Jspec` (`3W/4 ≥ W/2 ≥ 2·(boost+1)`).

The residual `4·(boost+1) ≤ W(span lo σ')` is the *only* genuinely new fact — a
committee-weight floor over the saturated window: past `T1` the window spans a full
epoch, whose committee union is the whole active set (`committee_coverage`), of weight
`E.total_active`, while `boost = proposer_score_boost·(TAB/SLOTS_PER_EPOCH)/100 ≤
40·(TAB/32)/100 = TAB/80`, so `4·(boost+1) ≤ TAB/20 + 4 ≤ TAB = W` with wide margin.
Its faithful discharge needs the `estimate`/`committee_coverage` epoch-scale weight
identification (`W(full epoch) = TAB`); the theorem below states that premise directly. -/


/-! ## Section 5 — why `hBb` base-enemy movement is not used

The relay-based recorded base-enemy transport `hBb : BbadVal@(w,m) ≤ BbadVal@(vc,nc)`
would require the former `BbadSet_subset_of_relays` / `hBb_of_relays` route. Its
recorded-root-agreement leg relied on `Synchrony.recorded_conflict_slashed` without
it slashed on any cross-node root disagreement without a same-target-epoch guard, so
it silently excluded legitimate cross-epoch re-voters. The corrected field now carries
a `(get_latest_message_epoch cfg lm) = (get_latest_message_epoch cfg lm')` (double-vote) guard, and with that guard the recorded-`BbadSet`
subset **cannot** be proved in general: a Byzantine validator re-voting a sibling in a
*different* target epoch is a recorded base-enemy member at `(w,m)` that the relays
cannot move back to `(vc,nc)`.

The base transport therefore no longer routes through the recorded-enemy `hBb` at all:
`Proof/GroundBeta.lean` (`bval_endpoint_strip_of_transport` / `ledger_descendStep_groundBeta`)
replaces it with the **store-independent** ground-truth-`Bval` endpoint strip — the full
window enemy `Bval(es)` is `span_fraction`-budgeted at the endpoint directly (no relay, no
subset), so the per-fork descent closes at every slot regime with only the honest transports.
Thus the base transport does not require a same-slot recorded-enemy relay. -/

/-! ## Section 6 — `hb`: the confirmed block relays to every later endpoint

`IHMechanize.dynamicsChainStruct_of_endpoint`'s first per-endpoint residual `hb` asks
that the confirmed block `b` is a known block at every honest endpoint `(w, m)`. The
confirmed root `b = E.confirmed cfg ext v₀ n₀` is a known block at its own confirming
store (`get_latest_confirmed` returns `confirmed_root` / the finalized root / a
`is_one_confirmed` descendant of the balance source — all in `block_roots`); `block_relay`
then lands it in every honest node's block set from the next slot on. `b_known_of_relay`
is that block-relay leg. Its slot gate `slot(n₀)+1 ≤ slot(m+1)` is the later-slot
regime; the **same-slot residue** (`slot(m) = slot(n₀)`, a *different* node `w` that has
not yet gossip-received `b`) is the intra-slot reach limit shared with `hBb` — the IH is
vacuous there (`slot(m') < slot(m) = slot(n₀)` is unreachable for `m' ≥ n₀`), so the full
`hb` shape carries that condition explicitly, just as `recorded_conflict_slashed` does for `hBb`.

`hcase` (`get_ancestor_roots (store w m) b jc ≠ [] ∨ b = jc`) is the L4 loop-inversion
descent: it is the AncestryRoots characterization of `b` sitting on the store's justified
chain, fed by the engine IH's justified-dominance leg + `L4Fold.find_latest_confirmed_
descendant_spec`. It is genuinely per-endpoint (the shell's own induction supplies the IH),
and is represented by an explicit per-endpoint premise. -/

/-- **`hb`, the block-relay leg.** A block known at an honest node's store is,
from the next slot on, known at every honest node — so the confirmed block `b` (known at
its confirming store `(v₀, n₀)`) is a known block at every later-slot honest endpoint
`(w, m)`. This is `Synchrony.block_relay` specialized to the confirmed root; it discharges
`dynamicsChainStruct_of_endpoint`'s `hb` in the later-slot regime (the same-slot residue is
the documented intra-slot reach limit). -/
theorem b_known_of_relay (hsyn : Synchrony cfg ext E)
    {v₀ w : ValidatorIndex} (hv₀ : v₀ ∈ E.honest) (hw : w ∈ E.honest)
    {n₀ m : ℕ} {b : Root} (hbknown : b ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hHn₀ : E.WithinHorizon cfg n₀) (hHm : E.WithinHorizon cfg m)
    (hgap : E.slot_at cfg n₀ + 1 ≤ E.slot_at cfg (m + 1)) :
    b ∈ (E.store cfg ext w m).block_roots :=
  hsyn.block_relay v₀ hv₀ n₀ b hHn₀ hbknown w hw m hHm hgap

end Execution

end FastConfirmation.Spec

end
