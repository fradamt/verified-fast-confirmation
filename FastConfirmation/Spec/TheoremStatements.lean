module
public import FastConfirmation.Spec.Model.FFGStateSemantics

@[expose] public section

/-!
# Spec / supporting statement vocabulary

This module defines supporting predicates used throughout the spec proof
architecture. It also records strong action-prefix candidate statements used
by the internal decomposition. The accepted public theorem is
`acceptedSpec_safety_next_slot` in
`Proof/AcceptedActualFCRNextSlotSafetyFacade.lean`.

The motivating spec note for `find_latest_confirmed_descendant` says:

> Assuming synchrony and `CONFIRMATION_BYZANTINE_THRESHOLD` value, the above
> criteria ensures that the block returned by this function will remain
> canonical in the view of all honest validators starting from the current
> moment in time.

The accepted result proves the helper claim at actual scheduled boundary calls
and proves stored-output safety across nodes from the following slot. It does
not assert the stronger cross-node claim at every arbitrary in-slot execution
prefix; finite counterexamples show that statement is false.

The FFG-side facts the algorithm consumes are isolated in
`JustificationInterface` — the exports of Casper-FFG justification (the
semantic soundness of `will_no_conflicting_checkpoint_be_justified` /
`will_current_target_be_justified`, and the observation propagation the
`FastConfirmationStore` observed-checkpoint fields are documented with).
These predicates remain low-level proof vocabulary. The accepted theorem uses
the separate accepted FFG-semantics and `PaperSafetySynchrony` interfaces.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Checkpoint `c` is justified according to `store`'s knowledge: it is one
of the store's justified/finalized checkpoint fields (finalized ⊆ justified),
their unrealized counterparts, or the unrealized justification of a known
block. -/
def JustifiedIn (store : Store Root) (c : Checkpoint Root) : Prop :=
  c = store.justified_checkpoint ∨
  c = store.unrealized_justified_checkpoint ∨
  c = store.finalized_checkpoint ∨
  c = store.unrealized_finalized_checkpoint ∨
  ∃ r ∈ store.block_roots, store.unrealized_justifications r = c

/-- The spec's proviso on both `will_*` predictions ("This function assumes
that all honest validators will be voting in support of the current epoch
target"): from second `n` on, every honest vote of a slot in the target's
epoch carries target `T`.

This is *not* an extra behavioral assumption on top of `HonestBehavior` —
honest validators always vote the target derived from their own head
(validator.md over fork-choice.md). But that per-validator fact yields
support for *`v`'s* target `T` only under **cross-validator head/boundary
agreement** (every honest head's epoch-boundary block is `T.root`), which is
exactly what the FCR's preceding checks are mid-way through establishing
when the gates are consulted. The property is an explicit, call-scoped
hypothesis. The older `SpecAssumptions` record does not contain it. The
accepted theorem requires it through `completed_calls.helper_provisos` at each
actual guarded FCR call whose next second is in the verification horizon.
Without the gating the fields would be inconsistent:
the `will_*` booleans are arithmetically true early in every epoch (the
elapsed-committee estimate is still small) even while honest heads — and
hence honest targets — are split across an adversarial boundary proposal. -/
def HonestVotesSupportTarget (E : Execution Root) (T : Checkpoint Root) (n : ℕ) :
    Prop :=
  E.WithinHorizon cfg n ∧
    ∀ v ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = T.epoch → E.slot_at cfg n ≤ s →
      ∀ k a, E.vote v s = some (k, a) → a.data.target = T

/-- The FFG exports the FCR consumes (see the module docstring). Each field is
stated at the altitude the algorithm uses it, over honest nodes' evolving
stores; the prediction-shaped fields are gated on the spec's own
`HonestVotesSupportTarget` proviso and on the relevant roots being known
(the totalized ancestry walk is meaningless on unknown roots). -/
structure JustificationInterface (E : Execution Root) : Prop where
  /-- semantic soundness of the `will_no_conflicting_checkpoint_be_justified`
      gate: if it holds at an honest node, every checkpoint justified
      anywhere (at any honest node, then or later) is ancestry-comparable
      with the current target — "no checkpoint conflicting with the current
      target can ever be justified". -/
  gate_sound : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    will_no_conflicting_checkpoint_be_justified cfg ext (E.store cfg ext v n) = true →
    HonestVotesSupportTarget cfg E (get_current_target cfg (E.store cfg ext v n)) n →
    ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
    ∀ c : Checkpoint Root, JustifiedIn (E.store cfg ext w m) c →
      c.root ∈ (E.store cfg ext w m).block_roots →
      (get_current_target cfg (E.store cfg ext v n)).root ∈
        (E.store cfg ext w m).block_roots →
      is_ancestor (E.store cfg ext w m) (get_node_for_root c.root)
        (get_node_for_root (get_current_target cfg (E.store cfg ext v n)).root) = true ∨
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (get_current_target cfg (E.store cfg ext v n)).root)
        (get_node_for_root c.root) = true
  /-- FFG accountable safety, consumed (< 1/3 of stake slashable under
      `CONFIRMATION_BYZANTINE_THRESHOLD ≤ 25`): checkpoints justified in
      honest views are unique per epoch. -/
  justified_unique : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ n m : ℕ,
    E.WithinHorizon cfg n → E.WithinHorizon cfg m →
    ∀ c c' : Checkpoint Root,
    JustifiedIn (E.store cfg ext v n) c → JustifiedIn (E.store cfg ext w m) c' →
      c.epoch = c'.epoch → c.root = c'.root
  /-- the observed justified checkpoints were attestation targets at every
      honest node (their checkpoint states are cached — the balance-source
      reads are in-domain; an FFG export: justification requires two-thirds
      attestations targeting the checkpoint, delivered under synchrony). -/
  observed_justified_cached : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    (E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint ∈
      (E.store cfg ext v n).checkpoint_state_keys ∧
    (E.fcr cfg ext v n).previous_epoch_observed_justified_checkpoint ∈
      (E.store cfg ext v n).checkpoint_state_keys
  /-- the justified checkpoint itself was a two-thirds-attested target,
      delivered under synchrony — its checkpoint state is cached at every
      honest node (`get_weight`/`get_proposer_score` read it on every
      `get_head`; without this the totalized read is junk). -/
  justified_cached : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    (E.store cfg ext v n).justified_checkpoint ∈
      (E.store cfg ext v n).checkpoint_state_keys
  /-- finalized/justified chain coherence in honest views (Casper: the
      finalized block is on every justified checkpoint's chain when both are
      known): the store invariant `update_checkpoints` alone cannot maintain
      is exported here. -/
  finalized_justified_ancestry : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    (E.store cfg ext v n).finalized_checkpoint.root ∈
        (E.store cfg ext v n).block_roots →
    (E.store cfg ext v n).justified_checkpoint.root ∈
        (E.store cfg ext v n).block_roots →
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root (E.store cfg ext v n).justified_checkpoint.root)
        (get_node_for_root (E.store cfg ext v n).finalized_checkpoint.root) = true
  /-- the FFG accounting export (what the spec's own argument uses):
      a post-anchor checkpoint justified in an honest view received epoch-`c`
      target attestations from two-thirds of its epoch's committee weight —
      observable as attestation events in honest schedules. -/
  justified_requires_targets : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ c : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c →
    E.genesis_store.justified_checkpoint.epoch < c.epoch →
    c.epoch < E.verification_horizon →
      ∃ S : Finset ValidatorIndex,
        S ⊆ E.span_committee (c.epoch * cfg.slots_per_epoch)
          (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) ∧
        (∀ i ∈ S, ∃ (w' : ValidatorIndex) (n' : ℕ) (a : Attestation Root)
            (ifb : Bool),
          E.WithinHorizon cfg n' ∧
          E.SlotWithinHorizon cfg a.data.slot ∧
          Event.attestation a ifb ∈ E.schedule w' n' ∧
          i ∈ a.attesting_indices ∧ a.data.target = c) ∧
        2 * E.total_active cfg ≤ 3 * E.weight S
  /-- semantic soundness of `will_current_target_be_justified`: if it holds
      at an honest node, the current target is justified in every honest view
      from the start of the next epoch. -/
  target_justified_sound : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    will_current_target_be_justified cfg ext (E.store cfg ext v n) = true →
    HonestVotesSupportTarget cfg E (get_current_target cfg (E.store cfg ext v n)) n →
    ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      ((get_current_target cfg (E.store cfg ext v n)).epoch + 2) * cfg.slots_per_epoch ≤
        E.slot_at cfg m →
      JustifiedIn (E.store cfg ext w m) (get_current_target cfg (E.store cfg ext v n))
  /-- the observed-justified-checkpoint propagation the `FastConfirmationStore`
      field documentation claims: an honest node's observed justified
      checkpoint is justified in every honest view from the same slot on. -/
  observed_justified : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg n → E.WithinHorizon cfg m →
    E.slot_at cfg n ≤ E.slot_at cfg m →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint)
  /-- Unrealized-family justification propagation (the
      unrealized/greatest-unrealized analog
      of `observed_justified`): an honest store's unrealized justified
      checkpoint and its FCR store's previous-epoch greatest unrealized
      checkpoint are justified in every honest view from the same slot on
      (both are computed by the same ≥2/3-attested unrealized-justification
      machinery the observed checkpoint reads). -/
  unrealized_justified : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg n → E.WithinHorizon cfg m →
    E.slot_at cfg n ≤ E.slot_at cfg m →
      JustifiedIn (E.store cfg ext w m)
        (E.store cfg ext v n).unrealized_justified_checkpoint ∧
      JustifiedIn (E.store cfg ext w m)
        ((E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint)
  /-- Greatest-unrealized cache:
      the previous-epoch greatest unrealized checkpoint an honest node's FCR
      store carries is among its store's keyed checkpoint states (same
      ≥2/3-attested-target caching provenance as `justified_checkpoint_cached`
      / `observed_justified_cached` — the checkpoint was an attestation
      target, and `store_target_checkpoint_state` keys every validated
      target; the pinned spec's rotation does not re-key). -/
  greatest_unrealized_cached : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    ((E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint) ∈
      (E.store cfg ext v n).checkpoint_state_keys
  /-- Checkpoint knownness: the
      justified and finalized checkpoint roots an honest store carries are
      known blocks (the real epoch processing justifies only known targets —
      `justified_requires_targets`' knownness half for the store's own
      fields; the abstract state transition cannot deliver it per-handler). -/
  checkpoint_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots ∧
    (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots
  /-- Cross-epoch justified-chain
      coherence (Casper accountable safety, the unequal-epoch complement of
      `justified_unique`): checkpoints justified in honest views with ordered
      epochs are ancestry-ordered, read at any honest store knowing both. -/
  justified_ancestry : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ c c' : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c → JustifiedIn (E.store cfg ext w m) c' →
    c.epoch ≤ c'.epoch →
    c.root ∈ (E.store cfg ext w m).block_roots →
    c'.root ∈ (E.store cfg ext w m).block_roots →
      is_ancestor (E.store cfg ext w m) (get_node_for_root c'.root)
        (get_node_for_root c.root) = true
  /-- Finalized-checkpoint
      propagation (Casper finality across honest views): an honest node's
      finalized checkpoint is, from that second on, an ancestor of every
      honest node's own finalized checkpoint — the cross-store descent the
      trajectory fold's reset anchors ride. -/
  finalized_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg k → E.WithinHorizon cfg m →
    k ≤ m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true
  /-- The justified balance
      source is cached: an honest store's justified checkpoint is among its
      keyed checkpoint states (the real pipeline justifies only checkpoints
      that gathered ≥2/3 attestations, and `on_attestation`'s
      `store_target_checkpoint_state` caches every validated target — the
      pinned spec's `update_checkpoints` does not re-cache, so the fact
      enters as an explicit FFG-pipeline property). -/
  justified_checkpoint_cached : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint ∈
      (E.store cfg ext w m).checkpoint_state_keys
  /-- Observed/unrealized
      checkpoint knownness: the roots of the store's unrealized justified
      checkpoint, its previous-epoch greatest unrealized checkpoint, and the
      FCR store's observed justified checkpoint are known blocks (the same
      ≥2/3-attested-target provenance as `checkpoint_known` — unrealized
      justification is computed over known blocks only). -/
  observed_checkpoint_known : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg n → E.WithinHorizon cfg m →
    E.slot_at cfg n ≤ E.slot_at cfg m →
    (E.store cfg ext v n).unrealized_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots ∧
    ((E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint).root ∈
      (E.store cfg ext w m).block_roots ∧
    ((E.fcr cfg ext v n).current_epoch_observed_justified_checkpoint).root ∈
      (E.store cfg ext w m).block_roots
  /-- Recorded justified
      support (the fork-choice counterpart of `justified_requires_targets`,
      whose ≥2/3-attested-target content it re-reads at the LMD layer): at
      every honest store, a checkpoint justified above the store's realized
      justified epoch retains recorded latest-message support descending
      from it that strictly dominates every competing subtree plus the
      proposer boost — packaged as the dominant filtered descent chain the
      GHOST walk follows (2/3 of an epoch's attesters named it as target;
      honest ones' newest messages keep descending from it — the
      justification-friendliness of LMD-GHOST the fork-choice design
      guarantees). Stated as the head-tracking conclusion the algorithm
      relies on. -/
  justified_descends : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ c : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c →
    c.root ∈ (E.store cfg ext w m).block_roots →
    (E.store cfg ext w m).justified_checkpoint.epoch < c.epoch →
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m)) (get_node_for_root c.root) = true
  /-- Checkpoint-boundary
      placement: the justified checkpoint's block sits at or below the
      boundary of any honest vote's target epoch from that store
      (`get_checkpoint_block` walks to the epoch's first slot; a
      checkpoint's block never overshoots its own epoch boundary, and
      honest targets never trail the justified epoch — the FFG-pipeline
      structure `vote_lands`'s validation gate reads). -/
  justified_block_boundary : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ (t : Checkpoint Root),
    E.WithinHorizon cfg m →
    (∃ v ∈ E.honest, ∃ s k a, E.SlotWithinHorizon cfg s ∧
      E.WithinHorizon cfg k ∧ E.vote v s = some (k, a) ∧ a.data.target = t) →
    (E.store cfg ext w m).justified_checkpoint.epoch ≤ t.epoch →
      ((E.store cfg ext w m).blocks
          (E.store cfg ext w m).justified_checkpoint.root).slot ≤
        compute_start_slot_at_epoch cfg t.epoch

/-- The legacy premise bundle uses the spec's trusted-anchor initialization
with anchor slot agreement and parent/root inequality. This legacy bundle
does not require a state-root commitment. The accepted trajectory additionally
requires `Externals.AnchorCommitsToState` in its `genesis` premise. This
abstract contract comes from the external interpretation; slot agreement is
independent, and the model does not prove a concrete hashing result.
The legacy bundle also requires
whole-second slot boundaries (mainnet: `12000 ms`), the behavioral and
network records, the externals-coherence and static-set idealisations, the
economic assumptions, and the FFG interface. -/
def SpecAssumptions (E : Execution Root) : Prop :=
  (∃ (anchor_state : BeaconState Root) (anchor_block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
    anchor_state.slot = anchor_block.message.slot ∧
    anchor_block.message.parent_root ≠ anchor_block.root) ∧
  WellFormedExecution E ∧
  1000 ∣ cfg.slot_duration_ms ∧
  HonestBehavior cfg ext E ∧
  Synchrony cfg ext E ∧
  ExternalsCoherence cfg ext E ∧
  StaticValidatorSet cfg E ∧
  ByzantineBound cfg E ∧
  JustificationInterface cfg ext E

/-- Strong all-prefix safety candidate used by the internal proof
decomposition. This is not the accepted public theorem: arbitrary in-slot
cross-node prefixes do not satisfy this conclusion. -/
def Spec_Safety : Prop :=
  ∀ E : Execution Root, SpecAssumptions cfg ext E →
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true

/-- Next-slot form over the older `SpecAssumptions` vocabulary. The accepted
public theorem uses `AcceptedActualFCRNextSlotSafetyAssumptions` and is stated as
`AcceptedSpec_Safety_next_slot`. -/
def Spec_Safety_next_slot : Prop :=
  ∀ E : Execution Root, SpecAssumptions cfg ext E →
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true

/-- **Chain consistency** — an honest node's confirmed roots all lie on one
chain: any two are ancestry-comparable in the node's (later) store. This is
the defensible spec-model rendering of the paper's monotonicity: strict
"once confirmed, always confirmed" ancestor-monotonicity is *false* for the
deployed algorithm without a liveness premise — the assumptions do not force
block production, and `get_latest_confirmed`'s staleness revert
(`get_block_epoch(confirmed) + 1 < current_epoch` → finalized root) fires by
design when the chain stalls, moving the confirmed root *backwards* along
the same chain. Strict monotonicity holds while the revert/restart branches
are idle; this file records that restricted conditional statement separately. -/
def Spec_Monotonicity : Prop :=
  ∀ E : Execution Root, SpecAssumptions cfg ext E →
    ∀ v ∈ E.honest, ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.confirmed cfg ext v m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true ∨
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.confirmed cfg ext v n))
        (get_node_for_root (E.confirmed cfg ext v m)) = true

/-- **Conditional strict monotonicity** — the refinement implies the comparability
form defers: if between the two instants neither the finalized-revert nor
the observed-justified restart branch of `get_latest_confirmed` fired at
`v` (no slot-start second in `(n, m]` at which the algorithm reset
`confirmed_root` to `store.finalized_checkpoint.root` or to
`current_epoch_observed_justified_checkpoint.root` *below* the previous
confirmed root), then confirmation is ancestor-monotone: the earlier
confirmed root is in the later one's chain. This is the statement that
exercises `get_latest_confirmed`'s walk structure (the comparability form
alone is derivable from two `Spec_Safety` instances). -/
def Spec_Monotonicity_no_revert : Prop :=
  ∀ E : Execution Root, SpecAssumptions cfg ext E →
    ∀ v ∈ E.honest, ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      (∀ k : ℕ, n < k → k ≤ m →
        get_block_slot (E.store cfg ext v k) (E.confirmed cfg ext v k) ≥
          get_block_slot (E.store cfg ext v k) (E.confirmed cfg ext v (k - 1))) →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.confirmed cfg ext v m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true

end FastConfirmation.Spec

end
