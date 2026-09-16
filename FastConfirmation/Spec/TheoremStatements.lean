import FastConfirmation.Spec.Model.FFGStateSemantics

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
`JustificationInterface` — the exports of Casper-FFG justification
(accountable safety, the ≥2/3-attested-target export, and the observation
propagation the `FastConfirmationStore` observed-checkpoint fields are
documented with). The semantic soundness of the two `will_*` gates is **not**
among them: no proof in the development ever applied it, so it is not a field.
Neither is the LMD head-tracking claim formerly carried as `justified_descends`:
it is an LMD-GHOST weight fact, not an FFG export, and it is not derivable from
the ≥2/3-attested-target export at this development's Byzantine design point. It
now lives as the explicitly-carried premise `Execution.HeadTracksJustified`
(`Proof/AheadFacade.lean`); see `docs/p6-justified-descends-derivation.md`.
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
when the gates are consulted. Hence it enters the gate-consuming statements as
an explicit hypothesis (avoiding circularity) and is **discharged at the
algorithm's call sites** by the L3/L4 proof from `HonestBehavior.votes_head` +
the established head agreement — never assumed globally; `SpecAssumptions` is
not strengthened by it. Without the gating a gate-soundness claim would be
inconsistent:
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
      `get_head`; without this the totalized read is junk).

      Pinned-spec origin: fork-choice.md:358
      `def get_weight(store, node): state =
      store.checkpoint_states[store.justified_checkpoint]`, an unguarded dict
      read — this field is that read's `KeyError`-freedom, made explicit.
      The real pipeline justifies only checkpoints that gathered ≥2/3
      attestations and `on_attestation`'s `store_target_checkpoint_state`
      caches every validated target, but `update_checkpoints` does not
      re-cache, so the fact enters as an explicit FFG-pipeline property.

      (This field absorbed the former `justified_checkpoint_cached`, which was
      the same proposition up to bound-variable renaming; see
      `docs/plumbing-spec-citations.md` P-2.) -/
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
      machinery the observed checkpoint reads).

      **DISCLOSURE (`docs/plumbing-spec-citations.md` P-4): this asserts
      cross-view propagation one rotation upstream of where the pinned spec
      documents it.**  fast-confirmation.md documents the all-honest-nodes
      property only for the two `*_observed_justified_checkpoint` fields
      (fast-confirmation.md:94: *"a justified checkpoint that has been observed
      by all honest nodes at the beginning of the current epoch assuming
      synchrony"*), which is what `observed_justified` above transcribes.  The
      field documentation of the checkpoint named in the SECOND conjunct here
      reads, verbatim (fast-confirmation.md:97):
      *"`previous_epoch_greatest_unrealized_checkpoint`: a greatest unrealized
      justified checkpoint at the start of the last slot of the previous epoch
      **according to a local view**"* — a local-view quantity.  Asserting that
      it, and the store's own `unrealized_justified_checkpoint`, are justified
      in EVERY honest view from the same slot on is the synchrony step the spec
      takes only one rotation later, applied here early.  It is sound under
      GST-0 honest-to-honest Δ-synchrony plus the ≥2/3-attested-target
      provenance both quantities share with the observed checkpoint, but it is
      an assumption of this development, not transcription. -/
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
      ≥2/3-attested-target caching provenance as `justified_cached`
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
      fields; the abstract state transition cannot deliver it per-handler).

      Pinned-spec origin: `on_block`'s
      `finalized_checkpoint_block = get_checkpoint_block(store,
      block.parent_root, store.finalized_checkpoint.epoch)` with
      `assert store.finalized_checkpoint.root == finalized_checkpoint_block`,
      and `get_filtered_block_tree`'s `base = store.justified_checkpoint.root`
      (fork-choice.md:448).

      Horizon-scoped like every other field of this record: the claim is made
      only at seconds `m` inside the verification horizon, which is the only
      regime any conclusion of this development is stated in
      (`docs/plumbing-spec-citations.md` P-5). -/
  checkpoint_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
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
  /- Deleted field: `justified_descends` — the LMD head-tracking claim that an
     honest store's `get_head` descends *every* checkpoint justified above that
     store's realized justified epoch. It was never an FFG export: it is an
     LMD-GHOST weight claim, and it is not derivable from a 2/3 justification
     quorum at this development's own design point
     `CONFIRMATION_BYZANTINE_THRESHOLD = 25`. No audited public witness ever
     reached it. It had two consumers: `AnchorClose`'s covering fold, which turned
     out to be redundant (the observed anchor's own `SafeFrom` witness was already
     threaded there and says exactly what the fold was deriving), and the legacy
     `SpecAssumptions` observed-anchor bundle, which now carries the fact as the
     named, explicitly-threaded premise `Execution.HeadTracksJustified`
     (`Proof/AheadFacade.lean`). The accepted/actual route never needed it: the
     rule re-checks `obs = store.unrealized_justifications head` at runtime. See
     `docs/plumbing-spec-citations.md` P-6 and
     `docs/p6-justified-descends-derivation.md` §7. -/
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

/-- The full premise bundle of the FCR guarantee: the genesis store is the
spec's own trusted-anchor initialization (`get_forkchoice_store`, with the
two facts its projection cannot carry: the dropped
`anchor_block.state_root == hash_tree_root(anchor_state)` assert renders as
slot agreement, and genuine hashing separates the anchor's parent from its
own root — `WellFormedStore` then *derives* via
`wellFormedStore_get_forkchoice_store`, it is not assumed), whole-second
slot boundaries (mainnet: `12000 ms`), the behavioral/network records, the
externals-coherence and static-set idealizations, the economic assumptions,
and the FFG interface. -/
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
