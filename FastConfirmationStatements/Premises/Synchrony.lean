module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Behavior

@[expose] public section

/-! Defines message, block, envelope, and equivocation-evidence delivery deadlines used by
FCR safety.

Each law states its timing directly. A source observation is at or before the
attestation deadline of its slot (`slot_start + A`, in whole seconds). The
receiver fact holds from the first second of the next slot (the boundary), at
a receiver second later than the source second. Motivation: in the paper, a
positive network delay `Δ` with `A + Δ < S` puts a message that an honest node
holds at the deadline at every honest node before the next slot. No law
refers to `Δ`, and no premise field states it. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The only permanent block-delivery exemption is the finalized-checkpoint
guard in `on_block`. The parent is already known at the receiver, so a late
or parent-missing block cannot satisfy this predicate. At every later
in-horizon second one of the two finalized guards still rejects it. -/
def PermanentBlockExclusion (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) (r : Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  let source := E.store cfg ext v n
  let receiver := E.store cfg ext w m
  r ∉ receiver.block_roots ∧
    (source.blocks r).parent_root ∈ receiver.block_roots ∧
    ∀ k, m ≤ k → E.WithinHorizon cfg k →
      let later := E.store cfg ext w k
      (source.blocks r).slot ≤
        compute_start_slot_at_epoch cfg later.finalized_checkpoint.epoch ∨
      later.finalized_checkpoint.root ≠
        get_checkpoint_block cfg later (source.blocks r).parent_root
          later.finalized_checkpoint.epoch

/-- Operational store-retention premise close to the membership conjunct.
Timing: a root that an honest node `v` stores at a second `n` at or before the
attestation deadline of its slot is in the store of every honest node `w` at
every in-horizon second `m` from `boundary = slot_start (slot_at n + 1)` on,
with `n < m`. The network must deliver each such block and its parents, and
honest clients must service ready blocks and retain accepted ones. Only the
exact permanent finalized-guard rejection is exempt, evaluated at
`boundary - 1`, before the next-slot tick. Python's delay consideration permits
a finalized-conflicting block to remain absent; the exemption is limited to
exactly that `on_block` guard. As in `PermanentBlockExclusion`, the parent
must already be known at the exclusion point.

Motivation: with the paper's `A + Δ < S` and immediate honest gossip, the
block arrives at a second `a < boundary`. If `on_block` accepts it, the
receiver keeps it. If the finalized guard rejects it, advancing finality along
its checkpoint chain preserves that rejection, from `a` on and thus from
`boundary - 1` on. Finality installed at the next tick cannot excuse a block
that arrived earlier. -/
def DeadlineBlockRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_start cfg (E.slot_at cfg n + 1) ≤ m →
      n < m →
      r ∈ (E.store cfg ext w m).block_roots ∨
        PermanentBlockExclusion cfg ext E v n r w
          (E.slot_start cfg (E.slot_at cfg n + 1) - 1)

/-- Timing: a root that an honest node stores at or before the attestation
deadline of its slot is in the store that each honest node's boundary vote
handler reads, at the first second of the next slot. That store is the tick
of the previous second's store followed by the events before the vote. A
permanently finalized-conflicting block is the only exemption, evaluated at
`boundary - 1` as in `DeadlineBlockRelay`. Both source and receiver seconds
are explicit and distinct; this does not assert same-second inter-node state
equality.

Motivation: the paper's `A + Δ < S` puts a cutoff-time block at the receiver
before the next slot. Immediate gossip and Python's delay consideration
require the honest client to order a ready block before an attestation at
that boundary. -/
def DeadlineBoundaryBlockPrefix (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest,
      let boundary := E.slot_start cfg (E.slot_at cfg n + 1)
      E.WithinHorizon cfg boundary → n < boundary →
      ∀ a before after,
        E.schedule w boundary =
          before ++ Event.attestation a false :: after →
        ¬ PermanentBlockExclusion cfg ext E v n r w (boundary - 1) →
        r ∈ (before.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w (boundary - 1))
            (E.time_at boundary))).block_roots
/-- Timing: an equivocating index that an honest node holds at or before the
attestation deadline of its slot is held by every honest node at every
in-horizon second from the next boundary on, at a receiver second later than
the source second. Motivation: slashing gossip within the paper's delay `Δ`,
with `A + Δ < S`, delivers the evidence before that boundary. Acceptance reads
only the slashable-data check and two indexed-attestation checks. These checks
read the attestations, signer pubkeys, and target-epoch domains. Pubkeys never
change. The genesis validators root is common, and this model has one fork,
so the domains are common.

The handler `on_attester_slashing` follows the Python and validates against
`store.block_states[store.justified_checkpoint.root]`. The relay field is a
premise, not a handler check: it states that every honest node holds the
indices by the next boundary. The missing-signer rejection needs a registry
change; it is outside the static-registry and one-fork scope here. The premise
still requires timely receipt and service. It matches clients
that validate network evidence against a newer state. Lighthouse, Prysm, Teku,
Lodestar, and Nimbus use the head state; Lighthouse advances it to the
wall-clock slot. Grandine follows the specification and uses the justified
state. All six clients apply valid gossip evidence to fork choice before block
inclusion, and none prunes the equivocation set at finalization.

The source time is when the node holds the index, not the evidence's arrival
time. An FCR call reads at a slot start, before its deadline; thus evidence
accepted late in a prior slot also has a valid cutoff observation. There is
no exclusion alternative and no same-second cross-node conclusion. -/
def DeadlineAttesterSlashingRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n (i : ValidatorIndex),
    E.WithinHorizon cfg n →
    i ∈ (E.store cfg ext v n).equivocating_indices →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_start cfg (E.slot_at cfg n + 1) ≤ m → n < m →
      i ∈ (E.store cfg ext w m).equivocating_indices

/-- The envelope counterpart of `DeadlineBoundaryBlockPrefix`. Timing: a
payload that an honest node has verified at or before the attestation
deadline of its slot is verified in the store that each honest node's
boundary vote handler reads, at the first second of the next slot. The
envelope can arrive at an earlier second or earlier in the boundary second;
one receipt is sufficient, because Python `on_execution_payload_envelope`
writes `store.payloads` and no handler removes an entry. The only exemption
is the permanent finalized-guard rejection of the block, evaluated at
`boundary - 1` as in `DeadlineBlockRelay`. Source and receiver seconds are
distinct; this does not assert same-second inter-node state equality.

Motivation: verified envelopes are gossiped within the paper's delay `Δ`, and
`A + Δ < S` puts a cutoff-time envelope at the receiver before the next slot.
Immediate gossip and Python's delay consideration require the honest client to
process a ready envelope before an attestation at that boundary. -/
def DeadlineBoundaryEnvelopePrefix (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    is_payload_verified (E.store cfg ext v n) r = true →
    r ∈ (E.store cfg ext v n).block_roots →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest,
      let boundary := E.slot_start cfg (E.slot_at cfg n + 1)
      E.WithinHorizon cfg boundary → n < boundary →
      ∀ a before after,
        E.schedule w boundary =
          before ++ Event.attestation a false :: after →
        ¬ PermanentBlockExclusion cfg ext E v n r w (boundary - 1) →
        is_payload_verified (before.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w (boundary - 1))
            (E.time_at boundary))) r = true

/-- One-slot operational closure for honest votes created inside the public
verification horizon.

This is the boundary case of the paper's synchrony premise.  The vote's slot
and creation time remain horizon-scoped; only its mandated receipt second may
be the first second of the immediately following epoch, just beyond the
exclusive public cutoff.  Keeping that receipt in the infinite execution
schedule avoids the impossible requirement that the cutoff contain its own
next epoch boundary.

Idealization: each honest single-validator vote reaches every honest node at
the exact next boundary second. Real gossip uses subnets and aggregates; the
fork-choice effect of the aggregate is the same. -/
structure HorizonVoteDeliveryLookahead (E : Execution Root) : Prop where
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))

/-- The synchrony fragment used by the accepted spec next-slot proof.

The network content is in the delivery laws: honest-attestation delivery,
block relay, the block and envelope boundary prefixes, and
equivocation-evidence relay. Each law states its timing in slot boundaries
and attestation deadlines; the paper's `A + Δ < S` is their motivation, not a
field. The exact relation to `Synchrony` is proved by
`synchrony_and_delivery_iff_nextSlot`. -/
structure NextSlotSynchronyPremises (E : Execution Root) : Prop where
  /-- Vote delivery includes the boundary just beyond the public horizon. -/
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E
  /-- A root stored by a cutoff observation is in every honest store from
      the next boundary on. Only the pre-tick finalized guard exempts. -/
  deadline_block_relay : DeadlineBlockRelay cfg ext E
  /-- A root stored by a cutoff observation is in the store read by each
      boundary vote handler; exclusion is tested before the tick. -/
  boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext E
  /-- A payload verified by a cutoff observation is verified in the store
      read by each boundary vote handler; exclusion is tested before the
      tick. -/
  boundary_envelope_prefix : DeadlineBoundaryEnvelopePrefix cfg ext E
  /-- Evidence held by a cutoff observation is held by every honest node
      from the next boundary on, without an exclusion branch. A premise over
      the literal justified-state handler; see the definition note on client
      evidence validation. -/
  attester_slashing_relay : DeadlineAttesterSlashingRelay cfg ext E


end FastConfirmation.Spec

end
