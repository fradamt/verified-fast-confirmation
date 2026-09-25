module
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Behavior

@[expose] public section

/-! Defines message, block, envelope, and equivocation-evidence delivery deadlines used by FCR safety. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution

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

/-- Slot-level block gossip from an honest observation no later than its
attestation deadline. The paper's positive `Δ` and strict `A + Δ < S`, plus
immediate honest gossip, put the raw block before the next slot. Python's
delay consideration permits a finalized-conflicting block to remain absent;
the exemption above is limited to exactly that `on_block` guard.

Set `boundary = slot_start (slot_at n + 1)`. The exemption starts at
`boundary - 1`, before the next-slot tick. A block arrives at an integer
second `a ≤ n + Δ < boundary`. If `on_block` accepts it, the receiver keeps
it. If the finalized guard rejects it, advancing finality along its checkpoint
chain preserves that rejection. Thus rejection holds from `a` on, and from
`boundary - 1` on. The cutoff gives `n ≤ deadline < boundary`, hence
`n ≤ boundary - 1`. Finality installed at the next tick cannot excuse a
block that should have arrived earlier. As in `PermanentBlockExclusion`,
the parent must already be known at the exclusion point. -/
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

/-- The paper's strict `A + Δ < S` places a cutoff-time block at the receiver
before the next slot's vote handler. Immediate gossip and Python's delay
consideration require the honest client to order a ready block before an
attestation at that boundary. A permanently finalized-conflicting block is
the only exemption, evaluated at `boundary - 1` as in `DeadlineBlockRelay`.
Both source and receiver seconds are explicit and
distinct; this does not assert same-second inter-node state equality. -/
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
/-- Evidence held by an honest node at or before the slot deadline reaches
every honest node by the next boundary. Slashing gossip takes at most positive
Δ, and strict `A + Δ < S` puts delivery before that boundary. Acceptance reads
only the slashable-data check and two indexed-attestation checks. These checks
read the attestations, signer pubkeys, and target-epoch domains. Pubkeys never
change. The genesis validators root is common, and this model has one fork,
so the domains are common.

The handler `on_attester_slashing` follows the Python and validates against
`store.block_states[store.justified_checkpoint.root]`. The relay field is a
premise, not a handler check: it states that every honest node holds the
indices by the next boundary. Literal Python can reject evidence at a node
whose justified state does not contain a signer. The premise matches clients
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

/-- Network synchrony — the FCR intro's assumption ("starting from the
current slot, attestations created by honest validators in any slot are
received by the end of that slot"), made operational, plus the block/message
propagation the spec leaves implicit (explicit in the paper's `Synchrony`
bundle). The fork choice's own `current_slot ≥ slot + 1` gate makes the first
second of slot `s+1` the earliest applicable processing time for a slot-`s`
      attestation. The exact relation to `NextSlotSynchronyPremises` is proved by
`synchrony_and_delivery_iff_nextSlot`. -/
structure Synchrony (E : Execution Root) : Prop where
  /-- The paper's timing parameter: a positive gossip delay `Δ` in
      milliseconds that fits after the attestation deadline, `A + Δ < S`.
      The delivery fields below state the network content at slot level. -/
  delta : ∃ delay_ms : ℕ,
    0 < delay_ms ∧
      get_attestation_due_ms cfg + delay_ms < cfg.slot_duration_ms
  /-- The honest vote deadline and positive Δ with strict `A + Δ < S`
      give receipt before the next slot. Honest clients retain early votes
      and process them at the first applicable slot start. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 →
    E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  /-- Deadline gossip with the pre-tick finalized-guard exemption. -/
  deadline_block_relay : DeadlineBlockRelay cfg ext E
  /-- Strict `A + Δ < S` and honest ready-message service put cutoff blocks
      before the next-slot vote handler; exclusion is tested before the tick. -/
  boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext E
  /-- Positive-Δ gossip and strict deadline fit give evidence by the next
      boundary from a cutoff holding time, with no exclusion. This is a premise:
      the literal justified-state check in `on_attester_slashing` can reject
      a signer that head-state clients accept (module note above). -/
  attester_slashing_relay : DeadlineAttesterSlashingRelay cfg ext E

/-- Verified envelopes are gossiped within positive Δ. The source cutoff and
strict `A + Δ < S` put them before the next slot. Honest clients delay a
handler until its block is known and process the ready envelope before a
boundary vote. The exact finalized-guard exemption is evaluated before the
tick, as in `DeadlineBlockRelay`; late and parent-missing blocks are not exempt.
The service occurrence and the vote prefix refer to the same envelope event. -/
def DeadlineEnvelopeDelivery (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    is_payload_verified (E.store cfg ext v n) r = true →
    r ∈ (E.store cfg ext v n).block_roots →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_start cfg (E.slot_at cfg n + 1) ≤ m → n < m →
      PermanentBlockExclusion cfg ext E v n r w
        (E.slot_start cfg (E.slot_at cfg n + 1) - 1) ∨
      ∃ (d k : ℕ) (signed : SignedExecutionPayloadEnvelope Root)
        (sourceObservation receiverObservation : EnvelopeObservation Root)
        (before after : List (Event Root)),
        n < d ∧ d ≤ m ∧
        E.slot_start cfg (E.slot_at cfg n + 1) ≤ d ∧ k ≤ n ∧
        Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k ∧
        signed.message.beacon_block_root = r ∧
        ext.is_data_available r sourceObservation = true ∧
        ext.verify_execution_payload_envelope
          ((E.store cfg ext v n).block_states r) signed sourceObservation = true ∧
        E.schedule w d = before ++
          Event.execution_payload_envelope signed receiverObservation :: after ∧
        r ∈ (before.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w (d - 1))
            (E.time_at d))).block_roots ∧
        (d = E.slot_start cfg (E.slot_at cfg n + 1) →
          ∀ (a : Attestation Root) (pre suf : List (Event Root)),
            E.schedule w d = pre ++ Event.attestation a false :: suf →
            ∃ middle : List (Event Root),
              pre = before ++
                Event.execution_payload_envelope signed receiverObservation :: middle)

/-- Available envelope data follows the same positive-Δ gossip bound and
source deadline. Honest data service makes it available at the receiver's
corresponding envelope observation after the next slot start. This remains
an explicit data-service contract; block receipt alone does not prove data
availability. Both observations are at distinct execution seconds. -/
def DeadlineDataAvailabilityRelay (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ k n (signed : SignedExecutionPayloadEnvelope Root)
      (sourceObservation : EnvelopeObservation Root),
    k ≤ n → E.WithinHorizon cfg n →
    Event.execution_payload_envelope signed sourceObservation ∈ E.schedule v k →
    ext.is_data_available signed.message.beacon_block_root sourceObservation = true →
    n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_start cfg (E.slot_at cfg n + 1) ≤ m → n < m →
      ∀ receiverSigned receiverObservation,
        receiverSigned.message.beacon_block_root = signed.message.beacon_block_root →
        Event.execution_payload_envelope receiverSigned receiverObservation ∈ E.schedule w m →
        ext.is_data_available signed.message.beacon_block_root receiverObservation = true

/-- The synchrony fragment used by the accepted spec next-slot proof.

The network content is in the delivery laws: honest-attestation delivery,
block relay, envelope delivery, data-availability relay, and
equivocation-evidence relay. `delta` records the paper's timing parameter: a
positive delay fits after the attestation deadline (`A + Δ < S`). The proofs
use the slot-level delivery laws, not the numeric delay. The exact relation to
`Synchrony` is proved by `synchrony_and_delivery_iff_nextSlot`. -/
structure NextSlotSynchronyPremises (E : Execution Root) : Prop where
  /-- The paper's timing parameter: a positive millisecond gossip delay
      `Δ` with the strict vote-to-next-slot bound `A + Δ < S`. -/
  delta : ∃ delay_ms : ℕ,
    0 < delay_ms ∧
      get_attestation_due_ms cfg + delay_ms < cfg.slot_duration_ms
  /-- Honest votes are sent by A. Positive-Δ gossip and strict fit give
      receipt before the next slot; the client then runs the vote handler. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 →
    E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  /-- Positive-Δ gossip from a cutoff observation, with strict fit and
      honest delay consideration. Only the pre-tick finalized guard exempts. -/
  deadline_block_relay : DeadlineBlockRelay cfg ext E
  /-- Strict `A + Δ < S` and honest ready-message service put cutoff blocks
      before the next-slot vote handler; exclusion is tested before the tick. -/
  boundary_block_prefix : DeadlineBoundaryBlockPrefix cfg ext E
  /-- Positive-Δ envelope gossip and strict fit give ready service before
      the boundary vote. The named contract has the pre-tick block exemption. -/
  envelope_delivery : DeadlineEnvelopeDelivery cfg ext E
  /-- Honest data service follows the same cutoff and positive-Δ bound;
      the receiver observation is at or after the next slot boundary. -/
  data_availability_relay : DeadlineDataAvailabilityRelay cfg ext E
  /-- Cutoff evidence gossip under positive Δ and strict fit, without an
      exclusion branch. A premise over the literal justified-state handler;
      see the module note on client evidence validation. -/
  attester_slashing_relay : DeadlineAttesterSlashingRelay cfg ext E

/-- One-slot operational closure for honest votes created inside the public
verification horizon.

This is the boundary case of the paper's synchrony premise.  The vote's slot
and creation time remain horizon-scoped; only its mandated receipt second may
be the first second of the immediately following epoch, just beyond the
exclusive public cutoff.  Keeping that receipt in the infinite execution
schedule avoids the impossible requirement that the cutoff contain its own
next epoch boundary. -/
structure HorizonVoteDeliveryLookahead (E : Execution Root) : Prop where
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))

end FastConfirmation.Spec

end
