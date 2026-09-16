import FastConfirmation.Spec.Model.Execution

/-!
# Spec / Model / Assumptions

This module defines core `Prop`-valued assumption records over an `Execution`.
Their provenance is mixed: direct FCR and consensus-spec premises, paper
hypotheses instantiated over the executable spec model, and coherence
contracts for projected or abstracted beacon-chain functionality. The complete
accepted theorem bundle is assembled in
`AcceptedActualFCRNextSlotSafetyAssumptions`.

Division of labor: `HonestBehavior` says *what* honest validators' messages
look like (validator spec); `Synchrony` says *when* they arrive (the FCR
intro's assumption) — there is exactly **one** synchrony assumption, its
delivery clause covering the horizon's boundary vote as well, so the former
separate `HorizonVoteDeliveryLookahead` record is now the derived lemma
`Synchrony.toDeliveryLookahead`; `ExternalsCoherence`/`StaticValidatorSet` pin the
abstracted beacon-chain machinery; `ByzantineBound` is the
`CONFIRMATION_BYZANTINE_THRESHOLD` + committee-weight-estimation soundness
(the spec's own "high probability" 5‰ assumption, consumed, not derived).
Facts *derivable* from the dynamics (store monotonicity, ancestor-closure,
registry constancy along evolution) are deliberately **not** assumed — they
are proved from the execution semantics.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The trusted anchor state (of the genesis store's justified checkpoint —
how `get_forkchoice_store` seeds every state map). -/
def anchor_state : BeaconState Root :=
  E.genesis_store.block_states E.genesis_store.justified_checkpoint.root

/-- Ground-truth validator registry: the anchor state's. -/
def registry : List Validator :=
  (E.anchor_state).validators

/-- Ground-truth effective balance of validator `i`. -/
def weight_of (i : ValidatorIndex) : Gwei :=
  ((E.registry).getD i default).effective_balance

/-- Ground-truth total weight of a validator set. -/
def weight (s : Finset ValidatorIndex) : Gwei :=
  ∑ i ∈ s, E.weight_of i

/-- Ground-truth total active balance (the anchor state's). -/
def total_active : Gwei :=
  get_total_active_balance cfg E.anchor_state

/-- The (ground-truth) union of committees over the inclusive slot span
`[a, b]` — the object `get_block_support_between_slots` and
`compute_adversarial_weight` reason about. -/
def span_committee (a b : Slot) : Finset ValidatorIndex :=
  (Finset.Icc a b).biUnion E.committee

end Execution

/-- Execution-level well-formedness: wire block roots are genuine commitments.
Equal roots identify equal block messages across scheduled block events and the
genesis store. -/
structure WellFormedExecution (E : Execution Root) : Prop where
  blocks_root_injective : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n →
    ∀ w' n' (b' : SignedBeaconBlock Root), Event.block b' ∈ E.schedule w' n' →
      b.root = b'.root → b.message = b'.message
  genesis_blocks_agree : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n → b.root ∈ E.genesis_store.block_roots →
      b.message = E.genesis_store.blocks b.root
  /-- No scheduled block reuses the unresolved parent root of a genesis-store
      block. In the concrete protocol, a block root commits to its block, so a
      block at that root is the anchor's lower-slot parent and is rejected by
      `on_block`'s finalized-slot gate. This projection treats roots as data and
      omits the pre-anchor block, so the coherence fact is explicit. -/
  anchor_parent_unscheduled : ∀ r ∈ E.genesis_store.block_roots,
    ∀ w n (b : SignedBeaconBlock Root), Event.block b ∈ E.schedule w n →
      b.root ≠ (E.genesis_store.blocks r).parent_root

/-- Honest validator behavior (validator.md "Attesting", plus the
no-equivocation/no-forgery discipline the slashing rules enforce). -/
structure HonestBehavior (E : Execution Root) : Prop where
  /-- vote-your-head: an honest validator assigned to slot `s` casts, at a
      voting second within slot `s`, exactly the validator-spec attestation
      computed from its own store at that second. -/
  votes_head : ∀ v ∈ E.honest, ∀ s : Slot, v ∈ E.committee s →
    E.SlotWithinHorizon cfg s →
    E.slot_at cfg 0 ≤ s →
    ∃ n index, E.WithinHorizon cfg n ∧ E.slot_at cfg n = s ∧
      E.vote v s =
        some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v)
  /-- honest validators vote only for slots they are assigned to. -/
  votes_assigned : ∀ v ∈ E.honest, ∀ s : Slot,
    E.vote v s ≠ none → v ∈ E.committee s
  /-- no forgery / no equivocation: every attestation naming an honest
      validator, anywhere in any node's schedule, carries the data of that
      validator's own recorded vote for that slot (BLS unforgeability + the
      attester-slashing discipline). -/
  no_forgery : ∀ w : ValidatorIndex, ∀ n : ℕ, ∀ (a : Attestation Root)
      (is_from_block : Bool),
    Event.attestation a is_from_block ∈ E.schedule w n →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  /-- honest votes are pairwise non-slashable ("How to avoid slashing",
      validator.md — honest source epochs are monotone in target epochs, so
      no double or surround vote): without this a surround pair of genuine
      honest votes would enable an `on_attester_slashing` that erases the
      validator's LMD weight. -/
  not_slashable : ∀ v ∈ E.honest, ∀ s s' : Slot, ∀ n n' : ℕ,
    ∀ a a' : Attestation Root,
    E.vote v s = some (n, a) → E.vote v s' = some (n', a') →
      is_slashable_attestation_data a.data a'.data = false
  /-- Honest validators are unslashed in the ground-registry snapshot; the
      honest set excludes validators with prior slashable offenses. -/
  honest_unslashed : ∀ v ∈ E.honest, (E.registry.getD v default).slashed = false

/-- Network synchrony — the FCR intro's assumption ("starting from the
current slot, attestations created by honest validators in any slot are
received by the end of that slot"), made operational, plus the block/message
propagation the spec leaves implicit (explicit in the paper's `Synchrony`
bundle). The fork choice's own `current_slot ≥ slot + 1` gate makes the first
second of slot `s+1` the earliest applicable processing time for a slot-`s`
attestation. -/
structure Synchrony (E : Execution Root) : Prop where
  /-- honest attestations of slot `s` are processed by every honest node at
      the first second of slot `s+1`.

      The *vote* is horizon-scoped — its slot and its creation second both lie
      inside the public verification horizon — but the mandated receipt second
      is not gated: it is named in the (infinite) execution schedule. For a
      vote cast in the horizon's last slot that receipt is the first second of
      the following epoch, just past the exclusive cutoff, which no
      receipt-gated phrasing can name; the cutoff cannot be asked to contain
      its own next epoch boundary.

      **This one field is exactly the old pair.** It is the conjunction of the
      previous receipt-gated clause (recovered verbatim by
      `Synchrony.toHorizonScopedDelivery`) and the previous separate boundary
      record `HorizonVoteDeliveryLookahead` (recovered verbatim by
      `Synchrony.toDeliveryLookahead`); `attestation_delivery_pair_iff` proves
      that conjunction and this field are the same proposition, so merging the
      two assumptions added no content. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  /-- blocks known to an honest node propagate by the **end of the same
      slot**: anything in `v`'s block set at a second of slot `s` is in every
      honest node's block set from the last second of slot `s` on — in
      particular *before* the first second of slot `s+1`, so that second's
      attestation fold finds the referenced blocks already known
      (`validate_on_attestation`'s known-block asserts). The `m+1` clock read is
      only the arithmetic characterization of "last second of the slot"; no
      execution-state assumption is made at `m+1`, so the endpoint itself (not
      its successor) is the horizon-scoped state. -/
  block_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      r ∈ (E.store cfg ext w m).block_roots
  /-- LMD messages relay: a latest message recorded by an honest node is,
      from the next slot on, recorded (or dominated by a newer one) at every
      honest node. -/
  latest_message_relay : ∀ v ∈ E.honest, ∀ n i (msg : LatestMessage Root),
    E.WithinHorizon cfg n →
    (E.store cfg ext v n).latest_messages i = some msg →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
      ∃ msg', (E.store cfg ext w m).latest_messages i = some msg' ∧
        msg.epoch ≤ msg'.epoch
  /-- Equivocation evidence known to an honest node is known to every honest
      node from the next slot onward. Attester slashings gossip and may be
      carried in blocks through `on_attester_slashing`; the safety argument
      requires all honest nodes to exclude the same detected equivocators. -/
  attester_slashing_relay : ∀ v ∈ E.honest, ∀ n (i : ValidatorIndex),
    E.WithinHorizon cfg n →
    i ∈ (E.store cfg ext v n).equivocating_indices →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
    E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
    i ∈ (E.store cfg ext w m).equivocating_indices

/-- The synchrony fragment used by the accepted spec next-slot proof.

The accepted next-slot argument needs honest-attestation delivery, block relay,
and equivocation-evidence relay. It does not use the additional
`latest_message_relay` field of the full `Synchrony` bundle. -/
structure PaperSafetySynchrony (E : Execution Root) : Prop where
  /-- Same single delivery clause as `Synchrony.attestation_delivery`: the
      vote is horizon-scoped, its mandated receipt second is named in the
      execution schedule without a horizon gate, and the field is exactly the
      old receipt-gated clause together with the old
      `HorizonVoteDeliveryLookahead`. -/
  attestation_delivery : ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
    E.SlotWithinHorizon cfg s →
    E.WithinHorizon cfg n →
    E.vote v s = some (n, a) →
    ∀ w ∈ E.honest,
      Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1))
  block_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    r ∈ (E.store cfg ext v n).block_roots →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      r ∈ (E.store cfg ext w m).block_roots
  attester_slashing_relay : ∀ v ∈ E.honest, ∀ n (i : ValidatorIndex),
    E.WithinHorizon cfg n →
    i ∈ (E.store cfg ext v n).equivocating_indices →
    ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
    E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
    i ∈ (E.store cfg ext w m).equivocating_indices

/-- Every full `Synchrony` witness supplies the narrower accepted-proof
fragment. -/
def Synchrony.toPaperSafetySynchrony
    (h : Synchrony cfg ext E) : PaperSafetySynchrony cfg ext E where
  attestation_delivery := h.attestation_delivery
  block_relay := h.block_relay
  attester_slashing_relay := h.attester_slashing_relay

instance : Coe (Synchrony cfg ext E) (PaperSafetySynchrony cfg ext E) where
  coe := Synchrony.toPaperSafetySynchrony cfg ext

/-! ### The delivery clause equals the old horizon-gated/boundary pair

Before the merge the model carried two synchrony assumptions: the
receipt-gated `attestation_delivery` clause of `Synchrony` /
`PaperSafetySynchrony`, and a separate one-field record
`HorizonVoteDeliveryLookahead` whose sole purpose was the boundary case (a
vote cast in the horizon's last slot has its mandated receipt second just past
the exclusive cutoff, which the gated phrasing cannot name).  The single
merged clause above is *literally* that pair: the theorem below proves the
conjunction of the two old propositions is the same proposition as the new
field, and the two `to…` lemmas recover each old form verbatim. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **No new assumption content.** The conjunction of the old receipt-gated
delivery clause and the old `HorizonVoteDeliveryLookahead.attestation_delivery`
is exactly the merged `attestation_delivery` field: the gated conjunct is the
merged clause with a hypothesis discarded, and the boundary conjunct is the
merged clause verbatim. -/
theorem attestation_delivery_pair_iff (E : Execution Root) :
    ((∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1))) ∧
      (∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1)))) ↔
      (∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1))) := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun v hv s n a hs hn hvote _ => h v hv s n a hs hn hvote, h⟩

/-- The old receipt-gated delivery clause, derived from the merged one by
discarding the receipt-side horizon hypothesis. -/
theorem PaperSafetySynchrony.toHorizonScopedDelivery
    {E : Execution Root} (h : PaperSafetySynchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  fun v hv s n a hs hn hvote _ => h.attestation_delivery v hv s n a hs hn hvote

/-- The old `HorizonVoteDeliveryLookahead` boundary clause — now a special
case of the merged delivery field rather than a separate assumption. -/
theorem PaperSafetySynchrony.toDeliveryLookahead
    {E : Execution Root} (h : PaperSafetySynchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  h.attestation_delivery

/-- The old receipt-gated delivery clause, from the full synchrony bundle. -/
theorem Synchrony.toHorizonScopedDelivery
    {E : Execution Root} (h : Synchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  (h.toPaperSafetySynchrony cfg ext).toHorizonScopedDelivery cfg ext

/-- The old boundary clause, from the full synchrony bundle. -/
theorem Synchrony.toDeliveryLookahead
    {E : Execution Root} (h : Synchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  h.attestation_delivery

/-- Coherence facts about the abstract `Externals`, true of the real
beacon-chain functions they stand for (registry/slot behavior of the state
transition; shuffling agreement with the ground-truth assignment — the spec's
own `MAX_SEED_LOOKAHEAD` consistency note; validity of honestly constructed
attestations). -/
structure ExternalsCoherence (E : Execution Root) : Prop where
  /-- `process_slots` targets its slot and preserves the registry. -/
  process_slots_slot : ∀ st (s : Slot), st.slot < s → (ext.process_slots st s).slot = s
  process_slots_registry : ∀ st s, (ext.process_slots st s).validators = st.validators
  /-- a valid state transition lands on the block's slot and preserves the
      registry (no deposits/exits in the window — the static-set idealization,
      spec's own balance-source design note). -/
  state_transition_slot : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st'.slot = b.message.slot
  state_transition_registry : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st'.validators = st.validators
  /-- a valid state transition requires the pre-state to precede the block's
      slot (the real `process_slots` assert inside `state_transition`) —
      gives Layer 0 the parent-slot ordering `WellFormedStore` preservation
      needs. -/
  state_transition_pre_slot_lt : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' → st.slot < b.message.slot
  /-- checkpoint-chain coherence of the abstract state transition: the
      checkpoints a post-state carries have epochs at most the block's
      epoch (the real epoch processing justifies only past-epoch targets;
      full chain-position coherence — roots on the block's ancestor chain —
      is added when the proof consumes it). -/
  state_transition_checkpoint_epoch : ∀ st (b : SignedBeaconBlock Root) st',
    ext.state_transition st b = some st' →
      st'.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg b.message.slot ∧
      st'.finalized_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot
  /-- Epoch processing adopts no future checkpoint: the new justified
      checkpoint's epoch is at most the state's epoch. This is the pull-up
      counterpart of `state_transition_checkpoint_epoch`; the concrete epoch
      processing considers only current- and previous-epoch targets. -/
  pjf_checkpoint_epoch : ∀ st : BeaconState Root,
    (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot
  /-- the store-computed slot committees agree with the ground-truth
      assignment on every honest store (the spec's committee-consistency
      window, idealized to the verified execution prefix). -/
  committees_agree : ∀ v ∈ E.honest, ∀ n (s : Slot),
    E.WithinHorizon cfg n → E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s
  /-- honestly *cast* singleton attestations pass the abstract
      index/signature validity check (restricted to data the validator
      actually signed — an unrestricted version would force fabricated data
      naming honest validators to validate, handing forged slashings to the
      adversary). -/
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  /-- BLS soundness (the converse): a validating attestation naming an honest
      validator carries data that validator actually signed — no forged
      slashings against honest validators. -/
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  /-- committee confinement: validating attestations carry only indices from
      the slot's committee (in the real pipeline `get_indexed_attestation`
      derives indices from the committee and aggregation bits — absorbed into
      the wire object, so the constraint is restored here; confines LMD
      supporters to the spans `ByzantineBound` budgets). -/
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot
  /-- the beacon chain assigns each validator to exactly one slot per epoch
      (`get_committee_assignment` uniqueness — a structural fact of the
      shuffling): two assigned slots in the same epoch coincide. -/
  committee_assignment_unique : ∀ (i : ValidatorIndex) (s s' : Slot),
    i ∈ E.committee s → i ∈ E.committee s' →
    compute_epoch_at_slot cfg s = compute_epoch_at_slot cfg s' → s = s'
  /-- Every active validator has a committee assignment in each in-horizon
      epoch. Together with `committee_assignment_unique`, this states that
      `get_beacon_committee` partitions the epoch's active validators across
      its slots. -/
  committee_coverage : ∀ (i : ValidatorIndex) (e : Epoch),
    e < E.verification_horizon →
    is_active_validator (E.registry.getD i default) e = true →
      ∃ s : Slot, E.SlotWithinHorizon cfg s ∧
        compute_epoch_at_slot cfg s = e ∧ i ∈ E.committee s
  /-- Committee members are active validators. The beacon-chain shuffling
      draws committees from the epoch's active set; cross-epoch stability is
      supplied by `StaticValidatorSet.activity_constant`. -/
  committee_members_active : ∀ (i : ValidatorIndex) (s : Slot),
    E.SlotWithinHorizon cfg s →
    i ∈ E.committee s →
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot cfg s) = true

/-- The static-validator-set idealization over the verified execution segment.
The trusted genesis initialization itself seeds registry constancy
mechanically; this record carries only the horizon and activity facts that are
not consequences of `get_forkchoice_store`. -/
structure StaticValidatorSet (cfg : Config) (E : Execution Root) : Prop where
  /-- The trusted anchor itself belongs to the verified uint64 segment, so the
      public conclusion domain cannot be empty merely because the chosen
      horizon predates initialization. -/
  genesis_within_horizon : E.WithinHorizon cfg 0
  /-- Paper Assumption 1, restricted to the concrete execution segment: the
      active validator set is constant at epochs below the exclusive
      verification horizon. This places no finite upper bound on the
      execution's unbounded `ℕ` clock. -/
  activity_constant : ∀ i : ValidatorIndex, ∀ e e' : Epoch,
    e < E.verification_horizon → e' < E.verification_horizon →
      is_active_validator (E.registry.getD i default) e =
        is_active_validator (E.registry.getD i default) e'
/-- Horizon-bounded activity constancy specialized to epochs no later than
execution-clock epochs. The caller-supplied clock bounds put both epochs below
`E.verification_horizon`. -/
theorem StaticValidatorSet.activity_constant_of_epoch_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {e e' : Epoch} {n n' : ℕ}
    (he : e ≤ compute_epoch_at_slot cfg (E.slot_at cfg n))
    (he' : e' ≤ compute_epoch_at_slot cfg (E.slot_at cfg n'))
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) e =
      is_active_validator (E.registry.getD i default) e' := by
  exact hsv.activity_constant i e e'
    (lt_of_le_of_lt he hn) (lt_of_le_of_lt he' hn')

/-- Slot form of `activity_constant_of_epoch_le`: slots bounded by execution
clock slots have activity-equivalent epochs. -/
theorem StaticValidatorSet.activity_constant_of_slot_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {s s' : Slot} {n n' : ℕ}
    (hs : s ≤ E.slot_at cfg n) (hs' : s' ≤ E.slot_at cfg n')
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s) =
      is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s') :=
  hsv.activity_constant_of_epoch_le (cfg := cfg)
    (Nat.div_le_div_right hs) (Nat.div_le_div_right hs') hn hn'

/-- The economic assumptions: the `CONFIRMATION_BYZANTINE_THRESHOLD` bound and
the committee-weight-estimation soundness — both against the ground truth,
both exactly the spec's own stated assumptions (the estimation soundness is
the "high probability" claim behind
`COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR`; see the spec's gist link). -/
structure ByzantineBound (E : Execution Root) : Prop where
  /-- Effective balances used by the economic model are phase0-quantized.
      This is an executable registry invariant, not part of the probabilistic
      committee estimate.  Out-of-range totalized reads have weight zero. -/
  effective_balance_quantized : ∀ i : ValidatorIndex,
    cfg.effective_balance_increment ∣ E.weight_of i
  /-- The spec-level high-probability committee estimate: the actual span
      weight does not exceed `estimate_committee_weight_between_slots`.
      The stronger post-`//100` inequality used by the arithmetic is derived
      from this field and effective-balance quantization in
      `Proof/EconomicRounding.lean`. -/
  estimate_sound : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    E.weight (E.span_committee a b) ≤
      estimate_committee_weight_between_slots cfg (E.total_active cfg) a b
  /-- Per-span Byzantine *fraction* bound (the paper's Assumption 2 at the spec's own design point
      `β = CONFIRMATION_BYZANTINE_THRESHOLD / 100`): in every slot span's
      committee union the non-honest weight is at most `β` of the whole,
      cross-multiplied to avoid division:
      `100 · byz(span) ≤ CONFIRMATION_BYZANTINE_THRESHOLD · W(span)`. Ground
      truth, uniform over spans — no `a ≤ b` guard, empty spans are trivially
      `0 ≤ 0`; same committee-sampling concentration family as `span_bound`.
      The proof uses both per-slot (`[t,t]`) and per-window instances. -/
  span_fraction : ∀ a b : Slot,
    E.SlotWithinHorizon cfg a → E.SlotWithinHorizon cfg b →
    100 * E.weight ((E.span_committee a b).filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold *
        E.weight (E.span_committee a b)

end FastConfirmation.Spec
