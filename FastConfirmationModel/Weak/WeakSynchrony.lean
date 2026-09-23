module
public import FastConfirmationModel.Spec.FastConfirmation.Rule
public import FastConfirmationModel.Execution.Run

@[expose] public section

/-!
# Spec / Model / WeakSynchrony

Weak-synchrony variant of the FCR network model and rule (working note:
"Weakening the synchrony assumptions of FCR").

**Model delta.** The adversary controls or eclipses up to
`CONFIRMATION_BYZANTINE_THRESHOLD` of the stake; "honest" continues to mean
honest *and not eclipsed* (eclipsing a validator is weaker than controlling
it, so eclipsed validators are simply accounted inside the Byzantine budget).
Synchrony holds **between honest validators only**: a message produced by an
honest validator is received by every honest validator within the delay bound.
The `Synchrony`/`NextSlotSynchronyPremises` records in `Assumptions.lean` already
quantify senders/holders and receivers over `E.honest`, so they are reused
verbatim. The current weak safety statements allow any observer index,
including an honest one. Their premise bundle has no dedicated observer
delivery or propagation field. The older `ObserverContext` record below is a
historical helper that requires an observer outside `E.honest`; audited
witnesses do not use it.
Authenticity of its inbox still follows from the global records
(`WellFormedExecution`, `HonestBehavior.no_forgery`), which range over every
node's schedule. Non-validator relay nodes need no separate treatment: honest
to honest delivery is assumed as a property of the network as a whole.

**Broadcast certificates.** An observer's local possession of a block does
not by itself imply dissemination to honest nodes. The replacement evidence is a
*broadcast certificate*: observed attesting weight, in the committees of a
slot span, voting for a block or one of its descendants, exceeding the
maximum adversarial weight of that span. Any surplus vote must come from an
honest committee member, who therefore held the block's chain by its assigned
slot and whose (re)broadcast reaches every honest validator within the bound.
Only one surplus honest attester is needed — the certificate threshold is
`support > budget`, not a majority.

**Rule delta** (`Weak` namespace):
1. The store-evidence equivocation discount is dropped:
   `Weak.compute_adversarial_weight` does not subtract
   `get_equivocation_score`. The discount's soundness rested on
   `Synchrony.attester_slashing_relay` applied to the observer's evidence,
   which the weak model removes. Dropping it is monotonically stricter, hence
   safe; equivocators' votes remain excluded from support sums (also
   stricter). Re-enabling the improvement for slashings carried in a
   broadcast-certified block is possible later.
2. The previous-epoch advancement of `find_latest_confirmed_descendant`
   additionally requires a broadcast certificate for the justification
   witness (`fcr_store.previous_slot_head`, the block carrying the previous
   epoch's justification): `Weak.has_justification_witness_certificate`.
   The certificate for the *confirmed* blocks themselves is automatic:
   `is_one_confirmed`'s support threshold already exceeds the adversarial
   budget, so a one-confirmed block carries `support − budget > 0` honest
   attesters — the proofs should route their synchrony applications through
   that surplus rather than through the observer's own receipt.
3. `Weak.is_one_confirmed` and its empty-slot support discount count only
   **duty-fresh** recorded LMD cells (`Weak.is_duty_fresh_message`). A cell
   from the last completed epoch is admitted. A cell from the preceding epoch
   is also admitted until that validator has a completed duty in the newer
   epoch. Both sums use the same check, so an old parent vote cannot fund a
   discount after an unobserved replacement may support a competing child.
   This replaces the earlier epoch-wide cutoff without assuming delivery to
   the observer. The scan is bounded to the completed part of one epoch.
4. `get_certified_head` walks backwards from the actual fork-choice head to
   the newest known ancestor with a completed-slot broadcast certificate. The
   weak selector scans only as far as this carrier and reads its own unrealized
   justification. An uncertified current-slot head therefore does not block
   confirmation of its certified ancestors. If no certificate exists, the
   helper falls back to the actual head; certificate-dependent guards fail.
5. Epoch-start bookkeeping banks the selected carrier's own unrealized
   justification only when its epoch is strictly newer than the banked epoch,
   using the incoming balance source to check its certificate.
   The observed-restart guard also uses a certified carrier at the query's
   balance source. The actual slot-head fields and fork-choice targets retain
   their original meaning. No certificate for an ancestor is treated as a
   certificate for a newer block or its justification.

The full weak safety proof covers the actual-call trajectory and its stored
confirmation state. The endpoint scope and standing assumptions are unchanged
by carrier selection. See `docs/weak-synchrony.md` for the development history.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Historical helper for an observer outside `E.honest`. Audited weak safety
witnesses use an arbitrary observer index and do not use this record. -/
structure ObserverContext (E : Execution Root) where
  obs : ValidatorIndex
  obs_not_honest : obs ∉ E.honest

namespace Weak

/-- Weak-model `compute_adversarial_weight`: the maximum adversarial weight in
the committees of `[start_slot, end_slot]`, **without** the store-evidence
equivocation discount (see the module docstring, rule delta 1). The `_store`
parameter is kept for signature parity with the strong rule. -/
def compute_adversarial_weight (_store : Store Root) (balance_source : BeaconState Root)
    (start_slot end_slot : Slot) : Gwei :=
  let total_active_balance := get_total_active_balance cfg balance_source
  let maximum_weight :=
    estimate_committee_weight_between_slots cfg total_active_balance start_slot end_slot
  maximum_weight / 100 * cfg.confirmation_byzantine_threshold

/-- Weak-model `get_adversarial_weight` (as in `LMDHelpers`, over the
undiscounted budget). -/
def get_adversarial_weight (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let block := store.blocks block_root
  if get_block_epoch cfg store block_root > get_block_epoch cfg store block.parent_root then
    let start_slot := compute_start_slot_at_epoch cfg (get_block_epoch cfg store block_root)
    compute_adversarial_weight cfg store balance_source start_slot (current_slot - 1)
  else
    compute_adversarial_weight cfg store balance_source block.slot (current_slot - 1)

/-- The last completed epoch, used as the reference for duty-based freshness.
At the first slot of an epoch this is the previous epoch. Provenance places
recorded votes before the current slot. A cell from the preceding epoch may
also remain usable if its validator has no completed duty in this epoch; the
predicate below checks that condition explicitly. -/
def recorded_cutoff_epoch (store : Store Root) : Epoch :=
  compute_epoch_at_slot cfg (get_current_slot cfg store - 1)

/-- A recorded vote remains usable until a later-epoch duty has completed.
The last completed epoch is enough for a current cell. A previous-epoch cell
also remains usable if this validator has no assigned slot in the completed
part of that epoch. The scan covers at most one epoch and needs no message
arrival guarantee at the observer. -/
def is_duty_fresh_message (store : Store Root) (i : ValidatorIndex)
    (lm : LatestMessage Root) : Bool :=
  let cutoff := recorded_cutoff_epoch cfg store
  decide (cutoff ≤ get_latest_message_epoch cfg lm) ||
    (decide (get_latest_message_epoch cfg lm + 1 = cutoff) &&
      decide (i ∉ (Finset.Icc (compute_start_slot_at_epoch cfg cutoff)
        (get_current_slot cfg store - 1)).biUnion
          (fun s => get_slot_committee cfg ext store s)))

/-- Weak-model `get_attestation_score`: counts only **duty-fresh** cells. -/
def get_duty_fresh_attestation_score (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) : Gwei :=
  let unslashed_and_active_indices :=
    (get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)
  ((unslashed_and_active_indices.filter fun i =>
      match store.latest_messages i with
      | none => false
      | some latest_message =>
          decide (i ∉ store.equivocating_indices) &&
            is_duty_fresh_message cfg ext store i latest_message &&
            is_ancestor store (get_supported_node store latest_message) node)
    |>.map fun i => (state.validators.getD i default).effective_balance).sum

/-- Weak-model `get_block_support_between_slots`, duty-fresh (rule delta 3). -/
def get_duty_fresh_block_support_between_slots (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root)
    (start_slot end_slot : Slot) : Gwei :=
  let participants :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let unslashed_and_active_indices :=
    participants.filter (fun i =>
      !(balance_source.validators.getD i default).slashed &&
        is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source))
  ∑ i ∈ unslashed_and_active_indices.filter (fun i =>
      (store.latest_messages i).any (fun latest_message =>
        decide (latest_message.root = block_root) &&
          is_duty_fresh_message cfg ext store i latest_message &&
          decide (i ∉ store.equivocating_indices))),
    (balance_source.validators.getD i default).effective_balance

/-- Parent support for the child's required Gloas payload branch, with the
weak rule's duty-fresh filter. -/
def get_duty_fresh_parent_payload_support_between_slots (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root)
    (payload_status : PayloadStatus) (start_slot end_slot : Slot) : Gwei :=
  let participants :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let unslashed_and_active_indices :=
    participants.filter (fun i =>
      !(balance_source.validators.getD i default).slashed &&
        is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source))
  ∑ i ∈ unslashed_and_active_indices.filter (fun i =>
      (store.latest_messages i).any (fun latest_message =>
        decide (latest_message.root = block_root) &&
          is_duty_fresh_message cfg ext store i latest_message &&
          decide (i ∉ store.equivocating_indices) &&
          decide ((get_supported_node store latest_message).payload_status = payload_status ∨
            (get_supported_node store latest_message).payload_status = .pending))),
    (balance_source.validators.getD i default).effective_balance

/-- Weak-model `compute_empty_slot_support_discount` (as in `LMDHelpers`, over
the undiscounted budget, and duty-fresh — rule delta 3: a stale recorded
parent-pointing cell must not fund the discount, see the module docstring). -/
def compute_empty_slot_support_discount (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root) : Gwei :=
  let block := store.blocks block_root
  let parent_block := store.blocks block.parent_root
  if parent_block.slot + 1 = block.slot then
    0
  else
    let parent_support_in_empty_slots :=
      get_duty_fresh_parent_payload_support_between_slots cfg ext store balance_source
        block.parent_root (get_parent_payload_status store block)
        (parent_block.slot + 1) (block.slot - 1)
    let adversarial_weight :=
      compute_adversarial_weight cfg store balance_source
        (parent_block.slot + 1) (block.slot - 1)
    if parent_support_in_empty_slots > adversarial_weight then
      parent_support_in_empty_slots - adversarial_weight
    else
      0

/-- Weak-model `get_support_discount`. -/
def get_support_discount (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Gwei :=
  compute_empty_slot_support_discount cfg ext store balance_source block_root

/-- Weak-model `compute_safety_threshold` (as in `LMDHelpers`, over the
undiscounted budget). -/
def compute_safety_threshold (store : Store Root) (block_root : Root)
    (balance_source : BeaconState Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let block := store.blocks block_root
  let parent_block := store.blocks block.parent_root
  let total_active_balance := get_total_active_balance cfg balance_source
  let proposer_score := compute_proposer_score cfg balance_source
  let maximum_support :=
    estimate_committee_weight_between_slots cfg total_active_balance
      (parent_block.slot + 1) (current_slot - 1)
  let support_discount := get_support_discount cfg ext store balance_source block_root
  let adversarial_weight := get_adversarial_weight cfg store balance_source block_root
  if support_discount < maximum_support + proposer_score + 2 * adversarial_weight then
    (maximum_support + proposer_score + 2 * adversarial_weight - support_discount) / 2
  else
    0

/-- Weak-model `is_one_confirmed`. Note that a `true` result is itself a
broadcast certificate for `block_root`: the support exceeds a threshold at
least as large as the adversarial budget of the same span, so at least one
counted attester is honest. -/
def is_one_confirmed (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) : Bool :=
  let support :=
    get_duty_fresh_attestation_score cfg ext store (get_node_for_root block_root) balance_source
  let safety_threshold := compute_safety_threshold cfg ext store block_root balance_source
  decide (support > safety_threshold)

/-- Reconfirm the confirmed chain with the previous epoch balance source.
This transcribes Python `fast-confirmation.md:665-702` at `8036a74a1`.
The checkpoint ancestry test and the previous-epoch lower bound match Python;
each root is checked by the weak `is_one_confirmed` (`P:697-701`), with
duty-fresh support and no equivocation discount in the adversarial budget. -/
def is_confirmed_chain_safe (fcr_store : FastConfirmationStore Root)
    (confirmed_root : Root) : Bool :=
  let store := fcr_store.store
  if fcr_store.current_epoch_observed_justified_checkpoint ≠
      get_checkpoint_for_block cfg store confirmed_root
        fcr_store.current_epoch_observed_justified_checkpoint.epoch then
    false
  else
    let current_epoch := get_current_store_epoch cfg store
    let start_root_exclusive :=
      if fcr_store.current_epoch_observed_justified_checkpoint.epoch + 1 ≥ current_epoch then
        fcr_store.current_epoch_observed_justified_checkpoint.root
      else
        let ancestor_at_previous_epoch_start :=
          (get_ancestor store (get_node_for_root confirmed_root)
            (compute_start_slot_at_epoch cfg (current_epoch - 1))).root
        if get_block_epoch cfg store ancestor_at_previous_epoch_start + 1 = current_epoch then
          (store.blocks ancestor_at_previous_epoch_start).parent_root
        else
          ancestor_at_previous_epoch_start
    let chain_roots := get_ancestor_roots store confirmed_root start_root_exclusive
    chain_roots.all (fun root =>
      is_one_confirmed cfg ext store (get_previous_balance_source fcr_store) root)


/-- Weak-model `compute_honest_ffg_support_for_current_target` (as in
`FFGHelpers`, over the undiscounted budget). -/
def compute_honest_ffg_support_for_current_target (store : Store Root) : Gwei :=
  let current_slot := get_current_slot cfg store
  let current_epoch := compute_epoch_at_slot cfg current_slot
  let balance_source := get_pulled_up_head_state cfg ext store
  let total_active_balance := get_total_active_balance cfg balance_source
  let ffg_support_for_checkpoint := get_current_target_score cfg ext store
  let ffg_weight_till_now :=
    estimate_committee_weight_between_slots cfg total_active_balance
      (compute_start_slot_at_epoch cfg current_epoch) (current_slot - 1)
  let remaining_ffg_weight := total_active_balance - ffg_weight_till_now
  let remaining_honest_ffg_weight :=
    remaining_ffg_weight / 100 * (100 - cfg.confirmation_byzantine_threshold)
  let adversarial_weight :=
    compute_adversarial_weight cfg store balance_source
      (compute_start_slot_at_epoch cfg current_epoch) (current_slot - 1)
  let min_honest_ffg_support :=
    ffg_support_for_checkpoint - min adversarial_weight ffg_support_for_checkpoint
  min_honest_ffg_support + remaining_honest_ffg_weight

/-- Observed attesting weight certifying possession of `block_root`: the
weight of unslashed, active, non-equivocating members of the committees of
`[start_slot, end_slot]` whose latest message (i) was cast for a slot in the
span — their assigned slot in the message's epoch — and (ii) votes for
`block_root` or one of its descendants. Casting such a vote presupposes having
processed `block_root`'s chain by the vote's slot. -/
def get_broadcast_certificate_support (store : Store Root)
    (balance_source : BeaconState Root) (block_root : Root)
    (start_slot end_slot : Slot) : Gwei :=
  let participants :=
    (Finset.Icc start_slot end_slot).biUnion (fun slot => get_slot_committee cfg ext store slot)
  let unslashed_and_active_indices :=
    participants.filter (fun i =>
      !(balance_source.validators.getD i default).slashed &&
        is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source))
  ∑ i ∈ unslashed_and_active_indices.filter (fun i =>
      (store.latest_messages i).any (fun latest_message =>
        decide (i ∉ store.equivocating_indices) &&
          decide (∃ s ∈ Finset.Icc start_slot end_slot,
            i ∈ get_slot_committee cfg ext store s ∧
              get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
          is_ancestor store (get_node_for_root latest_message.root)
            (get_node_for_root block_root))),
    (balance_source.validators.getD i default).effective_balance

/-- Broadcast certificate for `block_root` over `[start_slot, end_slot]`:
observed possession-certifying support strictly exceeds the maximum
adversarial weight of the span. The surplus is honest weight — a single
surplus honest attester suffices for dissemination, so no majority is
required. -/
def has_broadcast_certificate (store : Store Root) (balance_source : BeaconState Root)
    (block_root : Root) (start_slot end_slot : Slot) : Bool :=
  if get_current_slot cfg store = 0 then false
  else
    let support :=
      get_broadcast_certificate_support cfg ext store balance_source block_root
        start_slot end_slot
    decide (support > compute_adversarial_weight cfg store balance_source start_slot end_slot)

/-- Search from newest to oldest on the head chain. The fuel bounds the
walk even on malformed stores. Only known ancestors can supply a certificate. -/
def certified_head_search (store : Store Root) (balance_source : BeaconState Root) :
    Nat → Root → Option Root
  | 0, _ => none
  | fuel + 1, root =>
    if root ∈ store.block_roots ∧
        is_ancestor store (get_head cfg store) (get_node_for_root root) = true ∧
        has_broadcast_certificate cfg ext store balance_source root
          (get_block_slot store root) (get_current_slot cfg store - 1) = true then
      some root
    else if get_block_slot store (store.blocks root).parent_root < get_block_slot store root then
      certified_head_search store balance_source fuel (store.blocks root).parent_root
    else none

/-- Newest certified ancestor of the fork-choice head. If there is no
certificate, retain the head as a total fallback; the certificate guard still
fails. The fallback keeps the epoch-start path and total store API unchanged. -/
def get_certified_head (store : Store Root) (balance_source : BeaconState Root) : Root :=
  (certified_head_search cfg ext store balance_source
    (get_block_slot store (get_head cfg store).root + 1)
    (get_head cfg store).root).getD (get_head cfg store).root

/-- Certificate for the selected head-chain carrier, with completed-slot
votes only. This does not assert that the actual fork-choice head is certified. -/
def has_head_broadcast_certificate (store : Store Root)
    (balance_source : BeaconState Root) : Bool :=
  let head := get_certified_head cfg ext store balance_source
  has_broadcast_certificate cfg ext store balance_source head
    (get_block_slot store head) (get_current_slot cfg store - 1)

/-- Trust a realized target only when it equals the certified carrier's own
unrealized justification. The global equality guard is retained for the
weak-to-strong predicate bridge; it cannot substitute for the carrier check. -/
def will_no_conflicting_checkpoint_be_justified (store : Store Root)
    (balance_source : BeaconState Root) : Bool :=
  if get_current_target cfg store = store.unrealized_justified_checkpoint ∧
      get_current_target cfg store = store.unrealized_justifications
        (get_certified_head cfg ext store balance_source) ∧
      has_head_broadcast_certificate cfg ext store balance_source then
    true
  else
    let state := get_pulled_up_head_state cfg ext store
    let total_active_balance := get_total_active_balance cfg state
    let honest_ffg_support := compute_honest_ffg_support_for_current_target cfg ext store
    decide (3 * honest_ffg_support > 1 * total_active_balance)

/-- Weak-model `will_current_target_be_justified`. -/
def will_current_target_be_justified (store : Store Root) : Bool :=
  let state := get_pulled_up_head_state cfg ext store
  let total_active_balance := get_total_active_balance cfg state
  let honest_ffg_support := compute_honest_ffg_support_for_current_target cfg ext store
  decide (3 * honest_ffg_support ≥ 2 * total_active_balance)

/-- Broadcast certificate for the justification witness: the block carrying
the previous epoch's justification (`fcr_store.previous_slot_head`), certified
over the span from its slot to the last completed slot. Certified votes end at
`current_slot − 1`, so every honest validator holds the witness chain before
casting any of the projected votes of the current slot onward. -/
def has_justification_witness_certificate (fcr_store : FastConfirmationStore Root) : Bool :=
  let store := fcr_store.store
  let witness := fcr_store.previous_slot_head
  has_broadcast_certificate cfg ext store (get_current_balance_source fcr_store) witness
    (get_block_slot store witness) (get_current_slot cfg store - 1)

/-- Bank only the selected certified carrier's own unrealized justification.
The certificate uses the incoming balance source, before any fields change.
Write only if that checkpoint has a strictly newer epoch, as in Python
`fast-confirmation.md:924-928` at `8036a74a1`. If the certificate fails or the
epoch is not newer, retain the existing banked checkpoint. The actual slot-head
fields, previous-epoch rotation, and legacy global-maximum snapshot retain
their original writes. The legacy snapshot is not consumed by weak banking.

The accepted FFG contracts place each known block's unrealized justification
on that block's own ancestry. The banking invariant therefore stores the
supplier, its exact certificate, and the checkpoint read from that supplier.
It does not claim that the actual fork-choice head has been disseminated. -/
def update_fast_confirmation_variables (fcr_store : FastConfirmationStore Root) :
    FastConfirmationStore Root :=
  let store := fcr_store.store
  let bs := get_current_balance_source fcr_store
  -- Update prev and curr slot head (unconditional, as in the strong rule)
  let fcr_store :=
    { fcr_store with
      previous_slot_head := fcr_store.current_slot_head
      current_slot_head := (get_head cfg store).root }
  -- Update greatest unrealized justified checkpoint at the last slot of an
  -- epoch. Keep a separate epoch-start copy for the weak reset below.
  let fcr_store :=
    if is_start_slot_at_epoch cfg (get_current_slot cfg store + 1) then
      { fcr_store with
        previous_epoch_greatest_unrealized_checkpoint :=
          store.unrealized_justified_checkpoint }
    else fcr_store
  -- Update observed justified checkpoints at the start of an epoch; the
  -- current-epoch write is gated on a broadcast certificate for the supplier
  -- and banks that supplier's *own* unrealized justification
  if is_start_slot_at_epoch cfg (get_current_slot cfg store) then
    { fcr_store with
      current_epoch_greatest_unrealized_checkpoint :=
        fcr_store.previous_epoch_greatest_unrealized_checkpoint
      previous_epoch_observed_justified_checkpoint :=
        fcr_store.current_epoch_observed_justified_checkpoint
      current_epoch_observed_justified_checkpoint :=
        if has_head_broadcast_certificate cfg ext store bs then
          let certified_checkpoint :=
            store.unrealized_justifications (get_certified_head cfg ext store bs)
          if certified_checkpoint.epoch >
              fcr_store.current_epoch_observed_justified_checkpoint.epoch then
            certified_checkpoint
          else fcr_store.current_epoch_observed_justified_checkpoint
        else fcr_store.current_epoch_observed_justified_checkpoint }
  else fcr_store

/-- Weak-model previous-epoch advancement loop (as in `Confirmation`, over the
weak `is_one_confirmed`). -/
def find_latest_confirmed_descendant_prev_epoch_loop
    (fcr_store : FastConfirmationStore Root) (current_epoch : Epoch) :
    List Root → Root → Root
  | [], confirmed_root => confirmed_root
  | block_root :: rest, confirmed_root =>
    let store := fcr_store.store
    let block_epoch := get_block_epoch cfg store block_root
    if block_epoch = current_epoch then
      confirmed_root
    else if ¬ is_ancestor store (get_node_for_root fcr_store.previous_slot_head)
        (get_node_for_root block_root) then
      confirmed_root
    else if ¬ is_one_confirmed cfg ext store (get_current_balance_source fcr_store)
        block_root then
      confirmed_root
    else
      find_latest_confirmed_descendant_prev_epoch_loop fcr_store current_epoch
        rest block_root

/-- Weak-model tentative advancement loop (as in `Confirmation`, over the weak
predicates). -/
def find_latest_confirmed_descendant_tentative_loop
    (fcr_store : FastConfirmationStore Root) :
    List Root → Root → Root
  | [], tentative_confirmed_root => tentative_confirmed_root
  | block_root :: rest, tentative_confirmed_root =>
    let store := fcr_store.store
    let block_epoch := get_block_epoch cfg store block_root
    let tentative_confirmed_epoch := get_block_epoch cfg store tentative_confirmed_root
    if block_epoch > tentative_confirmed_epoch ∧
        ¬ will_current_target_be_justified cfg ext store then
      tentative_confirmed_root
    else if ¬ is_one_confirmed cfg ext store (get_current_balance_source fcr_store)
        block_root then
      tentative_confirmed_root
    else
      find_latest_confirmed_descendant_tentative_loop fcr_store rest block_root

/-- Scan the chain up to the newest certified ancestor of the actual head.
Each justification-dependent entry guard reads that carrier's own checkpoint
and certificate. The previous-slot witness remains a separate source with its
own certificate and ancestry guard. Epoch-start entry retains its original
escape; when no carrier is certified, the total fallback is the actual head. -/
def find_latest_confirmed_descendant (fcr_store : FastConfirmationStore Root)
    (latest_confirmed_root : Root) : Root :=
  let store := fcr_store.store
  let head := get_certified_head cfg ext store (get_current_balance_source fcr_store)
  let current_epoch := get_current_store_epoch cfg store
  let bs := get_current_balance_source fcr_store
  let confirmed_root := latest_confirmed_root
  let confirmed_root :=
    if get_block_epoch cfg store confirmed_root + 1 = current_epoch ∧
        (get_voting_source cfg store fcr_store.previous_slot_head).epoch + 2 ≥
          current_epoch ∧
        has_justification_witness_certificate cfg ext fcr_store ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
          (will_no_conflicting_checkpoint_be_justified cfg ext store bs ∧
            ((store.unrealized_justifications fcr_store.previous_slot_head).epoch + 1 ≥
                current_epoch ∨
              ((store.unrealized_justifications head).epoch + 1 ≥ current_epoch ∧
                has_head_broadcast_certificate cfg ext store bs)))) then
      let canonical_roots := get_ancestor_roots store head confirmed_root
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store current_epoch
        canonical_roots confirmed_root
    else confirmed_root
  if is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
      ((store.unrealized_justifications head).epoch + 1 ≥ current_epoch ∧
        has_head_broadcast_certificate cfg ext store bs) then
    let canonical_roots := get_ancestor_roots store head confirmed_root
    let tentative_confirmed_root :=
      find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
        canonical_roots confirmed_root
    if get_block_epoch cfg store tentative_confirmed_root = current_epoch ∨
        ((get_voting_source cfg store tentative_confirmed_root).epoch + 2 ≥
            current_epoch ∧
          (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∨
            will_no_conflicting_checkpoint_be_justified cfg ext store bs)) then
      tentative_confirmed_root
    else confirmed_root
  else confirmed_root

/-- Weak-model `get_latest_confirmed` (`P:1076-1132`, `8036a74a1`).
At epoch start, the revert-to-finalized branch uses the weak
`is_confirmed_chain_safe` (`P:1093-1098`), which reconfirms with the previous
balance source and weak `is_one_confirmed` (`P:697-701`). Namespace resolution
selects both this helper and the weak `find_latest_confirmed_descendant`.
The observed-checkpoint restart uses the certified carrier's own justification
and its broadcast certificate. -/
def get_latest_confirmed (fcr_store : FastConfirmationStore Root) : Root :=
  let store := fcr_store.store
  let confirmed_root := fcr_store.confirmed_root
  let current_epoch := get_current_store_epoch cfg store
  -- Revert to finalized block if the confirmed block is too old, is not
  -- canonical, or the confirmed chain cannot be re-confirmed at epoch start
  let head := (get_head cfg store).root
  let confirmed_root :=
    if get_block_epoch cfg store confirmed_root + 1 < current_epoch ∨
        ¬ is_ancestor store (get_node_for_root head) (get_node_for_root confirmed_root) ∨
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) ∧
          ¬ is_confirmed_chain_safe cfg ext fcr_store confirmed_root) then
      store.finalized_checkpoint.root
    else confirmed_root
  -- Restart the confirmation chain from the observed justified checkpoint
  -- when the epoch-start restart conditions are all met
  let is_epoch_start := is_start_slot_at_epoch cfg (get_current_slot cfg store)
  let observed_justified_block_slot :=
    get_block_slot store fcr_store.current_epoch_observed_justified_checkpoint.root
  let is_observed_justified_block_epoch_ok :=
    decide (compute_epoch_at_slot cfg observed_justified_block_slot + 1 = current_epoch)
  let is_head_unrealized_justified_ok :=
    decide (fcr_store.current_epoch_observed_justified_checkpoint =
      store.unrealized_justifications
        (get_certified_head cfg ext store (get_current_balance_source fcr_store))) &&
      has_head_broadcast_certificate cfg ext store (get_current_balance_source fcr_store)
  let is_confirmed_block_stale :=
    decide (get_block_slot store confirmed_root < observed_justified_block_slot)
  let confirmed_root :=
    if is_epoch_start && is_observed_justified_block_epoch_ok &&
        is_head_unrealized_justified_ok && is_confirmed_block_stale then
      fcr_store.current_epoch_observed_justified_checkpoint.root
    else confirmed_root
  -- Reject a chain that does not contain the greatest unrealized justified
  -- checkpoint saved at epoch start. Check the checkpoint at its epoch, not
  -- just its root: a skipped boundary can give another checkpoint root.
  let greatest := fcr_store.current_epoch_greatest_unrealized_checkpoint
  let confirmed_root :=
    if greatest ≠ get_checkpoint_for_block cfg store confirmed_root greatest.epoch then
      store.finalized_checkpoint.root
    else confirmed_root
  -- Attempt to further advance the latest confirmed block
  if get_block_epoch cfg store confirmed_root + 1 ≥ current_epoch then
    find_latest_confirmed_descendant cfg ext fcr_store confirmed_root
  else
    confirmed_root

/-- Weak-model `on_fast_confirmation` handler: runs the weak
`update_fast_confirmation_variables` (rule delta 5) then the weak
`get_latest_confirmed`, both picked up by namespace resolution as in
`get_latest_confirmed` above. -/
def on_fast_confirmation (fcr_store : FastConfirmationStore Root) :
    FastConfirmationStore Root :=
  let fcr_store := update_fast_confirmation_variables cfg ext fcr_store
  { fcr_store with confirmed_root := get_latest_confirmed cfg ext fcr_store }


end Weak

end FastConfirmation.Spec

end
