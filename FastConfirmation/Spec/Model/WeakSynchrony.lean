import FastConfirmation.Spec.Model.Confirmation
import FastConfirmation.Spec.Model.Assumptions

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
The `Synchrony`/`PaperSafetySynchrony` records in `Assumptions.lean` already
quantify senders/holders and receivers over `E.honest`, so they are reused
verbatim. The entire network-model change is that the observer running the FCR
is **not** a member of `E.honest`: it is an inbox — no delivery is guaranteed
*to* it, and nothing it holds is guaranteed to propagate *from* it.
Authenticity of its inbox still follows from the global records
(`WellFormedExecution`, `HonestBehavior.no_forgery`), which range over every
node's schedule. Non-validator relay nodes need no separate treatment: honest
to honest delivery is assumed as a property of the network as a whole.

**Broadcast certificates.** With the observer outside `E.honest`, its local
possession of a block no longer implies dissemination (`Synchrony.block_relay`
no longer applies to it as a holder). The replacement evidence is a
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
4. The previous-epoch and tentative advancement disjuncts of
   `find_latest_confirmed_descendant` that read an *unrealized* justification
   (as opposed to the already-gated witness-certificate read above) each
   additionally require `Weak.has_head_broadcast_certificate`: a broadcast
   certificate on the fork-choice head, over the span from the head's slot to
   the last completed slot. Possessing a block implies possessing its
   ancestry, so a certificate on the head dominates the deeper carrier that
   actually formed the justification. `Weak.will_no_conflicting_checkpoint_be_justified`
   is gated the same way, at its own short-circuit. See
   `docs/weak-synchrony.md` for the full site sweep and the findings this
   delta records but does not close.
5. `Weak.update_fast_confirmation_variables` (*certified bookkeeping*) gates
   the epoch-start installation of the current-epoch observed justified
   checkpoint — the key `get_current_balance_source` reads, and hence the key
   every other weak certificate in the call is evaluated against — on
   `Weak.has_head_broadcast_certificate` for the fork-choice head at update
   time, **and banks the certified head's own unrealized justification**
   (`store.unrealized_justifications (get_head store).root`) rather than the
   store-global running maximum
   (`fcr_store.previous_epoch_greatest_unrealized_checkpoint`, which keeps its
   ungated writes for parity with the strong rule but is no longer consumed by
   the weak banking). Banking only a justification observed *through* the
   certified block makes coverage of the banked value by the head certificate
   chain-intrinsic. If the gate fails the field keeps its previous
   (already-certified) value: stale-but-certified beats fresh-but-uncertified,
   so this is monotonically stricter than the strong rule and hence
   safety-free. Every other write of the strong function is unconditional, as
   before. See `docs/weak-synchrony.md`, "Rule delta 5", for the liveness cost
   and `Weak.CertifiedBankedJustification` for the resulting input invariant.

Stored-state maintenance across epochs (the revert-to-finalized and
epoch-start restart branches of `get_latest_confirmed`, and
`is_confirmed_chain_safe`) is deliberately out of scope here: the weak model
currently targets the one-shot confirmation case. See
`docs/weak-synchrony.md` for the proof-migration plan.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The confirming observer of the weak model: a node that runs the FCR over
its own store but is *not* an honest network participant. No synchrony law
applies to it — messages reach it only as the adversary and the schedule
permit, and nothing in its store is guaranteed to have propagated. It needs a
synchronized clock and an authentic inbox, both of which are inherited from
the global execution records rather than from `E.honest` membership. -/
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
  decide (cutoff ≤ get_latest_message_epoch lm) ||
    (decide (get_latest_message_epoch lm + 1 = cutoff) &&
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
      get_duty_fresh_block_support_between_slots cfg ext store balance_source block.parent_root
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
              get_latest_message_epoch latest_message = compute_epoch_at_slot cfg s) &&
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
  let support :=
    get_broadcast_certificate_support cfg ext store balance_source block_root
      start_slot end_slot
  decide (support > compute_adversarial_weight cfg store balance_source start_slot end_slot)

/-- Broadcast certificate for the fork-choice head, over the span from its
slot to the last completed slot. Possessing a block implies possessing its
ancestry, so a certificate on the block whose `unrealized_justifications` entry
the rule reads dominates the deeper carrier that actually formed the
justification — no certificate on the carrier is required (rule delta 4). -/
def has_head_broadcast_certificate (store : Store Root)
    (balance_source : BeaconState Root) : Bool :=
  let head := (get_head cfg store).root
  has_broadcast_certificate cfg ext store balance_source head
    (get_block_slot store head) (get_current_slot cfg store - 1)

/-- Weak-model `will_no_conflicting_checkpoint_be_justified`, gated by a
broadcast certificate on the fork-choice head (rule delta 4): the short-circuit
that the current target already matches the unrealized justified checkpoint is
only trusted once the head is certified as disseminated. -/
def will_no_conflicting_checkpoint_be_justified (store : Store Root)
    (balance_source : BeaconState Root) : Bool :=
  if get_current_target cfg store = store.unrealized_justified_checkpoint ∧
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

/-- Weak-model `update_fast_confirmation_variables` (rule delta 5, *certified
bookkeeping*).  Identical to the strong rule except for **one** write: the
epoch-start installation of the current-epoch observed justified checkpoint —
the key `get_current_balance_source` reads, and hence the key every other weak
certificate in the call is evaluated against — happens only when the block
supplying that justification is broadcast-certified, **and it banks that
block's own unrealized justification**.

*Bank only a justification observed in a certified block.* The supplier is the
fork-choice head at update time, and what is banked is
`store.unrealized_justifications (get_head store).root` — the justification
observed *through* the certified block — not the store-global running maximum
`fcr_store.previous_epoch_greatest_unrealized_checkpoint`.  With the
store-global value, coverage of the banked checkpoint by the head certificate
was an extrinsic claim, and a false one: between the second at which the
running maximum was captured (the end of the previous epoch) and the boundary
at which the gate fires, the store's checkpoints may move to a different
branch, so the certified head need not descend from the banked root at all
(the branch-switch hole recorded in `WeakBankedJustification.lean`).  Reading
the head's *own* entry makes the coverage chain-intrinsic instead: the
accepted FFG contracts tie `store.unrealized_justifications b` to `b`'s own
ancestry (`AcceptedFFGTransitionCoherence.au_checkpoint_of_known` places the
checkpoint on `b`'s chain), so a certificate on the head covers the banked
root by construction and the hole is closed at the source, with no extra
executable conjunct.

Cost: when a *side* branch carried a higher justification, this banks the
head-chain one instead — a lower epoch, hence strictly stricter in every
recency guard that reads the banked value, so still safety-free.  The
balance-source deviation from the strong rule (a possibly different, always
head-chain-observed checkpoint state) is benign in-model under
`StaticValidatorSet`.

The gate is evaluated against `bs`, the **incoming** (already-certified, by
`CertifiedBankedJustification` below) balance source, read off `fcr_store`
*before* any field is rewritten.  Evaluating it against the value being
installed would let an uncertified key certify itself: an unkeyed or
adversarial checkpoint state makes both the certificate support and the
adversarial budget degenerate.

If the gate fails the field keeps its previous value — stale-but-certified
beats fresh-but-uncertified.  This is monotonically stricter than the strong
rule in the sense that matters for safety (the field is only ever assigned a
certified, head-chain-observed justification, never a fresher one than the
strong rule's), hence safety-free; the liveness cost is documented in
`docs/weak-synchrony.md`, "Rule delta 5".

Field-by-field: the slot-head writes and the (unconditional)
`previous_epoch_greatest_unrealized_checkpoint` refresh are untouched — the
former is consumed only at an already-gated use site (`previous_slot_head`,
via `has_justification_witness_certificate`), and the latter is now
**vestigial** in the weak bookkeeping: rule delta 5 no longer reads it, and it
is kept written, verbatim and ungated, purely for field-for-field parity with
the strong rule (and for any future consumer of the strong-side rotation
lemmas). `previous_epoch_observed_justified_checkpoint` also stays
unconditional: it only feeds the deferred-scope `get_previous_balance_source`,
so rotating it ungated preserves rather than weakens any future invariant on
it. Only `current_epoch_observed_justified_checkpoint`'s installation is
gated, on `has_head_broadcast_certificate` verbatim — same function, same
span, same balance-source convention as delta 4.
```python
store = fcr_store.store
fcr_store.previous_slot_head = fcr_store.current_slot_head
fcr_store.current_slot_head = get_head(store).root
if is_start_slot_at_epoch(Slot(get_current_slot(store) + 1)):
    fcr_store.previous_epoch_greatest_unrealized_checkpoint = store.unrealized_justified_checkpoint
if is_start_slot_at_epoch(get_current_slot(store)):
    fcr_store.previous_epoch_observed_justified_checkpoint = (
        fcr_store.current_epoch_observed_justified_checkpoint)
    if has_head_broadcast_certificate(store, bs):                      # delta 5
        fcr_store.current_epoch_observed_justified_checkpoint = (
            store.unrealized_justifications[get_head(store).root])
``` -/
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
  -- epoch (unconditional, and vestigial: rule delta 5's banking no longer
  -- reads this field, it is kept for parity with the strong rule)
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
      previous_epoch_observed_justified_checkpoint :=
        fcr_store.current_epoch_observed_justified_checkpoint
      current_epoch_observed_justified_checkpoint :=
        if has_head_broadcast_certificate cfg ext store bs then
          store.unrealized_justifications (get_head cfg store).root
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

/-- Weak-model `find_latest_confirmed_descendant`. Identical to the strong
rule over the weak predicates, except that the previous-epoch advancement
additionally requires `has_justification_witness_certificate` (rule delta 2 in
the module docstring): the observer's own receipt of the justification witness
no longer certifies its dissemination, an attestation surplus does. Every
disjunct that reads an *unrealized* justification at `head` (as opposed to the
already-certified `previous_slot_head`) additionally requires
`has_head_broadcast_certificate` (rule delta 4). -/
def find_latest_confirmed_descendant (fcr_store : FastConfirmationStore Root)
    (latest_confirmed_root : Root) : Root :=
  let store := fcr_store.store
  let head := (get_head cfg store).root
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

/-- Weak-model `get_latest_confirmed`. Identical to the strong rule with the
weak `find_latest_confirmed_descendant` substituted for the advancement step
(picked up automatically by namespace resolution, as `Weak.find_latest_
confirmed_descendant` shadows the strong function inside this namespace).
The revert-to-finalized branch (`is_confirmed_chain_safe`) and the
epoch-start restart branch are the strong/deferred versions — stored-state
maintenance across epochs is out of scope for the weak model (module
docstring). -/
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
      store.unrealized_justifications head)
  let is_confirmed_block_stale :=
    decide (get_block_slot store confirmed_root < observed_justified_block_slot)
  let confirmed_root :=
    if is_epoch_start && is_observed_justified_block_epoch_ok &&
        is_head_unrealized_justified_ok && is_confirmed_block_stale then
      fcr_store.current_epoch_observed_justified_checkpoint.root
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

/-! ## Proof obligations

The two dissemination facts the weak-model safety proof must establish,
stated as named `Prop`s so the migration target is pinned without proof placeholders.
The proof plan lives in `docs/weak-synchrony.md`. -/

/-- **Obligation 1 — certificate surplus is honest.** In any store within the
horizon (in particular the observer's), a broadcast certificate implies some
*honest* validator cast a counted vote: a vote at its assigned slot in the
span, for `block_root` or a descendant. Follows from the certificate
inequality once the economic bound ties the counted non-honest weight to the
weak adversarial budget (the `ByzantineBound`/committee-estimation soundness
package, undiscounted).

Instance-specific premises: the balance source reads the ground registry
(`registryConstant`/`checkpoint_states_total_active_balance` discharge these at
the rule's actual balance sources, at every node), and the store-computed slot
committees read back the ground-truth assignment
(`Execution.PrefixCommitteeAgreement`; cf. `ObserverContext` — the honest-only
`ExternalsCoherence.committees_agree` is unusable at the observer). -/
def CertificateHonestSupporter (E : Execution Root) : Prop :=
  ∀ (v : ValidatorIndex) (n : ℕ) (balance_source : BeaconState Root)
    (block_root : Root) (start_slot end_slot : Slot),
    E.WithinHorizon cfg n →
    E.SlotWithinHorizon cfg start_slot →
    E.SlotWithinHorizon cfg end_slot →
    balance_source.validators = E.registry →
    get_total_active_balance cfg balance_source = E.total_active cfg →
    (∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s) →
    has_broadcast_certificate cfg ext (E.store cfg ext v n) balance_source block_root
      start_slot end_slot = true →
    ∃ w ∈ E.honest, ∃ s : Slot, start_slot ≤ s ∧ s ≤ end_slot ∧
      w ∈ E.committee s ∧
      ∃ (nw : ℕ) (a : Attestation Root), E.vote w s = some (nw, a) ∧
        a.data.slot = s ∧
        a.data.beacon_block_root ∈ (E.store cfg ext v n).block_roots ∧
        is_ancestor (E.store cfg ext v n) (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root block_root) = true

/-- **Obligation 2 — certificates disseminate.** A broadcast certificate over
`[start_slot, end_slot]` observed in any store within the horizon implies
every honest validator holds `block_root` from slot `end_slot + 1` onward.
This is the weak-model replacement for applying `Synchrony.block_relay` to the
observer as holder: the honest supporter of Obligation 1 held the chain by its
vote's slot (honest votes are computed from the voter's own store), and
`block_relay` applies to *that* validator.

Beyond Obligation 1's premises: the span starts at or after the execution's
first slot (`votes_head`'s scope), and `block_root` is known to the observing
store — carried instead of a genesis-start anchor hypothesis, which is strictly
stronger and would not survive checkpoint sync (intended call sites discharge
this knownness from `is_one_confirmed`, cf. `hbconf_of_genesisStart`). -/
def CertificateDissemination (E : Execution Root) : Prop :=
  ∀ (v : ValidatorIndex) (n : ℕ) (balance_source : BeaconState Root)
    (block_root : Root) (start_slot end_slot : Slot),
    E.WithinHorizon cfg n →
    E.SlotWithinHorizon cfg start_slot →
    E.SlotWithinHorizon cfg end_slot →
    E.slot_at cfg 0 ≤ start_slot →
    balance_source.validators = E.registry →
    get_total_active_balance cfg balance_source = E.total_active cfg →
    (∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s) →
    block_root ∈ (E.store cfg ext v n).block_roots →
    has_broadcast_certificate cfg ext (E.store cfg ext v n) balance_source block_root
      start_slot end_slot = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      end_slot + 1 ≤ E.slot_at cfg m →
      block_root ∈ (E.store cfg ext w m).block_roots

end Weak

end FastConfirmation.Spec
