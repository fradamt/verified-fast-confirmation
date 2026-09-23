module
public import FastConfirmationModel.Weak.StrongReference
public import FastConfirmationModel.Weak.WeakSynchrony

@[expose] public section

/-!
# Complete prior-slot evidence

The research note `orch/zk/full-rule-ideal-latency.md` reports 528 paired
traces, with full participation, equal balances and prior-slot delivery.
The generator scripts are unavailable. This record is a store-level contract,
not a claim to reconstruct those traces or their Altair transitions.
`prior_votes` expresses delivery after LMD overwrites: a later epoch may
replace a delivered vote. `fresh` is an added premise for all recorded cells.
The balance, checkpoint alignment, and strictly newer banking epoch fields
are added premises; the note does not prove them. Certificates are strict
inequalities on actual stored attestation weight, not assumptions about the
rule's output.

There is deliberately no actual-head certificate field. After-head calls in
the note have no completed-slot vote for the new head. The concrete regression
in `CompleteEvidenceWitness` exhibits this obstruction.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- Explicit store contract. It does not encode the missing experiment scripts,
BLS authentication, the Altair transition, or standard inclusion policy.
The empty equivocation set excludes recorded slashings; absence of conflicting
historical votes needs an execution contract. The latest-message projection
cannot retain each earlier attestation after an overwrite. -/
structure CompleteEvidence (cfg : Config) (ext : Externals Root)
    (f : FastConfirmationStore Root) : Prop where
  epoch_size : cfg.slots_per_epoch = 8 ∨ cfg.slots_per_epoch = 32
  threshold : cfg.confirmation_byzantine_threshold = 25
  after_genesis : 0 < get_current_slot cfg f.store
  no_equivocations : f.store.equivocating_indices = ∅
  prior_votes : ∀ s, s < get_current_slot cfg f.store →
    ∀ i ∈ get_slot_committee cfg ext f.store s,
      ∃ lm, f.store.latest_messages i = some lm ∧
        compute_epoch_at_slot cfg s ≤ get_latest_message_epoch cfg lm
  fresh : ∀ i lm, f.store.latest_messages i = some lm →
    Weak.is_duty_fresh_message cfg ext f.store i lm = true
  recorded_provenance : ∀ i lm, f.store.latest_messages i = some lm →
    ∃ s, s < get_current_slot cfg f.store ∧ i ∈ get_slot_committee cfg ext f.store s ∧
      get_latest_message_epoch cfg lm = compute_epoch_at_slot cfg s ∧
      get_block_slot f.store lm.root ≤ s
  balance_sources :
    (get_current_balance_source f).validators =
      (get_pulled_up_head_state cfg ext f.store).validators ∧
    (get_previous_balance_source f).validators =
      (get_pulled_up_head_state cfg ext f.store).validators ∧
    get_total_active_balance cfg (get_current_balance_source f) =
      get_total_active_balance cfg (get_pulled_up_head_state cfg ext f.store) ∧
    get_total_active_balance cfg (get_previous_balance_source f) =
      get_total_active_balance cfg (get_pulled_up_head_state cfg ext f.store)
  equal_balances : ∃ weight, 0 < weight ∧
    ∀ v ∈ (get_current_balance_source f).validators, v.effective_balance = weight
  carrier_support : Weak.compute_adversarial_weight cfg f.store
      (get_current_balance_source f)
      (get_block_slot f.store (Weak.get_certified_head cfg ext f.store
        (get_current_balance_source f))) (get_current_slot cfg f.store - 1) <
    Weak.get_broadcast_certificate_support cfg ext f.store (get_current_balance_source f)
      (Weak.get_certified_head cfg ext f.store (get_current_balance_source f))
      (get_block_slot f.store (Weak.get_certified_head cfg ext f.store
        (get_current_balance_source f))) (get_current_slot cfg f.store - 1)
  witness_support : Weak.compute_adversarial_weight cfg f.store
      (get_current_balance_source f) (get_block_slot f.store f.previous_slot_head)
      (get_current_slot cfg f.store - 1) <
    Weak.get_broadcast_certificate_support cfg ext f.store (get_current_balance_source f)
      f.previous_slot_head (get_block_slot f.store f.previous_slot_head)
      (get_current_slot cfg f.store - 1)
  realized_target_carrier : get_current_target cfg f.store =
      f.store.unrealized_justified_checkpoint →
    get_current_target cfg f.store = f.store.unrealized_justifications
      (Weak.get_certified_head cfg ext f.store (get_current_balance_source f))
  bank_alignment : is_start_slot_at_epoch cfg (get_current_slot cfg f.store) = true →
    f.store.unrealized_justifications
      (Weak.get_certified_head cfg ext f.store (get_current_balance_source f)) =
    (if is_start_slot_at_epoch cfg (get_current_slot cfg f.store + 1) then
      f.store.unrealized_justified_checkpoint
    else f.previous_epoch_greatest_unrealized_checkpoint)

  /-- At an epoch boundary, the certified carrier supplies a checkpoint whose
  epoch is strictly newer than the current observed checkpoint. This is extra
  store evidence for parity with the strong rule's unconditional bank write. -/
  bank_epoch_newer : is_start_slot_at_epoch cfg (get_current_slot cfg f.store) = true →
    f.current_epoch_observed_justified_checkpoint.epoch <
      (f.store.unrealized_justifications
        (Weak.get_certified_head cfg ext f.store (get_current_balance_source f))).epoch

end FastConfirmation.Spec

end
