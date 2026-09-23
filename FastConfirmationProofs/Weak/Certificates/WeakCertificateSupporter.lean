module
public import FastConfirmationModel.Weak.WeakSynchrony
public import FastConfirmationStatements.Weak.CertificateObligations
public import FastConfirmationProofs.Execution.Delivery.Delivery
public import FastConfirmationProofs.Handlers.SupportClasses
public import FastConfirmationProofs.Weak.Safety.WeakObserverProvenance

@[expose] public section

/-!
# Spec / Proof / WeakCertificateSupporter

Discharges `Weak.CertificateHonestSupporter` (`Spec/Model/WeakSynchrony.lean`,
Obligation 1): a broadcast certificate's counted support strictly exceeds the
undiscounted adversarial budget of its span, so the excess cannot come entirely
from non-honest committee members — some counted voter is honest.

The route mirrors the strong-model accounting of `Proof/QuorumAccounting.lean`
and `Proof/HonestWeight.lean`, replayed over
`Weak.get_broadcast_certificate_support`'s counted `Finset` instead of
`AttSupporters`:

* `Weak.mem_broadcast_certificate_support_set` unpacks membership in that
  `Finset` (a double `Finset.filter` of a `Finset.biUnion`) into its
  constituent facts.
* `Weak.broadcast_certificate_support_le_of_no_honest` is the economic core:
  if no honest validator is counted, the counted weight is confined to the
  ground-truth span committee's non-honest part, which `ByzantineWeightPremises.span_bound`
  bounds by the undiscounted `Weak.compute_adversarial_weight`.
* `Execution.honest_latest_message_vote` extracts, from an honest validator's
  recorded latest message at its assigned slot's epoch, that validator's
  genuine vote for that slot (a refactor of `Execution.latest_message_root`'s
  proof body dropping its `hvote` premise in favor of the committee
  membership it would otherwise derive from `hvote`).

`Execution.certificate_honest_supporter` composes them: the certificate
inequality plus the economic core forces some honest counted voter; unpacking
its membership (`mem_broadcast_certificate_support_set`) yields its recorded
message and assigned slot; `honest_latest_message_vote` turns that into the
voter's genuine vote; `Execution.latestMessageProvenance`'s block-roots
conjunct supplies the observer-store membership fact the target existential
needs.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## `F1` — membership in the broadcast-certificate support set -/

/-- Membership characterization of the `Finset` `Weak.get_broadcast_certificate_support`
sums over: `i` sits in the committee union of `[start_slot, end_slot]`, is
unslashed and active, and has a recorded latest message that (i) is not an
equivocator's, (ii) was cast for a slot in the span at that slot's epoch, and
(iii) supports `block_root` (its root is an ancestor of `block_root`). -/
theorem Weak.mem_broadcast_certificate_support_set
    (store : Store Root) (balance_source : BeaconState Root) (block_root : Root)
    (start_slot end_slot : Slot) (i : ValidatorIndex) :
    i ∈ ((((Finset.Icc start_slot end_slot).biUnion
              (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
            !(balance_source.validators.getD j default).slashed &&
              is_active_validator (balance_source.validators.getD j default)
                (get_current_epoch cfg balance_source))).filter (fun j =>
          (store.latest_messages j).any (fun latest_message =>
            decide (j ∉ store.equivocating_indices) &&
              decide (∃ s ∈ Finset.Icc start_slot end_slot,
                j ∈ get_slot_committee cfg ext store s ∧
                  get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
              is_ancestor store (get_node_for_root latest_message.root)
                (get_node_for_root block_root)))) ↔
      i ∈ (Finset.Icc start_slot end_slot).biUnion
          (fun slot => get_slot_committee cfg ext store slot) ∧
      (!(balance_source.validators.getD i default).slashed) = true ∧
      is_active_validator (balance_source.validators.getD i default)
          (get_current_epoch cfg balance_source) = true ∧
      ∃ lm, store.latest_messages i = some lm ∧
        i ∉ store.equivocating_indices ∧
        (∃ s ∈ Finset.Icc start_slot end_slot,
          i ∈ get_slot_committee cfg ext store s ∧
            get_latest_message_epoch cfg lm = compute_epoch_at_slot cfg s) ∧
        is_ancestor store (get_node_for_root lm.root) (get_node_for_root block_root) = true := by
  simp only [Finset.mem_filter, Option.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc]

/-! ## `F2` — the economic core -/

/-- If no honest validator is counted in the broadcast-certificate support of
`[start_slot, end_slot]`, the counted support is at most the undiscounted
adversarial budget of the span: every counted index sits in the ground-truth
span committee (`hcomm` readback, valid on `[start_slot, end_slot]` since every
slot in the span is at or below `end_slot`) and, absent an honest counted
index, in its non-honest part, whose ground-truth weight `ByzantineWeightPremises.span_bound`
bounds. -/
theorem Weak.broadcast_certificate_support_le_of_no_honest {E : Execution Root}
    (hbb : ByzantineWeightPremises cfg E)
    {store : Store Root} {balance_source : BeaconState Root} {block_root : Root}
    {start_slot end_slot : Slot}
    (hval : balance_source.validators = E.registry)
    (htab : get_total_active_balance cfg balance_source = E.total_active cfg)
    (hcomm : ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext store s = E.committee s)
    (hstartH : E.SlotWithinHorizon cfg start_slot)
    (hendH : E.SlotWithinHorizon cfg end_slot)
    (hno : ∀ i ∈ E.honest,
      i ∉ ((((Finset.Icc start_slot end_slot).biUnion
                (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
              !(balance_source.validators.getD j default).slashed &&
                is_active_validator (balance_source.validators.getD j default)
                  (get_current_epoch cfg balance_source))).filter (fun j =>
            (store.latest_messages j).any (fun latest_message =>
              decide (j ∉ store.equivocating_indices) &&
                decide (∃ s ∈ Finset.Icc start_slot end_slot,
                  j ∈ get_slot_committee cfg ext store s ∧
                    get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
                is_ancestor store (get_node_for_root latest_message.root)
                  (get_node_for_root block_root))))) :
    Weak.get_broadcast_certificate_support cfg ext store balance_source block_root
        start_slot end_slot ≤
      Weak.compute_adversarial_weight cfg store balance_source start_slot end_slot := by
  have hce : (Finset.Icc start_slot end_slot).biUnion
      (fun slot => get_slot_committee cfg ext store slot) =
        E.span_committee start_slot end_slot := by
    simp only [Execution.span_committee]
    apply Finset.biUnion_congr rfl
    intro slot hslot
    exact hcomm slot (E.slotWithinHorizon_mono cfg (Finset.mem_Icc.mp hslot).2 hendH)
  have hsubset : ((((Finset.Icc start_slot end_slot).biUnion
                (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
              !(balance_source.validators.getD j default).slashed &&
                is_active_validator (balance_source.validators.getD j default)
                  (get_current_epoch cfg balance_source))).filter (fun j =>
            (store.latest_messages j).any (fun latest_message =>
              decide (j ∉ store.equivocating_indices) &&
                decide (∃ s ∈ Finset.Icc start_slot end_slot,
                  j ∈ get_slot_committee cfg ext store s ∧
                    get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
                is_ancestor store (get_node_for_root latest_message.root)
                  (get_node_for_root block_root)))) ⊆
      (E.span_committee start_slot end_slot).filter (fun i => i ∉ E.honest) := by
    intro i hi
    obtain ⟨hcommem, -, -, -⟩ :=
      (Weak.mem_broadcast_certificate_support_set cfg ext store balance_source block_root
        start_slot end_slot i).mp hi
    exact Finset.mem_filter.mpr ⟨hce ▸ hcommem, fun hiHonest => hno i hiHonest hi⟩
  simp only [Weak.get_broadcast_certificate_support, Weak.compute_adversarial_weight]
  calc ∑ i ∈ ((((Finset.Icc start_slot end_slot).biUnion
                (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
              !(balance_source.validators.getD j default).slashed &&
                is_active_validator (balance_source.validators.getD j default)
                  (get_current_epoch cfg balance_source))).filter (fun j =>
            (store.latest_messages j).any (fun latest_message =>
              decide (j ∉ store.equivocating_indices) &&
                decide (∃ s ∈ Finset.Icc start_slot end_slot,
                  j ∈ get_slot_committee cfg ext store s ∧
                    get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
                is_ancestor store (get_node_for_root latest_message.root)
                  (get_node_for_root block_root)))),
      (balance_source.validators.getD i default).effective_balance
      = E.weight ((((Finset.Icc start_slot end_slot).biUnion
                (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
              !(balance_source.validators.getD j default).slashed &&
                is_active_validator (balance_source.validators.getD j default)
                  (get_current_epoch cfg balance_source))).filter (fun j =>
            (store.latest_messages j).any (fun latest_message =>
              decide (j ∉ store.equivocating_indices) &&
                decide (∃ s ∈ Finset.Icc start_slot end_slot,
                  j ∈ get_slot_committee cfg ext store s ∧
                    get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
                is_ancestor store (get_node_for_root latest_message.root)
                  (get_node_for_root block_root)))) := by
        simp only [Execution.weight]
        exact Finset.sum_congr rfl (fun i _ => by rw [Execution.weight_of, hval])
    _ ≤ E.weight ((E.span_committee start_slot end_slot).filter (fun i => i ∉ E.honest)) :=
        E.weight_mono hsubset
    _ ≤ estimate_committee_weight_between_slots cfg (E.total_active cfg) start_slot end_slot
          / 100 * cfg.confirmation_byzantine_threshold :=
        hbb.span_bound start_slot end_slot hstartH hendH
    _ = estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg balance_source) start_slot end_slot / 100 *
          cfg.confirmation_byzantine_threshold := by
        rw [← htab]

/-! ## `E` — honest latest-message vote extraction -/

/-- If honest `i`'s recorded latest message at node `(v, n)` was cast for a
slot in the epoch of `s` (`hepoch`), and `i` is assigned to `s` (`hcs`), then
`i`'s genuine vote for `s` exists and carries that message's data. A refactor
of `Execution.latest_message_root`'s proof body (`Proof/Delivery.lean:911`):
the schedule-connected witness (`schedLMProv`) and `no_forgery` already
identify the message with a genuine vote at *some* slot; here that slot is
pinned to `s` by `committee_assignment_unique` from the committee memberships
`hcs` and the one `votes_assigned` derives from the genuine vote, instead of
from an already-known vote at `s`. -/
theorem Execution.honest_latest_message_vote {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {v : ValidatorIndex} {n : ℕ}
    {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    {s : Slot} (hcs : i ∈ E.committee s)
    (hepoch : get_latest_message_epoch cfg lm = compute_epoch_at_slot cfg s) :
    ∃ (k : ℕ) (a : Attestation Root), E.vote i s = some (k, a) ∧
      a.data.slot = s ∧ a.data.beacon_block_root = lm.root := by
  obtain ⟨a1, u, t, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen v n i lm hlm
  obtain ⟨k, a2, hvote2, hdata2⟩ := hhb.no_forgery u t a1 ifb hsched i hi hvin
  have hcs1 : i ∈ E.committee a1.data.slot :=
    hhb.votes_assigned i hi a1.data.slot (by rw [hvote2]; exact Option.some_ne_none _)
  have hslot_eq : a1.data.slot = s :=
    hec.committee_assignment_unique i a1.data.slot s hcs1 hcs (hslotep.trans hepoch)
  refine ⟨k, a2, ?_, ?_, ?_⟩
  · rw [← hslot_eq]; exact hvote2
  · rw [← hdata2, hslot_eq]
  · rw [← hdata2]; exact hbbr

/-! ## Assembly -/

/-- **Obligation 1.** A broadcast certificate's counted support strictly
exceeds the undiscounted adversarial budget of its span
(`has_broadcast_certificate`); if no honest validator were counted, the
economic core (`broadcast_certificate_support_le_of_no_honest`) would bound
the support by that same budget, a contradiction. So some honest validator
`i` is counted: unpacking its membership gives its recorded message and the
slot `s` in the span at which it was cast, at `i`'s assigned slot's epoch;
`honest_latest_message_vote` turns this into `i`'s genuine vote for `s`, whose
data matches the message (root, hence the certified ancestry to `block_root`)
and whose root is known to the observing store
(`Execution.latestMessageProvenance`'s block-roots conjunct). -/
theorem Execution.certificate_honest_supporter (E : Execution Root)
    (hwf : WellFormedExecution E)
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    Weak.CertificateHonestSupporter cfg ext E := by
  intro v n balance_source block_root start_slot end_slot hnH hstartH hendH hval htab hcomm hcert
  set store := E.store cfg ext v n with hstoreeq
  have hgt : Weak.compute_adversarial_weight cfg store balance_source start_slot end_slot <
      Weak.get_broadcast_certificate_support cfg ext store balance_source block_root
        start_slot end_slot := by
    have hcert' := hcert
    simp only [Weak.has_broadcast_certificate] at hcert'
    by_cases h0 : get_current_slot cfg store = 0
    · rw [if_pos h0] at hcert'
      exact absurd hcert' Bool.false_ne_true
    · rw [if_neg h0] at hcert'
      simpa only [decide_eq_true_eq] using hcert'
  have hex : ∃ i ∈ E.honest,
      i ∈ ((((Finset.Icc start_slot end_slot).biUnion
                (fun slot => get_slot_committee cfg ext store slot)).filter (fun j =>
              !(balance_source.validators.getD j default).slashed &&
                is_active_validator (balance_source.validators.getD j default)
                  (get_current_epoch cfg balance_source))).filter (fun j =>
            (store.latest_messages j).any (fun latest_message =>
              decide (j ∉ store.equivocating_indices) &&
                decide (∃ s ∈ Finset.Icc start_slot end_slot,
                  j ∈ get_slot_committee cfg ext store s ∧
                    get_latest_message_epoch cfg latest_message = compute_epoch_at_slot cfg s) &&
                is_ancestor store (get_node_for_root latest_message.root)
                  (get_node_for_root block_root)))) := by
    by_contra hcon
    push_neg at hcon
    have hle := Weak.broadcast_certificate_support_le_of_no_honest cfg ext hbb hval htab hcomm
      hstartH hendH hcon
    exact absurd hle (not_le.mpr hgt)
  obtain ⟨i, hiHonest, hiF⟩ := hex
  obtain ⟨-, -, -, lm, hlm, -, ⟨s, hsIcc, hcsstore, hepocheq⟩, hisanc⟩ :=
    (Weak.mem_broadcast_certificate_support_set cfg ext store balance_source block_root
      start_slot end_slot i).mp hiF
  have hsIccle := Finset.mem_Icc.mp hsIcc
  have hsSWH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_mono cfg hsIccle.2 hendH
  have hcs : i ∈ E.committee s := by
    rw [← hcomm s hsSWH]; exact hcsstore
  obtain ⟨k, a, hvote, hslot_eq, hbroot⟩ :=
    E.honest_latest_message_vote cfg ext hhb hec hgen hiHonest hlm hcs hepocheq
  have hroot_mem := E.latestMessageRootKnown cfg ext hgen v n i lm hlm
  refine ⟨i, hiHonest, s, hsIccle.1, hsIccle.2, hcs, k, a, hvote, hslot_eq, ?_, ?_⟩
  · rw [hbroot]; exact hroot_mem
  · rw [hbroot]; exact hisanc

end FastConfirmation.Spec

end
