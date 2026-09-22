module
public import FastConfirmation.Spec.Proof.RecordedEpochSupplier
public import FastConfirmation.Spec.Proof.EdgeResiduals

@[expose] public section

/-!
# Endpoint ledger fields over the selected-margin domain

The selected-margin consumers need three facts at every honest endpoint:

* the endpoint's selected class is represented in the executable latest-message
  score;
* honest supporters of a competing child are confined to `Xclass`; and
* non-honest supporters of a competing child are confined to `Bwin`.

At the canonical endpoint cutoff
`sigma = get_current_slot (store w m) - 1`, these facts use only
`SelectedMarginAssumptions`.  In particular, they do not use the broad
`JustificationInterface`.  Provenance, parent-walk closure, recorded-root
knownness, the endpoint registry, and all horizon facts are derived below.

The one delivery input kept explicit is the presence of a recorded latest
message for every member of the selected class.  Together with
`WindowRecordedEpochMax`, this is exactly the output of the honest-vote delivery
supplier.  Keeping it explicit is important: `RecordedEpochMax` is a domination
property conditional on a message being present and, by itself, cannot prove
message existence.

No target-checkpoint-boundary walk is assumed here.  At the endpoint cutoff a
selected member's ground newest vote is identified directly with its recorded
latest message by `recorded_lm_is_newest_at`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The exact recorded-message existence residue needed at an endpoint.  Epoch
domination is deliberately separate (`RecordedEpochMax`), because the two facts
have different logical strength. -/
def EndpointRecordedPresence (w : ValidatorIndex) (m : ℕ)
    (b : Root) (lo sigma : Slot) : Prop :=
  ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
    ∃ lm, (E.store cfg ext w m).latest_messages i = some lm

/-- At the endpoint cutoff, a selected-class member's recorded latest message
supports the selected block.  The proof uses newest-vote uniqueness: the
`SupportsDesc` witness carried by `Sclass` and the ground vote reconstructed
from the recorded message are both newest through the same cutoff. -/
theorem recorded_support_of_sclass_at_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b : Root} {lo sigma : Slot}
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma)
    (hpresence : E.EndpointRecordedPresence cfg ext w m b lo sigma) :
    ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm)
          (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgenEq, _hgenSlot, _hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m hw hmH
  rw [← E.store_current_slot cfg ext w m] at hprov
  intro i hi
  have hi' := hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi'
  obtain ⟨⟨hspan, hih⟩, t, k, a, ht, hvote, hnew, hsupport⟩ := hi'
  obtain ⟨lm, hlm⟩ := hpresence i hi
  obtain ⟨t', k', a', ht', hvote', hnew', hroot'⟩ :=
    E.recorded_lm_is_newest_at cfg ext hA.honest_behavior
      hA.externals_coherence hgen hprov hsigma hih hlm
      (hmax i hih hspan lm hlm)
  have htt' : t = t' := newest_vote_unique
    (by rw [hvote]; exact Option.some_ne_none _)
    hnew
    (by rw [hvote']; exact Option.some_ne_none _)
    hnew' ht ht'
  subst t'
  have hpair : (k, a) = (k', a') := by
    rw [hvote] at hvote'
    exact Option.some.inj hvote'
  have haa' : a = a' := congrArg Prod.snd hpair
  have hroot : a.data.beacon_block_root = lm.root := by
    rw [haa']
    exact hroot'
  refine ⟨lm, hlm, ?_⟩
  simpa only [get_node_for_root, is_ancestor_supported_pending, hroot] using hsupport

/-- `selected_recording` at a canonical honest endpoint.  Registry and horizon
facts for the justified balance source are derived from
`SelectedMarginDomain.justified_checkpoint_cached`; no Casper interface field
is used. -/
theorem selected_recording_at_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma)
    (hpresence : E.EndpointRecordedPresence cfg ext w m b lo sigma) :
    ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) := by
  obtain ⟨ast, ablk, hgenEq, _hgenSlot, _hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hval := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
  have hcached := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hcached
  have hbsH : get_current_epoch cfg
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint) <
      E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hmH.2.2
  have hsigmaLe : sigma ≤ E.slot_at cfg m := by
    rw [hsigma, E.store_current_slot cfg ext w m]
    exact Nat.sub_le _ _
  have hsigmaH : E.SlotWithinHorizon cfg sigma :=
    E.slotWithinHorizon_of_le cfg hsigmaLe hmH
  have hrec := E.recorded_support_of_sclass_at_endpoint_minimal cfg ext hA
    hw hmH hsigma hmax hpresence
  exact E.hSmem_of_recorded cfg ext (hw := hw) (hmH := hmH) hA.honest_behavior
    hA.externals_coherence hA.static_validators hgen w m w m b b lo sigma
    hval hbsH hsigmaH hrec

/-- A full honest-vote ubiquity statement through `sigma` supplies both pieces
used above: `RecordedEpochMax` and selected-class message presence.  This is the
direct adapter for the delivery supplier. -/
theorem selected_recording_of_endpoint_ubiquity_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hubiq : ∀ i ∈ E.honest, ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ sigma → E.vote i t = some (k, a) →
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)) :
    ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) := by
  have hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma :=
    (E.RecordedEpochMax_of_ubiquity cfg ext hubiq).toWindow cfg ext
  have hpresence : E.EndpointRecordedPresence cfg ext w m b lo sigma := by
    intro i hi
    have hi' := hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi'
    obtain ⟨⟨_hspan, hih⟩, t, k, a, ht, hvote, _hnew, _hsupport⟩ := hi'
    obtain ⟨lm, hlm, _⟩ := hubiq i hih t k a ht hvote
    exact ⟨lm, hlm⟩
  exact E.selected_recording_at_endpoint_minimal cfg ext hA hw hmH
    hsigma hmax hpresence

/-- Selected-class message presence from the faithful post-anchor delivery
supplier.  A selected member belongs to `span_committee lo sigma`; one of those
assignments supplies an actual honest post-anchor vote, so the endpoint has a
latest message even when the particular `SupportsDesc` witness lies in the
totalized pre-anchor part of `Execution.vote`. -/
theorem endpointRecordedPresence_at_query_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {b : Root} {lo sigma : Slot}
    (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hsigmaLt : sigma < E.slot_at cfg m) :
    E.EndpointRecordedPresence cfg ext w m b lo sigma := by
  intro i hi
  have hi' := hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi'
  obtain ⟨⟨hiSpan, hih⟩, _hsupport⟩ := hi'
  simp only [Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc] at hiSpan
  obtain ⟨s, ⟨hloS, hsSigma⟩, hiCommittee⟩ := hiSpan
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg
      (hsSigma.trans (le_of_lt hsigmaLt)) hmH
  obtain ⟨n, index, hnH, hnSlot, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hih s hiCommittee hsH
      (hlo0.trans hloS)
  obtain ⟨msg, hmsg, _hepoch⟩ :=
    E.honestVote_recorded_at_query_minimal cfg ext hA hwalkDomain
      hw hmH hih (hlo0.trans hloS) hnH hnSlot hvoteHead
      (hsSigma.trans_lt hsigmaLt)
  exact ⟨msg, hmsg⟩

/-- Honest sibling confinement, in the exact field shape consumed by the
selected-margin structures.  The competing child's knownness and parent link
come from filtered-child membership; recorded-root knownness comes from
executable latest-message provenance. -/
theorem honest_sibling_confinement_at_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (ha : a ∈ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hparent : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks a).slot + 1)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks b))) → c' ≠ b →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint),
        i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo sigma := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ w m
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext w m] at hprov
  have hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots := by
    intro lm i hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hlmKnown
  have hjc := hA.domain.justified_root_known w hw m hmH
  intro c' hchild hne i hisupp hih
  rw [mem_get_node_children_resolved
    (get_parent_payload_status_ne_pending (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b))] at hchild
  have hc' : c' ∈ (E.store cfg ext w m).block_roots :=
    filtered_subset_block_roots cfg (E.store cfg ext w m) hjc c' hchild.2.1
  have hparent' : ((E.store cfg ext w m).blocks c').parent_root = a := hchild.2.2.1
  have hlo' : lo ≤ ((E.store cfg ext w m).blocks c').slot := by
    have hlt := hpsl c' hc' (by rw [hparent']; exact ha)
    rw [hparent'] at hlt
    exact hlo.trans hlt
  exact E.honest_sibling_confinement_window cfg ext hA.honest_behavior
    hA.externals_coherence hgen hprov hpsl hwalkK hsigma
    hb hb hc' ha hparent hparent' (Ne.symm hne)
    (is_ancestor_refl _ _) hlo' hlmknown
    hmax hisupp hih

/-- Byzantine sibling confinement into the full endpoint window `Bwin`.  The
window-side condition `lo ≤ sigma + 1` is derived from the selected parent/child
edge and the executable block-slot bound; it is not an extra premise. -/
theorem byzantine_sibling_confinement_at_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (ha : a ∈ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hparent : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks a).slot + 1) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks b))) → c' ≠ b →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint),
        i ∉ E.honest → i ∈ E.Bwin lo sigma := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ w m
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext w m] at hprov
  have hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots := by
    intro lm i hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hlmKnown
  have hjc := hA.domain.justified_root_known w hw m hmH
  have hparentLt : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks b).slot := by
    have hlt := hpsl b hb (by rw [hparent]; exact ha)
    rwa [hparent] at hlt
  have hbcur : ((E.store cfg ext w m).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hgenSlot⟩ w m b hb
  have hcurPos : 0 < get_current_slot cfg (E.store cfg ext w m) :=
    lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hparentLt) hbcur
  have hsigmaSucc : sigma + 1 = get_current_slot cfg (E.store cfg ext w m) := by
    rw [hsigma, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcurPos))]
  have hloSigma : lo ≤ sigma + 1 := by
    rw [hsigmaSucc]
    exact hlo.trans (Nat.succ_le_of_lt hparentLt |>.trans hbcur)
  intro c' hchild hne i hisupp hib
  rw [mem_get_node_children_resolved
    (get_parent_payload_status_ne_pending (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b))] at hchild
  have hc' : c' ∈ (E.store cfg ext w m).block_roots :=
    filtered_subset_block_roots cfg (E.store cfg ext w m) hjc c' hchild.2.1
  have hparent' : ((E.store cfg ext w m).blocks c').parent_root = a := hchild.2.2.1
  have hlo' : lo ≤ ((E.store cfg ext w m).blocks c').slot := by
    have hlt := hpsl c' hc' (by rw [hparent']; exact ha)
    rw [hparent'] at hlt
    exact hlo.trans hlt
  exact E.byz_confinement_bwin cfg ext hprov hpsl hwalkK
    hb hb hc' ha hparent hparent' (Ne.symm hne)
    (is_ancestor_refl _ _) hlo' hloSigma (le_refl sigma)
    (by rw [hsigma]) hlmknown hisupp hib

/-- The reusable endpoint ledger output.  Its final two fields are the
full-window score bounds obtained from the three set-level fields. -/
structure EndpointLedgerFields
    (w : ValidatorIndex) (m : ℕ) (a b : Root) (lo sigma : Slot) : Prop where
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  honest_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo sigma
  byzantine_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∉ E.honest → i ∈ E.Bwin lo sigma
  selected_score : E.Sval cfg ext w m b lo sigma ≤
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint) ≤
      E.Xval cfg ext w m b lo sigma + E.Bval lo sigma

/-! ## Crossing-specific endpoint obligations -/

/-- The overlap part of the confirmation discount is already present in the
endpoint ancestor class.  This is the endpoint form of
`crossing_parentSub_le_Aval`, with window-scoped recorded-epoch domination.

The proof does not use a generic `Aclass` transport (which would be invalid:
an `Aclass` member can move to `Sclass` when ancestry becomes known).  Instead,
`ParentStuck` reconstructs the member's store-independent ground newest vote,
whose root is exactly the selected block's parent.  That exact root makes the
member remain `Aclass` at the endpoint. -/
theorem crossingParentSub_le_endpoint_Aval_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {a b : Root} {es : Slot}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (haQ : a ∈ (E.store cfg ext v q).block_roots)
    (hbQ : b ∈ (E.store cfg ext v q).block_roots)
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hmax : E.WindowRecordedEpochMax cfg ext v q
      (((E.store cfg ext v q).blocks
        ((E.store cfg ext v q).blocks b).parent_root).slot + 1) es) :
    E.weight (E.crossingParentSub cfg (E.store cfg ext v q) bs b
        ((E.store cfg ext v q).blocks b).slot es) ≤
      E.Aval cfg ext w m b ((E.store cfg ext v q).blocks b).slot es := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpslQ : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hpslM : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hprovQ := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprovQ
  have hslotltQ : ((E.store cfg ext v q).blocks a).slot <
      ((E.store cfg ext v q).blocks b).slot := by
    have hlt := hpslQ b hbQ (by rw [hparentQ]; exact haQ)
    rwa [hparentQ] at hlt
  have hslotltM : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks b).slot := by
    have hlt := hpslM b hbM (by rw [hparentM]; exact haM)
    rwa [hparentM] at hlt
  have hbcurQ : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hgenSlot⟩ v q b hbQ
  have hbcQ : is_ancestor (E.store cfg ext v q) (get_node_for_root b)
      (get_node_for_root a) = true :=
    is_ancestor_of_parent hpslQ hbQ haQ hparentQ
  have hbcM : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
      (get_node_for_root a) = true :=
    is_ancestor_of_parent hpslM hbM haM hparentM
  have hparentNotDescM : ¬ is_ancestor (E.store cfg ext w m)
      (get_node_for_root a) (get_node_for_root b) = true := by
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
    rw [get_ancestor_stop (le_of_lt hslotltM)]
    intro hcon
    injection hcon with heq
    rw [heq] at hslotltM
    exact lt_irrefl _ hslotltM
  rw [Execution.Aval]
  apply E.weight_mono
  intro i hi
  have hi' : i ∈ ParentStuck cfg E (E.store cfg ext v q) bs b ∩
      E.span_committee ((E.store cfg ext v q).blocks b).slot es := by
    simpa only [crossingParentSub] using hi
  obtain ⟨hiParent, hiSpanMid⟩ := Finset.mem_inter.mp hi'
  have hiAQuery := E.ParentStuck_subset_Aclass_window cfg ext
    hA.honest_behavior hA.externals_coherence hgen hprovQ rfl hes
    (by simpa only [hparentQ] using hslotltQ) hbcurQ
    (by simpa only [hparentQ] using hbcQ) hmax hiParent
  have hiAQ := hiAQuery
  simp only [Execution.Aclass, Finset.mem_filter] at hiAQ
  obtain ⟨⟨hiSpanFull, hih⟩, _hiNotS, _hiAnc⟩ := hiAQ
  have hiParent' := hiParent
  simp only [ParentStuck, Finset.mem_filter] at hiParent'
  obtain ⟨hiPS, _⟩ := hiParent'
  simp only [ParentSupport, Finset.mem_filter] at hiPS
  obtain ⟨_, hiRecorded⟩ := hiPS
  cases hlm : (E.store cfg ext v q).latest_messages i with
  | none => rw [hlm] at hiRecorded; simp at hiRecorded
  | some lm =>
    rw [hlm] at hiRecorded
    simp only [Option.any_some, Bool.and_eq_true,
      decide_eq_true_eq] at hiRecorded
    obtain ⟨hlmParent, _hiNotEquiv⟩ := hiRecorded
    obtain ⟨t, k, att, htle, hvote, hnew, hattRoot⟩ :=
      E.recorded_lm_is_newest_at cfg ext hA.honest_behavior
        hA.externals_coherence hgen hprovQ hes hih hlm
        (hmax i hih hiSpanFull lm hlm)
    have hrootA : att.data.beacon_block_root = a := by
      exact hattRoot.trans (hlmParent.trans hparentQ)
    simp only [Execution.Aclass, Finset.mem_filter]
    refine ⟨⟨hiSpanMid, hih⟩, ?_, ?_⟩
    · rintro ⟨t₁, k₁, att₁, ht1le, hvote1, hnew1, hdesc⟩
      have htt : t = t₁ := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, hattEq⟩ := hvote1
      rw [← hattEq, hrootA] at hdesc
      exact hparentNotDescM hdesc
    · exact Or.inr ⟨t, k, att, htle, hvote, hnew,
        by rw [hrootA]; exact hbcM⟩

/-- Construct all endpoint ledger fields from the minimal selected domain,
canonical cutoff, edge geometry, and the two honest-vote delivery outputs. -/
theorem endpointLedgerFields_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (ha : a ∈ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hparent : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks a).slot + 1)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma)
    (hpresence : E.EndpointRecordedPresence cfg ext w m b lo sigma) :
    E.EndpointLedgerFields cfg ext w m a b lo sigma := by
  have hselected := E.selected_recording_at_endpoint_minimal cfg ext hA hw hmH
    hsigma hmax hpresence
  have hhon := E.honest_sibling_confinement_at_endpoint_minimal cfg ext hA
    hw hmH hsigma ha hb hparent hlo hmax
  have hbyz := E.byzantine_sibling_confinement_at_endpoint_minimal cfg ext hA
    hw hmH hsigma ha hb hparent hlo
  have hval := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
  refine ⟨hselected, hhon, hbyz,
    recorded_bside_ge cfg ext hval hselected, ?_⟩
  intro c' hchild hne
  exact recorded_sibling_le cfg ext hval
    (hhon c' hchild hne) (hbyz c' hchild hne)

/-- Fully executable endpoint-ledger supplier.  The only additional domain
adequacy premise is the honest vote's target-boundary walk, in the narrowly
scoped form exposed by `RecordedEpochSupplier`.  Window domination and message
presence are constructed internally.

`hlo0` is the trusted-anchor lower bound for the concrete ledger window.  It is
essential: values of the totalized vote function before `slot_at 0` are not
constrained by `HonestBehavior`. -/
theorem endpointLedgerFields_from_execution_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a b : Root} {lo sigma : Slot}
    (hsigma : sigma = get_current_slot cfg (E.store cfg ext w m) - 1)
    (ha : a ∈ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hparent : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks a).slot + 1)
    (hlo0 : E.slot_at cfg 0 ≤ lo) :
    E.EndpointLedgerFields cfg ext w m a b lo sigma := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hparentLt : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks b).slot := by
    have hlt := hpsl b hb (by rw [hparent]; exact ha)
    rwa [hparent] at hlt
  have hbcur : ((E.store cfg ext w m).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext w m) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hgenSlot⟩ w m b hb
  have hcurPos : 0 < get_current_slot cfg (E.store cfg ext w m) :=
    lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hparentLt) hbcur
  have hsigmaLt : sigma < E.slot_at cfg m := by
    calc
      sigma = get_current_slot cfg (E.store cfg ext w m) - 1 := hsigma
      _ < get_current_slot cfg (E.store cfg ext w m) :=
        Nat.sub_lt hcurPos Nat.one_pos
      _ = E.slot_at cfg m := E.store_current_slot cfg ext w m
  have hmax : E.WindowRecordedEpochMax cfg ext w m lo sigma :=
    E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
      hw hmH hlo0 hsigma hsigmaLt
  have hpresence : E.EndpointRecordedPresence cfg ext w m b lo sigma :=
    E.endpointRecordedPresence_at_query_minimal cfg ext hA hwalkDomain
      hw hmH hlo0 hsigmaLt
  exact E.endpointLedgerFields_minimal cfg ext hA hw hmH hsigma
    ha hb hparent hlo hmax hpresence

end Execution

end FastConfirmation.Spec

end
