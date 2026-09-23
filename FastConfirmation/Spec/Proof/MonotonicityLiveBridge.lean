module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRNextSlotSafetyFacade
public import FastConfirmation.Spec.Proof.HeadStack

@[expose] public section

/-!
# Vote and support bridges for live monotonicity

The first lemma links a recorded latest message to the honest vote that
produced it. The second isolates the full-epoch stake inequality used by
one-confirmation. Store-to-store ancestry transport and the executable
support estimate remain separate obligations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- An honest validator's recorded latest message comes from its own vote,
with the exact root and Gloas payload bit. -/
theorem latest_message_has_honest_vote
    (hhb : HonestBehavior cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {t : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages v = some msg) :
    ∃ s k a, E.vote v s = some (k, a) ∧
      msg = LatestMessage.mk s a.data.beacon_block_root
        (decide (a.data.index = 1)) := by
  obtain ⟨a, u, q, fromBlock, hsched, hvin, hmsgEq⟩ :=
    E.schedLMProvExact cfg ext hgen w t v msg hmsg
  obtain ⟨k, a', hvote, hdata⟩ :=
    hhb.no_forgery u q a fromBlock hsched v hv hvin
  exact ⟨a.data.slot, k, a', hvote, by simpa only [hdata] using hmsgEq⟩

/-- At an honest endpoint, the vote that set a latest message was cast in a
strictly earlier slot. This supplies the upper interval bound needed when
the live vote condition is applied to recorded support. -/
theorem latest_message_has_honest_vote_before_endpoint
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {t : ℕ} (hHt : E.WithinHorizon cfg t)
    {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages v = some msg) :
    ∃ s k a, E.vote v s = some (k, a) ∧
      msg = LatestMessage.mk s a.data.beacon_block_root
        (decide (a.data.index = 1)) ∧
      s < E.slot_at cfg t := by
  obtain ⟨s, k, a, hvote, hmsgEq⟩ :=
    E.latest_message_has_honest_vote cfg ext hhb hgen hv hmsg
  obtain ⟨_, _, _, _, _, hslotPast, _, _, _, hslotEq⟩ :=
    (E.latestMessageProvenance cfg ext hwf hec hgen w t hw hHt) v msg hmsg
  refine ⟨s, k, a, hvote, hmsgEq, ?_⟩
  have hmsgSlot : msg.slot = s := by rw [hmsgEq]
  rw [hmsgSlot] at hslotEq
  rw [hslotEq]
  exact Nat.lt_of_succ_le hslotPast

/-- A recorded honest message whose epoch reaches a known honest vote cannot
come from an earlier slot. Within the same epoch, committee assignment
uniqueness and no forgery identify the exact vote. -/
theorem honest_latest_message_slot_ge_vote
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hvote : E.vote v s = some (k, a))
    {t : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages v = some msg)
    (hepoch : compute_epoch_at_slot cfg s ≤ get_latest_message_epoch cfg msg) :
    s ≤ msg.slot := by
  by_contra hnot
  have hlt : msg.slot < s := Nat.lt_of_not_ge hnot
  have hEpochLe : get_latest_message_epoch cfg msg ≤
      compute_epoch_at_slot cfg s := by
    simpa only [get_latest_message_epoch, compute_epoch_at_slot] using
      Nat.div_le_div_right hlt.le
  have heq : compute_epoch_at_slot cfg s = get_latest_message_epoch cfg msg :=
    Nat.le_antisymm hepoch hEpochLe
  have hmsgEq := E.latest_message_eq_honest_vote cfg ext hhb hec hgen
    hv hvote hmsg heq
  have hslotEq : msg.slot = s := congrArg LatestMessage.slot hmsgEq
  exact (Nat.ne_of_lt hlt) hslotEq

/-- The recorded message produced after a slot's honest vote supports that
slot's live block in the message-setter's voting store. The equality of
block ancestry across the voting and observer stores is a later step. -/
theorem recorded_honest_message_supports_live_block_at_vote
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {observer i : ValidatorIndex} (hi : i ∈ E.honest)
    {n m : ℕ} (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hstart : E.slot_at cfg 0 ≤ s) (hend : s < E.slot_at cfg m)
    (hvote : E.vote i s = some (k, a))
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (hHm : E.WithinHorizon cfg m)
    {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w m).latest_messages i = some msg)
    (hepoch : compute_epoch_at_slot cfg s ≤ get_latest_message_epoch cfg msg) :
    ∃ r b k' a', E.BlockAt r b ∧ b.slot = s ∧
      b.proposer_index ∈ E.honest ∧
      E.vote i msg.slot = some (k', a') ∧
      msg.root = a'.data.beacon_block_root ∧
      msg.slot < E.slot_at cfg m ∧
      r ∈ (E.store cfg ext i k').block_roots ∧
      is_ancestor (E.store cfg ext i k')
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨r, b, hblock, hslot, hproposer, _, hsupport⟩ :=
    live.honest_block_each_slot s hstart hend
  obtain ⟨s', k', a', hvote', hmsgEq, hslotEnd⟩ :=
    E.latest_message_has_honest_vote_before_endpoint cfg ext
      hwf hhb hec hgen hi hw hHm hmsg
  have hslotEq : s' = msg.slot := by rw [hmsgEq]
  have hslotStart : s ≤ s' := by
    rw [hslotEq]
    exact E.honest_latest_message_slot_ge_vote cfg ext
      hhb hec hgen hi hvote hmsg hepoch
  obtain ⟨hknown, hancestor⟩ :=
    hsupport i hi s' k' a' hslotStart hslotEnd hvote'
  refine ⟨r, b, k', a', hblock, hslot, hproposer, ?_, ?_, ?_, hknown, ?_⟩
  · simpa only [hslotEq] using hvote'
  · rw [hmsgEq]
  · simpa only [hslotEq] using hslotEnd
  · simpa only [hmsgEq] using hancestor

/-- The time recorded by an honest vote in the live interval is in that
vote's slot. This also supplies the horizon fact used by block relay. -/
theorem honest_vote_time_in_slot
    (hhb : HonestBehavior cfg ext E)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hsm : s < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvote : E.vote i s = some (k, a)) :
    E.WithinHorizon cfg k ∧ E.slot_at cfg k = s := by
  have hassigned : i ∈ E.committee s :=
    hhb.votes_assigned i hi s (by rw [hvote]; simp)
  obtain ⟨k', index, hHk', hslot, hvote'⟩ :=
    hhb.votes_head i hi s hassigned
      (E.slotWithinHorizon_of_le cfg hsm.le hHm) hs0
  rw [hvote] at hvote'
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote'
  rcases hvote' with ⟨hk, _⟩
  rw [← hk] at hHk' hslot
  exact ⟨hHk', hslot⟩

/-- The accepted block-relay law carries every block known to the voter by
its vote time into an honest endpoint after the vote's slot. -/
theorem honest_vote_store_blocks_relay
    (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    {i w : ValidatorIndex} (hi : i ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hsm : s < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvote : E.vote i s = some (k, a)) :
    (E.store cfg ext i k).block_roots ⊆
      (E.store cfg ext w m).block_roots := by
  obtain ⟨hHk, hslot⟩ := E.honest_vote_time_in_slot cfg ext
    hhb hi hs0 hsm hHm hvote
  have hrelayTime : E.slot_at cfg k + 1 ≤ E.slot_at cfg (m + 1) := by
    rw [hslot]
    exact (Nat.succ_le_of_lt hsm).trans
      (E.slot_at_mono cfg (Nat.le_succ m))
  intro r hr
  exact hsyn.block_relay i hi k r hHk hr w hw m hHm hrelayTime

/-- Transport a supported live block from its voter's store to an honest
endpoint. The known vote root is supplied separately, since the live field
only gives knownness of the produced block. -/
theorem live_vote_support_transport
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {i w : ValidatorIndex} (hi : i ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hsm : s < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvote : E.vote i s = some (k, a))
    {r : Root}
    (hr : r ∈ (E.store cfg ext i k).block_roots)
    (hvoteRoot : a.data.beacon_block_root ∈
      (E.store cfg ext i k).block_roots)
    (hanc : is_ancestor (E.store cfg ext i k)
      (get_node_for_root a.data.beacon_block_root)
      (get_node_for_root r) = true) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root a.data.beacon_block_root)
      (get_node_for_root r) = true := by
  have hsub := E.honest_vote_store_blocks_relay cfg ext
    hhb hsyn hi hw hs0 hsm hHm hvote
  have hwalk := E.store_walkKnownK cfg ext hwf hec hgen i k
    r hr a.data.beacon_block_root hvoteRoot
  exact is_ancestor_transport cfg ext hwf hsub hvoteRoot hr hwalk hanc

/-- An accepted honest vote names the known fork-choice head at its voting
store. This discharges the remaining known-root input of support transport. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.honest_vote_root_known
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hsm : s < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hvote : E.vote i s = some (k, a)) :
    a.data.beacon_block_root ∈ (E.store cfg ext i k).block_roots := by
  obtain ⟨hHk, _⟩ := E.honest_vote_time_in_slot cfg ext
    h.trajectory.honest_behavior hi hs0 hsm hHm hvote
  have hassigned : i ∈ E.committee s :=
    h.trajectory.honest_behavior.votes_assigned i hi s (by rw [hvote]; simp)
  obtain ⟨k', index, _, _, hvote'⟩ :=
    h.trajectory.honest_behavior.votes_head i hi s hassigned
      (E.slotWithinHorizon_of_le cfg hsm.le hHm) hs0
  rw [hvote] at hvote'
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote'
  rcases hvote' with ⟨hk, ha⟩
  rw [← hk] at ha
  have hhead := E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
    h.semantics h.trajectory h.anchor_eq h.anchor_boundary hi k hHk
  have hroot : a.data.beacon_block_root =
      (get_head cfg (E.store cfg ext i k)).root := by
    rw [ha]
    rfl
  rw [hroot]
  exact hhead

/-- The target epoch of an accepted honest vote is its assigned slot's
epoch. The head state is at or before the voting slot. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.honest_vote_target_epoch
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} {k : ℕ} {index : CommitteeIndex}
    (hslot : E.slot_at cfg k = s)
    (hHk : E.WithinHorizon cfg k) :
    (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target.epoch =
      compute_epoch_at_slot cfg s := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hparent⟩ :=
    h.trajectory.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hgenSlot⟩
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot hparent
  have hhead := E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
    h.semantics h.trajectory h.anchor_eq h.anchor_boundary hi k hHk
  have hcore := E.store_wellFormedStoreCore cfg ext
    h.trajectory.externals_coherence.state_transition_slot hgws.core i k
  have hstateSlot : ((E.store cfg ext i k).block_states
      (get_head cfg (E.store cfg ext i k)).root).slot ≤ s := by
    rw [hcore.2 _ hhead]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      h.trajectory.whole_seconds hgenShort i k _ hhead
    rwa [E.store_current_slot cfg ext i k, hslot] at hblockSlot
  rw [honest_attestation_data_eq]
  exact honest_attestation_data_target_epoch cfg ext
    (E.store cfg ext i k) s index
    h.trajectory.externals_coherence.process_slots_slot hstateSlot

/-- Recorded honest support for each live block, now in the observer's
endpoint store. Vote ubiquity supplies the epoch premise at call sites. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.recorded_live_block_support
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer i : ValidatorIndex} (hi : i ∈ E.honest)
    {n m : ℕ} (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hs0 : E.slot_at cfg 0 ≤ s) (hsm : s < E.slot_at cfg m)
    (hvote : E.vote i s = some (k, a))
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (hHm : E.WithinHorizon cfg m)
    {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w m).latest_messages i = some msg)
    (hepoch : compute_epoch_at_slot cfg s ≤ get_latest_message_epoch cfg msg) :
    ∃ r b, E.BlockAt r b ∧ b.slot = s ∧
      b.proposer_index ∈ E.honest ∧
      r ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  obtain ⟨r, b, k', a', hblock, hslot, hproposer, hvote', hroot,
    hslotEnd, hrKnown, hanc⟩ :=
    E.recorded_honest_message_supports_live_block_at_vote cfg ext
      h.trajectory.wellFormed h.trajectory.honest_behavior
      h.trajectory.externals_coherence hgen hi live hs0 hsm hvote
      hw hHm hmsg hepoch
  have hs0' : E.slot_at cfg 0 ≤ msg.slot :=
    hs0.trans (E.honest_latest_message_slot_ge_vote cfg ext
      h.trajectory.honest_behavior h.trajectory.externals_coherence
      hgen hi hvote hmsg hepoch)
  have hrootKnown : a'.data.beacon_block_root ∈
      (E.store cfg ext i k').block_roots :=
    h.honest_vote_root_known cfg ext E hi hs0' hslotEnd hHm hvote'
  have hancVote : is_ancestor (E.store cfg ext i k')
      (get_node_for_root a'.data.beacon_block_root)
      (get_node_for_root r) = true := by
    simpa only [hroot] using hanc
  have htransport := E.live_vote_support_transport cfg ext
    h.trajectory.wellFormed h.trajectory.honest_behavior
    h.completed_calls.synchrony h.trajectory.externals_coherence
    h.trajectory.genesis_structure hi hw hs0' hslotEnd hHm
    hvote' hrKnown hrootKnown hancVote
  have hsub := E.honest_vote_store_blocks_relay cfg ext
    h.trajectory.honest_behavior h.completed_calls.synchrony
    hi hw hs0' hslotEnd hHm hvote'
  exact ⟨r, b, hblock, hslot, hproposer, hsub hrKnown,
    by simpa only [hroot] using htransport⟩

/-- Vote delivery from the accepted proof's local store domain. This is the
`vote_ubiquity` route without the legacy broad justification interface. -/
theorem vote_ubiquity_of_selected_margin_domain
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hdom : SelectedMarginDomain cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s) (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hbound : ((E.store cfg ext v n).blocks
      (E.store cfg ext v n).justified_checkpoint.root).slot ≤
      compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
    {m : ℕ} (hm : E.slot_start cfg (s + 1) ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        get_latest_message_epoch cfg msg := by
  have hhead := E.head_root_known_of_selectedMarginDomain cfg ext hdom hv n hHn
  have hjc := hdom.justified_root_known v hv n hHn
  have hwalk := E.store_walkKnownK cfg ext hwf hec hgen v n
    (E.store cfg ext v n).justified_checkpoint.root hjc
    (get_head cfg (E.store cfg ext v n)).root hhead
  apply E.vote_ubiquity cfg ext hwf hhb hsyn hec hdiv hgen hv hw hn hHn
    hvote
  · simpa only [honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root] using hhead
  · simpa only [honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root] using
      (WalkKnown.mono hbound hwalk)
  · exact hm
  · exact hHm

/-- The accepted bundle supplies vote ubiquity without a legacy
`JustificationInterface` field. The trusted-anchor target walk closes the
last vote-landing domain condition. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.vote_ubiquity
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex}
    (hs0 : E.slot_at cfg 0 ≤ s)
    (hn : E.slot_at cfg n = s) (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    {m : ℕ} (hm : E.slot_start cfg (s + 1) ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        get_latest_message_epoch cfg msg := by
  have hhead := E.headRootKnown_of_acceptedGlobalTrajectory cfg ext
    h.semantics h.trajectory h.anchor_eq h.anchor_boundary hv n hHn
  have hwalkDomain := E.postAnchorHonestVoteTargetWalkDomain_of_acceptedGlobalTrajectory
    cfg ext h.semantics h.trajectory h.anchor_eq h.anchor_boundary
  have hwalk := hwalkDomain v hv s n index hs0 hHn hn hvote
  have hheadVote :
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root ∈
        (E.store cfg ext v n).block_roots := by
    simpa only [honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root] using hhead
  have hwalkVote : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root := by
    simpa only [honest_attestation_data_eq,
      honest_attestation_data_beacon_block_root] using hwalk
  exact E.vote_ubiquity cfg ext h.trajectory.wellFormed h.trajectory.honest_behavior
    h.completed_calls.synchrony h.trajectory.externals_coherence
    h.trajectory.whole_seconds h.trajectory.genesis_structure
    hv hw hn hHn hvote hheadVote hwalkVote hm hHm

/-- An assigned honest voter has a recorded endpoint message that supports
an honestly proposed block of the queried slot. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.live_vote_recorded_support
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {observer i : ValidatorIndex} (hi : i ∈ E.honest)
    {n m : ℕ} (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s) (hsm : s < E.slot_at cfg m)
    (hcommittee : i ∈ E.committee s)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    (hHm : E.WithinHorizon cfg m)
    (hdelivery : E.slot_start cfg (s + 1) ≤ m) :
    ∃ msg r b,
      (E.store cfg ext w m).latest_messages i = some msg ∧
      E.BlockAt r b ∧ b.slot = s ∧ b.proposer_index ∈ E.honest ∧
      r ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨k, index, hHk, hslot, hvote⟩ :=
    h.trajectory.honest_behavior.votes_head i hi s hcommittee
      (E.slotWithinHorizon_of_le cfg hsm.le hHm) hs0
  obtain ⟨msg, hmsg, hEpoch⟩ :=
    h.vote_ubiquity cfg ext E hi hw hs0 hslot hHk hvote
      hdelivery hHm
  have htarget := h.honest_vote_target_epoch cfg ext E hi
    (index := index) hslot hHk
  have hEpoch' : compute_epoch_at_slot cfg s ≤
      get_latest_message_epoch cfg msg := by
    rw [← htarget]
    exact hEpoch
  obtain ⟨r, b, hblock, hblockSlot, hproposer, hr, hanc⟩ :=
    h.recorded_live_block_support cfg ext E hi live hs0 hsm hvote
      hw hHm hmsg hEpoch'
  exact ⟨msg, r, b, hmsg, hblock, hblockSlot, hproposer, hr, hanc⟩

/-- A latest message from an honest vote in the live interval names a vote
for a descendant of that slot's honestly proposed block. The ancestry is
in the voting store; support at another store needs transport. -/
theorem latest_honest_message_extends_live_block
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v observer : ValidatorIndex} (hv : v ∈ E.honest)
    {n m : ℕ} (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hstart : E.slot_at cfg 0 ≤ s) (hend : s < E.slot_at cfg m)
    (hvote : E.vote v s = some (k, a))
    {w : ValidatorIndex} {t : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages v = some msg)
    (hepoch : compute_epoch_at_slot cfg s = get_latest_message_epoch cfg msg) :
    ∃ r b, E.BlockAt r b ∧ b.slot = s ∧
      b.proposer_index ∈ E.honest ∧
      r ∈ (E.store cfg ext v k).block_roots ∧
      is_ancestor (E.store cfg ext v k)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨r, b, hblock, hslot, hproposer, _, hsupport⟩ :=
    live.honest_block_each_slot s hstart hend
  have hroot : msg.root = a.data.beacon_block_root := by
    have heq := E.latest_message_eq_honest_vote cfg ext hhb hec hgen
      hv hvote hmsg hepoch
    exact congrArg LatestMessage.root heq
  obtain ⟨hknown, hancestor⟩ :=
    hsupport v hv s k a (Nat.le_refl s) hend hvote
  exact ⟨r, b, hblock, hslot, hproposer, hknown, by simpa [hroot] using hancestor⟩

end Execution

/-- The configured margin makes the honest full-epoch stake exceed the
undiscounted threshold with the entire configured adversarial allowance.
The executable one-confirmation proof must identify its actual support and
threshold with these quantities. -/
theorem configured_margin_full_epoch_arith
    {total nonHonest honest allowance boost : ℕ}
    (hpart : honest + nonHonest = total)
    (hmargin : 2 * nonHonest + 2 * allowance + boost < total) :
    honest > (total + boost + 2 * allowance) / 2 := by
  omega

/-- A direct executable threshold bridge. Its premises are the support and
window bounds to be supplied by the execution proof; the discount can only
lower the threshold. -/
theorem one_confirmed_of_bounded_window
    (store : Store Root) (balanceSource : BeaconState Root) (block : Root)
    {total nonHonest honest allowance boost : ℕ}
    (hpart : honest + nonHonest = total)
    (hmargin : 2 * nonHonest + 2 * allowance + boost < total)
    (hsupport : honest ≤ get_attestation_score cfg store
      (get_node_for_root block) balanceSource)
    (hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      ((store.blocks (store.blocks block).parent_root).slot + 1)
      (get_current_slot cfg store - 1) ≤ total)
    (hboost : compute_proposer_score cfg balanceSource ≤ boost)
    (hadversarial : get_adversarial_weight cfg ext store balanceSource block ≤
      allowance) :
    is_one_confirmed cfg ext store balanceSource block = true := by
  have hbudget : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      ((store.blocks (store.blocks block).parent_root).slot + 1)
      (get_current_slot cfg store - 1) +
      compute_proposer_score cfg balanceSource +
      2 * get_adversarial_weight cfg ext store balanceSource block ≤
      total + boost + 2 * allowance :=
    Nat.add_le_add (Nat.add_le_add hwindow hboost)
      (Nat.mul_le_mul_left 2 hadversarial)
  have hthreshold : compute_safety_threshold cfg ext store block balanceSource ≤
      (total + boost + 2 * allowance) / 2 := by
    simp only [compute_safety_threshold]
    split_ifs
    · apply Nat.div_le_div_right
      exact (Nat.sub_le _ _).trans hbudget
    · exact Nat.zero_le _
  have hfull := configured_margin_full_epoch_arith hpart hmargin
  have hscore : compute_safety_threshold cfg ext store block balanceSource <
      get_attestation_score cfg store (get_node_for_root block) balanceSource :=
    lt_of_le_of_lt hthreshold (lt_of_lt_of_le hfull hsupport)
  simpa [is_one_confirmed] using hscore

end FastConfirmation.Spec

end
