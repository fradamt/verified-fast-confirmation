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


/-- Fixed-block form of the endpoint bridge. The live witness is selected
once outside the validator quantifier so the same block receives every
honest committee member's recorded support. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.recorded_fixed_live_block_support
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {m : ℕ} (hHm : E.WithinHorizon cfg m)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ t k a,
      s ≤ t → t < E.slot_at cfg m → E.vote j t = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {t : Slot} (hst : s ≤ t)
    {k : ℕ} {a : Attestation Root}
    (hvote : E.vote i t = some (k, a))
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w m).latest_messages i = some msg)
    (hepoch : compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg msg) :
    r ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := h.trajectory.genesis_structure
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  obtain ⟨s', k', a', hvote', hmsgEq, hslotEnd⟩ :=
    E.latest_message_has_honest_vote_before_endpoint cfg ext
      h.trajectory.wellFormed h.trajectory.honest_behavior
      h.trajectory.externals_coherence hgen hi hw hHm hmsg
  have hslotEq : s' = msg.slot := by rw [hmsgEq]
  have hslotStart : s ≤ s' := by
    rw [hslotEq]
    exact hst.trans (E.honest_latest_message_slot_ge_vote cfg ext
      h.trajectory.honest_behavior h.trajectory.externals_coherence
      hgen hi hvote hmsg hepoch)
  obtain ⟨hrKnown, hanc⟩ := hsupport i hi s' k' a'
    hslotStart hslotEnd hvote'
  have hs0' : E.slot_at cfg 0 ≤ msg.slot := hs0.trans (hslotEq ▸ hslotStart)
  have hrootKnown : a'.data.beacon_block_root ∈
      (E.store cfg ext i k').block_roots :=
    h.honest_vote_root_known cfg ext E hi hs0'
      (by simpa only [hslotEq] using hslotEnd) hHm
      (by simpa only [hslotEq] using hvote')
  have htransport := E.live_vote_support_transport cfg ext
    h.trajectory.wellFormed h.trajectory.honest_behavior
    h.completed_calls.synchrony h.trajectory.externals_coherence
    h.trajectory.genesis_structure hi hw hs0'
    (by simpa only [hslotEq] using hslotEnd) hHm
    (by simpa only [hslotEq] using hvote') hrKnown hrootKnown hanc
  have hsub := E.honest_vote_store_blocks_relay cfg ext
    h.trajectory.honest_behavior h.completed_calls.synchrony
    hi hw hs0' (by simpa only [hslotEq] using hslotEnd) hHm
    (by simpa only [hslotEq] using hvote')
  refine ⟨hsub hrKnown, ?_⟩
  simpa only [hmsgEq] using htransport


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


/-- An honest assignment at a later slot supplies endpoint support to a
fixed earlier live block once that vote has met the delivery deadline. -/
theorem AcceptedActualFCRNextSlotSafetyAssumptions.fixed_live_block_support_of_assignment
    (h : E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    {m : ℕ} (hHm : E.WithinHorizon cfg m)
    {r : Root}
    (hsupport : ∀ j ∈ E.honest, ∀ u k a,
      s ≤ u → u < E.slot_at cfg m → E.vote j u = some (k, a) →
        r ∈ (E.store cfg ext j k).block_roots ∧
        is_ancestor (E.store cfg ext j k)
          (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root r) = true)
    {t : Slot} (hst : s ≤ t) (htm : t < E.slot_at cfg m)
    {i w : ValidatorIndex} (hi : i ∈ E.honest) (hcommittee : i ∈ E.committee t)
    (hw : w ∈ E.honest)
    (hdelivery : E.slot_start cfg (t + 1) ≤ m) :
    ∃ msg, (E.store cfg ext w m).latest_messages i = some msg ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨k, index, hHk, hslotVote, hvote⟩ :=
    h.trajectory.honest_behavior.votes_head i hi t hcommittee
      (E.slotWithinHorizon_of_le cfg htm.le hHm) (hs0.trans hst)
  obtain ⟨msg, hmsg, hEpoch⟩ :=
    h.vote_ubiquity cfg ext E hi hw (hs0.trans hst)
      hslotVote hHk hvote hdelivery hHm
  have htarget := h.honest_vote_target_epoch cfg ext E hi
    (index := index) hslotVote hHk
  have hEpoch' : compute_epoch_at_slot cfg t ≤
      get_latest_message_epoch cfg msg := by
    rw [← htarget]
    exact hEpoch
  have hrecorded := h.recorded_fixed_live_block_support cfg ext E
    hi hHm hs0 hsupport hst hvote hw hmsg hEpoch'
  exact ⟨msg, hmsg, hrecorded.2⟩




end Execution



end FastConfirmation.Spec

end
