module
public import FastConfirmation.Spec.Proof.AnchorClose
public import FastConfirmation.Spec.Proof.CertExtract
public import FastConfirmation.Spec.Proof.VoterIndex

@[expose] public section

/-!
# Spec / Proof / Nucleus

The honest-quorum, vote-time, and cross-store transport nucleus for the
observed-anchor covering route.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

private theorem honest_quorum_arith {T Q B W C : ℕ}
    (hT : 0 < T) (hquorum : 2 * T ≤ 3 * Q) (hQB : Q ≤ B)
    (hfrac : 100 * B ≤ C * W) (hC : C ≤ 25) (hWT : W ≤ T) : False := by
  have hCW : C * W ≤ 25 * W := Nat.mul_le_mul_right W hC
  have hW25 : 25 * W ≤ 25 * T := Nat.mul_le_mul_left 25 hWT
  omega

namespace Execution

variable (E : Execution Root)

/-- A positive two-thirds quorum inside a horizon-bounded committee span
contains an honest validator. The explicit positivity premise excludes the
abstract model's degenerate zero-total-active configuration. -/
theorem honest_quorum_member (hSA : SpecAssumptions cfg ext E)
    (htotal : 0 < E.total_active cfg) {lo hi : Slot}
    {S : Finset ValidatorIndex} (hlohi : lo ≤ hi)
    (hhiH : E.SlotWithinHorizon cfg hi)
    (hS : S ⊆ E.span_committee lo hi)
    (hquorum : 2 * E.total_active cfg ≤ 3 * E.weight S) :
    ∃ i ∈ S, i ∈ E.honest := by
  obtain ⟨hgen, _hwfE, hdiv, _hhb, _hsync, hec, hsv, hbb, _hji⟩ := hSA
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hstore, _hslot, _hparent⟩ := hgen
    exact ⟨ast, ablk, hstore⟩
  have hanchor_slot := E.anchor_state_slot_le cfg hdiv hgen'
  have hanchor_epoch : get_current_epoch cfg E.anchor_state < E.verification_horizon := by
    exact lt_of_le_of_lt
      (by simpa only [get_current_epoch] using Nat.div_le_div_right hanchor_slot)
      hsv.genesis_within_horizon.2.2
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlohi hhiH
  have hspan_active : E.span_committee lo hi ⊆
      (get_active_validator_indices E.anchor_state
        (get_current_epoch cfg E.anchor_state)).toFinset := by
    intro i hi_mem
    rw [List.mem_toFinset]
    apply mem_active_of_active
    simpa only [Execution.registry] using
      (E.span_member_active cfg ext hec hsv hi_mem hhiH
        (get_current_epoch cfg E.anchor_state) hanchor_epoch)
  have hspan_total : E.weight (E.span_committee lo hi) ≤ E.total_active cfg := by
    refine le_trans (E.weight_mono hspan_active) ?_
    simp only [Execution.weight, Execution.weight_of, Execution.total_active,
      get_total_active_balance, get_total_balance, Execution.registry]
    exact Nat.le_max_right _ _
  by_contra hnone
  have hSbyz : S ⊆ (E.span_committee lo hi).filter (fun i => i ∉ E.honest) := by
    intro i hiS
    exact Finset.mem_filter.mpr ⟨hS hiS, fun hiH => hnone ⟨i, hiS, hiH⟩⟩
  exact honest_quorum_arith htotal hquorum (E.weight_mono hSbyz)
    (hbb.span_fraction lo hi hloH hhiH)
    cfg.confirmation_byzantine_threshold_le hspan_total

/-- An honest member named by a scheduled target attestation has a genuine
vote record at an indexed second. In the strictly-later-epoch branch, the
target epoch itself puts the vote after the confirmation slot; the upper bound
uses the exact `validate_on_attestation` no-future gate, which is not carried
by `justified_requires_targets`. -/
theorem honest_member_vote_indexed (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk →
        ablk.message.slot = GENESIS_SLOT)
    {i u : ValidatorIndex} {k_schedule n m : ℕ} {ifb : Bool}
    {a : Attestation Root} {c : Checkpoint Root} {es : Slot}
    (hi : i ∈ E.honest)
    (_hkScheduleH : E.WithinHorizon cfg k_schedule)
    (haSlotH : E.SlotWithinHorizon cfg a.data.slot)
    (hscheduled : Event.attestation a ifb ∈ E.schedule u k_schedule)
    (hi_attests : i ∈ a.attesting_indices) (htarget : a.data.target = c)
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hepoch : compute_epoch_at_slot cfg (es + 1) < c.epoch)
    (hprocessed : a.data.slot + 1 ≤ E.slot_at cfg m)
    (_hHm : E.WithinHorizon cfg m) :
    ∃ (k : ℕ) (index : CommitteeIndex),
      E.WithinHorizon cfg k ∧ E.slot_at cfg k = a.data.slot ∧
      E.vote i a.data.slot =
        some (k, honest_attestation cfg ext (E.store cfg ext i k) a.data.slot index i) ∧
      a.data =
        (honest_attestation cfg ext (E.store cfg ext i k) a.data.slot index i).data ∧
      n + 1 ≤ k ∧ E.slot_at cfg k < E.slot_at cfg m := by
  obtain ⟨hgen, hwfE, hdiv, hhb, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hcur0 : E.slot_at cfg 0 = 0 := by
    have hcur := E.store_current_slot cfg ext i 0
    rw [show E.store cfg ext i 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at hcur
    rw [← hcur, hslot, hanchor0 ast ablk hgeq, GENESIS_SLOT]
  obtain ⟨k_vote, a_vote, hvote, hdata⟩ :=
    hhb.no_forgery u k_schedule a ifb hscheduled i hi hi_attests
  have hcommittee : i ∈ E.committee a.data.slot :=
    hhb.votes_assigned i hi a.data.slot (by rw [hvote]; exact Option.some_ne_none _)
  have hs0 : E.slot_at cfg 0 ≤ a.data.slot := by rw [hcur0]; exact Nat.zero_le _
  obtain ⟨k, index, hkH, hk, hvote_head⟩ :=
    hhb.votes_head i hi a.data.slot hcommittee haSlotH hs0
  rw [hvote_head] at hvote
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote
  obtain ⟨_, hattestation⟩ := hvote
  have hdata_head : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k) a.data.slot index i).data :=
    hdata.trans (congrArg (fun x : Attestation Root => x.data) hattestation.symm)
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hhead_known : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots := E.head_root_known cfg ext hji hi k hkH
  have hhead_slot : ((E.store cfg ext i k).block_states
      (get_head cfg (E.store cfg ext i k)).root).slot ≤ a.data.slot := by
    have hcore :=
      E.store_wellFormedStoreCore cfg ext hec.state_transition_slot hgws.core i k
    rw [hcore.2 _ hhead_known]
    have hblock_slot := E.store_blocks_slot_le_current cfg ext hdiv
      ⟨ast, ablk, hgeq, hslot⟩ i k _ hhead_known
    rwa [E.store_current_slot cfg ext i k, hk] at hblock_slot
  have htarget_epoch :
      (honest_attestation cfg ext (E.store cfg ext i k) a.data.slot index i).data.target.epoch =
        c.epoch := by
    rw [← hdata_head, htarget]
  have hvote_epoch : compute_epoch_at_slot cfg a.data.slot = c.epoch := by
    rw [← htarget_epoch]
    exact (honest_attestation_data_target_epoch cfg ext (E.store cfg ext i k)
      a.data.slot index hec.process_slots_slot hhead_slot).symm
  have hbase_lt_vote : es + 1 < a.data.slot := by
    by_contra hnot
    have hmono := ce_mono cfg (not_lt.mp hnot)
    rw [hvote_epoch] at hmono
    exact (Nat.not_le_of_gt hepoch) hmono
  have hlower : n + 1 ≤ k :=
    Nat.le_of_lt (E.index_lt_of_slot_at_lt cfg (by rw [hn, hk]; exact hbase_lt_vote))
  refine ⟨k, index, hkH, hk, hvote_head, hdata_head, hlower, ?_⟩
  rw [hk]
  exact Nat.lt_of_succ_le hprocessed

/-- Read back an indexed honest vote at its source store: its wire slot is the
voter second's slot, its FFG target is the checkpoint block of its source head,
and its LMD root is that head. -/
theorem recorded_honest_vote_source
    {i : ValidatorIndex} {s : Slot} {k : ℕ} {index : CommitteeIndex}
    {a : Attestation Root}
    (hk : E.slot_at cfg k = s)
    (hvote : E.vote i s =
      some (k, honest_attestation cfg ext (E.store cfg ext i k) s index i))
    (hdata : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data) :
    E.slot_at cfg k = s ∧
      E.vote i s =
        some (k, honest_attestation cfg ext (E.store cfg ext i k) s index i) ∧
      a.data.target.root = get_checkpoint_block cfg (E.store cfg ext i k)
        (get_head cfg (E.store cfg ext i k)).root a.data.target.epoch ∧
      a.data.beacon_block_root = (get_head cfg (E.store cfg ext i k)).root := by
  refine ⟨hk, hvote, ?_, ?_⟩
  · rw [hdata]
    exact honest_attestation_data_target_root cfg ext (E.store cfg ext i k) s index
  · rw [hdata]
    exact honest_attestation_data_beacon_block_root cfg ext (E.store cfg ext i k) s index

/-- `get_checkpoint_block` is invariant when the destination contains the
source block set: provenance gives block agreement and `get_ancestor_congr`
rewrites the boundary walk. -/
theorem checkpoint_block_transport (hwf : WellFormedExecution E)
    {v w : ValidatorIndex} {n m : ℕ} {H : Root} {e : Epoch}
    (hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext w m).block_roots)
    (hH : H ∈ (E.store cfg ext v n).block_roots)
    (hwalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg e) H) :
    get_checkpoint_block cfg (E.store cfg ext v n) H e =
      get_checkpoint_block cfg (E.store cfg ext w m) H e := by
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x :=
    fun x hx => hwf.blocks_agree (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext w m) hx (hsub hx)
  simp only [get_checkpoint_block]
  rw [get_ancestor_congr hagree hH hwalk]

/-- Transport a voter's earlier source-head facts to the queried honest store.
The strict slot inequality supplies the block-relay deadline; the ancestry fact
then crosses stores through `is_ancestor_transport`. -/
theorem head_facts_transport (hwf : WellFormedExecution E)
    (hsync : Synchrony cfg ext E)
    {i w : ValidatorIndex} (hi : i ∈ E.honest) (hw : w ∈ E.honest)
    {k m : ℕ} {H glc : Root}
    (hHk : E.WithinHorizon cfg k) (hHm : E.WithinHorizon cfg m)
    (hkm : E.slot_at cfg k < E.slot_at cfg m)
    (hH : H ∈ (E.store cfg ext i k).block_roots)
    (hglc : glc ∈ (E.store cfg ext i k).block_roots)
    (hwalk : WalkKnown (E.store cfg ext i k)
      ((E.store cfg ext i k).blocks glc).slot H)
    (hHglc : is_ancestor (E.store cfg ext i k)
      (get_node_for_root H) (get_node_for_root glc) = true) :
    (E.store cfg ext i k).block_roots ⊆ (E.store cfg ext w m).block_roots ∧
      H ∈ (E.store cfg ext w m).block_roots ∧
      glc ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root H) (get_node_for_root glc) = true := by
  have hgate : E.slot_at cfg k + 1 ≤ E.slot_at cfg (m + 1) :=
    le_trans hkm (E.slot_at_mono cfg (Nat.le_succ m))
  have hsub : (E.store cfg ext i k).block_roots ⊆
      (E.store cfg ext w m).block_roots :=
    E.blockRoots_subset_of_legacy_relay cfg ext hsync hi hw hHk hHm hgate
  exact ⟨hsub, hsub hH, hsub hglc,
    is_ancestor_transport cfg ext hwf hsub hH hglc hwalk hHglc⟩

/-- **The missing current-epoch E5 bridge.** This is the exact equal branch of
the endpoint-epoch trichotomy needed by the observed-anchor producer. The
confirmation-side `glc` is anchored at the rotated observed/greatest-unrealized
checkpoint, and the endpoint carries a justified checkpoint in the confirmation
epoch; the required result is `AnchorCovSupply`'s covering disjunction.

This is deliberately exposed as a predicate, not asserted as a theorem. It is
the current-epoch FFG/LMD interplay condition:
the spec gates current-epoch confirmations on
`will_current_target_be_justified` precisely so this holds; formal derivation
requires the cross-validator target-agreement export whose non-circularity
constraint `Statements/Premises/Live.lean` documents. Concretely,
`HonestVotesSupportTarget` quantifies over same-slot and future target-epoch
votes, whereas the available shell IH covers only strictly earlier endpoint
stores, and `justified_requires_targets` carries no processed-by-endpoint time
conjunct. The committed `observed_justified` export supplies only `JustifiedIn`
for the rotated checkpoint, so deriving this bridge without the missing export
would be circular. -/
def CurrentEpochCoveringBridge (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ,
    get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n))
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1) →
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
        v (n + 1) →
      (E.store cfg ext w m).justified_checkpoint.epoch =
        compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)))
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true ∨
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true

/-- The strictly-later-epoch observed-anchor covering disjunction. An earlier
honest voter's source head descends from `glc` by the shell IH and from the
endpoint justified root by its transported FFG checkpoint equation; two
ancestors of that common head are comparable. The equal-epoch complement is
exactly `CurrentEpochCoveringBridge`; the conclusion here is in
`AnchorCovSupply`'s field shape. -/
theorem covering_comparability (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk →
        ablk.message.slot = GENESIS_SLOT)
    {i w : ValidatorIndex} (hi : i ∈ E.honest) (hw : w ∈ E.honest)
    {n k m : ℕ} {glc : Root}
    (hHk : E.WithinHorizon cfg k) (hHm : E.WithinHorizon cfg m)
    (hnk : n + 1 ≤ k) (hkm : E.slot_at cfg k < E.slot_at cfg m)
    (hcheckpoint : (E.store cfg ext w m).justified_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext i k)
        (get_head cfg (E.store cfg ext i k)).root
        (E.store cfg ext w m).justified_checkpoint.epoch)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
        is_ancestor (E.store cfg ext w' m')
          (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    is_ancestor (E.store cfg ext w m) (get_node_for_root glc)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true ∨
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root glc) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  let H := (get_head cfg (E.store cfg ext i k)).root
  let jc := (E.store cfg ext w m).justified_checkpoint
  obtain ⟨hwf_i, hwalk_i, _hjc_i⟩ :=
    E.store_domainK cfg ext hwfE hec hgen' hji i hi k hHk
  have hH : H ∈ (E.store cfg ext i k).block_roots :=
    E.head_root_known cfg ext hji hi k hHk
  have hanchor_mem0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor_mem : ablk.root ∈ (E.store cfg ext i k).block_roots :=
    (E.store_storeLE cfg ext i (Nat.zero_le k)).1 hanchor_mem0
  have hanchor_slot : ((E.store cfg ext i k).blocks ablk.root).slot = 0 := by
    rw [E.store_anchor_block cfg ext hwfE hgeq i k hanchor_mem,
      hanchor0 ast ablk hgeq, GENESIS_SLOT]
  have hwalk0 : WalkKnown (E.store cfg ext i k) 0 H := by
    have hwalk := hwalk_i ablk.root hanchor_mem H hH
    rwa [hanchor_slot] at hwalk
  have hHglc_i : is_ancestor (E.store cfg ext i k)
      (get_node_for_root H) (get_node_for_root glc) = true := by
    rw [get_node_for_root, is_ancestor_pending_root_eq _ _ _ .pending
      (get_head cfg (E.store cfg ext i k)).payload_status]
    exact hIH i hi k hnk hkm hHk
  have hglc : glc ∈ (E.store cfg ext i k).block_roots :=
    mem_of_is_ancestor_above_anchor hwf_i hwalk0 (Nat.zero_le _) hHglc_i
  have hwalk_glc_i : WalkKnown (E.store cfg ext i k)
      ((E.store cfg ext i k).blocks glc).slot H := hwalk_i glc hglc H hH
  obtain ⟨hsub, hH_wm, hglc_wm, hHglc_wm⟩ :=
    E.head_facts_transport cfg ext hwfE hsync hi hw hHk hHm hkm
      hH hglc hwalk_glc_i hHglc_i
  have hwalk_boundary_i : WalkKnown (E.store cfg ext i k)
      (compute_start_slot_at_epoch cfg jc.epoch) H := by
    exact hwalk0.mono (Nat.zero_le _)
  have hcheckpoint_transport := E.checkpoint_block_transport cfg ext hwfE hsub hH
    hwalk_boundary_i
  have hcheckpoint_wm : get_checkpoint_block cfg (E.store cfg ext w m) H jc.epoch =
      jc.root := hcheckpoint_transport.symm.trans hcheckpoint.symm
  have hsource_root :
      (get_ancestor (E.store cfg ext i k) (ForkChoiceNode.mk H .pending)
        (compute_start_slot_at_epoch cfg jc.epoch)).root = jc.root := by
    simpa only [get_checkpoint_block] using hcheckpoint.symm
  have hsource_spec := get_ancestor_spec hwf_i hwalk_boundary_i
  rw [hsource_root] at hsource_spec
  obtain ⟨hwf_wm, hwalk_wm, hjc_wm⟩ :=
    E.store_domainK cfg ext hwfE hec hgen' hji w hw m hHm
  have hjc_agree : (E.store cfg ext i k).blocks jc.root =
      (E.store cfg ext w m).blocks jc.root :=
    hwfE.blocks_agree (E.blockProvenance cfg ext i k)
      (E.blockProvenance cfg ext w m) hsource_spec.1 hjc_wm
  have hjc_boundary : ((E.store cfg ext w m).blocks jc.root).slot ≤
      compute_start_slot_at_epoch cfg jc.epoch := by
    rw [← hjc_agree]
    exact hsource_spec.2
  simp only [get_checkpoint_block] at hcheckpoint_wm
  have hHjc_wm : is_ancestor (E.store cfg ext w m)
      (get_node_for_root H) (get_node_for_root jc.root) = true := by
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
    have hcomp := get_ancestor_comp_root hwf_wm hjc_boundary
      (hwalk_wm jc.root hjc_wm H hH_wm)
    rw [hcheckpoint_wm, get_ancestor_stop (le_refl _)] at hcomp
    exact hcomp.symm
  exact is_ancestor_comparable hwf_wm
    (hwalk_wm jc.root hjc_wm H hH_wm)
    (hwalk_wm glc hglc_wm H hH_wm) hHjc_wm hHglc_wm

end Execution

end FastConfirmation.Spec

end
