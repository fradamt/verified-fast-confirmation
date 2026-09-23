module
public import FastConfirmationProofs.Execution.Trajectory.LatestMessageProvenance
public import FastConfirmationProofs.Execution.Trajectory.WFTrajectory
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Execution.Trajectory.PayloadPersistence
public import FastConfirmationProofs.Execution.StoreInvariants.BlockStateAgreement

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / Delivery

This module proves three facts about delivery of honest votes:

1. **`blocks_slot_le_current`** — a trajectory invariant: every known block's
   slot is at most the store's current slot. Genesis: the anchor's slot equals
   the initial current slot (the `get_forkchoice_store` time seed, exact under
   whole-second slots). Step: `on_block`'s not-future gate bounds each added
   block by the store's current slot, which the event fold holds fixed within a
   second; `on_tick` only advances the clock.

2. **Application success** — the delivered honest attestation passes
   `validate_on_attestation` / `is_valid_indexed_attestation` at the receiving
   node. The store-independent conjunct (`target.epoch =
   compute_epoch_at_slot a.data.slot`) is discharged from the honest
   construction; the epoch-window and current-slot conjuncts are pure `Clock`
   arithmetic; the block-knowledge and ancestor-agreement conjuncts are the
   cross-store transport steps — assembled as a hypothesis-shaped lemma with the
   transport facts as explicit premises.

3. **Ubiquity** — the delivered message persists at every honest node from the
   next slot on, using the `update_latest_messages` fold effect and the
   `no_forgery`/`committee_assignment_unique` uniqueness argument.

The whole-second-slots hypothesis `hdiv : 1000 ∣ cfg.slot_duration_ms` (mainnet
`12000` ms) is the same domain condition `Clock.lean` carries; it is needed for
the genesis case of `blocks_slot_le_current` (the anchor's slot lands exactly on its
boundary second).
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## The block-slot bound predicate -/

/-- Every known block's slot is at most `sl`. Instantiated along a trajectory
with `sl = E.slot_at cfg n` (the store's current slot). -/
def BlocksSlotLe (sl : Slot) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots, (store.blocks r).slot ≤ sl

namespace BlocksSlotLe

/-- The bound is an upper bound: a larger bound is weaker. -/
theorem mono_sl {sl sl' : Slot} {store : Store Root} (h : BlocksSlotLe sl store)
    (hle : sl ≤ sl') : BlocksSlotLe sl' store :=
  fun r hr => (h r hr).trans hle

end BlocksSlotLe

/-- `SameBlocks` carries the block-slot bound across: it reads only
`block_roots` and `blocks`. -/
theorem SameBlocks.blocksSlotLe {sl : Slot} {s t : Store Root} (h : SameBlocks s t)
    (hs : BlocksSlotLe sl s) : BlocksSlotLe sl t := by
  obtain ⟨hbr, hb, _⟩ := h
  simp only [BlocksSlotLe, ← hbr, ← hb]
  exact hs

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

/-! ## Genesis current slot -/

/-- The `get_forkchoice_store` seeds `time` to the exact start of the anchor's
slot, so under whole-second slots the initial current slot is the anchor's slot
(the genesis base of `blocks_slot_le_current`). -/
theorem get_current_slot_get_forkchoice_store (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (ast : BeaconState Root) (ablk : SignedBeaconBlock Root) :
    get_current_slot cfg (get_forkchoice_store cfg ast ablk) = ast.slot := by
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk; have := cfg.slot_duration_ms_pos; omega
    · exact h
  have h1000k : 0 < 1000 * k := by omega
  simp only [get_current_slot, get_slots_since_genesis, get_forkchoice_store, GENESIS_SLOT,
    Nat.zero_add, Nat.add_sub_cancel_left]
  rw [hk, mul_assoc, Nat.mul_div_cancel_left _ (by omega : (0:ℕ) < 1000),
    mul_comm (k * ast.slot) 1000, ← mul_assoc, Nat.mul_div_cancel_left _ h1000k]

/-! ## `on_block` preserves the block-slot bound -/

omit [Inhabited Root] in
/-- Block insertion keeps the bound: the added block's slot is `≤ sl` (`hnew`,
from `on_block`'s not-future gate), and every older block keeps its slot. The
key list `br` is left abstract with a membership bound so both branches of the
append-if are covered uniformly. -/
theorem blocksSlotLe_add {sl : Slot} {store : Store Root} (sb : SignedBeaconBlock Root)
    (state : BeaconState Root) (br : List Root)
    (hbr : ∀ r ∈ br, r = sb.root ∨ r ∈ store.block_roots)
    (hnew : sb.message.slot ≤ sl) (h : BlocksSlotLe sl store) :
    BlocksSlotLe sl { store with
      block_roots := br
      blocks := Function.update store.blocks sb.root sb.message
      block_states := Function.update store.block_states sb.root state } := by
  intro r hr
  dsimp only at hr ⊢
  by_cases hrb : r = sb.root
  · subst hrb; rw [Function.update_self]; exact hnew
  · rw [Function.update_of_ne hrb]; exact h r ((hbr r hr).resolve_left hrb)

/-- `on_block` preserves the block-slot bound `sl`, provided the store's current
slot is at most `sl` (the added block's slot is bounded by the current slot via
`on_block`'s not-future gate). The post-insertion tail is
block-identity-preserving. -/
theorem on_block_blocksSlotLe {sl : Slot} {store store' : Store Root}
    {sb : SignedBeaconBlock Root} (hcur : get_current_slot cfg store ≤ sl)
    (h : BlocksSlotLe sl store) (hh : on_block cfg ext store sb = some store') :
    BlocksSlotLe sl store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh with hp hpayload hslot hfin hfc
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      dsimp only at hh
      split at hh
      · cases hh
      · rename_i after_ptc hptc
        cases hh
        have hge : sb.message.slot ≤ get_current_slot cfg store := by omega
        have hnew : sb.message.slot ≤ sl := le_trans hge hcur
        refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).blocksSlotLe ?_
        refine (update_checkpoints_sameBlocks _ _ _).blocksSlotLe ?_
        refine (update_proposer_boost_root_sameBlocks cfg _ _ _).blocksSlotLe ?_
        refine (record_block_timeliness_sameBlocks cfg _ _).blocksSlotLe ?_
        refine (notify_ptc_messages_sameBlocks cfg ext hptc).blocksSlotLe ?_
        refine blocksSlotLe_add sb state _ ?_ hnew h
        intro r hr
        rw [List.mem_append, List.mem_singleton] at hr
        exact hr.symm

/-! ## Event dispatch, the event fold, and the trajectory invariant -/

/-- One dispatched event preserves the block-slot bound: block events use
`on_block_blocksSlotLe` (needing the current-slot bound), attestations and
attester slashings ride across by `SameBlocks`. -/
theorem apply_event_blocksSlotLe {sl : Slot} {s s' : Store Root} {e : Event Root}
    (hcur : get_current_slot cfg s ≤ sl) (h : BlocksSlotLe sl s)
    (he : apply_event cfg ext s e = some s') : BlocksSlotLe sl s' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_blocksSlotLe cfg ext hcur h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact (on_attestation_sameBlocks cfg ext he).blocksSlotLe h
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact (on_attester_slashing_sameBlocks ext he).blocksSlotLe h
  | execution_payload_envelope envelope observation =>
    exact (on_execution_payload_envelope_sameBlocks ext he).blocksSlotLe h
  | payload_attestation_message message fromBlock =>
    exact (on_payload_attestation_message_sameBlocks cfg ext he).blocksSlotLe h

/-- Folding the second's events preserves the block-slot bound: every event
keeps the store's current slot fixed (`apply_event_current_slot`), so the
current-slot bound is re-established at each step. -/
theorem blocksSlotLe_foldl {sl : Slot} :
    ∀ (l : List (Event Root)) (s : Store Root),
      get_current_slot cfg s ≤ sl → BlocksSlotLe sl s →
      BlocksSlotLe sl
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ h; exact h
  | cons e l ih =>
    intro s hcur h
    rw [List.foldl_cons]
    cases he : apply_event cfg ext s e with
    | none => simp only [Option.getD_none]; exact ih s hcur h
    | some s' =>
      simp only [Option.getD_some]
      refine ih s' ?_ (apply_event_blocksSlotLe cfg ext hcur h he)
      rw [apply_event_current_slot cfg ext he]; exact hcur

/-- Every known block's slot is at most the wall-clock slot `E.slot_at cfg n` at
every node and second of a trajectory whose genesis store is a
`get_forkchoice_store`. Base: the anchor's slot equals the initial current slot
(`get_current_slot_get_forkchoice_store`); step: weaken the bound by
`slot_at_mono`, ride `on_tick` across by `SameBlocks`, then fold the second's
events. -/
theorem Execution.store_blocksSlotLe {E : Execution Root}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    BlocksSlotLe (E.slot_at cfg n) (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg, hsloteq⟩ := hgen
    have hcur0 : E.slot_at cfg 0 = ast.slot := by
      have h1 := E.store_current_slot cfg ext v 0
      rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg,
        get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at h1
      exact h1.symm
    intro r hr
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg] at hr ⊢
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    subst hr
    simp only [get_forkchoice_store, Function.update_self]
    rw [hcur0]; exact hsloteq.ge
  | succ n ih =>
    change BlocksSlotLe (E.slot_at cfg (n + 1))
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have hontickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have honticksl :
        get_current_slot cfg (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
          E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen, Execution.slot_at]
    refine blocksSlotLe_foldl cfg ext _ _ (le_of_eq honticksl) ?_
    exact (on_tick_sameBlocks cfg (E.store cfg ext v n) (E.time_at (n + 1))).blocksSlotLe
      (ih.mono_sl (E.slot_at_mono cfg (Nat.le_succ n)))

/-- Restatement of `store_blocksSlotLe` against the store's own current slot. -/
theorem Execution.store_blocks_slot_le_current {E : Execution Root}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).slot ≤ get_current_slot cfg (E.store cfg ext v n) := by
  rw [E.store_current_slot cfg ext v n]
  exact E.store_blocksSlotLe cfg ext hdiv hgen v n

/-! ## Honest attestation construction readbacks

Field projections of the validator-spec attestation an honest node casts, and
the store-independent `validate_on_attestation` conjunct
`target.epoch = compute_epoch_at_slot a.data.slot` discharged from the
construction. -/

/-- The honest wire attestation is a singleton on the casting validator. -/
theorem honest_attestation_attesting_indices (store : Store Root) (s : Slot)
    (index : CommitteeIndex) (v : ValidatorIndex) :
    (honest_attestation cfg ext store s index v).attesting_indices = [v] := rfl

/-- The honest wire attestation carries the honestly built data. -/
theorem honest_attestation_data_eq (store : Store Root) (s : Slot)
    (index : CommitteeIndex) (v : ValidatorIndex) :
    (honest_attestation cfg ext store s index v).data =
      honest_attestation_data cfg ext store s index := rfl

/-- The honest attestation votes for its assigned slot. -/
theorem honest_attestation_data_slot (store : Store Root) (s : Slot)
    (index : CommitteeIndex) :
    (honest_attestation_data cfg ext store s index).slot = s := rfl

/-- The honest LMD vote is the store's current head. -/
theorem honest_attestation_data_beacon_block_root (store : Store Root) (s : Slot)
    (index : CommitteeIndex) :
    (honest_attestation_data cfg ext store s index).beacon_block_root =
      (get_head cfg store).root := rfl

/-- The honest FFG target root is the checkpoint block of the head for the target
epoch — exactly the `validate_on_attestation` LMD/FFG-consistency equation, at
the constructing store. -/
theorem honest_attestation_data_target_root (store : Store Root) (s : Slot)
    (index : CommitteeIndex) :
    (honest_attestation_data cfg ext store s index).target.root =
      get_checkpoint_block cfg store (get_head cfg store).root
        (honest_attestation_data cfg ext store s index).target.epoch := rfl

/-- The store-independent conjunct: the honest target epoch equals the epoch of
the vote slot. Discharged from the pulled-up head state landing on the vote slot
(`process_slots_slot` when the head trails the vote slot; otherwise the head
state already sits at the vote slot, using the head-slot bound `hhead` — supplied
along a trajectory by `blocks_slot_le_current` + `block_state_slot_eq`). -/
theorem honest_attestation_data_target_epoch (store : Store Root) (s : Slot)
    (index : CommitteeIndex)
    (hps : ∀ (st : BeaconState Root) (t : Slot), st.slot < t → (ext.process_slots st t).slot = t)
    (hhead : (store.block_states (get_head cfg store).root).slot ≤ s) :
    (honest_attestation_data cfg ext store s index).target.epoch =
      compute_epoch_at_slot cfg s := by
  simp only [honest_attestation_data, get_current_epoch]
  by_cases hlt : (store.block_states (get_head cfg store).root).slot < s
  · rw [if_pos hlt, hps _ _ hlt]
  · rw [if_neg hlt, Nat.le_antisymm hhead (not_lt.mp hlt)]

/-- Gloas honest attestations use only the two payload-presence indices. -/
theorem honest_attestation_data_index_shape (store : Store Root) (s : Slot)
    (index : CommitteeIndex) :
    (honest_attestation_data cfg ext store s index).index = 0 ∨
      (honest_attestation_data cfg ext store s index).index = 1 := by
  simp only [honest_attestation_data]
  split_ifs <;> simp

/-- An honest vote at the head block's own slot uses index zero. -/
theorem honest_attestation_data_same_slot_index (store : Store Root) (s : Slot)
    (index : CommitteeIndex) (hsame : (store.blocks (get_head cfg store).root).slot = s) :
    (honest_attestation_data cfg ext store s index).index = 0 := by
  simp [honest_attestation_data, hsame]

/-- A FULL fork-choice child can only be introduced from a verified envelope. -/
private theorem get_node_children_full_verified (store : Store Root) (blocks : List Root)
    (node child : ForkChoiceNode Root)
    (hmem : child ∈ get_node_children store blocks node)
    (hfull : child.payload_status = .full) :
    is_payload_verified store child.root = true := by
  by_cases hpending : node.payload_status = .pending
  · simp only [get_node_children, if_pos hpending] at hmem
    split_ifs at hmem with hv
    · simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · cases hfull
      · exact hv
    · simp only [List.mem_singleton] at hmem
      subst child
      cases hfull
  · simp only [get_node_children, if_neg hpending, List.mem_map] at hmem
    obtain ⟨root, _, rfl⟩ := hmem
    cases hfull

/-- Head descent preserves the condition that FULL nodes have verified envelopes. -/
private theorem get_head_aux_full_verified (store : Store Root) (blocks : List Root) :
    ∀ (fuel : ℕ) (head : ForkChoiceNode Root),
      (head.payload_status = .full → is_payload_verified store head.root = true) →
      (get_head_aux cfg store blocks fuel head).payload_status = .full →
      is_payload_verified store (get_head_aux cfg store blocks fuel head).root = true := by
  intro fuel
  induction fuel with
  | zero => intro head hh; exact hh
  | succ fuel ih =>
      intro head hh
      simp only [get_head_aux]
      split
      · exact hh
      · rename_i best hbest
        exact ih best (get_node_children_full_verified store blocks head best
          (List.argmax_mem hbest))

/-- An honest index-one vote comes from a FULL head, so its source has the envelope. -/
theorem honest_attestation_index_one_payload_verified (store : Store Root) (s : Slot)
    (index : CommitteeIndex) (v : ValidatorIndex)
    (hindex : (honest_attestation cfg ext store s index v).data.index = 1) :
    is_payload_verified store
      (honest_attestation cfg ext store s index v).data.beacon_block_root = true := by
  have hfull : (get_head cfg store).payload_status = .full := by
    by_contra hfull
    simp [honest_attestation, honest_attestation_data, hfull] at hindex
  apply get_head_aux_full_verified cfg store (get_filtered_block_tree cfg store)
    (2 * (get_filtered_block_tree cfg store).length + 2)
    (ForkChoiceNode.mk store.justified_checkpoint.root .pending) _ hfull
  intro h
  cases h

/-- Event prefixes preserve every envelope present in their base store. -/
private theorem foldl_payloadLE (pre : List (Event Root)) (store : Store Root) :
    PayloadLE store
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) store) := by
  induction pre generalizing store with
  | nil => exact PayloadLE.refl _
  | cons event pre ih =>
      exact (apply_event_getD_payloadLE cfg ext store event).trans (ih _)

/-- Operational envelope delivery, availability relay, and observation
determinism imply the former verified-payload relay outcome. State agreement
is derived from deterministic block transitions in `BlockStateAgreement`. -/
theorem Execution.payload_envelope_relay_of_parts {E : Execution Root}
    (hwf : WellFormedExecution E)
    (hsyn : NextSlotSynchronyPremises cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {n m : ℕ} (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (htiming : E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1))
    {r : Root} (hverified : is_payload_verified (E.store cfg ext v n) r = true) :
    is_payload_verified (E.store cfg ext w m) r = true := by
  obtain ⟨d, k, signed, sourceObservation, receiverObservation, before, after,
      hpositive, hdm, htimingD, hkn, hsourceEvent, hroot, hsourceKnown, hsourceData,
      hsourceVerify, hschedule, hreceiverKnown⟩ :=
    hsyn.envelope_delivery v hv n r hHn hverified w hw m hHm htiming
  have hHd : E.WithinHorizon cfg d := E.withinHorizon_mono cfg hdm hHm
  have hAtD : is_payload_verified (E.store cfg ext w d) r = true := by
    cases d with
    | zero => omega
    | succ pred =>
      have hreceiverEvent :
          Event.execution_payload_envelope signed receiverObservation ∈
            E.schedule w (pred + 1) := by
        rw [hschedule]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hreceiverData :
          ext.is_data_available signed.message.beacon_block_root receiverObservation = true :=
        hsyn.data_availability_relay v hv k n signed sourceObservation
          hkn hHn hsourceEvent (hroot ▸ hsourceData)
          w hw (pred + 1) hHd htimingD signed receiverObservation rfl hreceiverEvent
      let ticked := on_tick cfg (E.store cfg ext w pred) (E.time_at (pred + 1))
      let receiverPrefix := before.foldl
        (fun store event => (apply_event cfg ext store event).getD store) ticked
      have hprefixCausal : E.CausalStore cfg ext receiverPrefix := by
        apply Execution.HonestCausalStore.causal
        exact E.honestCausalStore_prefix cfg ext w hw pred hHd before
          (Event.execution_payload_envelope signed receiverObservation :: after)
          hschedule
      have hstates :
          (E.store cfg ext v n).block_states r = receiverPrefix.block_states r :=
        E.causal_block_states_agree cfg ext hwf hec
          (E.store_causal cfg ext v n) hprefixCausal hsourceKnown hreceiverKnown
      have hverifyReceiver :
          ext.verify_execution_payload_envelope (receiverPrefix.block_states r)
            signed receiverObservation = true := by
        rw [← hstates, ← hec.verify_envelope_deterministic
          ((E.store cfg ext v n).block_states r) signed sourceObservation receiverObservation]
        exact hsourceVerify
      let acceptedStore : Store Root :=
        { receiverPrefix with
          payloads := Function.update receiverPrefix.payloads r (some signed.message) }
      have hknownR : r ∈ receiverPrefix.block_roots := by
        simpa only [receiverPrefix, ticked, Nat.add_sub_cancel_left] using hreceiverKnown
      have hdataR : ext.is_data_available r receiverObservation = true := by
        rw [← hroot]
        exact hreceiverData
      have haccepted :
          on_execution_payload_envelope ext receiverPrefix signed receiverObservation =
            some acceptedStore := by
        simp [on_execution_payload_envelope, hroot, hknownR,
          hdataR, hverifyReceiver, acceptedStore]
      have hafterEvent : is_payload_verified
          ((apply_event cfg ext receiverPrefix
            (Event.execution_payload_envelope signed receiverObservation)).getD receiverPrefix)
          r = true := by
        simp [apply_event, haccepted, is_payload_verified, acceptedStore]
      change is_payload_verified
        ((E.schedule w (pred + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store) ticked) r = true
      rw [hschedule, List.foldl_append]
      change is_payload_verified
        (after.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ((apply_event cfg ext receiverPrefix
            (Event.execution_payload_envelope signed receiverObservation)).getD receiverPrefix)) r = true
      exact (foldl_payloadLE cfg ext after _) r hafterEvent
  exact E.is_payload_verified_mono cfg ext w hdm hAtD

/-- Envelope relay reaches the receiver before its next-slot event fold. Ticking
and every fold prefix preserve verification, including before an index-one vote. -/
theorem Execution.honest_payload_verified_at_delivery_prefix {E : Execution Root}
    (hwf : WellFormedExecution E)
    (hsyn : NextSlotSynchronyPremises cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {n m : ℕ} (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (htiming : E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1))
    (pre : List (Event Root)) (s : Slot) (index : CommitteeIndex)
    (hindex : (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.index = 1) :
    is_payload_verified
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext w m) (E.time_at (m + 1))))
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root = true := by
  have hsource := honest_attestation_index_one_payload_verified cfg ext
    (E.store cfg ext v n) s index v hindex
  have hrelay := E.payload_envelope_relay_of_parts cfg ext hwf hsyn hec
    hv hw hHn hHm htiming hsource
  exact (foldl_payloadLE cfg ext pre _)
    _ ((PayloadLE.of_payloads_eq (on_tick_payloads cfg _ _)) _ hrelay)

/-! ## `validate_on_attestation` at the receiving node

The delivered attestation's slot is `s` and the receiving node's current slot is
`s + 1` (the first second of slot `s+1`). The epoch-window conjunct is then pure
`Clock` arithmetic; the assembly lemma discharges `validate_on_attestation` from
the seven conjuncts, taking the cross-store transport ones (known blocks,
not-future, LMD/FFG consistency) as explicit premises. -/

/-- Pure epoch-window arithmetic on the two epoch numbers: if `es ≤ es1 ≤ es + 1`
then `es` is `es1` or `es1`'s saturating predecessor. -/
private theorem epoch_window_nat (es es1 : ℕ) (h1 : es ≤ es1) (h2 : es1 ≤ es + 1) :
    es = es1 ∨ es = es1 - 1 := by
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- Epoch-window conjunct: when the receiving store's current slot is exactly one
past the attestation's slot and the target epoch is the vote slot's epoch, the
target epoch is the current or previous epoch (`epochOf (s+1) ∈ {epochOf s,
epochOf s + 1}`, and `epochOf s` is `current` or `current - 1` accordingly). -/
theorem validate_target_epoch_of_current_succ (store : Store Root) (a : Attestation Root)
    (hcur : get_current_slot cfg store = a.data.slot + 1)
    (hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot) :
    validate_target_epoch_against_current_time cfg store a = true := by
  have hspe := cfg.slots_per_epoch_pos
  have hle : a.data.slot / cfg.slots_per_epoch ≤ (a.data.slot + 1) / cfg.slots_per_epoch :=
    Nat.div_le_div_right (Nat.le_succ _)
  have hle2 : (a.data.slot + 1) / cfg.slots_per_epoch ≤ a.data.slot / cfg.slots_per_epoch + 1 := by
    calc (a.data.slot + 1) / cfg.slots_per_epoch
        ≤ (a.data.slot + cfg.slots_per_epoch) / cfg.slots_per_epoch :=
          Nat.div_le_div_right (by omega)
      _ = a.data.slot / cfg.slots_per_epoch + 1 := Nat.add_div_right _ hspe
  simp only [validate_target_epoch_against_current_time, get_current_store_epoch, hcur,
    GENESIS_EPOCH, decide_eq_true_eq, hepoch, compute_epoch_at_slot]
  exact epoch_window_nat _ _ hle hle2

omit [Inhabited Root] in
/-- Assembly of `validate_on_attestation` (for a network attestation,
`is_from_block = false`) from its conjuncts: the epoch-window check `hwin`, the
epoch/slot match `hepoch`, the known-block checks `htroot`/`hbbr`, the not-future
check `hbslot`, the LMD/FFG-consistency check `hckpt`, and the fork-choice slot
gate `hcur`. Gloas also needs the index shape, index zero at the block's own
slot, and a locally verified payload for index one. These three facts are
explicit local premises. -/
theorem validate_on_attestation_of_facts (store : Store Root) (a : Attestation Root)
    (hwin : validate_target_epoch_against_current_time cfg store a = true)
    (hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot)
    (htroot : a.data.target.root ∈ store.block_roots)
    (hbbr : a.data.beacon_block_root ∈ store.block_roots)
    (hbslot : (store.blocks a.data.beacon_block_root).slot ≤ a.data.slot)
    (hckpt : a.data.target.root =
      get_checkpoint_block cfg store a.data.beacon_block_root a.data.target.epoch)
    (hcur : a.data.slot + 1 ≤ get_current_slot cfg store)
    (hindex : a.data.index = 0 ∨ a.data.index = 1)
    (hsame : (store.blocks a.data.beacon_block_root).slot = a.data.slot → a.data.index = 0)
    (hpayload : a.data.index = 1 → is_payload_verified store a.data.beacon_block_root = true) :
    validate_on_attestation cfg store a false = true := by
  have hsame' : (store.blocks a.data.beacon_block_root).slot ≠ a.data.slot ∨
      a.data.index = 0 := by
    by_cases h : (store.blocks a.data.beacon_block_root).slot = a.data.slot
    · exact Or.inr (hsame h)
    · exact Or.inl h
  have hpayload' : a.data.index ≠ 1 ∨
      is_payload_verified store a.data.beacon_block_root = true := by
    by_cases h : a.data.index = 1
    · exact Or.inr (hpayload h)
    · exact Or.inl h
  simp only [validate_on_attestation, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hwin, hepoch⟩, htroot⟩, hbbr⟩, hbslot⟩, hindex⟩,
    hsame'⟩, hpayload'⟩, hckpt⟩, hcur⟩

/-! ## Application-second effect on the receiving node's latest message

`on_attestation` applies the delivered singleton honest attestation through
`update_latest_messages`. For the non-equivocating casting validator the update
either installs the fresh slot/root/payload message or keeps an equal-slot
or newer message. Thus the receiving node records a message for the validator
at target epoch or later; a separate trajectory lemma proves persistence.
-/

omit [LinearOrder Root] [Inhabited Root] in
/-- A non-equivocating validator's singleton attestation leaves a latest
message at the attestation slot or a later slot. No epoch-validity premise is
needed for this exact-slot result. -/
theorem update_latest_messages_singleton_slot_ge (store : Store Root) (v : ValidatorIndex)
    (a : Attestation Root) (hne : v ∉ store.equivocating_indices) :
    ∃ m, (update_latest_messages store [v] a).latest_messages v = some m ∧
      a.data.slot ≤ m.slot := by
  have hfilter : ([v] : List ValidatorIndex).filter
      (fun i => decide (i ∉ store.equivocating_indices)) = [v] := by
    simp [hne]
  simp only [update_latest_messages, hfilter, List.foldl_cons, List.foldl_nil]
  split_ifs with hupd
  · exact ⟨⟨a.data.slot, a.data.beacon_block_root, decide (a.data.index = 1)⟩,
      by simp only [Function.update_self], le_refl _⟩
  · rcases hlm : store.latest_messages v with _ | lm
    · rw [hlm] at hupd; simp at hupd
    · refine ⟨lm, rfl, ?_⟩
      rw [hlm] at hupd
      simp only [gt_iff_lt, decide_eq_true_eq, not_lt] at hupd
      exact hupd

omit [LinearOrder Root] [Inhabited Root] in
/-- The epoch corollary needs the attestation's validated target/slot match.
Gloas stores slots and does not use the target epoch to replace a message. -/
theorem update_latest_messages_singleton_ge (store : Store Root) (v : ValidatorIndex)
    (a : Attestation Root) (hne : v ∉ store.equivocating_indices)
    (hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot) :
    ∃ m, (update_latest_messages store [v] a).latest_messages v = some m ∧
      a.data.target.epoch ≤ get_latest_message_epoch cfg m := by
  obtain ⟨m, hm, hslot⟩ := update_latest_messages_singleton_slot_ge store v a hne
  refine ⟨m, hm, ?_⟩
  rw [hepoch]
  exact Nat.div_le_div_right hslot

/-! ## The second's event fold: delivery and persistence (`Delivery`)

The remaining `Delivery` results reason about the receiving node `w`'s event
fold at the delivery second `slot_start (s + 1)`. `foldl_storeLE` is the
prefix-extension order the whole fold rides on; `on_attestation_singleton_ge`
is the handler-level effect at the delivered event's own position; and
`foldl_deliver_ge` propagates the installed message to the end of the second.
`store_latest_message_ge_mono` then carries it to every later second by the
`StoreLE` latest-message monotonicity — the persistence half of ubiquity. -/

/-- The second's event fold extends its base store in the `StoreLE` order (any
event list, any base): each step either applies a handler
(`apply_event_getD_storeLE`) or leaves the store unchanged. Specialised to a
fold *prefix*, this is "every prefix accumulator extends the base". -/
theorem foldl_storeLE (l : List (Event Root)) (s : Store Root) :
    StoreLE s
      (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  induction l generalizing s with
  | nil => exact StoreLE.refl s
  | cons e l ih => exact (apply_event_getD_storeLE cfg ext s e).trans (ih _)

omit [Inhabited Root] in
/-- Application-second effect (handler level): the delivered singleton honest
attestation, applied by `on_attestation` at a store `P` where it validates
(`hval`), its indexed check passes (`hvalid`), and the casting validator is not
equivocating (`hne`), succeeds and records for that validator a message of epoch
at least the attestation's target epoch. -/
theorem on_attestation_singleton_ge (P : Store Root) (a : Attestation Root)
    (v : ValidatorIndex) (hsingle : a.attesting_indices = [v])
    (hval : validate_on_attestation cfg P a false = true)
    (hvalid : ext.is_valid_indexed_attestation
        ((store_target_checkpoint_state cfg ext P a.data.target).checkpoint_states
          a.data.target) a = true)
    (hne : v ∉ P.equivocating_indices) :
    ∃ P' msg, on_attestation cfg ext P a false = some P' ∧
      P'.latest_messages v = some msg ∧ a.data.target.epoch ≤ (get_latest_message_epoch cfg msg) := by
  have hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot := by
    have hv := hval
    simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1.1.1.1.1.1.1.2
  have hsteq :
      (store_target_checkpoint_state cfg ext P a.data.target).equivocating_indices =
        P.equivocating_indices := by
    simp only [store_target_checkpoint_state]; split_ifs <;> rfl
  simp only [on_attestation]
  rw [if_neg (not_not_intro hval), if_neg (not_not_intro hvalid), hsingle]
  obtain ⟨msg, hmsg, hle⟩ :=
    update_latest_messages_singleton_ge cfg
      (store_target_checkpoint_state cfg ext P a.data.target) v a
      (by rw [hsteq]; exact hne) hepoch
  exact ⟨_, msg, rfl, hmsg, hle⟩

/-- Folding a `Event.attestation a false :: suf` from a base at which
`on_attestation` succeeds continues the fold from the successor store `P'`. -/
theorem foldl_cons_attestation (base : Store Root) (a : Attestation Root)
    (suf : List (Event Root)) {P' : Store Root}
    (hsucc : on_attestation cfg ext base a false = some P') :
    (Event.attestation a false :: suf).foldl
        (fun store event => (apply_event cfg ext store event).getD store) base =
      suf.foldl (fun store event => (apply_event cfg ext store event).getD store) P' := by
  rw [List.foldl_cons]
  congr 1
  show (apply_event cfg ext base (Event.attestation a false)).getD base = P'
  rw [show apply_event cfg ext base (Event.attestation a false) =
    on_attestation cfg ext base a false from rfl, hsucc, Option.getD_some]

/-- The second's event fold delivers a validator's message: if the fold list
decomposes as `pre ++ Event.attestation a false :: suf` and `on_attestation`
succeeds at the prefix store, recording for `v` a message of epoch ≥ `te`, then
the whole fold's store records for `v` a message of epoch ≥ `te` (persisted
through `suf` by `foldl_storeLE`'s latest-message monotonicity). -/
theorem foldl_deliver_ge {l pre suf : List (Event Root)} {s P' : Store Root}
    {a : Attestation Root} {v : ValidatorIndex} {te : Epoch} {msg : LatestMessage Root}
    (hl : l = pre ++ Event.attestation a false :: suf)
    (hsucc : on_attestation cfg ext
        (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) s)
        a false = some P')
    (hmsg : P'.latest_messages v = some msg) (hge : te ≤ (get_latest_message_epoch cfg msg)) :
    ∃ msg',
      (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s).latest_messages
          v = some msg' ∧ te ≤ (get_latest_message_epoch cfg msg') := by
  subst hl
  rw [List.foldl_append, foldl_cons_attestation cfg ext _ a suf hsucc]
  obtain ⟨msg', hmsg', hle'⟩ := (foldl_storeLE cfg ext suf P').latest_message_epoch_mono cfg v msg hmsg
  exact ⟨msg', hmsg', hge.trans hle'⟩

/-- Persistence to later seconds: once an honest-or-Byzantine node `w` has
recorded a message of epoch ≥ `te` for validator `v` at second `N`, it does at
every later second (the store's latest messages only grow in epoch, `StoreLE`). -/
theorem Execution.store_latest_message_ge_mono (E : Execution Root) {v w : ValidatorIndex}
    {te : Epoch} {N : ℕ}
    (h : ∃ msg, (E.store cfg ext w N).latest_messages v = some msg ∧ te ≤ (get_latest_message_epoch cfg msg))
    {m : ℕ} (hNm : N ≤ m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧ te ≤ (get_latest_message_epoch cfg msg) := by
  obtain ⟨msg, hmsg, hle⟩ := h
  obtain ⟨msg', hmsg', hle'⟩ := (E.store_storeLE cfg ext w hNm).latest_message_epoch_mono cfg v msg hmsg
  exact ⟨msg', hmsg', hle.trans hle'⟩



/-- The event fold keeps the store's current slot fixed: every handler preserves
`get_current_slot` (`apply_event_current_slot`), and a rejected event leaves
the store unchanged. -/
theorem foldl_get_current_slot (l : List (Event Root)) (s : Store Root) :
    get_current_slot cfg
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) =
      get_current_slot cfg s := by
  induction l generalizing s with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, ih]
    show get_current_slot cfg ((apply_event cfg ext s e).getD s) = get_current_slot cfg s
    cases he : apply_event cfg ext s e with
    | none => rw [Option.getD_none]
    | some s' => rw [Option.getD_some]; exact apply_event_current_slot cfg ext he


omit [Inhabited Root] in
/-- **Conjunct transport.** `validate_on_attestation` holds at any store `P` that
extends the honest voter's source store `S` on the block set (`hsub`), agrees
with it on `S`-known blocks (`hagree`), and reads the delivery slot on its clock
(`hcur : get_current_slot P = a.data.slot + 1`), given the source-store facts:
the target/head blocks are `S`-known (`hbbr`/`htroot`), the head block is not in
the future (`hbslot`), the LMD/FFG-consistency equation holds at `S` (`hckpt`)
on a `S`-known walk (`hwalk`), and the store-independent epoch match (`hepoch`).
The known-block checks ride on `hsub`; the not-future and `get_checkpoint_block`
checks transport by `hagree` (`get_ancestor_congr`); the epoch-window and gate
are pure `Clock` arithmetic. Index shape and the same-slot rule come from the
source. Index-one payload verification is required directly at `P`; block
extension does not imply payload delivery. -/
theorem validate_at_extension (S P : Store Root) (a : Attestation Root)
    (hagree : ∀ x ∈ S.block_roots, S.blocks x = P.blocks x)
    (hsub : S.block_roots ⊆ P.block_roots)
    (hcur : get_current_slot cfg P = a.data.slot + 1)
    (hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot)
    (hbbr : a.data.beacon_block_root ∈ S.block_roots)
    (htroot : a.data.target.root ∈ S.block_roots)
    (hbslot : (S.blocks a.data.beacon_block_root).slot ≤ a.data.slot)
    (hckpt : a.data.target.root =
      get_checkpoint_block cfg S a.data.beacon_block_root a.data.target.epoch)
    (hwalk : WalkKnown S (compute_start_slot_at_epoch cfg a.data.target.epoch)
      a.data.beacon_block_root)
    (hindex : a.data.index = 0 ∨ a.data.index = 1)
    (hsame : (S.blocks a.data.beacon_block_root).slot = a.data.slot → a.data.index = 0)
    (hpayload : a.data.index = 1 → is_payload_verified P a.data.beacon_block_root = true) :
    validate_on_attestation cfg P a false = true := by
  refine validate_on_attestation_of_facts cfg P a
    (validate_target_epoch_of_current_succ cfg P a hcur hepoch) hepoch
    (hsub htroot) (hsub hbbr) ?_ ?_ hcur.ge hindex ?_ hpayload
  · rw [← hagree _ hbbr]; exact hbslot
  · rw [hckpt]; simp only [get_checkpoint_block]
    rw [get_ancestor_congr hagree hbbr hwalk]
  · intro h
    apply hsame
    rw [hagree _ hbbr]
    exact h

/-! ## The application-second effect and ubiquity (`Delivery` parts 3–4)

Assembly at the delivery second `slot_start (s + 1)` of receiving honest node
`w`: the honest vote of `v` (assigned to slot `s`, cast at second `n`) is
`Synchrony`-delivered into `w`'s schedule there; at its fold position
`on_attestation` succeeds (`validate` by `validate_at_extension` on the
`block_relay`-relayed source store, indexed validity by
`honest_attestation_valid`, non-equivocation by `honest_not_equivocating`
pushed down the prefix), installing for `v` a message of epoch ≥ `epochOf s`.
`vote_lands` is that second's effect; `vote_ubiquity` extends it to every later
second.

The two source-store facts left as hypotheses — the head block is known
(`hhead_known`) and its FFG-target ancestor walk stays known (`hhead_walk`) —
are the `get_head`/`get_checkpoint_block` well-formedness inputs used by this
lemma. -/

/-- A fresh checkpoint state is validated through its reachable block-state
base. Slot processing preserves the indexed check; the cache need not already
contain the prepared state. -/
theorem honest_attestation_valid_prepared {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {store : Store Root}
    (hstore : E.HonestCausalStore cfg ext store) (a : Attestation Root)
    (hroot : a.data.target.root ∈ store.block_roots)
    (v : ValidatorIndex) (hv : v ∈ E.honest)
    (hsingle : a.attesting_indices = [v])
    (hcommittee : v ∈ E.committee a.data.slot)
    (hvote : ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) :
    ext.is_valid_indexed_attestation
      ((store_target_checkpoint_state cfg ext store a.data.target).checkpoint_states
        a.data.target) a = true := by
  by_cases hkey : a.data.target ∈ store.checkpoint_state_keys
  · simpa only [store_target_checkpoint_state, if_neg (not_not_intro hkey)] using
      hec.honest_attestation_valid _ a
        (hstore.checkpointState cfg ext hkey) v hv hsingle hcommittee hvote
  · have hbase := hec.honest_attestation_valid _ a
      (hstore.blockState cfg ext hroot) v hv hsingle hcommittee hvote
    simp only [store_target_checkpoint_state, if_pos hkey, Function.update_self]
    split_ifs with hslot
    · rw [hec.process_slots_attestation_valid _ _ _
        (hstore.blockState cfg ext hroot) hslot]
      exact hbase
    · exact hbase

/-- **Application-second effect.** Under honest behaviour, synchrony, externals
coherence and a well-formed execution from a `get_forkchoice_store` genesis,
the honest attestation `v` casts for its assigned slot `s` (at second `n`) is,
by the first second of slot `s + 1`, recorded at every honest node `w` with
epoch at least its FFG target epoch (`= epochOf s`). The head-known /
head-walk-known hypotheses feed the LMD/FFG-consistency and known-block
transport. For an index-one vote, payload-envelope relay supplies verification
at the receiver before the vote's fold position. -/
theorem Execution.vote_lands {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : NextSlotSynchronyPremises cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHdeliver : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hhead_known :
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root ∈
        (E.store cfg ext v n).block_roots)
    (hhead_walk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root) :
    ∃ msg, (E.store cfg ext w (E.slot_start cfg (s + 1))).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        (get_latest_message_epoch cfg msg) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  set a := honest_attestation cfg ext (E.store cfg ext v n) s index v with ha
  -- genesis well-formedness and the honest-attestation readbacks
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]; exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hgen_time : E.genesis_store.genesis_time ≤ E.genesis_store.time := hgws.time_ge_genesis
  have hpar_S : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled v n
  have hsingle : a.attesting_indices = [v] := by rw [ha]; rfl
  have hslot_a : a.data.slot = s := by rw [ha]; rfl
  -- head-state slot bound → the store-independent epoch conjunct
  have hhead : ((E.store cfg ext v n).block_states
      (get_head cfg (E.store cfg ext v n)).root).slot ≤ s := by
    have hb0 : (get_head cfg (E.store cfg ext v n)).root ∈ (E.store cfg ext v n).block_roots :=
      hhead_known
    have hcore := E.store_wellFormedStoreCore cfg ext hec.state_transition_slot hgws.core v n
    rw [hcore.2 _ hb0]
    have hbs := E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩ v n _ hb0
    rwa [E.store_current_slot cfg ext v n, hn] at hbs
  have hepoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot := by
    rw [hslot_a, ha]
    exact honest_attestation_data_target_epoch cfg ext (E.store cfg ext v n) s index
      hec.process_slots_slot hhead
  have hckpt : a.data.target.root = get_checkpoint_block cfg (E.store cfg ext v n)
      a.data.beacon_block_root a.data.target.epoch := by
    rw [ha]; exact honest_attestation_data_target_root cfg ext (E.store cfg ext v n) s index
  have htroot : a.data.target.root ∈ (E.store cfg ext v n).block_roots := by
    rw [hckpt]; simp only [get_checkpoint_block]
    exact (get_ancestor_spec hpar_S hhead_walk).1
  have hbslot : ((E.store cfg ext v n).blocks a.data.beacon_block_root).slot ≤ a.data.slot := by
    rw [hslot_a]
    have hbs := E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩ v n
      a.data.beacon_block_root hhead_known
    rwa [E.store_current_slot cfg ext v n, hn] at hbs
  -- committee / vote-existence for `honest_attestation_valid`
  have hcomm : v ∈ E.committee s :=
    hhb.votes_assigned v hv s
      (by rw [hvote]; exact Option.some_ne_none _)
  have hcomm_slot : v ∈ E.committee a.data.slot := by rw [hslot_a]; exact hcomm
  have hvote_ex : ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data :=
    ⟨n, a, by rw [hslot_a]; exact hvote, rfl⟩
  -- the delivery second and its predecessor
  have hs0 : E.slot_at cfg 0 ≤ s := hn ▸ E.slot_at_mono cfg (Nat.zero_le n)
  have hslotN : E.slot_at cfg (E.slot_start cfg (s + 1)) = s + 1 :=
    E.slot_at_slot_start cfg hdiv (le_trans hs0 (Nat.le_succ s)) hgen_time
  have hNpos : 0 < E.slot_start cfg (s + 1) := by
    rcases Nat.eq_zero_or_pos (E.slot_start cfg (s + 1)) with h0 | h
    · exfalso; rw [h0] at hslotN
      rw [hslotN] at hs0
      exact absurd hs0 (Nat.not_succ_le_self s)
    · exact h
  obtain ⟨Nm1, hNeq⟩ : ∃ k, E.slot_start cfg (s + 1) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hNpos).symm⟩
  have hslotNm1 : E.slot_at cfg (Nm1 + 1) = s + 1 := by rw [← hNeq]; exact hslotN
  have htiming : E.slot_at cfg n + 1 ≤ E.slot_at cfg (Nm1 + 1) :=
    le_of_eq (by rw [hn, hslotNm1])
  -- the ticked delivery base and its clock
  set tb := on_tick cfg (E.store cfg ext w Nm1) (E.time_at (Nm1 + 1)) with htb
  have hontickgen : tb.genesis_time = E.genesis_store.genesis_time := by
    rw [htb, ← (on_tick_storeLE cfg (E.store cfg ext w Nm1) (E.time_at (Nm1 + 1))).2.1,
      E.store_genesis_time cfg ext w Nm1]
  have hcur_tb : get_current_slot cfg tb = E.slot_at cfg (Nm1 + 1) := by
    rw [htb, get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen, Execution.slot_at]
  -- the delivered event and its fold decomposition
  have hmem : Event.attestation a false ∈ E.schedule w (Nm1 + 1) := by
    rw [← hNeq]
    exact hsyn.attestation_delivery v hv s n a
      (E.slotWithinHorizon_of_le cfg (by rw [hn]) hHn) hHn hvote hHdeliver w hw
  obtain ⟨pre, suf, hl⟩ := List.append_of_mem hmem
  -- the prefix store extends and agrees with the ticked base
  have htb_br : tb.block_roots = (E.store cfg ext w Nm1).block_roots := by
    rw [htb]; exact ((on_tick_sameBlocks cfg (E.store cfg ext w Nm1) (E.time_at (Nm1 + 1))).1).symm
  have hsub : (E.store cfg ext v n).block_roots ⊆
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        tb).block_roots := by
    intro r hr
    have hHNm1p : E.WithinHorizon cfg (Nm1 + 1) := by rwa [← hNeq]
    have hHNm1 : E.WithinHorizon cfg Nm1 :=
      E.withinHorizon_mono cfg (Nat.le_succ Nm1) hHNm1p
    have h1 : r ∈ (E.store cfg ext w Nm1).block_roots :=
      hsyn.block_relay v hv n r hHn hr w hw Nm1 hHNm1 htiming
    have h2 : r ∈ tb.block_roots := by rw [htb_br]; exact h1
    exact (foldl_storeLE cfg ext pre tb).1 h2
  have hprov_tb : BlockProvenance E tb := by
    rw [htb]
    exact on_tick_blockProvenance cfg (E.store cfg ext w Nm1) (E.time_at (Nm1 + 1))
      (E.blockProvenance cfg ext w Nm1)
  have hpre_sched : ∀ b, Event.block b ∈ pre → IsScheduledBlock E b :=
    fun b hb => ⟨w, Nm1 + 1, by rw [hl]; exact List.mem_append_left _ hb⟩
  have hprov_P : BlockProvenance E
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) :=
    blockProvenance_foldl cfg ext pre tb hpre_sched hprov_tb
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x =
        (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb).blocks x :=
    fun x hx => hwf.blocks_agree (E.blockProvenance cfg ext v n) hprov_P hx (hsub hx)
  have hcur_P : get_current_slot cfg
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) =
        a.data.slot + 1 := by
    rw [foldl_get_current_slot cfg ext pre tb, hcur_tb, hslotNm1, hslot_a]
  -- The honest index rules and envelope relay give receiver payload verification.
  have hindex : a.data.index = 0 ∨ a.data.index = 1 := by
    rw [ha]
    exact honest_attestation_data_index_shape cfg ext (E.store cfg ext v n) s index
  have hsame : ((E.store cfg ext v n).blocks a.data.beacon_block_root).slot =
      a.data.slot → a.data.index = 0 := by
    intro hs
    rw [ha] at hs ⊢
    exact honest_attestation_data_same_slot_index cfg ext (E.store cfg ext v n) s index hs
  have hpayload_P : a.data.index = 1 →
      is_payload_verified
        (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb)
        a.data.beacon_block_root = true := by
    intro hi
    rw [htb]
    exact E.honest_payload_verified_at_delivery_prefix cfg ext hwf hsyn hec hv hw hHn
      (E.withinHorizon_mono cfg (by omega : Nm1 ≤ E.slot_start cfg (s + 1)) hHdeliver)
      htiming pre s index hi
  -- validate + indexed validity + non-equivocation at the prefix store
  have hval : validate_on_attestation cfg
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) a false =
        true :=
    validate_at_extension cfg (E.store cfg ext v n)
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) a
      hagree hsub hcur_P hepoch hhead_known htroot hbslot hckpt hhead_walk
      hindex hsame hpayload_P
  have hvalid : ext.is_valid_indexed_attestation
      ((store_target_checkpoint_state cfg ext
          (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb)
          a.data.target).checkpoint_states a.data.target) a = true :=
    honest_attestation_valid_prepared cfg ext hec
      (E.honestCausalStore_prefix cfg ext w hw Nm1
        (by simpa only [← hNeq] using hHdeliver)
        pre (Event.attestation a false :: suf) hl)
      a (hsub htroot) v hv hsingle hcomm_slot hvote_ex
  have hne_full : v ∉ (E.store cfg ext w (Nm1 + 1)).equivocating_indices :=
    Execution.honest_not_equivocating cfg ext hhb hec ⟨ast, ablk, hgeq⟩ hv w (Nm1 + 1) hw (by simpa only [← hNeq] using hHdeliver)
  have hle_pf : StoreLE
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb)
      (E.store cfg ext w (Nm1 + 1)) := by
    have hEq : E.store cfg ext w (Nm1 + 1) =
        (Event.attestation a false :: suf).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) := by
      change (E.schedule w (Nm1 + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store) tb = _
      rw [hl, List.foldl_append]
    rw [hEq]; exact foldl_storeLE cfg ext _ _
  have hne : v ∉
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        tb).equivocating_indices :=
    fun hc => hne_full (hle_pf.2.2.1 hc)
  -- assemble the application-second effect
  obtain ⟨P', msg, hsucc, hmsg, hge⟩ :=
    on_attestation_singleton_ge cfg ext
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store) tb) a v
      hsingle hval hvalid hne
  rw [show E.slot_start cfg (s + 1) = Nm1 + 1 from hNeq]
  change ∃ msg, ((E.schedule w (Nm1 + 1)).foldl
    (fun store event => (apply_event cfg ext store event).getD store) tb).latest_messages v =
      some msg ∧ a.data.target.epoch ≤ (get_latest_message_epoch cfg msg)
  exact foldl_deliver_ge cfg ext hl hsucc hmsg hge

/-- **Ubiquity.** The honest vote's recorded message persists at every honest
node from the delivery second on: for `m ≥ slot_start (s + 1)`, node `w` has a
recorded message for `v` of epoch at least the vote's target epoch
(`vote_lands` + `store_latest_message_ge_mono`). -/
theorem Execution.vote_ubiquity {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : NextSlotSynchronyPremises cfg ext E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hhead_known :
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root ∈
        (E.store cfg ext v n).block_roots)
    (hhead_walk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.beacon_block_root)
    {m : ℕ} (hm : E.slot_start cfg (s + 1) ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤ (get_latest_message_epoch cfg msg) :=
  E.store_latest_message_ge_mono cfg ext
    (E.vote_lands cfg ext hwf hhb hsyn hec hdiv hgen hv hw hn hHn
      (E.withinHorizon_mono cfg hm hHm) hvote hhead_known hhead_walk) hm

/-! ## Schedule-connected latest-message provenance (`Delivery`)

`LatestMessageProvenance` (Provenance.lean) records the *data* of the setting
attestation but drops its schedule connection, which `HonestBehavior.no_forgery`
needs. `SchedLMProv` is the strengthened invariant: every recorded LMD message
carries a **schedule-connected** attestation naming the recorder, with matching
LMD root and slot-epoch. It is a lighter induction than the full provenance —
the block-slot facts are dropped and schedule membership is store-independent,
so it rides across every non-attestation handler by the bare
`latest_messages` equality, and the `on_attestation` fresh case threads the
applied event's schedule membership straight out of the fold. -/

/-- Schedule-connected latest-message provenance: every recorded message was set
by an attestation that appears in some node's schedule, names the recorder, and
whose LMD block / slot-epoch match the message. -/
def SchedLMProv (E : Execution Root) (cfg : Config) (store : Store Root) : Prop :=
  ∀ (i : ValidatorIndex) (m : LatestMessage Root),
    store.latest_messages i = some m →
    ∃ (a : Attestation Root) (u : ValidatorIndex) (t : ℕ) (ifb : Bool),
      Event.attestation a ifb ∈ E.schedule u t ∧
      i ∈ a.attesting_indices ∧
      a.data.beacon_block_root = m.root ∧
      compute_epoch_at_slot cfg a.data.slot = (get_latest_message_epoch cfg m)

omit [LinearOrder Root] [Inhabited Root] in
/-- Provenance rides across any store update that leaves `latest_messages`
untouched (every non-attestation handler): the same schedule-connected witness
serves, since schedule membership does not depend on the store. -/
theorem schedLMProv_of_latest_eq {E : Execution Root} {store store' : Store Root}
    (h : SchedLMProv E cfg store)
    (hlm : store'.latest_messages = store.latest_messages) :
    SchedLMProv E cfg store' := by
  intro i m hm
  rw [hlm] at hm
  exact h i m hm

omit [Inhabited Root] in
/-- `on_attestation` preserves schedule-connected provenance: pre-existing
messages transport (the target-checkpoint write leaves `latest_messages` fixed);
a freshly installed message takes the applied attestation `a` as its witness,
schedule-connected by `hsched`, with both the LMD root and the derived epoch
matching by construction of the slot-based latest message. -/
theorem on_attestation_sched {E : Execution Root} {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool}
    (hsched : ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : SchedLMProv E cfg store)
    (hh : on_attestation cfg ext store a ifb = some store') :
    SchedLMProv E cfg store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact h i m hold
  · obtain ⟨u, t, hmem⟩ := hsched
    exact ⟨a, u, t, ifb, hmem, hi, by rw [hmeq], by rw [hmeq]; rfl⟩

/-- One dispatched event preserves schedule-connected provenance: block and
attester-slashing events leave `latest_messages` fixed; attestation events use
`on_attestation_sched`, drawing the applied attestation's schedule connection
from `hsched`. -/
theorem apply_event_sched {E : Execution Root} {store store' : Store Root} {e : Event Root}
    (hsched : ∀ a ifb, e = Event.attestation a ifb →
      ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : SchedLMProv E cfg store)
    (he : apply_event cfg ext store e = some store') :
    SchedLMProv E cfg store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact schedLMProv_of_latest_eq cfg h (on_block_latest cfg ext he)
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_sched cfg ext (hsched a ifb rfl) h he
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact schedLMProv_of_latest_eq cfg h (on_attester_slashing_latest ext he)
  | execution_payload_envelope envelope observation =>
    exact schedLMProv_of_latest_eq cfg h (on_execution_payload_envelope_frame ext he).latest_messages
  | payload_attestation_message message fromBlock =>
    exact schedLMProv_of_latest_eq cfg h (on_payload_attestation_message_frame cfg ext he).latest_messages

/-- Folding the second's events preserves schedule-connected provenance: every
attestation event of the fold list is a schedule member (fed to
`on_attestation_sched`), so the invariant is re-established at each step. -/
theorem sched_foldl {E : Execution Root} :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ a ifb, Event.attestation a ifb ∈ l →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t) →
      SchedLMProv E cfg s →
      SchedLMProv E cfg
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ h; exact h
  | cons e l ih =>
    intro s hl h
    rw [List.foldl_cons]
    have hesched : ∀ a ifb, e = Event.attestation a ifb →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t :=
      fun a ifb he => hl a ifb (by rw [← he]; exact List.mem_cons_self)
    cases he : apply_event cfg ext s e with
    | none =>
      simp only [Option.getD_none]
      exact ih s (fun a ifb hb => hl a ifb (List.mem_cons_of_mem e hb)) h
    | some s' =>
      simp only [Option.getD_some]
      exact ih s' (fun a ifb hb => hl a ifb (List.mem_cons_of_mem e hb))
        (apply_event_sched cfg ext hesched h he)

/-- Schedule-connected provenance holds at every node and second of a
well-formed execution whose genesis store is a `get_forkchoice_store` (empty
latest messages). Base: genesis has no recorded messages; step: push through
`on_tick` (a `latest_messages`-preserving update), then fold the second's
events — all scheduled at `(v, n + 1)`. -/
theorem Execution.schedLMProv {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    SchedLMProv E cfg (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg⟩ := hgen
    intro i m hm
    have hm' : E.genesis_store.latest_messages i = some m := hm
    rw [hg] at hm'
    simp [get_forkchoice_store] at hm'
  | succ n ih =>
    change SchedLMProv E cfg
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    refine sched_foldl cfg ext _ _ (fun a ifb hmem => ⟨v, n + 1, hmem⟩) ?_
    exact schedLMProv_of_latest_eq cfg ih
      (on_tick_latest cfg (E.store cfg ext v n) (E.time_at (n + 1)))

/-! ## Exact-message identification (`Delivery`)

The undelivered `Delivery` result 4: at the epoch-equality case of
`vote_ubiquity`, the recorded message's LMD root is *exactly* the block the
honest voter voted. Route: `SchedLMProv` supplies a schedule-connected setting
attestation `a'` naming `v`; `no_forgery` pins `a'.data` to `v`'s own vote for
`a'.data.slot`; `committee_assignment_unique` (both slots assigned, same epoch)
forces `a'.data.slot = s`; `E.vote` functionality then identifies that vote with
the given `a`, so `a'.data.beacon_block_root = a.data.beacon_block_root`. -/

/-- **Exact-message identification.** If honest `v` votes `a` for slot `s`, and
at honest-or-Byzantine node `w`, second `m`, the recorded latest message `msg`
for `v` sits in slot `s`'s epoch (`compute_epoch_at_slot cfg s = (get_latest_message_epoch cfg msg)`),
then `msg`'s LMD root is exactly `a`'s LMD block. Works for any vote `a`; the
epoch premise is phrased on the vote slot (for an honest vote it equals the FFG
target epoch under the head-slot bound). -/
theorem Execution.latest_message_root {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a))
    {m : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w m).latest_messages v = some msg)
    (hepoch : compute_epoch_at_slot cfg s = (get_latest_message_epoch cfg msg)) :
    msg.root = a.data.beacon_block_root := by
  obtain ⟨a', u, t, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen w m v msg hmsg
  obtain ⟨m1, a'', hvote', hdata'⟩ := hhb.no_forgery u t a' ifb hsched v hv hvin
  have hcs : v ∈ E.committee a'.data.slot :=
    hhb.votes_assigned v hv a'.data.slot (by rw [hvote']; exact Option.some_ne_none _)
  have hcs' : v ∈ E.committee s :=
    hhb.votes_assigned v hv s (by rw [hvote]; exact Option.some_ne_none _)
  have hslot_eq : a'.data.slot = s :=
    hec.committee_assignment_unique v a'.data.slot s hcs hcs' (by rw [hslotep, hepoch])
  rw [hslot_eq, hvote] at hvote'
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote'
  obtain ⟨-, haa⟩ := hvote'
  rw [← hbbr, hdata', haa]


/-! ## Exact recorded message, including the payload bit -/

/-- Schedule provenance with the complete latest-message value. The payload
bit is set by `update_latest_messages` from the attestation index. -/
def SchedLMProvExact (E : Execution Root) (store : Store Root) : Prop :=
  ∀ (i : ValidatorIndex) (m : LatestMessage Root),
    store.latest_messages i = some m →
    ∃ (a : Attestation Root) (u : ValidatorIndex) (t : ℕ) (ifb : Bool),
      Event.attestation a ifb ∈ E.schedule u t ∧
      i ∈ a.attesting_indices ∧
      m = LatestMessage.mk a.data.slot a.data.beacon_block_root
        (decide (a.data.index = 1))

private theorem schedLMProvExact_of_latest_eq {E : Execution Root}
    {store store' : Store Root} (h : SchedLMProvExact E store)
    (hlm : store'.latest_messages = store.latest_messages) :
    SchedLMProvExact E store' := by
  intro i m hm
  rw [hlm] at hm
  exact h i m hm

private theorem on_attestation_sched_exact {E : Execution Root}
    {store store' : Store Root} {a : Attestation Root} {ifb : Bool}
    (hsched : ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : SchedLMProvExact E store)
    (hh : on_attestation cfg ext store a ifb = some store') :
    SchedLMProvExact E store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact h i m hold
  · obtain ⟨u, t, hmem⟩ := hsched
    exact ⟨a, u, t, ifb, hmem, hi, hmeq⟩

private theorem apply_event_sched_exact {E : Execution Root}
    {store store' : Store Root} {e : Event Root}
    (hsched : ∀ a ifb, e = Event.attestation a ifb →
      ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : SchedLMProvExact E store)
    (he : apply_event cfg ext store e = some store') :
    SchedLMProvExact E store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact schedLMProvExact_of_latest_eq h (on_block_latest cfg ext he)
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_sched_exact cfg ext (hsched a ifb rfl) h he
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact schedLMProvExact_of_latest_eq h (on_attester_slashing_latest ext he)
  | execution_payload_envelope envelope observation =>
    exact schedLMProvExact_of_latest_eq h
      (on_execution_payload_envelope_frame ext he).latest_messages
  | payload_attestation_message message fromBlock =>
    exact schedLMProvExact_of_latest_eq h
      (on_payload_attestation_message_frame cfg ext he).latest_messages

private theorem sched_exact_foldl {E : Execution Root} :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ a ifb, Event.attestation a ifb ∈ l →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t) →
      SchedLMProvExact E s →
      SchedLMProvExact E
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ h; exact h
  | cons e l ih =>
    intro s hl h
    rw [List.foldl_cons]
    have hesched : ∀ a ifb, e = Event.attestation a ifb →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t :=
      fun a ifb he => hl a ifb (by rw [← he]; exact List.mem_cons_self)
    cases he : apply_event cfg ext s e with
    | none =>
      simp only [Option.getD_none]
      exact ih s (fun a ifb hb => hl a ifb (List.mem_cons_of_mem e hb)) h
    | some s' =>
      simp only [Option.getD_some]
      exact ih s' (fun a ifb hb => hl a ifb (List.mem_cons_of_mem e hb))
        (apply_event_sched_exact cfg ext hesched h he)

/-- Every recorded honest or Byzantine latest message has an exact scheduled
setting attestation, including its slot and payload-status bit. -/
theorem Execution.schedLMProvExact {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    SchedLMProvExact E (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg⟩ := hgen
    intro i m hm
    have hm' : E.genesis_store.latest_messages i = some m := hm
    rw [hg] at hm'
    simp [get_forkchoice_store] at hm'
  | succ n ih =>
    change SchedLMProvExact E
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    refine sched_exact_foldl cfg ext _ _
      (fun a ifb hmem => ⟨v, n + 1, hmem⟩) ?_
    exact schedLMProvExact_of_latest_eq ih
      (on_tick_latest cfg (E.store cfg ext v n) (E.time_at (n + 1)))

/-- The exact latest message of an honest validator is its unique vote in the
recorded epoch. This includes the payload bit, which the root-only provenance
lemma does not recover. -/
theorem Execution.latest_message_eq_honest_vote {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} (hv : v ∈ E.honest)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hvote : E.vote v s = some (k, a))
    {m : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w m).latest_messages v = some msg)
    (hepoch : compute_epoch_at_slot cfg s = get_latest_message_epoch cfg msg) :
    msg = LatestMessage.mk s a.data.beacon_block_root
      (decide (a.data.index = 1)) := by
  obtain ⟨a', u, t, ifb, hsched, hvin, hmsgEq⟩ :=
    E.schedLMProvExact cfg ext hgen w m v msg hmsg
  obtain ⟨k', a'', hvote', hdata'⟩ :=
    hhb.no_forgery u t a' ifb hsched v hv hvin
  have hcs : v ∈ E.committee a'.data.slot :=
    hhb.votes_assigned v hv a'.data.slot
      (by rw [hvote']; exact Option.some_ne_none _)
  have hcs' : v ∈ E.committee s :=
    hhb.votes_assigned v hv s
      (by rw [hvote]; exact Option.some_ne_none _)
  have hslotep : compute_epoch_at_slot cfg a'.data.slot =
      get_latest_message_epoch cfg msg := by
    rw [hmsgEq]
    rfl
  have hslot_eq : a'.data.slot = s :=
    hec.committee_assignment_unique v a'.data.slot s hcs hcs'
      (by rw [hslotep, hepoch])
  rw [hslot_eq, hvote] at hvote'
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote'
  have hdata : a'.data = a.data := by
    rw [hdata', hvote'.2]
  have hroot : a'.data.beacon_block_root = a.data.beacon_block_root :=
    congrArg AttestationData.beacon_block_root hdata
  have hindex : a'.data.index = a.data.index :=
    congrArg AttestationData.index hdata
  simpa only [hslot_eq, hroot, hindex] using hmsgEq

/-- Two stores that record the same honest validator in the same target epoch
record the same entire message. Committee assignment uniqueness identifies the
vote slot; no forgery then identifies its root and payload bit. -/
theorem Execution.latest_message_eq_of_same_epoch {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {i v w : ValidatorIndex} (hi : i ∈ E.honest)
    {n m : ℕ} {src dst : LatestMessage Root}
    (hsrc : (E.store cfg ext v n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hepoch : get_latest_message_epoch cfg src = get_latest_message_epoch cfg dst) :
    src = dst := by
  obtain ⟨a, u, t, ifb, hsched, hia, hsrcEq⟩ :=
    E.schedLMProvExact cfg ext hgen v n i src hsrc
  obtain ⟨k, a', hvote, _⟩ := hhb.no_forgery u t a ifb hsched i hi hia
  have hslotep : compute_epoch_at_slot cfg a.data.slot =
      get_latest_message_epoch cfg src := by
    rw [hsrcEq]
    rfl
  have hslotep' : compute_epoch_at_slot cfg a.data.slot =
      get_latest_message_epoch cfg dst := hslotep.trans hepoch
  have hsrcEq' := E.latest_message_eq_honest_vote cfg ext hhb hec hgen
    hi hvote hsrc hslotep
  have hdstEq' := E.latest_message_eq_honest_vote cfg ext hhb hec hgen
    hi hvote hdst hslotep'
  exact hsrcEq'.trans hdstEq'.symm

end FastConfirmation.Spec

end
