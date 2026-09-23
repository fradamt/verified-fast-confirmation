module
public import FastConfirmation.Spec.Proof.Remainder
public import FastConfirmation.Spec.Proof.Delivery
public import FastConfirmation.Spec.Model.PayloadEffects

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Spec / Proof / Identities: the economic-core coherence package

This module packages the coherence identities used by the proof decomposition.
The closing package for the three enumerated residuals of the economic core that
`EconomicCore` / `Remainder` / `IHMechanize` bottom out in:

* **Section A — the store-epoch trajectory invariant** (Remainder item-2 residual).
  `Remainder.hjc_le_of_store_epoch_bound` reduces the epoch-ordering side condition
  `hjc_le` of the closed vote-landing exports to the single transparent invariant
  `justified_checkpoint.epoch ≤ get_current_store_epoch`. This section proves that
  invariant along execution trajectories (mirroring the `WFTrajectory` /
  `Delivery.store_blocksSlotLe` induction pattern exactly) and closes `hjc_le`. The
  invariant needs the `ExternalsCoherence.pjf_checkpoint_epoch` bound that
  `process_justification_and_finalization` justifies no future epoch
  (`PjfCheckpointEpoch`, the companion of `state_transition_checkpoint_epoch`); it is
  taken as an explicit hypothesis.

* **Section B — `hspan`**: the saturated-regime `Jspec` lower bound
  `2·(boost+1) ≤ Jspec lo σ'` that `VoteLanding.boost_dilution` (`hJlb`) consumes.
  Delivered modulo a minimal nondegeneracy hypothesis `4·(boost+1) ≤ total_active`
  and the full-epoch honest-coverage floor — the genuine tiny-`TAB` edge, **explicit**.

* **Section C — the V/pre class-decomposition identities** feeding
  `EconomicCore.INV2_base_bridged`: the three definitional enemy-atom choices
  (`B_V`/`B0`/`Bbad`, discharged by `rfl`), leaving the five genuine class-decomposition
  identities packaged as the transparent `VpreIdentities` coherence bundle, composed into
  a fully-instantiated `INV2_base_bridged`.

-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section A — the store-epoch trajectory invariant

The justified and unrealized-justified checkpoint epochs never sit in a future
epoch. Both are tracked together (`CkptEpochLe`): `on_tick`'s epoch-boundary
pull-up raises the justified checkpoint to the store's own *unrealized* justified
checkpoint, so the invariant on the justified epoch is not self-contained — the
unrealized epoch bound is the load-bearing companion.

The tracking mirrors `Delivery.BlocksSlotLe`: a fixed slot bound `SL`, both
checkpoint epochs `≤ compute_epoch_at_slot SL`, carried through `on_tick` + the
event fold at each second and re-anchored at the wall-clock slot `slot_at n`. -/

/-- Two stores agree on both checkpoints the invariant tracks (justified and
unrealized-justified). The `SameBlocks` analog for the checkpoint fields: most
handler helpers leave both untouched, so the invariant rides across them. -/
def SameCkpt (s t : Store Root) : Prop :=
  s.justified_checkpoint = t.justified_checkpoint ∧
  s.unrealized_justified_checkpoint = t.unrealized_justified_checkpoint

namespace SameCkpt

theorem refl (s : Store Root) : SameCkpt s s := ⟨rfl, rfl⟩

theorem trans {a b c : Store Root} (hab : SameCkpt a b) (hbc : SameCkpt b c) :
    SameCkpt a c := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

/-- Folding a `SameCkpt`-preserving step preserves `SameCkpt`. -/
theorem foldl {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, SameCkpt s (f s a)) (l : List α) (s : Store Root) :
    SameCkpt s (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact SameCkpt.refl s
  | cons a l ih => exact (hf s a).trans (ih (f s a))

end SameCkpt

/-- Payload and PTC writes preserve both tracked checkpoints. -/
theorem PayloadFrame.sameCkpt {store store' : Store Root}
    (h : PayloadFrame store store') : SameCkpt store store' :=
  ⟨h.justified_checkpoint.symm, h.unrealized_justified_checkpoint.symm⟩

/-- The store-epoch bound tracked along a trajectory: both checkpoints the
invariant follows have epoch at most `compute_epoch_at_slot SL`. -/
def CkptEpochLe (cfg : Config) (SL : Slot) (s : Store Root) : Prop :=
  s.justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL ∧
  s.unrealized_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL

/-- `CkptEpochLe` rides across a `SameCkpt` step. -/
theorem CkptEpochLe.of_sameCkpt {cfg : Config} {SL : Slot} {s t : Store Root}
    (h : SameCkpt s t) (hs : CkptEpochLe cfg SL s) : CkptEpochLe cfg SL t := by
  obtain ⟨hj, hu⟩ := h
  exact ⟨hj ▸ hs.1, hu ▸ hs.2⟩

/-- `CkptEpochLe` weakens to a larger slot bound (`compute_epoch_at_slot` monotone). -/
theorem CkptEpochLe.mono {cfg : Config} {SL SL' : Slot} {s : Store Root}
    (hle : SL ≤ SL') (hs : CkptEpochLe cfg SL s) : CkptEpochLe cfg SL' s := by
  have hmono : compute_epoch_at_slot cfg SL ≤ compute_epoch_at_slot cfg SL' :=
    Nat.div_le_div_right hle
  exact ⟨le_trans hs.1 hmono, le_trans hs.2 hmono⟩

/-! ### Field lemmas — `update_checkpoints` / `update_unrealized_checkpoints` (generic) -/

theorem update_checkpoints_unrealized_justified (store : Store Root) (jc fc : Checkpoint Root) :
    (update_checkpoints store jc fc).unrealized_justified_checkpoint =
      store.unrealized_justified_checkpoint := by
  simp only [update_checkpoints]; split_ifs <;> rfl

theorem update_unrealized_checkpoints_justified (store : Store Root) (jc fc : Checkpoint Root) :
    (update_unrealized_checkpoints store jc fc).justified_checkpoint =
      store.justified_checkpoint := by
  simp only [update_unrealized_checkpoints]; split_ifs <;> rfl

theorem update_latest_messages_sameCkpt (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root) :
    SameCkpt store (update_latest_messages store attesting_indices attestation) := by
  simp only [update_latest_messages]
  refine SameCkpt.foldl (fun s i => ?_) _ store
  dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

/-- `update_checkpoints` keeps both tracked epochs `≤ CE(SL)` when the adopted
justified checkpoint is itself within the bound: the justified epoch becomes the
larger of the two (both bounded), the unrealized epoch is untouched. -/
theorem update_checkpoints_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root)
    (jc fc : Checkpoint Root) (hjc : jc.epoch ≤ compute_epoch_at_slot cfg SL)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (update_checkpoints store jc fc) := by
  refine ⟨?_, ?_⟩
  · simp only [update_checkpoints]
    split_ifs <;> first | exact hjc | exact h.1
  · rw [update_checkpoints_unrealized_justified]; exact h.2

/-- `update_unrealized_checkpoints` keeps both tracked epochs `≤ CE(SL)` when the
adopted unrealized-justified checkpoint is within the bound: the unrealized epoch
becomes the larger of the two (both bounded), the justified epoch is untouched. -/
theorem update_unrealized_checkpoints_CkptEpochLe (cfg : Config) (SL : Slot)
    (store : Store Root) (ujc ufc : Checkpoint Root)
    (hujc : ujc.epoch ≤ compute_epoch_at_slot cfg SL) (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (update_unrealized_checkpoints store ujc ufc) := by
  refine ⟨?_, ?_⟩
  · rw [update_unrealized_checkpoints_justified]; exact h.1
  · simp only [update_unrealized_checkpoints]
    split_ifs <;> first | exact hujc | exact h.2

/-! ### Field lemmas — the transparent helpers leave both checkpoints untouched -/

variable [LinearOrder Root] [Inhabited Root]

omit [Inhabited Root] in
theorem record_block_timeliness_sameCkpt (cfg : Config) (store : Store Root) (root : Root) :
    SameCkpt store (record_block_timeliness cfg store root) := by
  simp only [record_block_timeliness]; exact ⟨rfl, rfl⟩

theorem update_proposer_boost_root_sameCkpt (cfg : Config) (store : Store Root)
    (head root : Root) : SameCkpt store (update_proposer_boost_root cfg store head root) := by
  simp only [update_proposer_boost_root]; split_ifs <;> exact ⟨rfl, rfl⟩

omit [Inhabited Root] in
theorem store_target_checkpoint_state_sameCkpt (cfg : Config) (ext : Externals Root)
    (store : Store Root) (target : Checkpoint Root) :
    SameCkpt store (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]; split_ifs <;> exact ⟨rfl, rfl⟩

/-! ### Epoch bound for pulled-up justification

The store-epoch invariant is preserved by every handler using
`ExternalsCoherence.state_transition_checkpoint_epoch` — **except**
`compute_pulled_up_tip`, whose `update_checkpoints`/`update_unrealized_checkpoints`
adopt `process_justification_and_finalization(block_state).current_justified_checkpoint`,
whose epoch requires a separate bound. `PjfCheckpointEpoch` is the
companion of `state_transition_checkpoint_epoch`: epoch processing justifies no
future epoch (the real `process_justification_and_finalization` only ever
justifies the current or previous epoch of the state it runs on). It is supplied
by `ExternalsCoherence.pjf_checkpoint_epoch`, definitionally the same `Prop`. -/

/-- Epoch processing justifies no future epoch: `pjf`'s current-justified
checkpoint has epoch at most the state's own epoch. The companion of
`ExternalsCoherence.state_transition_checkpoint_epoch`; supplied by the frozen
field `ExternalsCoherence.pjf_checkpoint_epoch` (definitionally identical). -/
def PjfCheckpointEpoch (cfg : Config) (ext : Externals Root) : Prop :=
  ∀ st : BeaconState Root,
    (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg st.slot

/-! ### `compute_pulled_up_tip` preserves the store-epoch bound -/

omit [Inhabited Root] in
/-- `compute_pulled_up_tip` keeps both tracked epochs `≤ CE(SL)` when the pulled-up
state's justified checkpoint is within the bound (`hpjf_bound`, supplied by
`PjfCheckpointEpoch` + the block-slot bound at the call site). The
unrealized-justifications write is `SameCkpt`; the `update_unrealized_checkpoints`
and guarded `update_checkpoints` both adopt the pulled-up state's justified
checkpoint, bounded by `hpjf_bound`. -/
theorem compute_pulled_up_tip_CkptEpochLe (cfg : Config) (ext : Externals Root) (SL : Slot)
    (store : Store Root) (block_root : Root)
    (hpjf_bound :
      (ext.process_justification_and_finalization
        (store.block_states block_root)).current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg SL)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (compute_pulled_up_tip cfg ext store block_root) := by
  simp only [compute_pulled_up_tip]
  split_ifs with hlt
  · refine update_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    refine update_unrealized_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h
  · refine update_unrealized_checkpoints_CkptEpochLe cfg SL _ _ _ hpjf_bound ?_
    exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

/-! ### The event handlers preserve the store-epoch bound -/

omit [Inhabited Root] in
/-- `on_attestation` preserves the bound: it only writes `checkpoint_states` /
`latest_messages`, both `SameCkpt`. -/
theorem on_attestation_CkptEpochLe (cfg : Config) (ext : Externals Root) (SL : Slot)
    {store store' : Store Root} {a : Attestation Root} {ifb : Bool}
    (h : CkptEpochLe cfg SL store) (hh : on_attestation cfg ext store a ifb = some store') :
    CkptEpochLe cfg SL store' := by
  simp only [on_attestation] at hh
  split_ifs at hh
  cases hh
  exact CkptEpochLe.of_sameCkpt (update_latest_messages_sameCkpt _ _ _)
    (CkptEpochLe.of_sameCkpt (store_target_checkpoint_state_sameCkpt cfg ext store _) h)

omit [Inhabited Root] in
/-- `on_attester_slashing` preserves the bound: it only grows
`equivocating_indices`, `SameCkpt`. -/
theorem on_attester_slashing_CkptEpochLe (cfg : Config) (ext : Externals Root) (SL : Slot)
    {store store' : Store Root} {asl : AttesterSlashing Root}
    (h : CkptEpochLe cfg SL store)
    (hh : on_attester_slashing ext store asl = some store') :
    CkptEpochLe cfg SL store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

omit [Inhabited Root] in
theorem on_payload_attestation_message_CkptEpochLe (cfg : Config) (ext : Externals Root)
    (SL : Slot) {store store' : Store Root} {message : PayloadAttestationMessage Root}
    {is_from_block : Bool} (h : CkptEpochLe cfg SL store)
    (hh : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    CkptEpochLe cfg SL store' :=
  CkptEpochLe.of_sameCkpt (on_payload_attestation_message_frame cfg ext hh).sameCkpt h

omit [Inhabited Root] in
theorem on_execution_payload_envelope_CkptEpochLe (cfg : Config) (ext : Externals Root)
    (SL : Slot) {store store' : Store Root} {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root} (h : CkptEpochLe cfg SL store)
    (hh : on_execution_payload_envelope ext store envelope observation = some store') :
    CkptEpochLe cfg SL store' :=
  CkptEpochLe.of_sameCkpt (on_execution_payload_envelope_frame ext hh).sameCkpt h

/-- `on_block` preserves the store-epoch bound. The block's own justified
checkpoint (from `state_transition`) is bounded by the block epoch, which is at
most `SL` by the not-future gate; the pulled-up tip's justified checkpoint is
bounded by `PjfCheckpointEpoch` at the block's post-state slot. -/
theorem on_block_CkptEpochLe (cfg : Config) (ext : Externals Root) (SL : Slot)
    (hst_ckpt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' →
        st'.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : CkptEpochLe cfg SL store)
    (hh : on_block cfg ext store sb = some store') :
    CkptEpochLe cfg SL store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · have hge : sb.message.slot ≤ get_current_slot cfg store := by
      by_contra hfuture
      simp [on_block, hknown, hfuture] at hh
    simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
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
        have hframe := notify_ptc_messages_frame cfg ext hptc
        have hblkSL : compute_epoch_at_slot cfg sb.message.slot ≤ compute_epoch_at_slot cfg SL :=
          Nat.div_le_div_right (le_trans hge hcur)
        have hcjc : state.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg SL :=
          le_trans (hst_ckpt _ _ _ hst) hblkSL
        refine compute_pulled_up_tip_CkptEpochLe cfg ext SL _ sb.root ?_ ?_
        · rw [← (update_checkpoints_sameBlocks _ _ _).2.2,
              ← (update_proposer_boost_root_sameBlocks cfg _ _ _).2.2,
              ← (record_block_timeliness_sameBlocks cfg _ _).2.2,
              hframe.block_states]
          simp only [Function.update_self]
          refine le_trans (hpjf state) ?_
          rw [hst_slot _ _ _ hst]; exact hblkSL
        · refine update_checkpoints_CkptEpochLe cfg SL _ _ _ hcjc ?_
          refine CkptEpochLe.of_sameCkpt (update_proposer_boost_root_sameCkpt cfg _ _ _) ?_
          refine CkptEpochLe.of_sameCkpt (record_block_timeliness_sameCkpt cfg _ _) ?_
          refine CkptEpochLe.of_sameCkpt hframe.sameCkpt ?_
          exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h

/-- One dispatched event preserves the bound (needs the current-slot bound for
the `on_block` case, re-established across the fold). -/
theorem apply_event_CkptEpochLe (cfg : Config) (ext : Externals Root) (SL : Slot)
    (hst_ckpt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' →
        st'.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext)
    {store store' : Store Root} {e : Event Root}
    (hcur : get_current_slot cfg store ≤ SL) (h : CkptEpochLe cfg SL store)
    (he : apply_event cfg ext store e = some store') :
    CkptEpochLe cfg SL store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_CkptEpochLe cfg ext SL hst_ckpt hst_slot hpjf hcur h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_CkptEpochLe cfg ext SL h he
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact on_attester_slashing_CkptEpochLe cfg ext SL h he
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_CkptEpochLe cfg ext SL h he
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_CkptEpochLe cfg ext SL h he

/-! ### `on_tick` preserves the store-epoch bound

`on_tick`'s only checkpoint write is `on_tick_per_slot`'s epoch-boundary
`update_checkpoints`, which adopts the store's own *unrealized*-justified
checkpoint — bounded by the second `CkptEpochLe` conjunct. It touches neither the
unrealized-justified checkpoint nor the current slot's epoch bound, so no
slot-arithmetic is needed. -/

omit [LinearOrder Root] in
theorem on_tick_per_slot_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root) (time : ℕ)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
      | exact CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h
      | exact update_checkpoints_CkptEpochLe cfg SL _ _ _
          (CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h).2 (CkptEpochLe.of_sameCkpt ⟨rfl, rfl⟩ h)

omit [LinearOrder Root] in
theorem on_tick_aux_CkptEpochLe (cfg : Config) (SL : Slot) (tick_slot fuel : ℕ)
    (store : Store Root) (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel generalizing store with
  | zero => exact h
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_CkptEpochLe cfg SL store _ h)
    · exact h

omit [LinearOrder Root] in
theorem on_tick_CkptEpochLe (cfg : Config) (SL : Slot) (store : Store Root) (time : ℕ)
    (h : CkptEpochLe cfg SL store) :
    CkptEpochLe cfg SL (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_CkptEpochLe cfg SL _ time (on_tick_aux_CkptEpochLe cfg SL _ _ _ h)

/-! ### The event fold and the trajectory invariant -/

/-- Folding a second's scheduled events preserves the bound: every event keeps
the store's current slot fixed (`apply_event_get_current_slot`), so the
current-slot bound is re-established at each step. -/
theorem CkptEpochLe_foldl (cfg : Config) (ext : Externals Root) (SL : Slot)
    (hst_ckpt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' →
        st'.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot cfg b.message.slot)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root) (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hpjf : PjfCheckpointEpoch cfg ext) :
    ∀ (l : List (Event Root)) (s : Store Root),
      get_current_slot cfg s ≤ SL → CkptEpochLe cfg SL s →
      CkptEpochLe cfg SL
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
      refine ih s' ?_ (apply_event_CkptEpochLe cfg ext SL hst_ckpt hst_slot hpjf hcur h he)
      rw [apply_event_get_current_slot cfg ext he]; exact hcur

/-- **The store-epoch invariant.** At every node and second of a trajectory whose
genesis store is a `get_forkchoice_store`, both tracked checkpoint epochs are at
most `compute_epoch_at_slot (slot_at n)`. Mirrors `Delivery.store_blocksSlotLe`'s
induction exactly (genesis anchor slot from `get_current_slot_get_forkchoice_store`;
step weakens the bound by `slot_at_mono`, rides `on_tick`, folds the events). -/
theorem Execution.store_CkptEpochLe (E : Execution Root) (cfg : Config) (ext : Externals Root)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    CkptEpochLe cfg (E.slot_at cfg n) (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg, _⟩ := hgen
    have hcur0 : E.slot_at cfg 0 = ast.slot := by
      have h1 := E.store_current_slot cfg ext v 0
      rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg,
        get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at h1
      exact h1.symm
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hg]
    constructor
    · rw [hcur0]; exact le_of_eq (by simp only [get_forkchoice_store, get_current_epoch])
    · rw [hcur0]; exact le_of_eq (by simp only [get_forkchoice_store, get_current_epoch])
  | succ n ih =>
    change CkptEpochLe cfg (E.slot_at cfg (n + 1))
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have ih' : CkptEpochLe cfg (E.slot_at cfg (n + 1)) (E.store cfg ext v n) :=
      ih.mono (E.slot_at_mono cfg (Nat.le_succ n))
    have hontick : CkptEpochLe cfg (E.slot_at cfg (n + 1))
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) :=
      on_tick_CkptEpochLe cfg (E.slot_at cfg (n + 1)) _ _ ih'
    have hontickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have honticksl :
        get_current_slot cfg (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
          E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen, Execution.slot_at]
    exact CkptEpochLe_foldl cfg ext (E.slot_at cfg (n + 1))
      (fun st b st' hh => (hec.state_transition_checkpoint_epoch st b st' hh).1)
      hec.state_transition_slot hec.pjf_checkpoint_epoch _ _ (le_of_eq honticksl) hontick

/-- **The store-epoch bound** (Remainder item-2 residual, closed outright from the
frozen field `ExternalsCoherence.pjf_checkpoint_epoch` via `PjfCheckpointEpoch`): a
store's justified checkpoint never sits in a future epoch. -/
theorem Execution.store_justified_epoch_le (E : Execution Root) (cfg : Config)
    (ext : Externals Root) (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    (v : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext v n).justified_checkpoint.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  have hb := E.store_CkptEpochLe cfg ext hec hdiv hgen v n
  simp only [get_current_store_epoch]
  rw [E.store_current_slot cfg ext v n]
  exact hb.1

/-- **`hjc_le` CLOSED.** The epoch-ordering side condition carried by
`ExportWiring`'s vote-landing exports (`Remainder.hjc_le_of_store_epoch_bound`),
discharged from the store-epoch invariant. The head-slot bound `hhead` is taken
as an input in `Remainder`'s exact shape (`Delivery.store_blocks_slot_le_current`
+ block-state slot). -/
theorem Execution.hjc_le_closed (E : Execution Root) (cfg : Config) (ext : Externals Root)
    (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧ ast.slot = ablk.message.slot)
    {v : ValidatorIndex} {n : ℕ} {s : Slot} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s)
    (hhead : ((E.store cfg ext v n).block_states
        (get_head cfg (E.store cfg ext v n)).root).slot ≤ s) :
    (E.store cfg ext v n).justified_checkpoint.epoch ≤
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch :=
  E.hjc_le_of_store_epoch_bound cfg ext hec hn hhead
    (E.store_justified_epoch_le cfg ext hec hdiv hgen v n)

/-! ## Section B — `hspan`: the saturated `Jspec` lower bound (EXPLICIT tiny-`TAB` edge)

`VoteLanding.boost_dilution` consumes the saturated-regime `Jspec` lower bound
`hJlb σ' : 2·(boost+1) ≤ Jspec lo σ'` for every `σ'` at least two epochs past `es`
(the post-`T1` saturation regime, where the confirmation window covers a full
epoch). This is the genuine tiny-`TAB` edge: without a nondegeneracy floor a total
active balance below `4·(boost+1)` leaves no honest weight to dominate twice the
proposer boost, and the bound genuinely fails.

It is delivered modulo two explicit coherence inputs (no new assumption fields):

* `hnondeg` — the nondegeneracy `4·(boost+1) ≤ total_active` (the tiny-`TAB`
  exclusion the task calls for);
* `hcov` — the full-epoch honest-coverage floor `total_active ≤ 2·Jspec lo σ'` on
  the saturated span. It follows from `committee_coverage` (a span covering a full
  epoch contains every active validator, so its honest weight is
  `≥ (100−CBT)/100 ≥ 1/2` of `total_active`) + `span_fraction`; the `Finset`
  coverage-weight identity `weight(active) = total_active` is the residual, **explicit**
  (not delivered here). -/

/-- Pure-ℕ core (over plain variables — `omega` mis-atomizes the `Gwei`-typed
opaque `Jspec`/`total_active` terms inline). -/
private theorem hspan_arith {x T J : ℕ} (h1 : 4 * x ≤ T) (h2 : T ≤ 2 * J) : 2 * x ≤ J := by
  omega

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hspan`**, in `VoteLanding.boost_dilution`'s exact `hJlb` shape. From the
tiny-`TAB` nondegeneracy `4·(boost+1) ≤ total_active` and the saturated-span
honest-coverage floor `total_active ≤ 2·Jspec lo σ'`, the saturated `Jspec` lower
bound `2·(boost+1) ≤ Jspec lo σ'` holds. Both inputs are **explicit** (see the
section docstring); the arithmetic `4x ≤ T ≤ 2J ⟹ 2x ≤ J` is `hspan_arith`. -/
theorem hspan_of_coverage (cfg : Config) (lo es : Slot) (boost : ℕ)
    (hnondeg : 4 * (boost + 1) ≤ E.total_active cfg)
    (hcov : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ 2 * E.Jspec lo σ') :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      2 * (boost + 1) ≤ E.Jspec lo σ' := by
  intro σ' h1 h2 hσH
  exact hspan_arith hnondeg (hcov σ' h1 h2 hσH)

/-! ## Section C — the V/pre class-decomposition identities and `INV2_base_bridged`

`EconomicCore.INV2_base_bridged` takes eight V/pre identities as free inputs over
free atoms `aV xV apre xpre B_V B0 Bbad`. This section **pins the atom choices** and
discharges the three definitional identities (`hBV`/`hBfull`/`hBbadVal` — the enemy
atoms `B_V := Bval sa es`, `B0 := Bval lo es`, `Bbad := BbadVal`), leaving the five
genuine `Finset` class-decomposition identities as the transparent `VpreIdentities`
coherence bundle:

* `hJV` — supporter confinement `Sval [lo,es] + aV + xV = Jspec [sa,es]` (the honest
  `weight_partition` at `lo := sa`, once `Sval [lo,es] = Sval [sa,es]` — a supporter
  is assigned in the V-region `[sa,es]`, a `LatestMessageProvenance` + slot-monotone
  confinement);
* `hJfull` — the two-region window partition with `ParentStuck` (`span_committee`
  slot-split + `committee_assignment_unique` same-epoch disjointness);
* `hXval` — the sibling-stuck two-region split `xV + xpre = Xval [lo,es]`;
* `hR4b` / `hBbadfin` — the byz-partition inequalities over disjoint recorded
  predicates (`Bval` covering + `weight_add`-family).

These five form the explicit residual bundle (the `same-slot availability` family — the
supporter-confinement / two-region-split / byz-partition `Finset` algebra); the
bundle makes the atom choices and the definitional identities machine-checked, so
`INV2_base_bridged_instantiated` reduces `INV2(es)` to exactly the five
`VpreIdentities` fields plus the store-coherence package. -/

variable (cfg : Config) (ext : Externals Root)

/-- The five genuine V/pre class-decomposition identities feeding
`INV2_base_bridged`, with the enemy atoms pinned definitionally
(`B_V := Bval sa es`, `B0 := Bval lo es`, `Bbad := BbadVal`). The carried residual
(supporter confinement + two-region splits + byz partition). -/
structure VpreIdentities (v : ValidatorIndex) (n : ℕ) (bs : BeaconState Root) (b : Root)
    (lo es sa : Slot) (aV xV apre xpre : ℕ) : Prop where
  /-- Supporter confinement: honest window `[lo,es]` supporters partition `Jspec [sa,es]`. -/
  hJV : E.Sval cfg ext v n b lo es + aV + xV = E.Jspec sa es
  /-- Two-region honest window partition with `ParentStuck`. -/
  hJfull : E.Sval cfg ext v n b lo es + aV + xV
      + (E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) + apre + xpre)
    = E.Jspec lo es
  /-- Sibling-stuck two-region split. -/
  hXval : xV + xpre = E.Xval cfg ext v n b lo es
  /-- V-span byz partition inequality. -/
  hR4b : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map
      (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es ≤ E.Bval sa es
  /-- Full-window byz partition inequality. -/
  hBbadfin : E.BbadVal cfg ext v n b lo es
      + (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es
      + E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) ≤ E.Bval lo es

/-- **`INV2_base_bridged` fully instantiated per confirmed block** (`Identities` item 1).
The three definitional atom identities (`hBV`/`hBfull`/`hBbadVal`, i.e. the enemy-atom
choices) are discharged by `rfl`; the five genuine class-decomposition identities are
supplied by the transparent `VpreIdentities` bundle. Reduces `INV2(es)` from a
confirmed instance to exactly `VpreIdentities` + the per-store coherence package. -/
theorem INV2_base_bridged_instantiated
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} {lo es sa : Slot}
    {aV xV apre xpre : ℕ}
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hlo : lo = ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hsa : sa =
      (if get_block_epoch cfg (E.store cfg ext v n) b >
          get_block_epoch cfg (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).parent_root
        then compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
        else ((E.store cfg ext v n).blocks b).slot))
    (hloH : E.SlotWithinHorizon cfg lo)
    (hesH : E.SlotWithinHorizon cfg es)
    (hsaH : E.SlotWithinHorizon cfg sa)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root)
    (hdom : E.RecordedEpochMax cfg ext v n es)
    (hV : VpreIdentities E cfg ext v n bs b lo es sa aV xV apre xpre) :
    E.INV2 cfg ext v n b lo es es (compute_proposer_score cfg bs) :=
  E.INV2_base_bridged cfg ext hhb hec hbb hgen hv hnH hwf hprov
    hconf hval htab hlo hes hsa hloH hesH hsaH hbH
    hslotlt hwalk hdom (aV := aV) (xV := xV) (apre := apre) (xpre := xpre)
    (B_V := E.Bval sa es) (B0 := E.Bval lo es) (Bbad := E.BbadVal cfg ext v n b lo es)
    hV.hJV rfl hV.hJfull rfl hV.hR4b hV.hBbadfin hV.hXval rfl

end FastConfirmation.Spec

end
