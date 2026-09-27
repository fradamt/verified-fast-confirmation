module
public import FastConfirmationProofs.FFG.Concrete.BridgeLaws
public import FastConfirmationProofs.FFG.Concrete.CanonicalTiming
public import FastConfirmationProofs.FFG.Concrete.CertificateTranslation
public import FastConfirmationProofs.FFG.Concrete.PointwiseAttestation
public import FastConfirmationProofs.Execution.Delivery.Registry
public import FastConfirmationInternal.Premises.Externals
public import FastConfirmationStatements.Premises.ConcreteSafety

@[expose] public section

/-! Proves for the concrete bridge the fields of the internal records
`BeaconExternalsPremises` and `StaticValidatorSet` that follow from the bridge
and `ConcreteGenesis`: the slot laws, the checkpoint-epoch laws, the anchor
checkpoint epochs, default-state rejection, the static registry, the genesis
horizon, and constant activity. With the residual public record
`ConcreteBridge.ConcreteExternalsPremises` they give both internal records
(`ConcreteExternalsPremises.beaconExternals`, `staticValidatorSet`). The
residual fields (committee agreement, signature soundness, committee
confinement, slot-processing validity, and envelope determinism) read the
execution ground truth or the opaque `base` methods, so the bridge does not
prove them. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-! ### Registry frames of the concrete functions -/

section Frames

variable [DecidableEq Root]

omit [DecidableEq Root] in
theorem slotStep_validators {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} (h : slotStep cfg preset state = .ok next) :
    next.validators = state.validators := by
  obtain ⟨s1, hs1, hcase⟩ := slotStep_eq_ok h
  obtain ⟨-, -, rfl⟩ := process_slot_eq_ok.mp hs1
  rcases hcase with ⟨-, rfl⟩ | ⟨-, mid, hmid, rfl⟩
  · rfl
  · obtain ⟨_, _, _, _, rfl, -⟩ := process_justification_and_finalization_outcome hmid
    rfl

omit [DecidableEq Root] in
theorem slotFold_validators {cfg : Config} {preset : FFGPreset} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root),
      steps.foldlM (fun s _ => slotStep cfg preset s) state = .ok next →
      next.validators = state.validators := by
  intro steps
  induction steps with
  | nil =>
    intro state next h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    rfl
  | cons _ steps ih =>
    intro state next h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    exact (ih mid next hrest).trans (slotStep_validators hmid)

omit [DecidableEq Root] in
/-- Concrete `process_slots` keeps the registry. -/
theorem process_slots_validators {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {target : Slot}
    (h : process_slots cfg preset state target = .ok next) :
    next.validators = state.validators := by
  obtain ⟨-, -, hfold⟩ := process_slots_eq_ok.mp h
  exact slotFold_validators _ _ _ hfold

theorem attestationFold_validators {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state next : FFGBeaconState Root),
      attestations.foldlM (fun s vote =>
        process_attestation cfg preset schedule s vote parentSlot) state = .ok next →
      next.validators = state.validators := by
  intro attestations
  induction attestations with
  | nil =>
    intro state next h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    rfl
  | cons vote attestations ih =>
    intro state next h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    rw [ih mid next hrest]
    obtain ⟨_, _, _, _, _, rfl, _, _⟩ := process_attestation_flags hmid
    rfl

/-- Concrete `state_transition` keeps the registry. -/
theorem state_transition_validators {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {oracle : BlockValidityOracle Root}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (h : state_transition cfg preset schedule oracle state block = .ok next) :
    next.validators = state.validators := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  obtain ⟨paid, headed, hpaid, hheaded, hfold⟩ := process_block_eq_ok hblock
  obtain ⟨_, _, rfl⟩ := process_parent_execution_payload_eq_ok hpaid
  obtain ⟨-, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  have hatSlot := process_slots_validators hslots
  exact (attestationFold_validators _ _ _ hfold).trans hatSlot

end Frames

/-! ### Laws of the bridge interface -/

namespace ConcreteBridge

section Laws

variable [DecidableEq Root] (B : ConcreteBridge Root)

/-- `process_slots` of the bridge targets its slot. -/
theorem slots_slot (st : BeaconState Root) (target : Slot) :
    (B.slots st target).slot = target := by
  unfold slots
  split
  · split
    · split
      · rename_i next h
        exact (process_slots_slot h).1
      · rfl
    · rfl
  · rfl

/-- `process_slots` of the bridge keeps the registry. -/
theorem slots_validators (st : BeaconState Root) (target : Slot) :
    (B.slots st target).validators = st.validators := by
  unfold slots
  split
  · rename_i cs hd
    split
    · split
      · rename_i next h
        rw [(B.decode_some hd).1]
        exact process_slots_validators h
      · rfl
    · rfl
  · rfl

/-- A successful bridge transition lands on the block slot, after the
pre-state slot, and keeps the registry. -/
theorem transition_frame {st post : BeaconState Root} {sb : SignedBeaconBlock Root}
    (h : B.transition st sb = some post) :
    post.slot = sb.message.slot ∧ st.slot < sb.message.slot ∧
      post.validators = st.validators := by
  obtain ⟨cs, wire, stateRoot, cpost, hd, -, -, hm, hst, -, -, rfl⟩ := B.transition_eq_some h
  obtain ⟨hs1, hs2⟩ := state_transition_slot hst
  rw [(B.decode_some hd).1]
  have hmslot : sb.message.slot = wire.slot := hm.1
  rw [hmslot]
  exact ⟨hs1, hs2, state_transition_validators hst⟩

/-- PJF of the bridge adopts no future justified checkpoint. -/
theorem pjf_checkpoint_epoch (st : BeaconState Root)
    (h : st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot B.setup.cfg st.slot) :
    (B.pjf st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot B.setup.cfg st.slot := by
  have hfallback : (fallbackPJF B.setup.cfg st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot B.setup.cfg st.slot := by
    unfold fallbackPJF
    split_ifs
    assumption
  unfold pjf
  split
  · rename_i cs hd
    split
    · rename_i next hnext
      have hst := (B.decode_some hd).1
      subst hst
      obtain ⟨_, _, j, _, rfl, hcase⟩ := process_justification_and_finalization_outcome hnext
      change j.epoch ≤ compute_epoch_at_slot B.setup.cfg cs.slot
      rcases hcase with ⟨-, -, rfl, -⟩ | ⟨-, -, hj, -⟩
      · exact h
      · rcases hj with rfl | ⟨_, -, -, hje, -⟩ | ⟨_, -, -, hje, -⟩
        · exact h
        · rw [hje]
          exact Nat.sub_le _ _
        · rw [hje]
    · exact hfallback
  · exact hfallback

end Laws

end ConcreteBridge

section Premise

variable [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-! ### Slot laws -/

omit [Inhabited Root] in
/-- `BeaconExternalsPremises.process_slots_slot` for the bridge. -/
theorem interface_process_slots_slot (st : BeaconState Root) (s : Slot) (_ : st.slot < s) :
    (B.interface.process_slots st s).slot = s :=
  B.slots_slot st s

omit [Inhabited Root] in
/-- `BeaconExternalsPremises.state_transition_slot` for the bridge. -/
theorem interface_state_transition_slot (st : BeaconState Root) (sb : SignedBeaconBlock Root)
    (st' : BeaconState Root) (h : B.interface.state_transition st sb = some st') :
    st'.slot = sb.message.slot :=
  (B.transition_frame h).1

omit [Inhabited Root] in
/-- `BeaconExternalsPremises.state_transition_pre_slot_lt` for the bridge. -/
theorem interface_state_transition_pre_slot_lt (st : BeaconState Root)
    (sb : SignedBeaconBlock Root) (st' : BeaconState Root)
    (h : B.interface.state_transition st sb = some st') : st.slot < sb.message.slot :=
  (B.transition_frame h).2.1

/-! ### Checkpoint-epoch laws -/

omit [Inhabited Root] in
/-- `BeaconExternalsPremises.state_transition_checkpoint_epoch` for the
bridge. The post-state is reachable and in scope, so the invariants bound its
checkpoints; the antecedent is not needed. -/
theorem interface_state_transition_checkpoint_epoch (hB : B.Admissible)
    (st : BeaconState Root) (sb : SignedBeaconBlock Root) (st' : BeaconState Root)
    (h : B.interface.state_transition st sb = some st') :
    st'.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot B.setup.cfg sb.message.slot ∧
      st'.finalized_checkpoint.epoch ≤ compute_epoch_at_slot B.setup.cfg sb.message.slot := by
  obtain ⟨cs, wire, -, cpost, hd, -, -, hm, hst, -, hin, rfl⟩ := B.transition_eq_some h
  obtain ⟨-, ⟨blocks, votes, hreach⟩, -⟩ := B.decode_some hd
  have hreach' := Reachable.block wire hreach hst
  have hinv := provenanceInvariant_of_reachable hB.setup hreach' hin
  have hfin := finalityInvariant_of_reachable hB.setup hreach' hin
  have hslot : sb.message.slot = cpost.slot := hm.1.trans (state_transition_slot hst).1.symm
  rw [hslot, project_current_justified, project_finalized]
  have h1 := hinv.current_epoch_le
  have h2 := hfin.finalized_le_previous
  have h3 := hfin.previous_le_current
  constructor <;> beacon_omega

omit [Inhabited Root] in
/-- `BeaconExternalsPremises.pjf_checkpoint_epoch` for the bridge. -/
theorem interface_pjf_checkpoint_epoch (st : BeaconState Root)
    (hle : st.current_justified_checkpoint.epoch ≤ compute_epoch_at_slot B.setup.cfg st.slot) :
    (B.interface.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
      compute_epoch_at_slot B.setup.cfg st.slot :=
  B.pjf_checkpoint_epoch st hle

/-- `BeaconExternalsPremises.anchor_state_checkpoint_epoch` for the bridge:
the anchor state is the projected genesis state, whose checkpoints have epoch
zero. -/
theorem anchor_state_checkpoint_epoch {E : Execution Root} (hg : B.ConcreteGenesis E) :
    E.anchor_state.current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot B.setup.cfg E.anchor_state.slot ∧
      E.anchor_state.finalized_checkpoint.epoch ≤
        compute_epoch_at_slot B.setup.cfg E.anchor_state.slot := by
  rw [B.registry_eq hg]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-! ### Default-state rejection -/

/-- `BeaconExternalsPremises.valid_attestation_default` for the bridge: the
structural check of the fixed schedule rejects an empty index list, and the
default state has no validators. -/
theorem interface_valid_attestation_default (a : Attestation Root) :
    B.interface.is_valid_indexed_attestation (default : BeaconState Root) a = false := by
  change (legacy_indexed_structure B.setup.preset (default : BeaconState Root) a &&
    B.base.is_valid_indexed_attestation default a) = false
  have hv : (default : BeaconState Root).validators = [] := rfl
  cases h : a.attesting_indices with
  | nil => simp [legacy_indexed_structure, h]
  | cons i is => simp [legacy_indexed_structure, h, hv]

/-! ### The static registry -/

theorem genesis_store_eq {E : Execution Root} (hg : B.ConcreteGenesis E) :
    ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store B.setup.cfg ast ablk := by
  obtain ⟨ablk, -, -, -, -, -, hgs⟩ := hg
  exact ⟨_, ablk, hgs⟩

/-- Every node store of a run with the concrete bridge keeps the execution
registry. -/
theorem store_registryConstant {E : Execution Root}
    (hg : B.ConcreteGenesis E) (v : ValidatorIndex) (n : ℕ) :
    RegistryConstant E.registry (E.store B.setup.cfg B.interface v n) := by
  induction n with
  | zero => exact E.genesis_registryConstant B.setup.cfg (B.genesis_store_eq hg)
  | succ n ih =>
    change RegistryConstant E.registry
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event B.setup.cfg B.interface store event).getD store)
        (on_tick B.setup.cfg (E.store B.setup.cfg B.interface v n) (E.time_at (n + 1))))
    refine registryConstant_foldl
      (fun store event hstore => apply_event_getD_registryConstant B.setup.cfg B.interface
        (fun _ _ _ h => (B.transition_frame h).2.2) B.slots_validators
        store event hstore) _ _ ?_
    exact on_tick_registryConstant B.setup.cfg _ _ ih

/-- Every exact-prefix store of a run with the concrete bridge keeps the
execution registry. -/
theorem prefix_registryConstant {E : Execution Root}
    (hg : B.ConcreteGenesis E) {store : Store Root}
    (h : E.ScheduledPrefixStore B.setup.cfg B.interface store) :
    RegistryConstant E.registry store := by
  cases h with
  | genesis => exact E.genesis_registryConstant B.setup.cfg (B.genesis_store_eq hg)
  | scheduledPrefix p =>
    unfold Execution.ScheduledEventPrefix.store
    refine registryConstant_foldl
      (fun store event hstore => apply_event_getD_registryConstant B.setup.cfg B.interface
        (fun _ _ _ h => (B.transition_frame h).2.2) B.slots_validators
        store event hstore) _ _ ?_
    exact on_tick_registryConstant B.setup.cfg _ _
      (B.store_registryConstant hg p.node p.previousSecond)

/-- `BeaconExternalsPremises.registry_static_in_horizon` for the bridge. The
concrete transition writes no validator record, and it rejects a block with
a registry-changing operation (`FFGWireBlock.InFixedScope`). -/
theorem registry_static_in_horizon {E : Execution Root}
    (hg : B.ConcreteGenesis E) (state : BeaconState Root)
    (h : RegistryStateInHorizon B.setup.cfg B.interface E state) :
    state.validators = E.registry := by
  have hreach : ∀ {st : BeaconState Root},
      E.ReachableValidationState B.setup.cfg B.interface st → st.validators = E.registry := by
    intro st hst
    obtain ⟨store, hstore, hst⟩ := hst
    have hreg := B.prefix_registryConstant hg (hstore.causal B.setup.cfg B.interface)
    rcases hst with ⟨root, hroot, rfl⟩ | ⟨checkpoint, hcheckpoint, rfl⟩
    · exact hreg.1 root hroot
    · exact hreg.2 checkpoint hcheckpoint
  rcases h with h | ⟨base, slot, hbase, -, rfl⟩
  · exact hreach h
  · change (B.slots base slot).validators = _
    rw [B.slots_validators]
    exact hreach hbase

/-- `StaticValidatorSet.activity_constant` for the bridge. The execution
registry is the scope registry, whose activity is fixed through the last
scope epoch (`FixedFFGScope.activity_fixed`); an index outside the registry
reads the default validator at every epoch. -/
theorem activity_constant (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hh : E.verification_horizon = B.setup.scope.last_epoch + 1) (i : ValidatorIndex)
    (e e' : Epoch) (he : e < E.verification_horizon) (he' : e' < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) e =
      is_active_validator (E.registry.getD i default) e' := by
  have hreg : E.registry = B.setup.scope.validators := by
    unfold Execution.registry
    rw [B.registry_eq hg]
    rfl
  rw [hreg]
  by_cases hi : i < B.setup.scope.validators.length
  · have hf : ∀ x : Epoch, B.setup.scope.first_epoch ≤ x → x ≤ B.setup.scope.last_epoch →
        is_active_validator (B.setup.scope.validators[i]'hi) x =
          is_active_validator (B.setup.scope.validators[i]'hi) B.setup.scope.first_epoch :=
      B.setup.scope.activity_fixed ⟨i, hi⟩
    have h0 := hB.setup.scope_from_genesis
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hf e (by beacon_omega) (by beacon_omega), hf e' (by beacon_omega) (by beacon_omega)]
  · have hexit : (default : Validator).exit_epoch = 0 := rfl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
      Option.getD_none]
    simp [is_active_validator, hexit]

/-- `StaticValidatorSet.genesis_within_horizon` for the bridge: the genesis
store starts at the `uint64` genesis time and slot 0, and epoch 0 is in the
horizon. -/
theorem genesis_within_horizon (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hh : E.verification_horizon = B.setup.scope.last_epoch + 1) :
    E.WithinHorizon B.setup.cfg 0 := by
  obtain ⟨ablk, -, -, -, -, -, hgs⟩ := hg
  have htime : E.time_at 0 = B.setup.genesisTime := by
    simp [Execution.time_at, hgs, get_forkchoice_store, project, FFGSetup.genesis,
      FFGBeaconState.genesis, FFGBeaconState.toBeaconState]
  have hslot : E.slot_at B.setup.cfg 0 = 0 := by
    simp [Execution.slot_at, htime, hgs, get_forkchoice_store, project, FFGSetup.genesis,
      FFGBeaconState.genesis, FFGBeaconState.toBeaconState, GENESIS_SLOT]
  refine ⟨htime ▸ hB.genesis_time, by rw [hslot]; exact Nat.zero_le _, ?_⟩
  rw [hslot, hh]
  simp [compute_epoch_at_slot]

/-- The static validator set of a run with the concrete bridge. -/
theorem staticValidatorSet (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hh : E.verification_horizon = B.setup.scope.last_epoch + 1) :
    StaticValidatorSet B.setup.cfg E :=
  ⟨B.genesis_within_horizon hB hg hh, B.activity_constant hB hg hh⟩

/-- The internal external contracts of a run with the concrete bridge: the
residual public contracts and the bridge theorems. -/
theorem ConcreteExternalsPremises.beaconExternals {B : ConcreteBridge Root}
    (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (h : B.ConcreteExternalsPremises E) :
    BeaconExternalsPremises B.setup.cfg B.interface E where
  process_slots_slot := B.interface_process_slots_slot
  registry_static_in_horizon := B.registry_static_in_horizon hg
  state_transition_slot := B.interface_state_transition_slot
  state_transition_pre_slot_lt := B.interface_state_transition_pre_slot_lt
  state_transition_checkpoint_epoch := fun st b st' _ _ hst =>
    B.interface_state_transition_checkpoint_epoch hB st b st' hst
  pjf_checkpoint_epoch := B.interface_pjf_checkpoint_epoch
  anchor_state_checkpoint_epoch := B.anchor_state_checkpoint_epoch hg
  committees_agree := h.committees_agree
  honest_attestation_valid := h.honest_attestation_valid
  valid_attestation_honest := h.valid_attestation_honest
  on_attestation_committee := h.on_attestation_committee
  committee_assignment_unique := h.committee_assignment_unique
  committee_coverage := h.committee_coverage
  committee_members_active := h.committee_members_active
  valid_attestation_default := B.interface_valid_attestation_default
  process_slots_attestation_valid := h.process_slots_attestation_valid
  verify_envelope_deterministic := h.verify_envelope_deterministic

/-- The residual public contracts are fields of the internal record. -/
theorem ConcreteExternalsPremises.of_beaconExternals {B : ConcreteBridge Root}
    {E : Execution Root}
    (h : BeaconExternalsPremises B.setup.cfg B.interface E) :
    B.ConcreteExternalsPremises E :=
  ⟨h.committees_agree, h.honest_attestation_valid, h.valid_attestation_honest,
    h.on_attestation_committee, h.committee_assignment_unique, h.committee_coverage,
    h.committee_members_active, h.process_slots_attestation_valid,
    h.verify_envelope_deterministic⟩

end ConcreteBridge

end Premise

end FastConfirmation.Spec.ConcreteFFG

end
