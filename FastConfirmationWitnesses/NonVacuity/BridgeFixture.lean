module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.Concrete.SafetyTranslation
public import FastConfirmationProofs.FFG.Concrete.PointwiseAttestation

@[expose] public section

/-! Shared fixture for finite witnesses of `ConcreteBridge.SafetyPremises`.

A witness bridge uses finite tables for the two commitments. The state
functions of `B.interface` decode a state classically, so the kernel cannot
evaluate them. `lookupInterface` is a computable copy: it decodes a state by
a table lookup and an equality test, and it runs the pointwise forms of the
concrete transition. `interface_eq_lookupInterface` proves that the two
interfaces are equal when every table state is in the decode domain. A
witness proves its premises for the lookup interface by kernel evaluation
and rewrites them to `B.interface`. -/

namespace FastConfirmation.Spec
deriving instance DecidableEq for FFGBlockHeader
deriving instance DecidableEq for FFGBeaconState
deriving instance DecidableEq for BeaconState
end FastConfirmation.Spec

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-! ### Table commitments -/

section Tables

variable [DecidableEq Root]

/-- The committed root of a state in a finite table: the first key whose
state is the given state, or `junk`. -/
def tableRoot (entries : List (Root × FFGBeaconState Root)) (junk : Root)
    (state : FFGBeaconState Root) : Root :=
  ((entries.find? fun e => e.2 = state).map Prod.fst).getD junk

/-- The opening of a root in a finite table: the state of the first entry with
that key. -/
def tableOpen (entries : List (Root × FFGBeaconState Root)) (id : Root) :
    Option (FFGBeaconState Root) :=
  (entries.find? fun e => e.1 = id).map Prod.snd

theorem tableOpen_mem {entries : List (Root × FFGBeaconState Root)} {id : Root}
    {state : FFGBeaconState Root} (h : tableOpen entries id = some state) :
    (id, state) ∈ entries := by
  unfold tableOpen at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hkey : e.1 = id := by simpa using List.find?_some he
  rw [← hkey]
  exact List.mem_of_find?_eq_some he

theorem tableOpen_sound (entries : List (Root × FFGBeaconState Root)) (junk : Root)
    (hvalues : (entries.map Prod.snd).Nodup) (id : Root) (state : FFGBeaconState Root)
    (h : tableOpen entries id = some state) : tableRoot entries junk state = id := by
  unfold tableOpen at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hemem : e ∈ entries := List.mem_of_find?_eq_some he
  have hekey : e.1 = id := by simpa using List.find?_some he
  unfold tableRoot
  cases hf : entries.find? (fun x => decide (x.2 = e.2)) with
  | none =>
    exact absurd (List.find?_eq_none.mp hf e hemem) (by simp)
  | some e' =>
    have h1 : e' ∈ entries := List.mem_of_find?_eq_some hf
    have h2 : e'.2 = e.2 := by simpa using List.find?_some hf
    have heq : e' = e := List.inj_on_of_nodup_map hvalues h1 hemem h2
    simp [heq, hekey]

/-- A finite state commitment. Its states must be pairwise distinct. -/
def tableStates (entries : List (Root × FFGBeaconState Root)) (junk : Root)
    (hvalues : (entries.map Prod.snd).Nodup) : StateCommitment Root where
  root := tableRoot entries junk
  open_ := tableOpen entries
  open_sound := tableOpen_sound entries junk hvalues

/-- A finite block commitment. -/
def tableBlocks (entries : List (Root × (FFGWireBlock Root × Root))) : BlockCommitment Root where
  open_ := fun r => (entries.find? fun e => e.1 = r).map Prod.snd

end Tables

/-! ### Sort-free indexing -/

/-- The attesting indices of a wire attestation before deduplication. -/
def attestingList (schedule : FixedCommitteeSchedule) (vote : FFGWireAttestation Root) :
    List ValidatorIndex :=
  ((get_committee_indices vote.committee_bits).foldl (fun (acc : ℕ × List ValidatorIndex)
      committeeIndex =>
    let committee := (schedule.committee vote.data.slot committeeIndex).getD []
    let members := ((List.range committee.length).filter fun i =>
      vote.aggregation_bits.getD (acc.1 + i) false).map fun i => committee.getD i 0
    (acc.1 + committee.length, acc.2 ++ members)) (0, [])).2

theorem get_attesting_indices_eq_toFinset (schedule : FixedCommitteeSchedule)
    (vote : FFGWireAttestation Root) :
    get_attesting_indices schedule vote = (attestingList schedule vote).toFinset := by
  unfold get_attesting_indices attestingList
  rfl

theorem sort_toFinset (l : List ℕ) :
    (l.toFinset).sort (· ≤ ·) = l.dedup.insertionSort (· ≤ ·) := by
  unfold Finset.sort
  rw [List.toFinset_val, Multiset.coe_sort, List.mergeSort_eq_insertionSort]

/-- Insertion into a sorted list of indices. The kernel of an importing module
cannot unfold `List.orderedInsert`, so the witnesses use this copy. -/
def sortedInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: sortedInsert a l

/-- Insertion sort of indices, a copy of `List.insertionSort (· ≤ ·)`. -/
def insertionSortNat : List ℕ → List ℕ
  | [] => []
  | b :: l => sortedInsert b (insertionSortNat l)

theorem sortedInsert_eq (a : ℕ) (l : List ℕ) :
    sortedInsert a l = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => simp [sortedInsert]
  | cons b l ih =>
    simp only [sortedInsert, List.orderedInsert_cons, ih]

theorem insertionSortNat_eq (l : List ℕ) : insertionSortNat l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [insertionSortNat]
  | cons b l ih =>
    simp only [insertionSortNat, List.insertionSort_cons, ih, sortedInsert_eq]

/-- The indexed projection of a wire attestation without `Finset.sort`. -/
def indexedList (schedule : FixedCommitteeSchedule) (vote : FFGWireAttestation Root) :
    IndexedAttestation Root :=
  ⟨insertionSortNat (attestingList schedule vote).dedup, vote.data⟩

theorem indexed_eq_indexedList (B : ConcreteBridge Root) (vote : FFGWireAttestation Root) :
    B.indexed vote = indexedList B.setup.schedule vote := by
  unfold ConcreteBridge.indexed indexedList get_indexed_attestation
  rw [get_attesting_indices_eq_toFinset, sort_toFinset, insertionSortNat_eq]

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

/-! ### The lookup interface -/

section Lookup

variable [LinearOrder Root] [Inhabited Root] (B : ConcreteBridge Root)

/-- `decode` by table lookup: the opened state, if its projection is the
input state. -/
def lookupDecode (st : BeaconState Root) : Option (FFGBeaconState Root) :=
  match st.source_identity with
  | none => none
  | some id =>
    match B.states.open_ id with
    | none => none
    | some state => if B.project state = st then some state else none

/-- `pjf` over `lookupDecode`. -/
def lookupPJF (st : BeaconState Root) : BeaconState Root :=
  match lookupDecode B st with
  | some state =>
    match process_justification_and_finalization B.setup.cfg B.setup.preset state with
    | .ok next => B.project next
    | .error _ => ConcreteBridge.fallbackPJF B.setup.cfg st
  | none => ConcreteBridge.fallbackPJF B.setup.cfg st

/-- `fallbackSlots` over `lookupPJF`. -/
def lookupFallbackSlots (st : BeaconState Root) (target : Slot) : BeaconState Root :=
  { st with
    slot := target
    current_justified_checkpoint :=
      if compute_epoch_at_slot B.setup.cfg st.slot < compute_epoch_at_slot B.setup.cfg target then
        (lookupPJF B st).current_justified_checkpoint
      else st.current_justified_checkpoint }

/-- `slots` over `lookupDecode`. -/
def lookupSlots (st : BeaconState Root) (target : Slot) : BeaconState Root :=
  match lookupDecode B st with
  | some state =>
    if compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch then
      match process_slots B.setup.cfg B.setup.preset state target with
      | .ok next => B.project next
      | .error _ => lookupFallbackSlots B st target
    else lookupFallbackSlots B st target
  | none => lookupFallbackSlots B st target

/-- `MessageMatches` with the sort-free indexed projection. -/
def lookupMatches (message : BeaconBlock Root) (wire : FFGWireBlock Root) : Prop :=
  message.slot = wire.slot ∧ message.parent_root = wire.parent_root ∧
    message.proposer_index = wire.proposer_index ∧
    message.parent_block_hash = wire.parent_block_hash ∧
    message.block_hash = wire.block_hash ∧
    message.attestations = wire.attestations.map (indexedList B.setup.schedule) ∧
    message.payload_attestations.length = wire.payload_attestation_count

instance (message : BeaconBlock Root) (wire : FFGWireBlock Root) :
    Decidable (lookupMatches B message wire) := by
  unfold lookupMatches
  infer_instance

/-- `transition` over `lookupDecode` and the pointwise concrete transition. -/
def lookupTransition (st : BeaconState Root) (sb : SignedBeaconBlock Root) :
    Option (BeaconState Root) :=
  match lookupDecode B st, B.blocks.open_ sb.root with
  | some state, some (wire, stateRoot) =>
    if wire.root = sb.root ∧ lookupMatches B sb.message wire then
      match state_transition_pointwise B.setup.cfg B.setup.preset B.setup.schedule
          B.setup.oracle state wire with
      | .ok post =>
        if B.states.open_ stateRoot = some post ∧
            compute_epoch_at_slot B.setup.cfg post.slot ≤ B.setup.scope.last_epoch then
          some (B.project post)
        else none
      | .error _ => none
    else none
  | _, _ => none

/-- The computable copy of `B.interface`. -/
def lookupInterface : BeaconFunctionInterface Root :=
  { fixed_schedule_compatibility_bundle B.setup.preset B.setup.schedule B.base with
    process_slots := lookupSlots B
    state_transition := lookupTransition B
    process_justification_and_finalization := lookupPJF B
    AnchorCommitsToState := fun block state =>
      block.slot = 0 ∧ state = B.project B.setup.genesis }

omit [Inhabited Root] in
theorem decode_eq_lookupDecode
    (hdomain : ∀ id state, B.states.open_ id = some state → B.InDomain state) :
    B.decode = lookupDecode B := by
  funext st
  unfold ConcreteBridge.decode lookupDecode
  cases st.source_identity with
  | none => rfl
  | some id =>
    dsimp only
    cases hopen : B.states.open_ id with
    | none => rfl
    | some state =>
      dsimp only
      by_cases hp : B.project state = st
      · simp [hp, hdomain id state hopen]
      · simp [hp]

omit [Inhabited Root] in
/-- **The lookup interface is the bridge interface** when every table state is
in the decode domain. -/
theorem interface_eq_lookupInterface
    (hdomain : ∀ id state, B.states.open_ id = some state → B.InDomain state) :
    B.interface = lookupInterface B := by
  have hdecode := decode_eq_lookupDecode B hdomain
  have hpjf : B.pjf = lookupPJF B := by
    funext st
    unfold ConcreteBridge.pjf lookupPJF
    rw [hdecode]
    rfl
  have hslots : B.slots = lookupSlots B := by
    funext st target
    unfold ConcreteBridge.slots lookupSlots ConcreteBridge.fallbackSlots lookupFallbackSlots
    rw [hdecode, hpjf]
    rfl
  have hmatch : ∀ message wire, B.MessageMatches message wire ↔ lookupMatches B message wire := by
    intro message wire
    unfold ConcreteBridge.MessageMatches lookupMatches
    have hmap : wire.attestations.map B.indexed =
        wire.attestations.map (indexedList B.setup.schedule) := by
      apply List.map_congr_left
      intro vote _
      exact indexed_eq_indexedList B vote
    rw [hmap]
  have htransition : B.transition = lookupTransition B := by
    funext st sb
    unfold ConcreteBridge.transition lookupTransition
    rw [hdecode]
    cases lookupDecode B st with
    | none => rfl
    | some state =>
      cases B.blocks.open_ sb.root with
      | none => rfl
      | some entry =>
        obtain ⟨wire, stateRoot⟩ := entry
        dsimp only
        rw [state_transition_eq_pointwise]
        by_cases hc : wire.root = sb.root ∧ lookupMatches B sb.message wire
        · have hc' : wire.root = sb.root ∧ B.MessageMatches sb.message wire :=
            ⟨hc.1, (hmatch _ _).mpr hc.2⟩
          rw [if_pos hc, if_pos hc']
          cases state_transition_pointwise B.setup.cfg B.setup.preset B.setup.schedule
              B.setup.oracle state wire with
          | error => rfl
          | ok post =>
            dsimp only
            by_cases hp : B.states.open_ stateRoot = some post ∧
                compute_epoch_at_slot B.setup.cfg post.slot ≤ B.setup.scope.last_epoch
            · rw [if_pos hp, if_pos hp]
            · rw [if_neg hp, if_neg hp]
        · have hc' : ¬ (wire.root = sb.root ∧ B.MessageMatches sb.message wire) := by
            rintro ⟨h1, h2⟩
            exact hc ⟨h1, (hmatch _ _).mp h2⟩
          rw [if_neg hc, if_neg hc']
  unfold ConcreteBridge.interface lookupInterface
  rw [hpjf, hslots, htransition]

end Lookup

end FastConfirmation.Spec.ConcreteFFG

end
