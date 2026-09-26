module
public import FastConfirmationProofs.FFG.Concrete.SlotRuns
public import FastConfirmationInternal.FFG.ConcreteBridge
public import FastConfirmationStatements.Premises.FFG

@[expose] public section

/-! Proves the Phase0 source laws `Phase0BoundarySourceCoherence` and
`Phase0SourceCoherence` for the concrete bridge interface `ConcreteBridge.ext`.
On decoded states the laws are the concrete slot-run results of `SlotRuns`:
one boundary gives the eager PJF checkpoint, two or more boundaries from an
epoch of at least two give it again, and same-epoch slot or block processing
keeps the checkpoint. Outside the decode domain the junk values satisfy the
laws by construction. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

omit [DecidableEq Root] in
@[simp] theorem project_slot (cs : FFGBeaconState Root) : (B.project cs).slot = cs.slot := rfl

omit [DecidableEq Root] in
@[simp] theorem project_current_justified (cs : FFGBeaconState Root) :
    (B.project cs).current_justified_checkpoint = cs.current_justified_checkpoint := rfl

omit [DecidableEq Root] in
@[simp] theorem project_finalized (cs : FFGBeaconState Root) :
    (B.project cs).finalized_checkpoint = cs.finalized_checkpoint := rfl

omit [DecidableEq Root] in
@[simp] theorem project_validators (cs : FFGBeaconState Root) :
    (B.project cs).validators = cs.validators := rfl

/-- A reduced state decodes exactly to the admitted concrete state that it
projects. -/
theorem decode_eq_some {st : BeaconState Root} {cs : FFGBeaconState Root} :
    B.decode st = some cs ↔ st = B.project cs ∧ B.Admits cs := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · cases h
    · split at h
      · cases h
      · split_ifs at h with hc
        cases h
        exact ⟨hc.1.symm, hc.2⟩
  · rintro ⟨rfl, hadm⟩
    unfold decode
    simp only [project, B.states.open_root]
    rw [if_pos ⟨rfl, hadm⟩]

theorem decode_project {cs : FFGBeaconState Root} (h : B.Admits cs) :
    B.decode (B.project cs) = some cs :=
  (B.decode_eq_some).mpr ⟨rfl, h⟩

omit [DecidableEq Root] in
theorem epoch_lt_slot_lt {cfg : Config} {x y : Slot}
    (h : compute_epoch_at_slot cfg x < compute_epoch_at_slot cfg y) : x < y := by
  by_contra hxy
  have := compute_epoch_at_slot_mono (cfg := cfg) (Nat.le_of_not_lt hxy)
  beacon_omega

/-! ### The three state methods on decoded states -/

theorem pjf_decoded (hB : B.Admissible) {st : BeaconState Root} {cs : FFGBeaconState Root}
    (hd : B.decode st = some cs) {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} (hreach : Reachable B.setup blocks votes cs) :
    ∃ Y, process_justification_and_finalization B.setup.cfg B.setup.preset cs = .ok Y ∧
      B.pjf st = B.project Y ∧
      Y.current_justified_checkpoint =
        cjFormula B.setup blocks votes (compute_epoch_at_slot B.setup.cfg cs.slot)
          cs.current_justified_checkpoint := by
  have hH := ((B.decode_eq_some).mp hd).2.2
  obtain ⟨Y, hY, hcj⟩ := eager_pjf hB.setup hB.numeric
    (provenanceInvariant_of_reachable hB.setup hreach hH) (lengthsOK_of_reachable hreach) hH
  refine ⟨Y, hY, ?_, hcj⟩
  unfold pjf
  rw [hd]
  dsimp only
  rw [hY]

theorem pjf_none {st : BeaconState Root} (hd : B.decode st = none) :
    B.pjf st = fallbackPJF B.setup.cfg st := by
  unfold pjf
  rw [hd]

theorem slots_decoded (hB : B.Admissible) {st : BeaconState Root} {cs : FFGBeaconState Root}
    (hd : B.decode st = some cs) {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} (hreach : Reachable B.setup blocks votes cs)
    {target : Slot} (hlt : cs.slot < target)
    (hin : compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch) :
    ∃ next, process_slots B.setup.cfg B.setup.preset cs target = .ok next ∧
      B.slots st target = B.project next ∧
      next.current_justified_checkpoint =
        cjRun B.setup blocks votes (compute_epoch_at_slot B.setup.cfg cs.slot)
          (compute_epoch_at_slot B.setup.cfg target -
            compute_epoch_at_slot B.setup.cfg cs.slot) cs.current_justified_checkpoint := by
  have hH := ((B.decode_eq_some).mp hd).2.2
  obtain ⟨next, hnext, -, -, hcj⟩ := process_slots_ok hB.setup hB.numeric
    (provenanceInvariant_of_reachable hB.setup hreach hH) (lengthsOK_of_reachable hreach)
    hlt hin
  refine ⟨next, hnext, ?_, hcj⟩
  unfold slots
  rw [hd]
  dsimp only
  rw [if_pos hin, hnext]

theorem slots_out {st : BeaconState Root} {cs : FFGBeaconState Root}
    (hd : B.decode st = some cs) {target : Slot}
    (hout : ¬ compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch) :
    B.slots st target = B.fallbackSlots st target := by
  unfold slots
  rw [hd]
  dsimp only
  rw [if_neg hout]

theorem slots_none {st : BeaconState Root} (hd : B.decode st = none) (target : Slot) :
    B.slots st target = B.fallbackSlots st target := by
  unfold slots
  rw [hd]

/-- A successful bridge transition: the decoded pre-state, the opened wire
block, and the successful concrete transition within the fixed scope. -/
theorem transition_eq_some {st post : BeaconState Root} {sb : SignedBeaconBlock Root}
    (h : B.transition st sb = some post) :
    ∃ cs wire stateRoot cpost, B.decode st = some cs ∧
      B.blocks.open_ sb.root = some (wire, stateRoot) ∧ wire.root = sb.root ∧
      B.MessageMatches sb.message wire ∧
      state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cs wire =
        .ok cpost ∧
      B.states.root cpost = stateRoot ∧
      compute_epoch_at_slot B.setup.cfg cpost.slot ≤ B.setup.scope.last_epoch ∧
      post = B.project cpost := by
  unfold transition at h
  split at h
  · rename_i cs wire stateRoot hd ho
    split_ifs at h with hc
    split at h
    · rename_i cpost hst
      split_ifs at h with hc2
      cases h
      exact ⟨cs, wire, stateRoot, cpost, hd, ho, hc.1, hc.2, hst, hc2.1, hc2.2, rfl⟩
    · cases h
  · cases h

/-- The slots result that a successful bridge transition runs. -/
theorem transition_slots {st post : BeaconState Root} {sb : SignedBeaconBlock Root}
    (h : B.transition st sb = some post) :
    ∃ cs atSlot, B.decode st = some cs ∧
      process_slots B.setup.cfg B.setup.preset cs sb.message.slot = .ok atSlot ∧
      B.slots st sb.message.slot = B.project atSlot ∧
      post.current_justified_checkpoint = atSlot.current_justified_checkpoint ∧
      post.slot = sb.message.slot := by
  obtain ⟨cs, wire, stateRoot, cpost, hd, -, -, hm, hst, -, hin, rfl⟩ := B.transition_eq_some h
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok hst
  obtain ⟨hpslot, -⟩ := state_transition_slot hst
  have hmslot : sb.message.slot = wire.slot := hm.1
  rw [hmslot]
  refine ⟨cs, atSlot, hd, hslots, ?_, (process_block_checkpoints hblock).2.2.1, hpslot⟩
  unfold slots
  rw [hd]
  dsimp only
  rw [if_pos (by rw [← hpslot]; exact hin), hslots]

/-! ### The Phase0 laws -/

/-- **Phase0 boundary laws of the concrete bridge.** -/
theorem phase0BoundarySourceCoherence (hB : B.Admissible) :
    Phase0BoundarySourceCoherence B.setup.cfg B.ext where
  process_slots_one_boundary := by
    intro st target hlt he
    change (B.slots st target).current_justified_checkpoint =
      (B.pjf st).current_justified_checkpoint
    have hcross : compute_epoch_at_slot B.setup.cfg st.slot <
        compute_epoch_at_slot B.setup.cfg target := by beacon_omega
    cases hd : B.decode st with
    | none => rw [B.slots_none hd]; simp [fallbackSlots, hcross]
    | some cs =>
      obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
      simp only [project_slot] at hcross hlt he
      by_cases hin : compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch
      · obtain ⟨next, -, hs, hcj⟩ := B.slots_decoded hB hd hreach hlt hin
        obtain ⟨Y, -, hp, hY⟩ := B.pjf_decoded hB hd hreach
        rw [hs, hp, project_current_justified, project_current_justified, hcj, hY]
        rw [he, show compute_epoch_at_slot B.setup.cfg cs.slot + 1 -
          compute_epoch_at_slot B.setup.cfg cs.slot = 1 by beacon_omega]
        rfl
      · rw [B.slots_out hd hin]; simp [fallbackSlots, hcross]
  process_slots_same_target_epoch := by
    intro st target target' hlt he
    change (B.slots st target).current_justified_checkpoint =
      (B.slots st target').current_justified_checkpoint
    have hlt' : compute_epoch_at_slot B.setup.cfg st.slot <
        compute_epoch_at_slot B.setup.cfg target' := he ▸ hlt
    cases hd : B.decode st with
    | none => rw [B.slots_none hd, B.slots_none hd]; simp [fallbackSlots, hlt, hlt']
    | some cs =>
      obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
      simp only [project_slot] at hlt hlt'
      by_cases hin : compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch
      · obtain ⟨next, -, hs, hcj⟩ :=
          B.slots_decoded hB hd hreach (epoch_lt_slot_lt hlt) hin
        obtain ⟨next', -, hs', hcj'⟩ :=
          B.slots_decoded hB hd hreach (epoch_lt_slot_lt hlt') (he ▸ hin)
        rw [hs, hs', project_current_justified, project_current_justified, hcj, hcj', he]
      · rw [B.slots_out hd hin, B.slots_out hd (he ▸ hin)]
        simp [fallbackSlots, hlt, hlt']
  state_transition_process_slots := by
    intro pre sb post h _
    obtain ⟨cs, atSlot, -, -, hs, hcj, -⟩ := B.transition_slots h
    change post.current_justified_checkpoint =
      (B.slots pre sb.message.slot).current_justified_checkpoint
    rw [hs, project_current_justified, hcj]
  process_slots_checkpoint_epoch := by
    intro st target hlt _
    change (B.slots st target).current_justified_checkpoint = st.current_justified_checkpoint ∨
      (B.slots st target).current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot B.setup.cfg st.slot
    cases hd : B.decode st with
    | none =>
      rw [B.slots_none hd]
      simp only [fallbackSlots, if_pos hlt, B.pjf_none hd, fallbackPJF]
      split_ifs with hle
      · exact Or.inl rfl
      · exact Or.inr (by simp [GENESIS_EPOCH])
    | some cs =>
      obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
      have hinv := provenanceInvariant_of_reachable hB.setup hreach hH
      simp only [project_slot, project_current_justified] at hlt ⊢
      by_cases hin : compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch
      · obtain ⟨next, -, hs, hcj⟩ := B.slots_decoded hB hd hreach (epoch_lt_slot_lt hlt) hin
        rw [hs, project_current_justified, hcj]
        exact cjRun_epoch_le hB.setup hinv.target_epoch_le _ _
      · rw [B.slots_out hd hin]
        obtain ⟨Y, -, hp, hY⟩ := B.pjf_decoded hB hd hreach
        simp only [fallbackSlots, project_slot, if_pos hlt, hp, project_current_justified,
          project_current_justified, hY]
        exact cjRun_epoch_le hB.setup hinv.target_epoch_le 1 _
  process_slots_two_boundaries := by
    intro st target hE hge _
    change (B.slots st target).current_justified_checkpoint =
      (B.pjf st).current_justified_checkpoint
    have hcross : compute_epoch_at_slot B.setup.cfg st.slot <
        compute_epoch_at_slot B.setup.cfg target := by beacon_omega
    cases hd : B.decode st with
    | none => rw [B.slots_none hd]; simp [fallbackSlots, hcross]
    | some cs =>
      obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
      have hinv := provenanceInvariant_of_reachable hB.setup hreach hH
      simp only [project_slot, GENESIS_EPOCH] at hcross hE hge
      by_cases hin : compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch
      · obtain ⟨next, -, hs, hcj⟩ := B.slots_decoded hB hd hreach (epoch_lt_slot_lt hcross) hin
        obtain ⟨Y, -, hp, hY⟩ := B.pjf_decoded hB hd hreach
        rw [hs, hp, project_current_justified, project_current_justified, hcj, hY]
        exact cjRun_two_boundaries hB.setup hinv.target_epoch_le
          (by beacon_omega) (by beacon_omega) _
      · rw [B.slots_out hd hin]; simp [fallbackSlots, hcross]

/-- **Phase0 same-epoch laws of the concrete bridge.** -/
theorem phase0SourceCoherence (hB : B.Admissible) :
    Phase0SourceCoherence B.setup.cfg B.ext where
  process_slots_current_justified := by
    intro st target hlt he
    change (B.slots st target).current_justified_checkpoint = st.current_justified_checkpoint
    cases hd : B.decode st with
    | none => rw [B.slots_none hd]; simp [fallbackSlots, he]
    | some cs =>
      obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
      simp only [project_slot, project_current_justified] at hlt he ⊢
      obtain ⟨next, -, hs, hcj⟩ := B.slots_decoded hB hd hreach hlt (he ▸ hH)
      rw [hs, project_current_justified, hcj, he, Nat.sub_self]
      rfl
  state_transition_current_justified := by
    intro pre sb post h he
    obtain ⟨cs, atSlot, hd, hslots, -, hcj, -⟩ := B.transition_slots h
    obtain ⟨rfl, ⟨blocks, votes, hreach⟩, hH⟩ := (B.decode_eq_some).mp hd
    simp only [project_slot] at he
    obtain ⟨hatslot, hlt⟩ := process_slots_slot hslots
    obtain ⟨next, hnext, -, -, hcj'⟩ := process_slots_ok hB.setup hB.numeric
      (provenanceInvariant_of_reachable hB.setup hreach hH) (lengthsOK_of_reachable hreach)
      hlt (he ▸ hH)
    rw [hslots] at hnext
    cases hnext
    rw [hcj, hcj', he, Nat.sub_self]
    rfl

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
