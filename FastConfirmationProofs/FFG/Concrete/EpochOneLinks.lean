module
public import FastConfirmationProofs.FFG.Concrete.BridgeLaws
public import FastConfirmationProofs.FFG.Concrete.FinalizationSoundness

@[expose] public section

/-! Proves that a concrete run has no target-included vote from a source of
epoch `GENESIS_EPOCH + 1` to a target of epoch `GENESIS_EPOCH + 2`, so no
finalization link `1 -> 2` exists. A target-epoch-2 vote matches the current
justified checkpoint in epoch 2, or the previous justified checkpoint in
epoch 3. PJF returns early at the ends of epochs 0 and 1, and the end of
epoch 2 copies the current justified checkpoint (epoch 0) to the previous
one, so both checkpoints have epoch 0. With `EpochOneFinalizationScope`, no
accepted block state of a reachable in-scope run finalizes epoch 1
(`ConcreteBridge.epochOneFinalizationScope_finalized_ne_one`). -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### The justified checkpoints of the early epochs -/

/-- The current justified checkpoint has epoch 0 up to epoch 2, and the
previous justified checkpoint has epoch 0 up to epoch 3. -/
def EarlyCheckpoints (cfg : Config) (state : FFGBeaconState Root) : Prop :=
  (compute_epoch_at_slot cfg state.slot ≤ 2 → state.current_justified_checkpoint.epoch = 0) ∧
    (compute_epoch_at_slot cfg state.slot ≤ 3 → state.previous_justified_checkpoint.epoch = 0)

omit [DecidableEq Root] in
theorem earlyCheckpoints_slotStep {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} (h : slotStep cfg preset state = .ok next)
    (hI : EarlyCheckpoints cfg state) : EarlyCheckpoints cfg next := by
  obtain ⟨s1, hs1, hcase⟩ := slotStep_eq_ok h
  obtain ⟨-, -, rfl⟩ := process_slot_eq_ok.mp hs1
  obtain ⟨hc, hp⟩ := hI
  rcases hcase with ⟨hb, rfl⟩ | ⟨hb, mid, hmid, rfl⟩
  · have he := epoch_succ_of_not_boundary (cfg := cfg) hb
    refine ⟨fun h2 => hc ?_, fun h3 => hp ?_⟩
    · change compute_epoch_at_slot cfg (state.slot + 1) ≤ 2 at h2
      rw [he] at h2
      exact h2
    · change compute_epoch_at_slot cfg (state.slot + 1) ≤ 3 at h3
      rw [he] at h3
      exact h3
  · have he := epoch_succ_of_boundary (cfg := cfg) hb
    obtain ⟨bits, pj, j, f, rfl, hout⟩ := process_justification_and_finalization_outcome hmid
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · change compute_epoch_at_slot cfg (state.slot + 1) ≤ 2 at h2
      rw [he] at h2
      change j.epoch = 0
      rcases hout with ⟨-, -, hj, -⟩ | ⟨hE, -⟩
      · rw [hj]
        exact hc (by beacon_omega)
      · change 2 ≤ compute_epoch_at_slot cfg state.slot at hE
        beacon_omega
    · change compute_epoch_at_slot cfg (state.slot + 1) ≤ 3 at h3
      rw [he] at h3
      change pj.epoch = 0
      rcases hout with ⟨-, hpj, -, -⟩ | ⟨-, hpj, -⟩
      · rw [hpj]
        exact hp (by beacon_omega)
      · rw [hpj]
        exact hc (by beacon_omega)

omit [DecidableEq Root] in
theorem earlyCheckpoints_slotFold {cfg : Config} {preset : FFGPreset} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root),
      steps.foldlM (fun s _ => slotStep cfg preset s) state = .ok next →
      EarlyCheckpoints cfg state → EarlyCheckpoints cfg next := by
  intro steps
  induction steps with
  | nil =>
    intro state next h hI
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact hI
  | cons _ steps ih =>
    intro state next h hI
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    exact ih mid next hrest (earlyCheckpoints_slotStep hmid hI)

omit [DecidableEq Root] in
theorem earlyCheckpoints_process_slots {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {target : Slot}
    (h : process_slots cfg preset state target = .ok next)
    (hI : EarlyCheckpoints cfg state) : EarlyCheckpoints cfg next := by
  obtain ⟨-, -, hfold⟩ := process_slots_eq_ok.mp h
  exact earlyCheckpoints_slotFold _ _ _ hfold hI

/-- Every reachable state has the early checkpoints. -/
theorem earlyCheckpoints_of_reachable {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state) :
    EarlyCheckpoints S.cfg state := by
  induction h with
  | genesis => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | slots _ hslots ih => exact earlyCheckpoints_process_slots hslots ih
  | block _ _ htrans ih =>
    obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok htrans
    obtain ⟨hc, hp⟩ := earlyCheckpoints_process_slots hslots ih
    obtain ⟨-, hpj, hcj, -⟩ := process_block_checkpoints hblock
    unfold EarlyCheckpoints
    rw [process_block_slot hblock, hpj, hcj]
    exact ⟨hc, hp⟩

/-! ### Body votes of a block -/

/-- A vote of an ordered body fold ran on a state with the checkpoints and
slot of the fold start, and its target epoch is the current or the previous
epoch of that state. -/
theorem attestationVotes_pre {S : FFGSetup Root} {block : FFGWireBlock Root}
    {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state : FFGBeaconState Root)
      (r : IncludedVote Root), r ∈ attestationVotes S block parentSlot state attestations →
      r.pre.current_justified_checkpoint = state.current_justified_checkpoint ∧
        r.pre.previous_justified_checkpoint = state.previous_justified_checkpoint ∧
        r.pre.slot = state.slot ∧
        (r.vote.data.target.epoch = compute_epoch_at_slot S.cfg r.pre.slot ∨
          r.vote.data.target.epoch = compute_epoch_at_slot S.cfg r.pre.slot - 1) := by
  intro attestations
  induction attestations with
  | nil => intro state r h; simp [attestationVotes] at h
  | cons vote attestations ih =>
    intro state r h
    unfold attestationVotes at h
    split at h
    · rename_i next hnext
      obtain ⟨flags, current, previous, -, htarget, hnexteq, -, -⟩ :=
        process_attestation_flags hnext
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨rfl, rfl, rfl, htarget⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih next r h
        rw [hnexteq] at h1 h2 h3
        exact ⟨h1, h2, h3, h4⟩
    · simp at h

/-- A body vote of an accepted block ran on a state with the checkpoints and
slot of the slot-processed parent state. -/
theorem blockVotes_pre {S : FFGSetup Root} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root}
    (h : state_transition S.cfg S.preset S.schedule S.oracle state block = .ok next)
    {r : IncludedVote Root} (hr : r ∈ blockVotes S state block) :
    ∃ atSlot, process_slots S.cfg S.preset state block.slot = .ok atSlot ∧
      r.pre.current_justified_checkpoint = atSlot.current_justified_checkpoint ∧
      r.pre.previous_justified_checkpoint = atSlot.previous_justified_checkpoint ∧
      r.pre.slot = atSlot.slot ∧
      (r.vote.data.target.epoch = compute_epoch_at_slot S.cfg r.pre.slot ∨
        r.vote.data.target.epoch = compute_epoch_at_slot S.cfg r.pre.slot - 1) := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  obtain ⟨paid, headed, hpaid, hheaded, -⟩ := process_block_eq_ok hblock
  rw [blockVotes_eq hslots hpaid hheaded] at hr
  obtain ⟨h1, h2, h3, h4⟩ := attestationVotes_pre _ _ r hr
  obtain ⟨_, _, rfl⟩ := process_parent_execution_payload_eq_ok hpaid
  obtain ⟨-, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  exact ⟨atSlot, hslots, h1, h2, h3, h4⟩

/-! ### No link from epoch 1 to epoch 2 -/

/-- **Target-epoch-2 sources.** Every target-included vote of a reachable run
with target epoch `GENESIS_EPOCH + 2` has a source of epoch `GENESIS_EPOCH`. -/
theorem targetIncluded_epoch_two_source {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state) :
    ∀ r, TargetIncluded S votes r → r.vote.data.target.epoch = GENESIS_EPOCH + 2 →
      r.vote.data.source.epoch = GENESIS_EPOCH := by
  induction h with
  | genesis => intro r hr; exact absurd hr.1 (by simp)
  | slots _ _ ih => exact ih
  | @block blocks votes state next blk hreach htrans ih =>
    intro r hr htarget
    obtain ⟨hmem, flags, hflags, htimely⟩ := hr
    rcases List.mem_append.mp hmem with hold | hnew
    · exact ih r ⟨hold, flags, hflags, htimely⟩ htarget
    · obtain ⟨atSlot, hslots, hcj, hpj, hslot, htgt⟩ := blockVotes_pre htrans hnew
      obtain ⟨hc, hp⟩ :=
        earlyCheckpoints_of_reachable (Reachable.slots hreach hslots)
      obtain ⟨hsrc, -, -⟩ := get_attestation_participation_flag_indices_eq_ok hflags
      simp only [GENESIS_EPOCH] at htarget ⊢
      rw [hsrc]
      rw [← hslot] at hc hp
      split_ifs with hcur
      · rw [hcj]
        exact hc (by rw [← hcur, htarget])
      · rw [hpj]
        rcases htgt with h' | h'
        · exact absurd h' hcur
        · exact hp (by beacon_omega)

/-- **No `1 -> 2` link.** A reachable run of an admissible setup has no
supermajority link from a checkpoint of epoch `GENESIS_EPOCH + 1` to a
checkpoint of epoch `GENESIS_EPOCH + 2`. -/
theorem no_link_epoch_one_to_two {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    {source target : Checkpoint Root} (hs : source.epoch = GENESIS_EPOCH + 1)
    (ht : target.epoch = GENESIS_EPOCH + 2) :
    IsEmpty (SupermajorityLink S votes source target) := by
  refine ⟨fun L => ?_⟩
  have hinc := S.cfg.effective_balance_increment_pos
  have hfloor := hS.balance_floor
  have hne : L.signers.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsm := L.supermajority
    have hzero : S.scope.weight ∅ = 0 := by simp [FixedFFGScope.weight]
    rw [hempty, hzero] at hsm
    beacon_omega
  obtain ⟨i, hi⟩ := hne
  obtain ⟨r, hr, -, hsrc, htgt⟩ := L.signer_vote i hi
  have := targetIncluded_epoch_two_source h r hr (by rw [htgt, ht])
  rw [hsrc, hs] at this
  simp [GENESIS_EPOCH] at this

/-- No finalization link from a checkpoint of epoch `GENESIS_EPOCH + 1` to a
target of epoch `GENESIS_EPOCH + 2` exists in a reachable run. -/
theorem no_finalizationLink_epoch_one_to_two {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    {finalized target : Checkpoint Root} (hf : finalized.epoch = GENESIS_EPOCH + 1)
    (ht : target.epoch = GENESIS_EPOCH + 2) :
    ¬ FinalizationLink S blocks votes finalized target := fun hl =>
  let ⟨L⟩ := hl.link
  (no_link_epoch_one_to_two hS h hf ht).false L

end FastConfirmation.Spec.ConcreteFFG

namespace FastConfirmation.Spec.ConcreteFFG.ConcreteBridge
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

/-- **Content of the epoch-1 scope.** Under `EpochOneFinalizationScope`, the
committed state of an accepted root in a reachable run does not finalize
epoch `GENESIS_EPOCH + 1`: the field admits that finality only through a
`1 -> 2` finalization link, and no such link exists. -/
theorem epochOneFinalizationScope_finalized_ne_one (B : ConcreteBridge Root)
    (hB : B.Admissible) {E : Execution Root} (hscope : B.EpochOneFinalizationScope E)
    {r : Root} (hr : E.RootKnownInScheduledPrefix B.setup.cfg B.interface r)
    {cs : FFGBeaconState Root} (hcs : B.committedState r = some cs)
    {bl : List (FFGWireBlock Root)} {vo : List (IncludedVote Root)}
    (hreach : Reachable B.setup bl vo cs) :
    cs.finalized_checkpoint.epoch ≠ GENESIS_EPOCH + 1 := by
  intro hf
  obtain ⟨target, hl, ht⟩ := (hscope r cs hr hcs bl vo hreach).1 hf
  exact no_finalizationLink_epoch_one_to_two hB.setup hreach hf ht hl

end FastConfirmation.Spec.ConcreteFFG.ConcreteBridge

end
