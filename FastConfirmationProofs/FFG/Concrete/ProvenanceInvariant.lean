module
public import FastConfirmationProofs.FFG.Concrete.ChainHistory

@[expose] public section

/-! Proves that every in-horizon reachable concrete FFG state satisfies
`ProvenanceInvariant`: its history, its participation-flag provenance, and the
supermajority-link justification of its checkpoints. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### Certificates grow with the vote list -/

/-- A link stays valid when more votes are recorded. -/
def SupermajorityLink.mono {S : FFGSetup Root} {votes votes' : List (IncludedVote Root)}
    {source target : Checkpoint Root} (h : ∀ r, r ∈ votes → r ∈ votes')
    (link : SupermajorityLink S votes source target) :
    SupermajorityLink S votes' source target where
  signers := link.signers
  source_before_target := link.source_before_target
  signer_vote := fun i hi => by
    obtain ⟨r, ⟨hr, hflags⟩, hrest⟩ := link.signer_vote i hi
    exact ⟨r, ⟨h r hr, hflags⟩, hrest⟩
  signer_active := link.signer_active
  signer_unslashed := link.signer_unslashed
  supermajority := link.supermajority

theorem Justified.mono {S : FFGSetup Root} {votes votes' : List (IncludedVote Root)}
    {c : Checkpoint Root} (h : ∀ r, r ∈ votes → r ∈ votes') (hj : Justified S votes c) :
    Justified S votes' c := by
  induction hj with
  | anchor => exact .anchor
  | link _ l ih => exact .link ih (l.mono h)

theorem targetIncluded_append_singleton {S : FFGSetup Root} {votes : List (IncludedVote Root)}
    {r r' : IncludedVote Root} :
    TargetIncluded S (votes ++ [r]) r' ↔ TargetIncluded S votes r' ∨
      (r' = r ∧ ∃ flags, r.flags S = .ok flags ∧ timelyTargetFlagIndex ∈ flags) := by
  unfold TargetIncluded
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hr | rfl, hf⟩
    · exact Or.inl ⟨hr, hf⟩
    · exact Or.inr ⟨rfl, hf⟩
  · rintro (⟨hr, hf⟩ | ⟨rfl, hf⟩)
    · exact ⟨Or.inl hr, hf⟩
    · exact ⟨Or.inr rfl, hf⟩

theorem checkpoint_eq_of {a b : Checkpoint Root} (h1 : a.epoch = b.epoch)
    (h2 : a.root = b.root) : a = b := by
  cases a; cases b; simp_all

/-! ### Attestation step -/

/-- The participation effect of one successful attestation call, in terms of
the timely-target bit. -/
theorem process_attestation_flags {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {vote : FFGWireAttestation Root} {parentSlot : Slot}
    (h : process_attestation cfg preset schedule state vote parentSlot = .ok next) :
    ∃ flags current previous,
      get_attestation_participation_flag_indices cfg preset state vote.data
        (state.slot - vote.data.slot) parentSlot = .ok flags ∧
      (vote.data.target.epoch = compute_epoch_at_slot cfg state.slot ∨
        vote.data.target.epoch = compute_epoch_at_slot cfg state.slot - 1) ∧
      next = { state with
        current_epoch_participation := current
        previous_epoch_participation := previous } ∧
      (∀ i, has_flag (current.getD i 0) 1 = true ↔
        has_flag (state.current_epoch_participation.getD i 0) 1 = true ∨
          (vote.data.target.epoch = compute_epoch_at_slot cfg state.slot ∧
            i ∈ get_attesting_indices schedule vote ∧ 1 ∈ flags)) ∧
      (∀ i, has_flag (previous.getD i 0) 1 = true ↔
        has_flag (state.previous_epoch_participation.getD i 0) 1 = true ∨
          (vote.data.target.epoch ≠ compute_epoch_at_slot cfg state.slot ∧
            i ∈ get_attesting_indices schedule vote ∧ 1 ∈ flags)) := by
  obtain ⟨flags, hflags, htarget, hatt, hcur, hprev⟩ := process_attestation_eq_ok h
  obtain ⟨-, hle, -⟩ := get_attestation_participation_flag_indices_eq_ok hflags
  have hupdate : ∀ (participation : List ℕ),
      participation.length = state.validators.length → ∀ i,
      has_flag ((participationUpdate flags ((get_attesting_indices schedule vote).sort (· ≤ ·))
        participation).getD i 0) 1 = true ↔
        has_flag (participation.getD i 0) 1 = true ∨
          (i ∈ get_attesting_indices schedule vote ∧ 1 ∈ flags) := by
    intro participation hlen i
    rw [has_flag_participationUpdate hle, Finset.mem_sort]
    constructor
    · rintro (h | ⟨hi, -, h1⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hi, h1⟩
    · rintro (h | ⟨hi, h1⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hi, by rw [hlen]; exact hatt i hi, h1⟩
  refine ⟨flags, ?_⟩
  by_cases hE : vote.data.target.epoch = compute_epoch_at_slot cfg state.slot
  · obtain ⟨hlen, rfl⟩ := hcur hE
    refine ⟨_, state.previous_epoch_participation, hflags, htarget, rfl, ?_, ?_⟩
    · intro i
      rw [hupdate _ hlen i]
      simp [hE]
    · intro i
      simp [hE]
  · obtain ⟨hlen, rfl⟩ := hprev hE
    refine ⟨state.current_epoch_participation, _, hflags, htarget, rfl, ?_, ?_⟩
    · intro i
      simp [hE]
    · intro i
      rw [hupdate _ hlen i]
      simp [hE]

/-- One successful attestation call keeps the invariant and records its vote. -/
theorem provenanceInvariant_attestation {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    {vote : FFGWireAttestation Root} {parentSlot : Slot}
    (hinv : ProvenanceInvariant S blocks votes state)
    (h : process_attestation S.cfg S.preset S.schedule state vote parentSlot = .ok next) :
    ProvenanceInvariant S blocks (votes ++ [⟨block, vote, state, parentSlot⟩]) next := by
  obtain ⟨flags, current, previous, hflags, htarget, rfl, hcur, hprev⟩ :=
    process_attestation_flags h
  obtain ⟨hsrc, -, htgt⟩ := get_attestation_participation_flag_indices_eq_ok hflags
  set r : IncludedVote Root := ⟨block, vote, state, parentSlot⟩ with hr
  have hTI : ∀ r', TargetIncluded S (votes ++ [r]) r' ↔ TargetIncluded S votes r' ∨
      (r' = r ∧ 1 ∈ flags) := by
    intro r'
    rw [targetIncluded_append_singleton]
    constructor
    · rintro (h | ⟨rfl, fl, hfl, h1⟩)
      · exact Or.inl h
      · have : fl = flags := by
          have e : r.flags S = Except.ok flags := hflags
          rw [e] at hfl
          cases hfl
          rfl
        subst this
        exact Or.inr ⟨rfl, h1⟩
    · rintro (h | ⟨rfl, h1⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, flags, hflags, h1⟩
  have hmem : ∀ r', r' ∈ votes → r' ∈ votes ++ [r] := fun r' h => List.mem_append_left _ h
  have hprevE : get_previous_epoch S.cfg state = compute_epoch_at_slot S.cfg state.slot - 1 :=
    rfl
  refine
    { validators_eq := hinv.validators_eq
      blocks_ordered := hinv.blocks_ordered
      parent_linked := hinv.parent_linked
      header_root := hinv.header_root
      header_slot := hinv.header_slot
      blocks_le_header := hinv.blocks_le_header
      header_le_slot := hinv.header_le_slot
      ring := hinv.ring
      target_epoch_le := ?_
      current_flags := ?_
      previous_flags := ?_
      current_sources := ?_
      previous_sources := ?_
      target_on_chain := ?_
      source_justified := ?_
      early_sources := hinv.early_sources
      current_epoch_le := hinv.current_epoch_le
      previous_epoch_le := hinv.previous_epoch_le
      current_justified := hinv.current_justified.mono hmem
      previous_justified := hinv.previous_justified.mono hmem
      finalized_justified := hinv.finalized_justified.mono hmem }
  · intro r' hr'
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact hinv.target_epoch_le r' hr'
    · rw [List.mem_singleton.mp hr']
      show vote.data.target.epoch ≤ compute_epoch_at_slot S.cfg state.slot
      rcases htarget with h | h <;> beacon_omega
  · intro i
    show _ ↔ ∃ r', TargetIncluded S (votes ++ [r]) r' ∧ i ∈ r'.attesters S ∧
      r'.vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot
    rw [hcur i, hinv.current_flags i]
    constructor
    · rintro (⟨r', h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨r', (hTI r').mpr (Or.inl h1), h2, h3⟩
      · exact ⟨r, (hTI r).mpr (Or.inr ⟨rfl, h3⟩), h2, h1⟩
    · rintro ⟨r', h1, h2, h3⟩
      rcases (hTI r').mp h1 with h4 | ⟨rfl, h5⟩
      · exact Or.inl ⟨r', h4, h2, h3⟩
      · exact Or.inr ⟨h3, h2, h5⟩
  · intro i
    show _ ↔ ∃ r', TargetIncluded S (votes ++ [r]) r' ∧ i ∈ r'.attesters S ∧
      r'.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot
    rw [hprev i, hinv.previous_flags i]
    constructor
    · rintro (⟨r', h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨r', (hTI r').mpr (Or.inl h1), h2, h3⟩
      · refine ⟨r, (hTI r).mpr (Or.inr ⟨rfl, h3⟩), h2, ?_⟩
        show vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot
        rcases htarget with h | h <;> beacon_omega
    · rintro ⟨r', h1, h2, h3⟩
      rcases (hTI r').mp h1 with h4 | ⟨rfl, h5⟩
      · exact Or.inl ⟨r', h4, h2, h3⟩
      · refine Or.inr ⟨?_, h2, h5⟩
        change vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot at h3
        beacon_omega
  · intro r' h1 h2
    rcases (hTI r').mp h1 with h4 | ⟨rfl, -⟩
    · exact hinv.current_sources r' h4 h2
    · change vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot at h2
      show vote.data.source = state.current_justified_checkpoint
      rw [hsrc, if_pos h2]
  · intro r' h1 h2
    rcases (hTI r').mp h1 with h4 | ⟨rfl, -⟩
    · exact hinv.previous_sources r' h4 h2
    · change vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot at h2
      show vote.data.source = state.previous_justified_checkpoint
      rw [hsrc, if_neg (by beacon_omega)]
  · intro r' h1
    rcases (hTI r').mp h1 with h4 | ⟨rfl, h5⟩
    · exact hinv.target_on_chain r' h4
    · have hread := (get_block_root_eq_ok.mp (htgt.mp h5)).2
      obtain ⟨-, hlt, hle, -, hcell⟩ := get_block_root_at_slot_eq_ok.mp hread
      refine ⟨hlt, ?_⟩
      have := hinv.ring _ hlt hle
      rw [hcell] at this
      exact Option.some.inj this
  · intro r' hr'
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact (hinv.source_justified r' hr').mono hmem
    · rw [List.mem_singleton.mp hr']
      show Justified S (votes ++ [r]) vote.data.source
      rw [hsrc]
      split_ifs
      · exact hinv.current_justified.mono hmem
      · exact hinv.previous_justified.mono hmem

/-- The ordered attestation fold keeps the invariant and records every call. -/
theorem provenanceInvariant_attestations {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {block : FFGWireBlock Root} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (votes : List (IncludedVote Root))
      (state next : FFGBeaconState Root),
      ProvenanceInvariant S blocks votes state →
      attestations.foldlM (fun s vote =>
        process_attestation S.cfg S.preset S.schedule s vote parentSlot) state = .ok next →
      ProvenanceInvariant S blocks
        (votes ++ attestationVotes S block parentSlot state attestations) next ∧
      next.slot = state.slot := by
  intro attestations
  induction attestations with
  | nil =>
    intro votes state next hinv h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    simpa [attestationVotes] using hinv
  | cons vote attestations ih =>
    intro votes state next hinv h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    have hinv' := provenanceInvariant_attestation (block := block) hinv hmid
    obtain ⟨hnext, hslot⟩ := ih _ mid next hinv' hrest
    have hvotes : attestationVotes S block parentSlot state (vote :: attestations) =
        ⟨block, vote, state, parentSlot⟩ :: attestationVotes S block parentSlot mid attestations := by
      simp [attestationVotes, hmid]
    refine ⟨?_, ?_⟩
    · rw [hvotes]
      simpa [List.append_assoc] using hnext
    · obtain ⟨_, _, _, _, _, rfl, _, _⟩ := process_attestation_flags hmid
      exact hslot

/-! ### Block header step -/

/-- The parent-payload, header and bid writes append the block to the chain. -/
theorem provenanceInvariant_header {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state paid headed : FFGBeaconState Root} {block : FFGWireBlock Root}
    (hinv : ProvenanceInvariant S blocks votes state)
    (hpaid : process_parent_execution_payload S.preset state block = .ok paid)
    (hheaded : process_block_header paid block = .ok headed) :
    ProvenanceInvariant S (blocks ++ [block]) votes (process_execution_payload_bid headed block) ∧
      block.slot = state.slot ∧ (process_execution_payload_bid headed block).slot = state.slot := by
  obtain ⟨availability, hash, rfl⟩ := process_parent_execution_payload_eq_ok hpaid
  obtain ⟨hslot, hlt, hparent, rfl⟩ := process_block_header_eq_ok hheaded
  refine ⟨?_, hslot, rfl⟩
  refine
    { validators_eq := hinv.validators_eq
      blocks_ordered := ?_
      parent_linked := ?_
      header_root := tipRoot_append.symm
      header_slot := tipSlot_append.symm
      blocks_le_header := ?_
      header_le_slot := ?_
      ring := ?_
      target_epoch_le := hinv.target_epoch_le
      current_flags := hinv.current_flags
      previous_flags := hinv.previous_flags
      current_sources := hinv.current_sources
      previous_sources := hinv.previous_sources
      target_on_chain := ?_
      source_justified := hinv.source_justified
      early_sources := hinv.early_sources
      current_epoch_le := hinv.current_epoch_le
      previous_epoch_le := hinv.previous_epoch_le
      current_justified := hinv.current_justified
      previous_justified := hinv.previous_justified
      finalized_justified := hinv.finalized_justified }
  · refine List.pairwise_append.mpr ⟨hinv.blocks_ordered, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact Nat.lt_of_le_of_lt (hinv.blocks_le_header a ha) hlt
  · exact parentLinked_append.mpr ⟨hinv.parent_linked, hparent.trans hinv.header_root⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hinv.blocks_le_header b hb) hlt)
    · rw [List.mem_singleton.mp hb]
      exact Nat.le_refl _
  · exact Nat.le_of_eq hslot
  · intro y hy hle
    rw [chainRootAt_append_of_lt (by change y < state.slot at hy; beacon_omega)]
    exact hinv.ring y hy hle
  · intro r hr
    obtain ⟨h1, h2⟩ := hinv.target_on_chain r hr
    refine ⟨h1, ?_⟩
    rw [chainRootAt_append_of_lt (by beacon_omega)]
    exact h2

/-! ### Epoch processing facts -/

theorem get_unslashed_participating_indices_mem {cfg : Config} {state : FFGBeaconState Root}
    {flag : ℕ} {epoch : Epoch} {set : Finset ValidatorIndex}
    (h : get_unslashed_participating_indices cfg state flag epoch = .ok set) (i : ℕ) :
    i ∈ set ↔ i < state.validators.length ∧
      is_active_validator (state.validators.getD i default) epoch = true ∧
      has_flag ((if epoch = compute_epoch_at_slot cfg state.slot then
        state.current_epoch_participation else state.previous_epoch_participation).getD i 0)
        flag = true ∧
      (state.validators.getD i default).slashed = false := by
  unfold get_unslashed_participating_indices at h
  simp only [except_bind_eq_ok, except_pure_eq_ok] at h
  obtain ⟨_, -, _, -, rfl⟩ := h
  simp only [List.mem_toFinset, List.mem_filter, ConcreteFFG.get_active_validator_indices,
    List.mem_range, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
  tauto

/-- The outcome of PJF: before epoch 2 it returns the state; afterwards the
previous justified checkpoint takes the old current one, and the new current
and finalized checkpoints are as in `weigh_justification_and_finalization`. -/
theorem process_justification_and_finalization_outcome {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root}
    (h : process_justification_and_finalization cfg preset state = .ok next) :
    ∃ bits pj j f, next = { state with
        justification_bits := bits
        previous_justified_checkpoint := pj
        current_justified_checkpoint := j
        finalized_checkpoint := f } ∧
      ((compute_epoch_at_slot cfg state.slot ≤ 1 ∧ pj = state.previous_justified_checkpoint ∧
          j = state.current_justified_checkpoint ∧ f = state.finalized_checkpoint) ∨
        (2 ≤ compute_epoch_at_slot cfg state.slot ∧ pj = state.current_justified_checkpoint ∧
          (j = state.current_justified_checkpoint ∨
            (∃ set, get_unslashed_participating_indices cfg state 1
                (compute_epoch_at_slot cfg state.slot - 1) = .ok set ∧
              ConcreteFFG.get_total_active_balance cfg state * 2 ≤
                ConcreteFFG.get_total_balance cfg state set * 3 ∧
              j.epoch = compute_epoch_at_slot cfg state.slot - 1 ∧
              get_block_root cfg preset state j.epoch = .ok j.root) ∨
            (∃ set, get_unslashed_participating_indices cfg state 1
                (compute_epoch_at_slot cfg state.slot) = .ok set ∧
              ConcreteFFG.get_total_active_balance cfg state * 2 ≤
                ConcreteFFG.get_total_balance cfg state set * 3 ∧
              j.epoch = compute_epoch_at_slot cfg state.slot ∧
              get_block_root cfg preset state j.epoch = .ok j.root)) ∧
          (f = state.finalized_checkpoint ∨ f = state.previous_justified_checkpoint ∨
            f = state.current_justified_checkpoint))) := by
  rcases process_justification_and_finalization_eq_ok h with ⟨hE, rfl⟩ |
    ⟨hE, previous, current, hp, hc, hw⟩
  · exact ⟨_, _, _, _, rfl, Or.inl ⟨hE, rfl, rfl, rfl⟩⟩
  · obtain ⟨bits, j, f, rfl, hj, hf⟩ := weigh_justification_and_finalization_eq_ok hw
    refine ⟨bits, _, j, f, rfl, Or.inr ⟨hE, rfl, ?_, hf⟩⟩
    rcases hj with hj | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl hj
    · exact Or.inr (Or.inl ⟨previous, hp, h1, h2, h3⟩)
    · exact Or.inr (Or.inr ⟨current, hc, h1, h2, h3⟩)

theorem slotStep_eq_ok {cfg : Config} {preset : FFGPreset} {state next : FFGBeaconState Root}
    (h : slotStep cfg preset state = .ok next) :
    ∃ s1, process_slot preset state = .ok s1 ∧
      ((¬ (state.slot + 1) % cfg.slots_per_epoch = 0 ∧
          next = { s1 with slot := state.slot + 1 }) ∨
        ((state.slot + 1) % cfg.slots_per_epoch = 0 ∧
          ∃ mid, process_justification_and_finalization cfg preset s1 = .ok mid ∧
            next = { process_participation_flag_updates mid with slot := state.slot + 1 })) := by
  unfold slotStep at h
  rw [except_bind_eq_ok] at h
  obtain ⟨s1, hs1, h⟩ := h
  have hslot : s1.slot = state.slot := by
    obtain ⟨-, -, rfl⟩ := process_slot_eq_ok.mp hs1
    rfl
  refine ⟨s1, hs1, ?_⟩
  dsimp only at h
  split at h
  · rename_i hc
    rw [except_bind_eq_ok] at h
    obtain ⟨s2, hs2, h⟩ := h
    rw [except_pure_eq_ok] at h
    subst h
    obtain ⟨mid, hmid, rfl⟩ := process_epoch_eq_ok.mp hs2
    have hb : (state.slot + 1) % cfg.slots_per_epoch = 0 := by
      rw [← hslot]; simpa using hc
    refine Or.inr ⟨hb, mid, hmid, ?_⟩
    obtain ⟨_, _, _, _, rfl, _⟩ := process_justification_and_finalization_outcome hmid
    simp [process_participation_flag_updates, hslot]
  · rename_i hc
    simp only [except_bind_eq_ok, except_pure_eq_ok] at h
    obtain ⟨w, hw, rfl⟩ := h
    cases hw
    have hb : ¬ (state.slot + 1) % cfg.slots_per_epoch = 0 := by
      rw [← hslot]; simpa using hc
    exact Or.inl ⟨hb, by rw [hslot]⟩

theorem epoch_succ_of_not_boundary {cfg : Config} {x : Slot}
    (h : ¬ (x + 1) % cfg.slots_per_epoch = 0) :
    compute_epoch_at_slot cfg (x + 1) = compute_epoch_at_slot cfg x := by
  unfold compute_epoch_at_slot
  rw [Nat.succ_div, if_neg (by rw [Nat.dvd_iff_mod_eq_zero]; exact h), Nat.add_zero]

theorem epoch_succ_of_boundary {cfg : Config} {x : Slot}
    (h : (x + 1) % cfg.slots_per_epoch = 0) :
    compute_epoch_at_slot cfg (x + 1) = compute_epoch_at_slot cfg x + 1 := by
  unfold compute_epoch_at_slot
  rw [Nat.succ_div, if_pos (by rw [Nat.dvd_iff_mod_eq_zero]; exact h)]

theorem boundary_slot_eq {cfg : Config} {x : Slot} (h : (x + 1) % cfg.slots_per_epoch = 0) :
    x + 1 = (compute_epoch_at_slot cfg x + 1) * cfg.slots_per_epoch := by
  rw [← epoch_succ_of_boundary h]
  unfold compute_epoch_at_slot
  exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm

theorem compute_epoch_at_slot_mono {cfg : Config} {x y : Slot} (h : x ≤ y) :
    compute_epoch_at_slot cfg x ≤ compute_epoch_at_slot cfg y :=
  Nat.div_le_div_right h

/-! ### Fixed weights -/

theorem total_active_balance_eq {S : FFGSetup Root} (hS : S.Admissible)
    {state : FFGBeaconState Root} (hval : state.validators = S.scope.validators)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    ConcreteFFG.get_total_active_balance S.cfg state =
      max S.cfg.effective_balance_increment S.scope.activeBalance := by
  unfold ConcreteFFG.get_total_active_balance ConcreteFFG.get_total_balance
    ConcreteFFG.get_active_validator_indices FixedFFGScope.activeBalance
  rw [hval]
  congr 1
  rw [List.sum_toFinset _ ((List.nodup_range).filter _)]
  congr 2
  apply List.filter_congr
  intro i hi
  have hi' : i < S.scope.validators.length := List.mem_range.mp hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  have := S.scope.activity_fixed ⟨i, hi'⟩ (compute_epoch_at_slot S.cfg state.slot)
    (by rw [hS.scope_from_genesis]; exact Nat.zero_le _) hH
  rw [hS.scope_from_genesis] at this ⊢
  exact this

theorem total_balance_eq {S : FFGSetup Root} {state : FFGBeaconState Root}
    (hval : state.validators = S.scope.validators) (set : Finset ValidatorIndex) :
    ConcreteFFG.get_total_balance S.cfg state set =
      max S.cfg.effective_balance_increment (S.scope.weight set) := by
  unfold ConcreteFFG.get_total_balance FixedFFGScope.weight
  rw [hval]

/-- A passing two-thirds test is a real two-thirds weighted quorum when the
active weight is at least two increments. -/
theorem supermajority_of_threshold {inc total weight : ℕ} (hinc : 0 < inc)
    (hfloor : 2 * inc ≤ total) (h : max inc total * 2 ≤ max inc weight * 3) :
    2 * total ≤ 3 * weight := by
  rcases Nat.le_total inc weight with hw | hw
  · rw [max_eq_right hw, max_eq_right (by omega)] at h
    omega
  · rw [max_eq_left hw, max_eq_right (by omega)] at h
    omega

/-! ### Justification by one PJF pass -/

/-- A PJF two-thirds test at the end of an epoch justifies the checkpoint that
PJF reads, by a supermajority link from the state's justified checkpoint of
the target epoch. -/
theorem justified_of_epoch_test {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state s1 : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hE2 : 2 ≤ compute_epoch_at_slot S.cfg state.slot)
    (hbound : (state.slot + 1) % S.cfg.slots_per_epoch = 0)
    (hs1 : process_slot S.preset state = .ok s1) {epoch : Epoch}
    {set : Finset ValidatorIndex} {root : Root}
    (hepoch : epoch = compute_epoch_at_slot S.cfg state.slot ∨
      epoch + 1 = compute_epoch_at_slot S.cfg state.slot)
    (hset : get_unslashed_participating_indices S.cfg s1 1 epoch = .ok set)
    (hth : ConcreteFFG.get_total_active_balance S.cfg s1 * 2 ≤
      ConcreteFFG.get_total_balance S.cfg s1 set * 3)
    (hroot : get_block_root S.cfg S.preset s1 epoch = .ok root) :
    Justified S votes ⟨epoch, root⟩ := by
  obtain ⟨hlen, -, rfl⟩ := process_slot_eq_ok.mp hs1
  set E := compute_epoch_at_slot S.cfg state.slot with hEdef
  set x := state.slot with hxdef
  set N := S.preset.slots_per_historical_root with hNdef
  set spe := S.cfg.slots_per_epoch with hspedef
  have hspe : 0 < spe := S.cfg.slots_per_epoch_pos
  have hring2 : 2 * spe ≤ N := hS.ring_covers_two_epochs
  have hx : x + 1 = (E + 1) * spe := boundary_slot_eq hbound
  have hstart : compute_start_slot_at_epoch S.cfg epoch = epoch * spe := rfl
  have hEspe : (E + 1) * spe = E * spe + spe := Nat.succ_mul E spe
  -- The PJF read is the chain root of the epoch start.
  have hchain : root = chainRootAt S.genesisRoot blocks (epoch * spe) := by
    obtain ⟨-, hread⟩ := get_block_root_eq_ok.mp hroot
    obtain ⟨-, hlt, hle, -, hcell⟩ := get_block_root_at_slot_eq_ok.mp hread
    rw [hstart] at hlt hle hcell
    change epoch * spe < x at hlt
    have hlt' : x < epoch * spe + N := by
      rcases hepoch with h | h
      · rw [h]; beacon_omega
      · rw [← h] at hx
        have : (epoch + 1 + 1) * spe = epoch * spe + 2 * spe := by ring
        beacon_omega
    change (state.block_roots.set (x % N) state.latest_block_header.root)[epoch * spe % N]? =
      some root at hcell
    rw [List.getElem?_set_ne (mod_ne_of_lt_of_lt_add hlt hlt')] at hcell
    rw [hinv.ring _ hlt (by beacon_omega)] at hcell
    exact (Option.some.inj hcell).symm
  have hval : S.scope.validators = state.validators := hinv.validators_eq.symm
  -- The source checkpoint of the tested epoch.
  let source := if epoch = E then state.current_justified_checkpoint
    else state.previous_justified_checkpoint
  have hsource : Justified S votes source := by
    by_cases h : epoch = E
    · simp only [source, if_pos h]; exact hinv.current_justified
    · simp only [source, if_neg h]; exact hinv.previous_justified
  refine .link hsource
    { signers := set
      source_before_target := ?_
      signer_vote := ?_
      signer_active := ?_
      signer_unslashed := ?_
      supermajority := ?_ }
  · have h1 := hinv.current_epoch_le
    have h2 := hinv.previous_epoch_le
    by_cases h : epoch = E
    · simp only [source, if_pos h]
      show state.current_justified_checkpoint.epoch < epoch
      beacon_omega
    · simp only [source, if_neg h]
      show state.previous_justified_checkpoint.epoch < epoch
      rcases hepoch with h' | h'
      · exact absurd h' h
      · beacon_omega
  · intro i hi
    obtain ⟨-, -, hflag, -⟩ := (get_unslashed_participating_indices_mem hset i).mp hi
    by_cases h : epoch = E
    · rw [if_pos h] at hflag
      obtain ⟨r, hr, hri, hre⟩ := (hinv.current_flags i).mp hflag
      refine ⟨r, hr, hri, ?_, ?_⟩
      · simp only [source, if_pos h]; exact hinv.current_sources r hr hre
      · have hre' : r.vote.data.target.epoch = epoch := by rw [hre]; exact h.symm
        refine checkpoint_eq_of hre' ?_
        rw [(hinv.target_on_chain r hr).2, hchain, hre']
        rfl
    · rw [if_neg h] at hflag
      have he : epoch + 1 = E := by
        rcases hepoch with h' | h'
        · exact absurd h' h
        · exact h'
      obtain ⟨r, hr, hri, hre⟩ := (hinv.previous_flags i).mp hflag
      have hre' : r.vote.data.target.epoch = epoch := by beacon_omega
      refine ⟨r, hr, hri, ?_, ?_⟩
      · simp only [source, if_neg h]; exact hinv.previous_sources r hr hre
      · refine checkpoint_eq_of hre' ?_
        rw [(hinv.target_on_chain r hr).2, hchain, hre']
        rfl
  · intro i hi
    obtain ⟨hlt, hact, -, -⟩ := (get_unslashed_participating_indices_mem hset i).mp hi
    change i < state.validators.length at hlt
    change is_active_validator (state.validators.getD i default) epoch = true at hact
    rw [← hval] at hlt hact
    exact ⟨hlt, hact⟩
  · intro i hi
    obtain ⟨-, -, -, hsl⟩ := (get_unslashed_participating_indices_mem hset i).mp hi
    change (state.validators.getD i default).slashed = false at hsl
    rw [← hval] at hsl
    exact hsl
  · change ConcreteFFG.get_total_active_balance S.cfg state * 2 ≤
      ConcreteFFG.get_total_balance S.cfg state set * 3 at hth
    rw [total_active_balance_eq hS (hinv.validators_eq) hH,
      total_balance_eq (hinv.validators_eq) set] at hth
    exact supermajority_of_threshold S.cfg.effective_balance_increment_pos hS.balance_floor hth

/-! ### Slot step -/

/-- Transfer of the invariant to a state with the same epoch, flags,
checkpoints, header and registry, a later slot, and a ring that still holds
the chain roots. -/
theorem ProvenanceInvariant.of_same_epoch {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hval : next.validators = state.validators)
    (hheader : next.latest_block_header = state.latest_block_header)
    (hslot : state.slot ≤ next.slot)
    (hE : compute_epoch_at_slot S.cfg next.slot = compute_epoch_at_slot S.cfg state.slot)
    (hcur : next.current_epoch_participation = state.current_epoch_participation)
    (hprev : next.previous_epoch_participation = state.previous_epoch_participation)
    (hcj : next.current_justified_checkpoint = state.current_justified_checkpoint)
    (hpj : next.previous_justified_checkpoint = state.previous_justified_checkpoint)
    (hfin : next.finalized_checkpoint = state.finalized_checkpoint)
    (hring : ∀ y, y < next.slot → next.slot ≤ y + S.preset.slots_per_historical_root →
      next.block_roots[y % S.preset.slots_per_historical_root]? =
        some (chainRootAt S.genesisRoot blocks y)) :
    ProvenanceInvariant S blocks votes next where
  validators_eq := hval.trans hinv.validators_eq
  blocks_ordered := hinv.blocks_ordered
  parent_linked := hinv.parent_linked
  header_root := by rw [hheader]; exact hinv.header_root
  header_slot := by rw [hheader]; exact hinv.header_slot
  blocks_le_header := by rw [hheader]; exact hinv.blocks_le_header
  header_le_slot := by rw [hheader]; exact Nat.le_trans hinv.header_le_slot hslot
  ring := hring
  target_epoch_le := by rw [hE]; exact hinv.target_epoch_le
  current_flags := by rw [hE, hcur]; exact hinv.current_flags
  previous_flags := by rw [hE, hprev]; exact hinv.previous_flags
  current_sources := by rw [hE, hcj]; exact hinv.current_sources
  previous_sources := by rw [hE, hpj]; exact hinv.previous_sources
  target_on_chain := fun r hr =>
    ⟨Nat.lt_of_lt_of_le (hinv.target_on_chain r hr).1 hslot, (hinv.target_on_chain r hr).2⟩
  source_justified := hinv.source_justified
  early_sources := by rw [hE, hcj, hpj]; exact hinv.early_sources
  current_epoch_le := by rw [hE, hcj]; exact hinv.current_epoch_le
  previous_epoch_le := by rw [hE, hpj]; exact hinv.previous_epoch_le
  current_justified := by rw [hcj]; exact hinv.current_justified
  previous_justified := by rw [hpj]; exact hinv.previous_justified
  finalized_justified := by rw [hfin]; exact hinv.finalized_justified

theorem has_flag_replicate_zero (n i : ℕ) :
    has_flag ((List.replicate n 0).getD i 0) 1 = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- One iteration of the slot loop keeps the invariant. At an epoch end, the
new justified checkpoints come from `justified_of_epoch_test`. -/
theorem provenanceInvariant_slotStep {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (h : slotStep S.cfg S.preset state = .ok next) :
    ProvenanceInvariant S blocks votes next ∧ next.slot = state.slot + 1 := by
  obtain ⟨s1, hs1, hcase⟩ := slotStep_eq_ok h
  obtain ⟨hlen, -, hs1def⟩ := process_slot_eq_ok.mp hs1
  have hN : 0 < S.preset.slots_per_historical_root := S.preset.ring_pos
  have hheadroot : state.latest_block_header.root =
      chainRootAt S.genesisRoot blocks state.slot := by
    rw [hinv.header_root, chainRootAt_of_forall_le]
    intro b hb
    exact Nat.le_trans (hinv.blocks_le_header b hb) hinv.header_le_slot
  have hring : ∀ y, y < state.slot + 1 →
      state.slot + 1 ≤ y + S.preset.slots_per_historical_root →
      (state.block_roots.set (state.slot % S.preset.slots_per_historical_root)
        state.latest_block_header.root)[y % S.preset.slots_per_historical_root]? =
        some (chainRootAt S.genesisRoot blocks y) := by
    rw [hheadroot]
    exact ring_after_slot hlen hN hinv.ring
  rcases hcase with ⟨hb, rfl⟩ | ⟨hb, mid, hmid, rfl⟩
  · subst hs1def
    refine ⟨hinv.of_same_epoch rfl rfl (Nat.le_succ _) (epoch_succ_of_not_boundary hb)
      rfl rfl rfl rfl rfl hring, rfl⟩
  · have hE1 := epoch_succ_of_boundary (cfg := S.cfg) hb
    obtain ⟨bits, pj, j, f, rfl, hout⟩ := process_justification_and_finalization_outcome hmid
    subst hs1def
    refine ⟨?_, rfl⟩
    set E := compute_epoch_at_slot S.cfg state.slot with hEdef
    have hle := hinv.target_epoch_le
    refine
      { validators_eq := hinv.validators_eq
        blocks_ordered := hinv.blocks_ordered
        parent_linked := hinv.parent_linked
        header_root := hinv.header_root
        header_slot := hinv.header_slot
        blocks_le_header := hinv.blocks_le_header
        header_le_slot := Nat.le_trans hinv.header_le_slot (Nat.le_succ _)
        ring := hring
        target_epoch_le := ?_
        current_flags := ?_
        previous_flags := ?_
        current_sources := ?_
        previous_sources := ?_
        target_on_chain := fun r hr =>
          ⟨Nat.lt_succ_of_lt (hinv.target_on_chain r hr).1, (hinv.target_on_chain r hr).2⟩
        source_justified := hinv.source_justified
        early_sources := ?_
        current_epoch_le := ?_
        previous_epoch_le := ?_
        current_justified := ?_
        previous_justified := ?_
        finalized_justified := ?_ }
    · intro r hr
      show _ ≤ compute_epoch_at_slot S.cfg (state.slot + 1)
      rw [hE1]
      exact Nat.le_succ_of_le (hle r hr)
    · intro i
      show has_flag ((List.replicate _ 0).getD i 0) 1 = true ↔ _
      rw [has_flag_replicate_zero]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro r hr _ he
      have := hle r hr.1
      change r.vote.data.target.epoch = compute_epoch_at_slot S.cfg (state.slot + 1) at he
      rw [hE1] at he
      beacon_omega
    · intro i
      show has_flag (state.current_epoch_participation.getD i 0) 1 = true ↔ ∃ r,
        TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
          r.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg (state.slot + 1)
      rw [hE1, hinv.current_flags i]
      simp only [Nat.add_right_cancel_iff, hEdef]
    · intro r hr he
      have := hle r hr.1
      change r.vote.data.target.epoch = compute_epoch_at_slot S.cfg (state.slot + 1) at he
      rw [hE1] at he
      beacon_omega
    · intro r hr he
      change r.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg (state.slot + 1) at he
      rw [hE1, Nat.add_right_cancel_iff] at he
      rw [hinv.current_sources r hr he]
      show state.current_justified_checkpoint = pj
      rcases hout with ⟨hE, rfl, -, -⟩ | ⟨-, rfl, -, -⟩
      · exact (hinv.early_sources (by beacon_omega)).symm
      · rfl
    · intro he
      change compute_epoch_at_slot S.cfg (state.slot + 1) ≤ 2 at he
      rw [hE1] at he
      rcases hout with ⟨-, rfl, rfl, -⟩ | ⟨hE, -⟩
      · exact hinv.early_sources (by beacon_omega)
      · exact absurd hE (by beacon_omega)
    · show j.epoch ≤ compute_epoch_at_slot S.cfg (state.slot + 1) - 1
      rw [hE1]
      have := hinv.current_epoch_le
      rcases hout with ⟨-, -, rfl, -⟩ | ⟨-, -, hj | ⟨_, -, -, hje, -⟩ | ⟨_, -, -, hje, -⟩, -⟩
      · beacon_omega
      · rw [hj]; beacon_omega
      · beacon_omega
      · beacon_omega
    · show pj.epoch ≤ compute_epoch_at_slot S.cfg (state.slot + 1) - 2
      rw [hE1]
      have := hinv.current_epoch_le
      have := hinv.previous_epoch_le
      rcases hout with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -⟩
      · beacon_omega
      · beacon_omega
    · show Justified S votes j
      rcases hout with ⟨-, -, rfl, -⟩ |
        ⟨hE, -, hj | ⟨set, hset, hth, hje, hroot⟩ | ⟨set, hset, hth, hje, hroot⟩, -⟩
      · exact hinv.current_justified
      · rw [hj]; exact hinv.current_justified
      · have := justified_of_epoch_test hS hinv hH hE hb hs1 (Or.inr (by beacon_omega))
          (hje ▸ hset) (hth) (hroot)
        exact this
      · have := justified_of_epoch_test hS hinv hH hE hb hs1 (Or.inl hje)
          (hje ▸ hset) (hth) (hroot)
        exact this
    · show Justified S votes pj
      rcases hout with ⟨-, rfl, -, -⟩ | ⟨-, rfl, -⟩
      · exact hinv.previous_justified
      · exact hinv.current_justified
    · show Justified S votes f
      rcases hout with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl | rfl | rfl⟩
      · exact hinv.finalized_justified
      · exact hinv.finalized_justified
      · exact hinv.previous_justified
      · exact hinv.current_justified

theorem slotStep_slot {cfg : Config} {preset : FFGPreset} {state next : FFGBeaconState Root}
    (h : slotStep cfg preset state = .ok next) : next.slot = state.slot + 1 := by
  obtain ⟨s1, -, hcase⟩ := slotStep_eq_ok h
  rcases hcase with ⟨-, rfl⟩ | ⟨-, _, _, rfl⟩ <;> rfl

theorem slotFold_slot {cfg : Config} {preset : FFGPreset} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root),
      steps.foldlM (fun s _ => slotStep cfg preset s) state = .ok next →
      next.slot = state.slot + steps.length := by
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
    rw [ih mid next hrest, slotStep_slot hmid, List.length_cons]
    beacon_omega

theorem process_slots_slot {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {target : Slot}
    (h : process_slots cfg preset state target = .ok next) :
    next.slot = target ∧ state.slot < target := by
  obtain ⟨-, hlt, hfold⟩ := process_slots_eq_ok.mp h
  rw [slotFold_slot _ _ _ hfold, List.length_range]
  exact ⟨by beacon_omega, hlt⟩

/-- `process_slots` keeps the invariant up to the horizon. -/
theorem provenanceInvariant_slotFold {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root),
      ProvenanceInvariant S blocks votes state →
      steps.foldlM (fun s _ => slotStep S.cfg S.preset s) state = .ok next →
      compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch →
      ProvenanceInvariant S blocks votes next := by
  intro steps
  induction steps with
  | nil =>
    intro state next hinv h _
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact hinv
  | cons step steps ih =>
    intro state next hinv h hH
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    have hle : state.slot ≤ next.slot := by
      rw [slotFold_slot _ _ _ hrest, slotStep_slot hmid]
      beacon_omega
    have hHs : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch :=
      Nat.le_trans (compute_epoch_at_slot_mono hle) hH
    exact ih mid next (provenanceInvariant_slotStep hS hinv hHs hmid).1 hrest hH

theorem provenanceInvariant_process_slots {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} {target : Slot}
    (hinv : ProvenanceInvariant S blocks votes state)
    (h : process_slots S.cfg S.preset state target = .ok next)
    (hH : compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch) :
    ProvenanceInvariant S blocks votes next := by
  obtain ⟨-, -, hfold⟩ := process_slots_eq_ok.mp h
  exact provenanceInvariant_slotFold hS _ _ _ hinv hfold hH

/-! ### Reachable states -/

theorem provenanceInvariant_genesis (S : FFGSetup Root) :
    ProvenanceInvariant S [] [] S.genesis where
  validators_eq := rfl
  blocks_ordered := List.Pairwise.nil
  parent_linked := trivial
  header_root := rfl
  header_slot := rfl
  blocks_le_header := by simp
  header_le_slot := Nat.le_refl _
  ring := fun y hy => absurd hy (Nat.not_lt_zero _)
  target_epoch_le := by simp
  current_flags := by
    intro i
    show has_flag ((List.replicate _ 0).getD i 0) 1 = true ↔ _
    rw [has_flag_replicate_zero]
    simp [TargetIncluded]
  previous_flags := by
    intro i
    show has_flag ((List.replicate _ 0).getD i 0) 1 = true ↔ _
    rw [has_flag_replicate_zero]
    simp [TargetIncluded]
  current_sources := by simp [TargetIncluded]
  previous_sources := by simp [TargetIncluded]
  target_on_chain := by simp [TargetIncluded]
  source_justified := by simp
  early_sources := fun _ => rfl
  current_epoch_le := Nat.zero_le _
  previous_epoch_le := Nat.zero_le _
  current_justified := .anchor
  previous_justified := .anchor
  finalized_justified := .anchor

theorem attestationFold_slot {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state next : FFGBeaconState Root),
      attestations.foldlM (fun s vote =>
        process_attestation cfg preset schedule s vote parentSlot) state = .ok next →
      next.slot = state.slot := by
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

theorem process_block_slot {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} (h : process_block cfg preset schedule state block = .ok next) :
    next.slot = state.slot := by
  obtain ⟨paid, headed, hpaid, hheaded, hfold⟩ := process_block_eq_ok h
  obtain ⟨_, _, rfl⟩ := process_parent_execution_payload_eq_ok hpaid
  obtain ⟨-, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  have := attestationFold_slot _ _ _ hfold
  exact this

theorem state_transition_slot {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {oracle : BlockValidityOracle Root}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (h : state_transition cfg preset schedule oracle state block = .ok next) :
    next.slot = block.slot ∧ state.slot < block.slot := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  obtain ⟨hatSlot, hlt⟩ := process_slots_slot hslots
  exact ⟨(process_block_slot hblock).trans hatSlot, hlt⟩

/-- A successful block transition keeps the invariant, appends the block, and
records its body votes. -/
theorem provenanceInvariant_state_transition {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (hinv : ProvenanceInvariant S blocks votes state)
    (h : state_transition S.cfg S.preset S.schedule S.oracle state block = .ok next)
    (hH : compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch) :
    ProvenanceInvariant S (blocks ++ [block]) (votes ++ blockVotes S state block) next := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  have hnextslot : next.slot = atSlot.slot := process_block_slot hblock
  obtain ⟨paid, headed, hpaid, hheaded, hfold⟩ := process_block_eq_ok hblock
  have hinv1 := provenanceInvariant_process_slots hS hinv hslots (by rw [← hnextslot]; exact hH)
  obtain ⟨hinv2, -, -⟩ := provenanceInvariant_header hinv1 hpaid hheaded
  obtain ⟨hinv3, -⟩ := provenanceInvariant_attestations (block := block) _ _ _ _ hinv2 hfold
  rw [blockVotes_eq hslots hpaid hheaded]
  exact hinv3

/-- **Invariant of reachable states.** Every reachable state whose epoch is
within the fixed scope satisfies `ProvenanceInvariant`. -/
theorem provenanceInvariant_of_reachable {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    ProvenanceInvariant S blocks votes state := by
  induction h with
  | genesis => exact provenanceInvariant_genesis S
  | slots hreach hslots ih =>
    obtain ⟨hnext, hlt⟩ := process_slots_slot hslots
    have hHs := Nat.le_trans (compute_epoch_at_slot_mono (Nat.le_of_lt (hnext ▸ hlt))) hH
    exact provenanceInvariant_process_slots hS (ih hHs) hslots hH
  | block blk hreach htrans ih =>
    obtain ⟨hns, hlt⟩ := state_transition_slot htrans
    have hHs := Nat.le_trans (compute_epoch_at_slot_mono (Nat.le_of_lt (hns ▸ hlt))) hH
    exact provenanceInvariant_state_transition hS (ih hHs) htrans hH

end FastConfirmation.Spec.ConcreteFFG

end
