module
public import FastConfirmationProofs.FFG.Concrete.BridgeStore
public import FastConfirmationProofs.FFG.Concrete.InclusionGuards
public import FastConfirmationProofs.FFG.Concrete.JustificationSoundness

@[expose] public section

/-! Proves the inclusion evidence of the canonical relation
`ConcreteBridge.TargetIncludedAt`. A target-included body vote of an accepted
block passed the guards of `process_attestation`: its target epoch is the
epoch of its slot, its slot is before the carrier slot, and its attesters are
members of the fixed committees of its slot. Its slot is in the horizon because
the carrier post-state is in the fixed scope and the horizon is the scope end.
Its scheduled `is_from_block` delivery is the input `BodyDelivery`. The
result is the accepted inclusion relation `canonicalInclusion`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

/-! ### Body votes -/

omit [LinearOrder Root] [Inhabited Root] in
theorem mem_attestationVotes_slot [DecidableEq Root] {S : FFGSetup Root}
    {block : FFGWireBlock Root} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state : FFGBeaconState Root)
      (r : IncludedVote Root), r ∈ attestationVotes S block parentSlot state attestations →
      r.pre.slot = state.slot
  | [], _, _, h => by simp [attestationVotes] at h
  | vote :: attestations, state, r, h => by
    unfold attestationVotes at h
    split at h
    · rename_i next hnext
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · rw [mem_attestationVotes_slot attestations next r h]
        exact (process_attestation_guards hnext).2.2.1
    · simp at h

omit [LinearOrder Root] [Inhabited Root] in
/-- A body vote of a successful transition: the vote is in the block body, its
`process_attestation` call succeeded, and the call ran at the block slot. -/
theorem blockVote_of_transition [DecidableEq Root] {S : FFGSetup Root}
    {cp cs : FFGBeaconState Root} {wire : FFGWireBlock Root}
    (hst : state_transition S.cfg S.preset S.schedule S.oracle cp wire = .ok cs)
    {r : IncludedVote Root} (hr : r ∈ blockVotes S cp wire) :
    r.block = wire ∧ r.vote ∈ wire.attestations ∧ r.pre.slot = wire.slot ∧
      ∃ next, process_attestation S.cfg S.preset S.schedule r.pre r.vote r.parentSlot =
        .ok next := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok hst
  obtain ⟨paid, headed, hpaid, hheaded, -⟩ := process_block_eq_ok hblock
  rw [blockVotes_eq hslots hpaid hheaded] at hr
  obtain ⟨hb, hv, -, hnext⟩ := mem_attestationVotes _ _ r hr
  have hslot := mem_attestationVotes_slot _ _ r hr
  obtain ⟨hwslot, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  exact ⟨hb, hv, hslot.trans hwslot.symm, hnext⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- An attester of a wire vote is a member of a selected committee of the vote
slot. -/
theorem mem_get_attesting_indices {schedule : FixedCommitteeSchedule}
    {vote : FFGWireAttestation Root} {i : ValidatorIndex}
    (h : i ∈ get_attesting_indices schedule vote) :
    ∃ ci ∈ get_committee_indices vote.committee_bits,
      i ∈ (schedule.committee vote.data.slot ci).getD [] := by
  unfold get_attesting_indices at h
  simp only [List.mem_toFinset] at h
  suffices hfold : ∀ (L : List CommitteeIndex) (acc : ℕ × List ValidatorIndex),
      i ∈ (L.foldl (fun (x : ℕ × List ValidatorIndex) committeeIndex =>
        let committee := (schedule.committee vote.data.slot committeeIndex).getD []
        (x.1 + committee.length, x.2 ++ ((List.range committee.length).filter fun j =>
          vote.aggregation_bits.getD (x.1 + j) false).map fun j => committee.getD j 0))
        acc).2 →
      i ∈ acc.2 ∨ ∃ ci ∈ L, i ∈ (schedule.committee vote.data.slot ci).getD [] by
    rcases hfold _ (0, []) h with h | h
    · simp at h
    · exact h
  intro L
  induction L with
  | nil => intro acc h; exact Or.inl h
  | cons ci L ih =>
    intro acc h
    rcases ih _ h with h | ⟨cj, hcj, hmem⟩
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · right
        refine ⟨ci, List.mem_cons_self, ?_⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        have hj' := (List.mem_range.mp (List.mem_filter.mp hj).1)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
        exact List.getElem_mem hj'
    · exact Or.inr ⟨cj, List.mem_cons_of_mem _ hcj, hmem⟩

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The slot committee of the bridge interface is the fixed schedule of the
setup, for every store. -/
theorem get_slot_committee_interface (store : Store Root) (s : Slot) :
    get_slot_committee B.setup.cfg B.interface store s =
      (Finset.range ((B.setup.schedule.count (compute_epoch_at_slot B.setup.cfg s)).getD 0)).biUnion
        fun ci => ((B.setup.schedule.committee s ci).getD []).toFinset := by
  rfl

/-- The committees of the execution are the fixed slot committees of the
setup at every in-horizon slot. -/
def FixedCommittees (E : Execution Root) : Prop :=
  ∀ s, E.SlotWithinHorizon B.setup.cfg s → ∀ store : Store Root,
    get_slot_committee B.setup.cfg B.interface store s = E.committee s

/-- `committees_agree` at one honest in-horizon store gives the fixed
committees, because the slot committee of the bridge interface does not read
the store. -/
theorem fixedCommittees_of_agree {E : Execution Root}
    (hagree : ∀ v ∈ E.honest, ∀ n (s : Slot), E.WithinHorizon B.setup.cfg n →
      E.SlotWithinHorizon B.setup.cfg s →
      get_slot_committee B.setup.cfg B.interface (E.store B.setup.cfg B.interface v n) s =
        E.committee s)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ} (hn : E.WithinHorizon B.setup.cfg n) :
    B.FixedCommittees E := by
  intro s hs store
  rw [get_slot_committee_interface,
    ← get_slot_committee_interface B (E.store B.setup.cfg B.interface v n)]
  exact hagree v hv n s hn hs

/-- A body vote of an accepted block: the carrier message, its matching wire
block in the fixed scope, and the successful `process_attestation` call of the
vote at the block slot. -/
theorem carrierVote_facts (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {carrier : Root} {r : IncludedVote Root} (h : B.CarrierVote E carrier r) :
    ∃ b, E.BlockKnownInScheduledPrefix B.setup.cfg B.interface carrier b ∧
      ∃ wire, B.MessageMatches b wire ∧
        compute_epoch_at_slot B.setup.cfg wire.slot ≤ B.setup.scope.last_epoch ∧
        r.vote ∈ wire.attestations ∧ r.pre.slot = wire.slot ∧
        ∃ next, process_attestation B.setup.cfg B.setup.preset B.setup.schedule r.pre r.vote
          r.parentSlot = .ok next := by
  obtain ⟨⟨store, hstore, hr⟩, hne, wire, stateRoot, cp, hopen, hcp, hvote⟩ := h
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨cs, -, -, hdom, -, hslot, hrest⟩ := hs.known carrier hr
  obtain ⟨wire', ho', -, hm, -, cp', hcp', hst⟩ := hrest hne
  rw [hopen] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  rw [hm.2.1, hcp] at hcp'
  obtain rfl := Option.some.inj hcp'
  obtain ⟨-, hv, hpre, hnext⟩ := blockVote_of_transition hst hvote
  refine ⟨store.blocks carrier, ⟨store, hstore, hr, rfl⟩, wire, hm, ?_, hv, hpre, hnext⟩
  rw [← hm.1, ← hslot]
  exact hdom.2

/-- **Inclusion evidence.** A target-included body vote of an accepted block
was received from the block, its slot is in the horizon and before the carrier
slot, its target epoch is the epoch of its slot, and its attesters are members
of the committee of its slot. -/
theorem targetIncludedAt_evidence (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    {carrier : Root} {a : Attestation Root} (h : B.TargetIncludedAt E carrier a) :
    ∃ b, E.BlockKnownInScheduledPrefix B.setup.cfg B.interface carrier b ∧
      (∃ (w : ValidatorIndex) (n : ℕ), Event.attestation a true ∈ E.schedule w n) ∧
      E.SlotWithinHorizon B.setup.cfg a.data.slot ∧ a.data.slot < b.slot ∧
      a.data.target.epoch = compute_epoch_at_slot B.setup.cfg a.data.slot ∧
      ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot := by
  obtain ⟨r, hcv, rfl, -⟩ := h
  obtain ⟨b, hbk, wire, hm, hep, hvin, hpre, next, hnext⟩ := B.carrierVote_facts hB hg hcv
  obtain ⟨htarget, hdelay, -, count, hcount, hci⟩ := process_attestation_guards hnext
  have hpos := B.setup.preset.min_delay_pos
  have hlt : r.vote.data.slot < wire.slot :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) (hdelay.trans_eq hpre)
  have hspe := B.setup.cfg.slots_per_epoch_pos
  have hwithin : E.SlotWithinHorizon B.setup.cfg r.vote.data.slot := by
    have hwlt : wire.slot < (B.setup.scope.last_epoch + 1) * B.setup.cfg.slots_per_epoch :=
      (Nat.div_lt_iff_lt_mul hspe).mp (Nat.lt_succ_of_le hep)
    have hnum := hB.numeric
    refine ⟨((hlt.trans hwlt).le.trans (Nat.le_add_right _ _)).trans hnum, ?_⟩
    rw [hscope]
    exact Nat.lt_succ_of_le ((compute_epoch_at_slot_mono hlt.le).trans hep)
  obtain ⟨w, n, hwn⟩ := hdel carrier b hbk _ (by
    rw [hm.2.2.2.2.2.1]
    exact List.mem_map_of_mem hvin)
  refine ⟨b, hbk, ⟨w, n + 1, hwn⟩, hwithin, ?_, htarget, ?_⟩
  · rw [hm.1]
    exact hlt
  · intro i hi
    have hi' : i ∈ get_attesting_indices B.setup.schedule r.vote := by
      simpa [indexed, get_indexed_attestation] using hi
    obtain ⟨ci, hcim, hmem⟩ := mem_get_attesting_indices hi'
    change i ∈ E.committee r.vote.data.slot
    rw [← hcomm _ hwithin E.genesis_store, get_slot_committee_interface, Finset.mem_biUnion]
    refine ⟨ci, ?_, List.mem_toFinset.mpr hmem⟩
    rw [Finset.mem_range, ← htarget, hcount]
    exact hci ci hcim

/-- A target-included vote is a body vote of its carrier. -/
theorem bodyIncludedAt_of_targetIncludedAt {E : Execution Root} {carrier : Root}
    {a : Attestation Root} (hB : B.Admissible) (hg : B.ConcreteGenesis E)
    (h : B.TargetIncludedAt E carrier a) : B.BodyIncludedAt E carrier a := by
  obtain ⟨r, hcv, rfl, -⟩ := h
  obtain ⟨hknown, hne, wire, stateRoot, cp, hopen, hcp, hvote⟩ := hcv
  refine ⟨hknown, hne, wire, stateRoot, hopen, r.vote, ?_, rfl⟩
  obtain ⟨store, hstore, hr⟩ := hknown
  obtain ⟨cs, -, -, -, -, -, hrest⟩ := (B.bridgedStore_prefix hB hg hstore).known carrier hr
  obtain ⟨wire', ho', -, hm, -, cp', hcp', hst⟩ := hrest hne
  rw [hopen] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  rw [hm.2.1, hcp] at hcp'
  obtain rfl := Option.some.inj hcp'
  exact (blockVote_of_transition hst hvote).2.1

/-- A body vote of an accepted block was received from the block. -/
theorem bodyIncludedAt_received (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hdel : B.BodyAttestationsDelivered E) {carrier : Root}
    {a : Attestation Root} (h : B.BodyIncludedAt E carrier a) :
    ∃ (w : ValidatorIndex) (n : ℕ), Event.attestation a true ∈ E.schedule w n := by
  obtain ⟨⟨store, hstore, hr⟩, hne, wire, stateRoot, hopen, vote, hvin, rfl⟩ := h
  obtain ⟨cs, -, -, -, -, -, hrest⟩ := (B.bridgedStore_prefix hB hg hstore).known carrier hr
  obtain ⟨wire', ho', -, hm, -⟩ := hrest hne
  rw [hopen] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  obtain ⟨w, n, hwn⟩ := hdel carrier (store.blocks carrier) ⟨store, hstore, hr, rfl⟩ _ (by
    rw [hm.2.2.2.2.2.1]
    exact List.mem_map_of_mem hvin)
  exact ⟨w, n + 1, hwn⟩

/-- **The canonical inclusion relation** `I`: target-included body votes of
accepted blocks, with their inclusion evidence. -/
noncomputable def canonicalInclusion (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E) :
    Execution.AcceptedBlockAttestationInclusion B.setup.cfg B.interface E where
  Included := B.TargetIncludedAt E
  evidence := fun h =>
    have hev := B.targetIncludedAt_evidence hB hg hscope hcomm hdel h
    { carrier_message := hev.choose
      received_from_block := hev.choose_spec.2.1
      slot_within_horizon := hev.choose_spec.2.2.1
      slot_before_carrier := hev.choose_spec.2.2.2.1
      target_epoch := hev.choose_spec.2.2.2.2.1
      attesters_in_committee := hev.choose_spec.2.2.2.2.2
      carrier_accepted := hev.choose_spec.1 }

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
