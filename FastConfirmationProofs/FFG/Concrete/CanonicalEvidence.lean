module
public import FastConfirmationProofs.FFG.Concrete.CertificateTranslation
public import FastConfirmationProofs.FFG.Concrete.CanonicalInterpretation
public import FastConfirmationProofs.FFG.Certificates.EarlyFinalizingSigner

@[expose] public section

/-! Proves the fields of `CanonicalOpenFields` for the canonical inclusion
relation. A formed checkpoint is the anchor reading of a checkpoint justified
in the chain run of its carrier, so its included certificate is the translated
concrete certificate. A non-anchor formed checkpoint has a supermajority link
whose signers include an honest validator (`ByzantineWeightPremises`). Its
included body vote reached some node from the block, so by `no_forgery` the
honest validator cast a vote with the same data. The finalized selectors
translate the concrete finalization links of F4. The epoch-one field is the
scope condition `EpochOneFinalizationScope`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- A formed checkpoint is the anchor reading of a checkpoint justified in the
chain run of its carrier. -/
theorem formed_justified (hB : B.Admissible) {E : Execution Root} {store : Store Root}
    {x : Root} {cs : FFGBeaconState Root} {bl : List (FFGWireBlock Root)}
    {vo : List (IncludedVote Root)} (hrun : B.ChainRun store x cs bl vo) {c : Checkpoint Root}
    (hf : B.CarriedOrRealizable E x c) : ∃ j, Justified B.setup vo j ∧ c = B.readAsAnchor j := by
  have hinv := provenanceInvariant_of_reachable hB.setup hrun.reachable hrun.in_scope
  obtain ⟨Y, hY, -⟩ := eager_pjf hB.setup hB.numeric hinv (lengthsOK_of_reachable hrun.reachable)
    hrun.in_scope
  have he := B.unrealizedState_of x hrun.committed hY
  have hej := eager_justification_soundness hB.setup hrun.reachable hrun.in_scope hY
  obtain ⟨-, h | h | h | h | h⟩ := hf
  · exact ⟨_, hinv.current_justified, by rw [h, B.realizedJustified_of x hrun.committed]⟩
  · exact ⟨_, hinv.finalized_justified, by rw [h, B.realizedFinalized_of x hrun.committed]⟩
  · exact ⟨_, hej.1, by rw [h, B.unrealizedJustified_of x he]⟩
  · exact ⟨_, hej.2.2, by rw [h, B.unrealizedFinalized_of x he]⟩
  · obtain ⟨cs', target, next, hcs', htarget, hslots, rfl⟩ := h
    rw [hrun.committed] at hcs'
    cases hcs'
    obtain ⟨-, hlt⟩ := process_slots_slot hslots
    obtain ⟨next', hnext', hinv', -, -⟩ := process_slots_ok hB.setup hB.numeric hinv
      (lengthsOK_of_reachable hrun.reachable) hlt htarget
    rw [hslots] at hnext'
    cases hnext'
    exact ⟨_, hinv'.current_justified, rfl⟩

/-- A target-included vote precedes its carrier slot in every bridged store
that knows the carrier. -/
theorem targetIncludedAt_slot_lt {E : Execution Root} {store : Store Root}
    (hs : B.BridgedStore store) {carrier : Root} (hc : carrier ∈ store.block_roots)
    {a : Attestation Root} (h : B.TargetIncludedAt E carrier a) :
    a.data.slot < (store.blocks carrier).slot := by
  obtain ⟨r, ⟨-, hne, wire, sr, cp, hopen, hcp, hmem⟩, rfl, -⟩ := h
  obtain ⟨cs, -, -, -, -, -, hrest⟩ := hs.known carrier hc
  obtain ⟨wire', ho', -, hm, -, cp', hcp', hst⟩ := hrest hne
  rw [hopen] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  rw [hm.2.1, hcp] at hcp'
  obtain rfl := Option.some.inj hcp'
  obtain ⟨-, -, hpre, next, hnext⟩ := blockVote_of_transition hst hmem
  obtain ⟨-, hdelay, -⟩ := process_attestation_guards hnext
  have hpos := B.setup.preset.min_delay_pos
  change r.vote.data.slot < _
  rw [hm.1, ← hpre]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) hdelay

/-- **Formed evidence.** -/
theorem formed_evidence (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hwf : WellFormedExecution E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    (hhb : HonestBehavior B.setup.cfg B.interface E)
    (hbyz : ByzantineWeightPremises B.setup.cfg E) (hspe : 1 < B.setup.cfg.slots_per_epoch)
    {x : Root} {c : Checkpoint Root} (hf : B.CarriedOrRealizable E x c) :
    IncludedCheckpointEvidence B.setup.cfg B.interface E (B.TargetIncludedAt E)
      B.anchorCheckpoint x c := by
  obtain ⟨store, hstore, hx⟩ := hf.1
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨cs, bl, vo, hrun⟩ := B.chainRun_of_known hB hs hx
  obtain ⟨j, hj, rfl⟩ := B.formed_justified hB hrun hf
  have hjc := onChain_of_justified hB.setup hrun.reachable hrun.in_scope hj
  refine ⟨⟨B.includedCertified hB hg hscope hcomm hdel hstore hx hrun hj⟩, ?_, ?_⟩
  · rw [B.readAsAnchor_root hs hx hrun.chain hjc]
    exact B.descends_ancestor hB hg hstore hx _
  · by_cases hanc : B.readAsAnchor j = B.anchorCheckpoint
    · exact Or.inl hanc
    right
    cases hj with
    | anchor => exact absurd B.readAsAnchor_stub hanc
    | link hsrc link =>
      obtain ⟨L⟩ := B.includedLink hB hg hscope hcomm hdel hstore hx hrun hsrc link
      obtain ⟨i, hi, hhon, -⟩ := Execution.supermajority_honest_signer_before_last_slot
        B.setup.cfg hbyz hspe L.target_span_within.1 L.target_span_within.2 L.signers_in_epoch
        L.supermajority
      obtain ⟨a, ⟨c', hdesc, hTI⟩, hia, -, htgt⟩ := L.signer_attestation i hi
      obtain ⟨-, -, ⟨w, n, hsched⟩, hwithin, -, -, -⟩ :=
        B.targetIncludedAt_evidence hB hg hscope hcomm hdel hTI
      obtain ⟨m, a'', -, hvote, hdata⟩ := hhb.no_forgery w n a true hsched i hhon hia
      obtain ⟨hck, hcle, -⟩ := B.chain_ancestor hB hg hwf hstore hdesc hx hTI.choose_spec.1.1
      have hslot : a.data.slot < (store.blocks x).slot :=
        lt_of_lt_of_le (B.targetIncludedAt_slot_lt hs hck hTI) hcle
      refine ⟨store.blocks x, ⟨store, hstore, hx, rfl⟩, i, hhon, a.data.slot, m, a'', hslot,
        hwithin, hvote, by rw [← hdata], by rw [← hdata]; exact htgt, a, ⟨c', hdesc, hTI⟩, hia,
        hdata⟩

/-- **Finalization translation.** A concrete finalization link of the chain run
of an accepted block is an included finalization certificate on the block for
the anchor reading of the finalized checkpoint. -/
theorem finalized_evidence (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store)
    {x : Root} (hx : x ∈ store.block_roots) {cs : FFGBeaconState Root}
    {bl : List (FFGWireBlock Root)} {vo : List (IncludedVote Root)}
    (hrun : B.ChainRun store x cs bl vo) {f : Checkpoint Root} (P : Epoch → Prop)
    (h : f = B.setup.stub ∨ ∃ target, FinalizationLink B.setup bl vo f target ∧ P target.epoch) :
    B.readAsAnchor f = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint x
        (B.readAsAnchor f), P F.child.epoch := by
  rcases h with rfl | ⟨target, hl, hP⟩
  · exact Or.inl B.readAsAnchor_stub
  right
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨link⟩ := hl.link
  have hjf := onChain_of_justified hB.setup hrun.reachable hrun.in_scope hl.justified
  refine ⟨{ justified := B.includedCertified hB hg hscope hcomm hdel hstore hx hrun hl.justified
            child := B.readAsAnchor target
            child_epoch := ?_
            middle_justified := ?_
            finalizing_link :=
              (B.includedLink hB hg hscope hcomm hdel hstore hx hrun hl.justified link).some }, ?_⟩
  · rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch]
    exact hl.target_epoch
  · intro h2
    rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch] at h2
    refine ⟨B.readAsAnchor (chainCheckpoint B.setup bl (f.epoch + 1)), ?_, ?_,
      ⟨B.includedCertified hB hg hscope hcomm hdel hstore hx hrun (hl.middle_justified h2)⟩⟩
    · rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch]
      rfl
    · rw [B.readAsAnchor_root hs hx hrun.chain (onChain_chainCheckpoint _ _ _),
        B.readAsAnchor_root hs hx hrun.chain hjf]
      apply B.descends_ancestors hB hg hstore hx
      rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · change P (B.readAsAnchor target).epoch
    rw [B.readAsAnchor_epoch]
    exact hP

/-- **Realized finalized evidence.** -/
theorem realized_finalized_evidence (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E) {r : Root}
    {b : BeaconBlock Root} (h : E.BlockKnownInScheduledPrefix B.setup.cfg B.interface r b) :
    B.realizedFinalized r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint r
          (B.realizedFinalized r),
        F.child.epoch < compute_epoch_at_slot B.setup.cfg b.slot := by
  obtain ⟨store, hstore, hr, rfl⟩ := h
  obtain ⟨cs, bl, vo, hrun⟩ := B.chainRun_of_known hB (B.bridgedStore_prefix hB hg hstore) hr
  rw [B.realizedFinalized_of r hrun.committed, ← hrun.slot_eq]
  exact B.finalized_evidence hB hg hscope hcomm hdel hstore hr hrun
    (fun e => e < compute_epoch_at_slot B.setup.cfg cs.slot)
    (finalization_soundness hB.setup hrun.reachable hrun.in_scope)

/-- **Unrealized finalized evidence.** -/
theorem unrealized_finalized_evidence (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E) {r : Root}
    {b : BeaconBlock Root} (h : E.BlockKnownInScheduledPrefix B.setup.cfg B.interface r b) :
    B.unrealizedFinalized r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint r
          (B.unrealizedFinalized r),
        F.child.epoch ≤ compute_epoch_at_slot B.setup.cfg b.slot := by
  obtain ⟨store, hstore, hr, rfl⟩ := h
  obtain ⟨cs, bl, vo, hrun⟩ := B.chainRun_of_known hB (B.bridgedStore_prefix hB hg hstore) hr
  have hinv := provenanceInvariant_of_reachable hB.setup hrun.reachable hrun.in_scope
  obtain ⟨Y, hY, -⟩ := eager_pjf hB.setup hB.numeric hinv (lengthsOK_of_reachable hrun.reachable)
    hrun.in_scope
  rw [B.unrealizedFinalized_of r (B.unrealizedState_of r hrun.committed hY), ← hrun.slot_eq]
  exact B.finalized_evidence hB hg hscope hcomm hdel hstore hr hrun
    (fun e => e ≤ compute_epoch_at_slot B.setup.cfg cs.slot)
    (eager_finalization_soundness hB.setup hrun.reachable hrun.in_scope hY)

/-- **Epoch-one finalization**, from the scope condition. -/
theorem epoch_one_evidence (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    (hone : B.EpochOneFinalizationScope E) (r : Root)
    (hr : E.RootKnownInScheduledPrefix B.setup.cfg B.interface r) :
    ((B.realizedFinalized r).epoch = GENESIS_EPOCH + 1 →
      B.realizedFinalized r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint r
          (B.realizedFinalized r),
        F.child.epoch = GENESIS_EPOCH + 2) ∧
    ((B.unrealizedFinalized r).epoch = GENESIS_EPOCH + 1 →
      B.unrealizedFinalized r = B.anchorCheckpoint ∨
      ∃ F : IncludedCertifiedFinalized B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint r
          (B.unrealizedFinalized r),
        F.child.epoch = GENESIS_EPOCH + 2) := by
  obtain ⟨store, hstore, hx⟩ := hr
  obtain ⟨cs, bl, vo, hrun⟩ := B.chainRun_of_known hB (B.bridgedStore_prefix hB hg hstore) hx
  have hinv := provenanceInvariant_of_reachable hB.setup hrun.reachable hrun.in_scope
  obtain ⟨Y, hY, -⟩ := eager_pjf hB.setup hB.numeric hinv (lengthsOK_of_reachable hrun.reachable)
    hrun.in_scope
  have hscope' := hone r cs ⟨store, hstore, hx⟩ hrun.committed bl vo hrun.reachable
  constructor
  · intro h1
    rw [B.realizedFinalized_of r hrun.committed] at h1 ⊢
    rw [B.readAsAnchor_epoch] at h1
    exact B.finalized_evidence hB hg hscope hcomm hdel hstore hx hrun
      (fun e => e = GENESIS_EPOCH + 2) (Or.inr (hscope'.1 h1))
  · intro h1
    rw [B.unrealizedFinalized_of r (B.unrealizedState_of r hrun.committed hY)] at h1 ⊢
    rw [B.readAsAnchor_epoch] at h1
    exact B.finalized_evidence hB hg hscope hcomm hdel hstore hx hrun
      (fun e => e = GENESIS_EPOCH + 2) (Or.inr (hscope'.2 Y hY h1))

/-- **The open fields of the canonical interpretation**, for the canonical
inclusion relation. -/
theorem canonicalOpenFields (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hwf : WellFormedExecution E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    (hhb : HonestBehavior B.setup.cfg B.interface E)
    (hbyz : ByzantineWeightPremises B.setup.cfg E) (hspe : 1 < B.setup.cfg.slots_per_epoch)
    (hone : B.EpochOneFinalizationScope E) :
    B.CanonicalOpenFields E (B.canonicalInclusion hB hg hscope hcomm hdel) where
  formed_evidence := fun hf => B.formed_evidence hB hg hwf hscope hcomm hdel hhb hbyz hspe hf
  realized_finalized_evidence := fun h =>
    B.realized_finalized_evidence hB hg hscope hcomm hdel h
  unrealized_finalized_evidence := fun h =>
    B.unrealized_finalized_evidence hB hg hscope hcomm hdel h
  epoch_one_finalization_one_step := fun r hr =>
    B.epoch_one_evidence hB hg hscope hcomm hdel hone r hr

/-! ### Link endpoints on accepted carriers (repair R-d) -/

/-- The target of an attestation included on the chain of an accepted block is
the checkpoint of that block at the target epoch: the vote is a
target-included body vote of a store ancestor, so its target root is the
ancestor root that `get_block_root` read. -/
theorem includedOnChain_target (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store) {x : Root}
    (hx : x ∈ store.block_roots) {a : Attestation Root}
    (ha : AttestationIncludedOnChain E (B.TargetIncludedAt E) x a) :
    a.data.target = B.checkpointAt x a.data.target.epoch := by
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨c', hdesc, hTI⟩ := ha
  obtain ⟨r, ⟨hc', hne, wire, sr, cp, hopen, hcp, hmem⟩, rfl, flags, hflags, hflag⟩ := hTI
  obtain ⟨hck, -, hanc⟩ := B.chain_ancestor hB hg hwf hstore hdesc hx hc'
  obtain ⟨cs, bl, vo, hrun⟩ := B.chainRun_of_known hB hs hx
  have hr := hrun.votes_complete c' hck hne hanc wire sr cp hopen hcp r hmem
  have hroot := targetIncluded_target_on_chain hB.setup hrun.reachable hrun.in_scope
    ⟨hr, flags, hflags, hflag⟩
  rw [B.checkpointAt_eq hs hx]
  change r.vote.data.target = ⟨r.vote.data.target.epoch, (get_ancestor store
    (ForkChoiceNode.mk x .pending)
      (compute_start_slot_at_epoch B.setup.cfg r.vote.data.target.epoch)).root⟩
  rw [← hrun.chain, ← hroot]

/-- The target of an included link on an accepted block is the checkpoint of
that block at the target epoch. -/
theorem link_target_on_carrier (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store) {x : Root}
    (hx : x ∈ store.block_roots) {source target : Checkpoint Root}
    (L : IncludedSupermajorityLink B.setup.cfg E (B.TargetIncludedAt E) x source target) :
    target = B.checkpointAt x target.epoch := by
  have hsm := L.supermajority
  rw [B.total_active_eq hB hg, B.weight_eq hg] at hsm
  have hfloor := hB.setup.balance_floor
  have hinc := B.setup.cfg.effective_balance_increment_pos
  obtain ⟨i, hi⟩ : L.signers.Nonempty := by
    rcases Finset.eq_empty_or_nonempty L.signers with he | hne
    · rw [he, FixedFFGScope.weight, Finset.sum_empty] at hsm
      beacon_omega
    · exact hne
  obtain ⟨a, ha, -, -, htgt⟩ := L.signer_attestation i hi
  rw [← htgt]
  exact B.includedOnChain_target hB hg hwf hstore hx ha

/-- **Link checkpoint agreement** of the canonical state: the endpoints of a
contributing included link on an accepted carrier are checkpoints of the
carrier. -/
theorem canonical_link_checkpoint_agreement (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) :
    IncludedLinkCheckpointAgreement B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint
      B.checkpointAt (E.RootKnownInScheduledPrefix B.setup.cfg B.interface) where
  endpoints_on_carrier := by
    intro x source target hx L hcontributing
    obtain ⟨store, hstore, hxk⟩ := hx
    have hs := B.bridgedStore_prefix hB hg hstore
    refine ⟨?_, B.link_target_on_carrier hB hg hwf hstore hxk L⟩
    cases hcontributing with
    | anchor =>
      rw [B.checkpointAt_eq hs hxk]
      change B.anchorCheckpoint = ⟨0, (get_ancestor store (ForkChoiceNode.mk x .pending)
        (0 * B.setup.cfg.slots_per_epoch)).root⟩
      rw [Nat.zero_mul, B.ancestor_zero hs hxk]
      rfl
    | link _ L' => exact B.link_target_on_carrier hB hg hwf hstore hxk L'

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
