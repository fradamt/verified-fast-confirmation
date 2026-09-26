module
public import FastConfirmationProofs.FFG.Concrete.CanonicalCheckpoints
public import FastConfirmationProofs.FFG.Concrete.CanonicalInclusion
public import FastConfirmationProofs.FFG.Concrete.FinalizationSoundness

@[expose] public section

/-! Translates the concrete justification and finalization certificates of an
accepted block into the included certificates of the canonical inclusion
relation `TargetIncludedAt`. The committed parent chain of an accepted block
is a reachable run whose votes are the body votes of the store ancestors of
the block (`chain_votes`). A supermajority link of that run is an included
supermajority link on the block: each signer vote is target-included in the
body of an ancestor block, the ancestor descends in the execution, and the
fixed registry weighs as the execution registry. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-! ### Weights -/

/-- The execution registry is the fixed registry of the setup. -/
theorem registry_eq {E : Execution Root} (hg : B.ConcreteGenesis E) :
    E.anchor_state = B.project B.setup.genesis := by
  have hs := B.bridgedStore_genesis hg
  obtain ⟨cs, hcs, hstate, -⟩ := hs.known _ hs.genesis_known
  rw [B.committedState_genesis] at hcs
  cases hcs
  unfold Execution.anchor_state
  rw [B.genesis_justified hg]
  exact hstate

theorem weight_eq {E : Execution Root} (hg : B.ConcreteGenesis E) (s : Finset ValidatorIndex) :
    E.weight s = B.setup.scope.weight s := by
  unfold Execution.weight Execution.weight_of Execution.registry FixedFFGScope.weight
  rw [B.registry_eq hg]
  rfl

theorem total_active_eq (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E) :
    E.total_active B.setup.cfg = B.setup.scope.activeBalance := by
  unfold Execution.total_active
  rw [B.registry_eq hg]
  have h := total_active_balance_eq (S := B.setup) hB.setup (state := B.setup.genesis) rfl
    (by change compute_epoch_at_slot B.setup.cfg 0 ≤ _; simp [compute_epoch_at_slot])
  have hfloor := hB.setup.balance_floor
  have hinc := B.setup.cfg.effective_balance_increment_pos
  change ConcreteFFG.get_total_active_balance B.setup.cfg B.setup.genesis = _
  rw [h]
  have hle : B.setup.cfg.effective_balance_increment ≤ B.setup.scope.activeBalance :=
    le_trans (Nat.le_mul_of_pos_left _ (by decide)) hfloor
  exact max_eq_right hle

/-! ### The votes of the committed chain -/

omit [Inhabited Root] in
/-- **Chain votes.** A known root of a bridged store has a reachable run of
its committed state whose block list is the store ancestor walk and whose
votes are exactly the body votes of its non-genesis store ancestors: each
recorded vote is a body vote of an ancestor block, and each body vote of an
ancestor block is recorded. -/
theorem chain_votes (hB : B.Admissible) {store : Store Root} (hs : B.BridgedStore store) :
    ∀ n, ∀ x ∈ store.block_roots, (store.blocks x).slot ≤ n →
      ∃ cs bl vo, B.committedState x = some cs ∧ Reachable B.setup bl vo cs ∧
        (∀ y, chainRootAt B.setup.genesisRoot bl y =
          (get_ancestor store (ForkChoiceNode.mk x .pending) y).root) ∧
        (∀ r ∈ vo, ∃ a ∈ store.block_roots, a ≠ B.setup.genesisRoot ∧
          (store.blocks a).slot = r.block.slot ∧
          (get_ancestor store (ForkChoiceNode.mk x .pending) r.block.slot).root = a ∧
          ∃ sr cp, B.blocks.open_ a = some (r.block, sr) ∧
            B.committedState r.block.parent_root = some cp ∧ r ∈ blockVotes B.setup cp r.block) ∧
        (∀ a ∈ store.block_roots, a ≠ B.setup.genesisRoot →
          (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks a).slot).root = a →
          ∀ wire sr cp, B.blocks.open_ a = some (wire, sr) →
            B.committedState wire.parent_root = some cp →
            ∀ r ∈ blockVotes B.setup cp wire, r ∈ vo) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    by_cases hgen : x = B.setup.genesisRoot
    · subst hgen
      have hstop : ∀ y, (get_ancestor store (ForkChoiceNode.mk B.setup.genesisRoot .pending)
          y).root = B.setup.genesisRoot := fun y => by
        rw [get_ancestor_stop (by rw [hs.genesis_slot]; exact Nat.zero_le _)]
      refine ⟨_, [], [], B.committedState_genesis, .genesis, fun y => ?_, by simp, ?_⟩
      · rw [hstop y]; rfl
      · intro a _ hne hanc
        exact absurd ((hstop _).symm.trans hanc).symm hne
    obtain ⟨cs, hcs, -, ⟨-, hH⟩, -, hslot, hrest⟩ := hs.known x hx
    obtain ⟨wire, hwopen, hwroot, hm, hpk, cp, hcp, htrans⟩ := hrest hgen
    obtain ⟨cp', hcp', hslotp, hHp, -⟩ := B.known_witness hs hpk
    rw [hcp] at hcp'
    cases hcp'
    obtain ⟨hwslot, hlt⟩ := state_transition_slot htrans
    have hxslot : (store.blocks x).slot = wire.slot := hm.1
    have hplt : (store.blocks (store.blocks x).parent_root).slot < (store.blocks x).slot := by
      rw [← hslotp, ← hslot, hwslot]; exact hlt
    obtain ⟨cp', bp, vp, hcp', hreachp, hchain, hvotes, hanc⟩ :=
      ih _ (Nat.lt_of_lt_of_le hplt hn) _ hpk le_rfl
    rw [hcp] at hcp'
    cases hcp'
    have hinvp := provenanceInvariant_of_reachable hB.setup hreachp hHp
    have hstep : ∀ y, y < wire.slot →
        (get_ancestor store (ForkChoiceNode.mk x .pending) y).root =
          (get_ancestor store (ForkChoiceNode.mk (store.blocks x).parent_root .pending) y).root :=
      fun y hy => get_ancestor_step hs.parentSlotLt hx (by rw [hxslot]; exact hy)
        (hs.walkKnown y _ _ hpk le_rfl)
    have hself : (get_ancestor store (ForkChoiceNode.mk x .pending) wire.slot).root = x := by
      rw [get_ancestor_stop (by rw [hxslot])]
    refine ⟨cs, bp ++ [wire], vp ++ blockVotes B.setup cp wire, hcs,
      Reachable.block wire hreachp htrans, fun y => ?_, ?_, ?_⟩
    · by_cases hy : y < wire.slot
      · rw [chainRootAt_append_of_lt hy, hchain y, hstep y hy]
      · rw [chainRootAt_of_forall_le, tipRoot_append, hwroot,
          get_ancestor_stop (by rw [hxslot]; exact Nat.le_of_not_lt hy)]
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · have := (hinvp.blocks_le_header b hb).trans hinvp.header_le_slot
          beacon_omega
        · rw [List.mem_singleton.mp hb]; exact Nat.le_of_not_lt hy
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨a, ha, hne, haslot, hpanc, hrestr⟩ := hvotes r hr
        have hrb : r.block.slot < wire.slot := by
          have h1 := (hinvp.blocks_le_header _ (includedVote_provenance hreachp r hr).1).trans
            hinvp.header_le_slot
          rw [hslotp] at h1
          rw [← hxslot]
          exact Nat.lt_of_le_of_lt h1 hplt
        exact ⟨a, ha, hne, haslot, (hstep _ hrb).trans hpanc, hrestr⟩
      · obtain ⟨hrblock, -, -, -⟩ := blockVote_of_transition htrans hr
        rw [hrblock]
        refine ⟨x, hx, hgen, hxslot, hself, B.states.root cs, cp, hwopen, ?_, hr⟩
        rw [← hm.2.1]
        exact hcp
    · intro a ha hne hanca wire' sr cp'' hopen hcp'' r hr
      by_cases hle : wire.slot ≤ (store.blocks a).slot
      · have hax : a = x := by
          rw [get_ancestor_stop (by rw [hxslot]; exact hle)] at hanca
          exact hanca.symm
        subst hax
        rw [hwopen] at hopen
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hopen)
        rw [← hm.2.1, hcp] at hcp''
        cases hcp''
        exact List.mem_append_right _ hr
      · rw [hstep _ (Nat.lt_of_not_le hle)] at hanca
        exact List.mem_append_left _ (hanc a ha hne hanca wire' sr cp'' hopen hcp'' r hr)

/-! ### Execution descent of store ancestors -/

/-- A store ancestor of a known root of an exact prefix store is an execution
ancestor. -/
theorem descends_ancestor (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store)
    {x : Root} (hx : x ∈ store.block_roots) (y : Slot) :
    E.RootDescends x (get_ancestor store (ForkChoiceNode.mk x .pending) y).root := by
  have hs := B.bridgedStore_prefix hB hg hstore
  have hprov := Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.interface E hstore
  obtain ⟨-, hay⟩ := get_ancestor_spec hs.parentSlotLt (hs.walkKnown y _ x hx le_rfl)
  apply E.rootDescends_of_getAncestor hprov hs.parentSlotLt (hs.walkKnown _ _ x hx le_rfl)
  rw [← get_ancestor_comp_root hs.parentSlotLt hay (hs.walkKnown _ _ x hx le_rfl),
    get_ancestor_stop le_rfl]

/-- Store ancestors at an earlier slot descend from store ancestors at a later
slot. -/
theorem descends_ancestors (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store)
    {x : Root} (hx : x ∈ store.block_roots) {y y' : Slot} (h : y' ≤ y) :
    E.RootDescends (get_ancestor store (ForkChoiceNode.mk x .pending) y).root
      (get_ancestor store (ForkChoiceNode.mk x .pending) y').root := by
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨ht, -⟩ := get_ancestor_spec hs.parentSlotLt (hs.walkKnown y _ x hx le_rfl)
  rw [← get_ancestor_comp_root hs.parentSlotLt h (hs.walkKnown _ _ x hx le_rfl)]
  exact B.descends_ancestor hB hg hstore ht y'

omit [Inhabited Root] in
/-- The genesis root is the store ancestor at slot zero. -/
theorem ancestor_zero {store : Store Root} (hs : B.BridgedStore store) {x : Root}
    (hx : x ∈ store.block_roots) :
    (get_ancestor store (ForkChoiceNode.mk x .pending) 0).root = B.setup.genesisRoot := by
  obtain ⟨ha, hslot⟩ := get_ancestor_spec hs.parentSlotLt (hs.walkKnown 0 _ x hx le_rfl)
  exact hs.slot_zero ha hslot

omit [Inhabited Root] in
/-- The root of the anchor reading of an on-chain checkpoint is the store
ancestor at its epoch start. -/
theorem readAsAnchor_root {store : Store Root} (hs : B.BridgedStore store) {x : Root}
    (hx : x ∈ store.block_roots) {bl : List (FFGWireBlock Root)}
    (hchain : ∀ y, chainRootAt B.setup.genesisRoot bl y =
      (get_ancestor store (ForkChoiceNode.mk x .pending) y).root)
    {j : Checkpoint Root} (hj : OnChain B.setup bl j) :
    (B.readAsAnchor j).root = (get_ancestor store (ForkChoiceNode.mk x .pending)
      (compute_start_slot_at_epoch B.setup.cfg (B.readAsAnchor j).epoch)).root := by
  rcases B.readAsAnchor_onChain hj with h | h
  · rw [h]
    change B.setup.genesisRoot = (get_ancestor store _ (0 * B.setup.cfg.slots_per_epoch)).root
    rw [Nat.zero_mul, B.ancestor_zero hs hx]
  · conv_lhs => rw [h]
    exact hchain _

omit [LinearOrder Root] [Inhabited Root] in
/-- The first and last slots of an in-scope epoch are in the horizon. -/
theorem span_within (hB : B.Admissible) {E : Execution Root}
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1) {t : Epoch}
    (ht : t ≤ B.setup.scope.last_epoch) :
    E.SlotWithinHorizon B.setup.cfg (t * B.setup.cfg.slots_per_epoch) ∧
      E.SlotWithinHorizon B.setup.cfg
        (t * B.setup.cfg.slots_per_epoch + (B.setup.cfg.slots_per_epoch - 1)) := by
  have hspe := B.setup.cfg.slots_per_epoch_pos
  have hlast : t * B.setup.cfg.slots_per_epoch + (B.setup.cfg.slots_per_epoch - 1) <
      (B.setup.scope.last_epoch + 1) * B.setup.cfg.slots_per_epoch := by
    have := Nat.mul_le_mul_right B.setup.cfg.slots_per_epoch (Nat.add_le_add_right ht 1)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.sub_lt hspe Nat.one_pos) _) this
  have hnum := hB.numeric
  have hmax : (B.setup.scope.last_epoch + 1) * B.setup.cfg.slots_per_epoch ≤ UINT64_MAX :=
    (Nat.le_add_right _ _).trans hnum
  have hep : ∀ k, k < B.setup.cfg.slots_per_epoch →
      compute_epoch_at_slot B.setup.cfg (t * B.setup.cfg.slots_per_epoch + k) = t := by
    intro k hk
    unfold compute_epoch_at_slot
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hspe, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hle : t * B.setup.cfg.slots_per_epoch + (B.setup.cfg.slots_per_epoch - 1) ≤
      UINT64_MAX := (Nat.le_of_lt hlast).trans hmax
  refine ⟨⟨(Nat.le_add_right _ _).trans hle, ?_⟩, ⟨hle, ?_⟩⟩
  · have := hep 0 hspe
    rw [Nat.add_zero] at this
    rw [this, hscope]
    exact Nat.lt_succ_of_le ht
  · rw [hep _ (by omega), hscope]
    exact Nat.lt_succ_of_le ht

/-! ### The chain run of an accepted block -/

/-- The committed chain run of a known root: a reachable in-scope run of its
committed state whose block list is the store ancestor walk and whose votes
are the body votes of the store ancestors. -/
structure ChainRun (store : Store Root) (x : Root) (cs : FFGBeaconState Root)
    (bl : List (FFGWireBlock Root)) (vo : List (IncludedVote Root)) : Prop where
  committed : B.committedState x = some cs
  reachable : Reachable B.setup bl vo cs
  in_scope : compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch
  slot_eq : cs.slot = (store.blocks x).slot
  chain : ∀ y, chainRootAt B.setup.genesisRoot bl y =
    (get_ancestor store (ForkChoiceNode.mk x .pending) y).root
  votes_of : ∀ r ∈ vo, ∃ a ∈ store.block_roots, a ≠ B.setup.genesisRoot ∧
    (store.blocks a).slot = r.block.slot ∧
    (get_ancestor store (ForkChoiceNode.mk x .pending) r.block.slot).root = a ∧
    ∃ sr cp, B.blocks.open_ a = some (r.block, sr) ∧
      B.committedState r.block.parent_root = some cp ∧ r ∈ blockVotes B.setup cp r.block
  votes_complete : ∀ a ∈ store.block_roots, a ≠ B.setup.genesisRoot →
    (get_ancestor store (ForkChoiceNode.mk x .pending) (store.blocks a).slot).root = a →
    ∀ wire sr cp, B.blocks.open_ a = some (wire, sr) →
      B.committedState wire.parent_root = some cp →
      ∀ r ∈ blockVotes B.setup cp wire, r ∈ vo

omit [Inhabited Root] in
theorem chainRun_of_known (hB : B.Admissible) {store : Store Root} (hs : B.BridgedStore store)
    {x : Root} (hx : x ∈ store.block_roots) : ∃ cs bl vo, B.ChainRun store x cs bl vo := by
  obtain ⟨cs, bl, vo, hcs, hreach, hchain, hvotes, hanc⟩ := B.chain_votes hB hs _ x hx le_rfl
  obtain ⟨cs', hcs', hslot, hH, -⟩ := B.known_witness hs hx
  rw [hcs] at hcs'
  cases hcs'
  exact ⟨cs, bl, vo, ⟨hcs, hreach, hH, hslot, hchain, hvotes, hanc⟩⟩

omit [LinearOrder Root] [Inhabited Root] in
theorem readAsAnchor_stub : B.readAsAnchor B.setup.stub = B.anchorCheckpoint := by
  unfold readAsAnchor
  simp [FFGSetup.stub, GENESIS_EPOCH]

omit [LinearOrder Root] [Inhabited Root] in
theorem readAsAnchor_of_ne {c : Checkpoint Root} (h : c.epoch ≠ GENESIS_EPOCH) :
    B.readAsAnchor c = c := by
  unfold readAsAnchor
  simp [h]

/-! ### Included links and certificates -/

/-- **Link translation.** A supermajority link of the chain run of an accepted
block, from a justified source, is an included supermajority link on the
block between the anchor readings of its endpoints. -/
theorem includedLink (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store)
    {x : Root} (hx : x ∈ store.block_roots) {cs : FFGBeaconState Root}
    {bl : List (FFGWireBlock Root)} {vo : List (IncludedVote Root)}
    (hrun : B.ChainRun store x cs bl vo) {source target : Checkpoint Root}
    (hsource : Justified B.setup vo source) (link : SupermajorityLink B.setup vo source target) :
    Nonempty (IncludedSupermajorityLink B.setup.cfg E (B.TargetIncludedAt E) x
      (B.readAsAnchor source) (B.readAsAnchor target)) := by
  have hs := B.bridgedStore_prefix hB hg hstore
  have hinv := provenanceInvariant_of_reachable hB.setup hrun.reachable hrun.in_scope
  have hread_t : B.readAsAnchor target = target := by
    apply B.readAsAnchor_of_ne
    change target.epoch ≠ 0
    exact Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) link.source_before_target)
  obtain ⟨i0, hi0⟩ := link.signers_nonempty hB.setup
  obtain ⟨r0, hr0, -, -, ht0⟩ := link.signer_vote i0 hi0
  have htle : target.epoch ≤ B.setup.scope.last_epoch := by
    rw [← ht0]
    exact (hinv.target_epoch_le r0 hr0.1).trans hrun.in_scope
  have hsig : ∀ i ∈ link.signers, ∃ r, TargetIncluded B.setup vo r ∧ i ∈ r.attesters B.setup ∧
      r.vote.data.source = source ∧ r.vote.data.target = target ∧
      ∃ a, E.RootDescends x a ∧ B.TargetIncludedAt E a (B.indexed r.vote) := by
    intro i hi
    obtain ⟨r, hr, hri, hsrc, htgt⟩ := link.signer_vote i hi
    obtain ⟨a, ha, hne, -, hanc, sr, cp, hopen, hcp, hmem⟩ := hrun.votes_of r hr.1
    refine ⟨r, hr, hri, hsrc, htgt, a, ?_,
      r, ⟨⟨store, hstore, ha⟩, hne, r.block, sr, cp, hopen, hcp, hmem⟩, rfl, hr.2⟩
    rw [← hanc]
    exact B.descends_ancestor hB hg hstore hx _
  have hmemA : ∀ (r : IncludedVote Root) (i : ValidatorIndex), i ∈ r.attesters B.setup →
      i ∈ (B.indexed r.vote).attesting_indices := by
    intro r i hri
    simpa [indexed, get_indexed_attestation, IncludedVote.attesters] using hri
  refine ⟨{ signers := link.signers
            source_before_target := ?_
            target_descends_source := ?_
            target_epoch_within := ?_
            target_span_within := ?_
            signers_in_epoch := ?_
            signer_attestation := ?_
            supermajority := ?_ }⟩
  · rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch]
    exact link.source_before_target
  · have hjt := onChain_of_justified hB.setup hrun.reachable hrun.in_scope (.link hsource link)
    have hjs := onChain_of_justified hB.setup hrun.reachable hrun.in_scope hsource
    rw [B.readAsAnchor_root hs hx hrun.chain hjt, B.readAsAnchor_root hs hx hrun.chain hjs]
    apply B.descends_ancestors hB hg hstore hx
    rw [B.readAsAnchor_epoch, B.readAsAnchor_epoch]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt link.source_before_target)
  · rw [hread_t, hscope]
    exact Nat.lt_succ_of_le htle
  · rw [hread_t]
    exact B.span_within hB hscope htle
  · intro i hi
    obtain ⟨r, -, hri, -, htgt, a, -, hTI⟩ := hsig i hi
    obtain ⟨-, -, -, -, -, htep, hcommittee⟩ :=
      B.targetIncludedAt_evidence hB hg hscope hcomm hdel hTI
    have hmem := hcommittee i (hmemA r i hri)
    change r.vote.data.target.epoch = compute_epoch_at_slot B.setup.cfg r.vote.data.slot at htep
    rw [htgt] at htep
    rw [hread_t]
    unfold Execution.span_committee
    rw [Finset.mem_biUnion]
    refine ⟨r.vote.data.slot, Finset.mem_Icc.mpr ?_, hmem⟩
    have := slot_mem_epoch (cfg := B.setup.cfg) r.vote.data.slot
    rw [← htep] at this
    beacon_omega
  · intro i hi
    obtain ⟨r, -, hri, hsrc, htgt, a, hdesc, hTI⟩ := hsig i hi
    refine ⟨B.indexed r.vote, ⟨a, hdesc, hTI⟩, hmemA r i hri, ?_, ?_⟩
    · change CheckpointReadsAs r.vote.data.source (B.readAsAnchor source)
      rw [hsrc]
      exact B.readsAs_readAsAnchor source
    · change r.vote.data.target = _
      rw [htgt, hread_t]
  · rw [B.total_active_eq hB hg, B.weight_eq hg]
    exact link.supermajority

/-- **Certificate translation.** A checkpoint justified in the chain run of an
accepted block has an included justification certificate on the block for
its anchor reading. -/
theorem includedCertified (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hscope : E.verification_horizon = B.setup.scope.last_epoch + 1)
    (hcomm : B.FixedCommittees E) (hdel : B.BodyAttestationsDelivered E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.interface store)
    {x : Root} (hx : x ∈ store.block_roots) {cs : FFGBeaconState Root}
    {bl : List (FFGWireBlock Root)} {vo : List (IncludedVote Root)}
    (hrun : B.ChainRun store x cs bl vo) {j : Checkpoint Root} (hj : Justified B.setup vo j) :
    IncludedCertifiedJustified B.setup.cfg E (B.TargetIncludedAt E) B.anchorCheckpoint x
      (B.readAsAnchor j) := by
  induction hj with
  | anchor =>
    rw [B.readAsAnchor_stub]
    exact .anchor
  | link hsrc link ih =>
    exact .link ih (B.includedLink hB hg hscope hcomm hdel hstore hx hrun hsrc link).some

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
