module
public import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
public import FastConfirmation.Spec.Proof.CurrentTargetCertificateRealization
public import FastConfirmation.Spec.Proof.PaperA32SupportRealization
public import FastConfirmation.Spec.Proof.ActualResetCheckpointRealization
public import FastConfirmation.Spec.Proof.HistoricalCurrentTargetTrajectory

@[expose] public section

/-!
# Assumption 3.2 at actual calls

This module proves the current-epoch part of the actual-call bridge.  The
global-UJ-only analysis below still exposes the placement fact that cannot be
derived from a global carrier, but the executable arithmetic gate does not
need that route: a non-anchor target, including a non-anchor UJ target,
reconstructs the concrete fixed-source quorum.  Thus the actual direct call
requires no separate placement premise, and this module adds neither a producer nor an
assumption.

For a selected block in the query's current epoch, the selected induction
window covers all of the following epoch.  Synchrony supplies block knownness,
so the paper's full canonicity antecedent follows.  In the concrete-quorum
branch, the gate's fixed-source quorum then supplies the complete support
antecedent.

In the equality branch, the global unrealized-justified trajectory supplies
an AU carrier.  If the checkpoint is the trusted anchor, the selected block
itself is an early carrier.  Otherwise every required early-carrier field is
derived except that the trajectory carrier need not descend from the later
selected block; it may only descend from the selected epoch-boundary
checkpoint.  `SelectedEarlyA32PlacementResidualAt` records exactly this
remaining placement condition rather than hiding it behind a producer premise.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Exact remaining placement condition in the early-UJ branch.  All query-local carrier fields are
present, including AU provenance and descent from the selected checkpoint
root.  The only unavailable field is descent from the later selected block. -/
def SelectedEarlyA32PlacementResidualAt
    (anchor : Checkpoint Root) (S : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ) (selected : Root)
    (baseEpoch : Epoch) : Prop :=
  ∃ carrier : Root,
    carrier ∈ (E.store cfg ext v q).block_roots ∧
    E.RootDescends carrier (S.C selected baseEpoch).root ∧
    get_block_epoch cfg (E.store cfg ext v q) carrier < baseEpoch + 2 ∧
    S.AU cfg carrier (S.C selected baseEpoch) ∧
    ¬ E.RootDescends carrier selected

/-- A current-epoch selected block identifies the executable current target
with the common semantic checkpoint `C(selected,e)`. -/
theorem currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor
    (hA : SelectedMarginAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q)) :
    get_current_target cfg (E.store cfg ext v q) = S.C selected e := by
  have hA0 := hA.toNoConflictPinningAssumptions cfg ext
  have hboundary' : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := anchor) := by
    simpa only [hanchor] using hboundary
  have hanchorLeCurrent :=
    E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary' v q
  have hanchorLe : anchor.epoch ≤ e := by
    simpa only [heCurrent] using hanchorLeCurrent
  have hheadKnown : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v q) with hhead | hhead
    · exact hhead
    · rw [hhead]
      exact hA.domain.justified_root_known v hv q hqH
  have hboundaryWalk : WalkKnown (E.store cfg ext v q)
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.store cfg ext v q)))
      (get_head cfg (E.store cfg ext v q)).root := by
    have hwalk := E.walkKnown_epochBoundary_of_anchor_le cfg ext hA0
      hboundary hanchor hheadKnown hanchorLe
    simpa only [heCurrent] using hwalk
  have hparentSlots : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      hA.genesis hA.wellFormed.anchor_parent_unscheduled v q
  have htarget := current_target_eq_checkpoint_of_current_epoch_ancestor cfg
    hparentSlots hheadSelected
      (hselectedEpoch.trans heCurrent) hboundaryWalk
  have hcheckpoint := hcoh.checkpoint_of_known v hv q hqH selected
    hselected e
  calc
    get_current_target cfg (E.store cfg ext v q) =
        get_checkpoint_for_block cfg (E.store cfg ext v q) selected
          (get_block_epoch cfg (E.store cfg ext v q) selected) := htarget
    _ = get_checkpoint_for_block cfg (E.store cfg ext v q) selected e := by
      rw [hselectedEpoch]
    _ = S.C selected e := hcheckpoint.symm

/-- For a current-epoch selected result, the post-query selected induction
window covers the whole next epoch.  Strict epoch separation supplies the
lower and upper timing inequalities, and block relay supplies the knownness
conjunct which `SelectedCanonicalBeforeEndpointAt` intentionally omits. -/
theorem canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m) :
    E.CanonicalThroughoutEpoch cfg ext selected (e + 1) := by
  intro w' hw' m' hm'H hm'Epoch
  have hqEpoch : compute_epoch_at_slot cfg (E.slot_at cfg q) = e := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg q) =
          get_current_store_epoch cfg (E.store cfg ext v q) := by
        simp only [get_current_store_epoch, E.store_current_slot cfg ext v q]
      _ = e := heCurrent.symm
  have hslotLower : E.slot_at cfg q < E.slot_at cfg m' := by
    by_contra hnot
    have hle : E.slot_at cfg m' ≤ E.slot_at cfg q := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m') ≤
      compute_epoch_at_slot cfg (E.slot_at cfg q) at hepochLe
    rw [hm'Epoch, hqEpoch] at hepochLe
    exact (Nat.not_succ_le_self e) (by
      simpa only [Nat.succ_eq_add_one] using hepochLe)
  have hindexLower : E.slot_start cfg (E.slot_at cfg q) ≤ m' :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotLower.le
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext w m]
  have hslotUpper : E.slot_at cfg m' < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg m' := Nat.le_of_not_gt hnot
    have hepochLe := Nat.div_le_div_right
      (c := cfg.slots_per_epoch) hle
    change compute_epoch_at_slot cfg (E.slot_at cfg m) ≤
      compute_epoch_at_slot cfg (E.slot_at cfg m') at hepochLe
    rw [hmEpoch, hm'Epoch] at hepochLe
    have hbad : Nat.succ (e + 1) ≤ e + 1 := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        hlate.trans hepochLe
    exact (Nat.not_succ_le_self (e + 1)) hbad
  have hrelayGate : E.slot_at cfg q + 1 ≤ E.slot_at cfg (m' + 1) :=
    (Nat.succ_le_of_lt hslotLower).trans
      (E.slot_at_mono cfg (Nat.le_succ m'))
  have hknown : selected ∈ (E.store cfg ext w' m').block_roots :=
    hA.synchrony.block_relay v hv q selected hqH hselected
      w' hw' m' hm'H hrelayGate
  exact ⟨hknown, hcanonical w' hw' m' hindexLower hslotUpper hm'H⟩

/-- **The epoch-`e` sibling of the lemma above, in `EngineInv` form.**

`docs/crossing-call-support-residue.md` §2.2/§2.3: the endpoint-filter supply's
own binder `hIH : SelectedCanonicalBeforeEndpointAt q selected m` *is* capped
safety — canonicity of `selected` at every honest endpoint whose slot is below
`slot_at m`.  Under the A1 guard `e + 2 ≤ currentEpoch (store w m)` that cap
strictly dominates `start(e+1)`, which is the whole of the epoch-`e` vote span
the A3.2 quorum consumes.  So the binder converts to `EngineInv` capped at
`start(e+1)` and the capped target-agreement twin
(`honestVotesSupportTarget_of_engineInv_currentEpochCandidate`) then yields the
*uncapped* support predicate.

The arithmetic is the same shape as `hslotUpper` above: an endpoint at or below
`start(e+1)` cannot be at or after an endpoint whose epoch is at least
`e + 2`. -/
theorem engineInv_of_selectedCanonical_lateEndpoint
    (hA : SelectedMarginAssumptions cfg ext E)
    {q : ℕ} {selected : Root} {e : Epoch}
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m) :
    EngineInv cfg ext E selected q
      (compute_start_slot_at_epoch cfg (e + 1)) := by
  -- the late endpoint sits at or after the start of epoch `e + 2`
  have hmEpoch : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot cfg ext w m]
  have hboundary : compute_start_slot_at_epoch cfg (e + 2) ≤
      E.slot_at cfg m := by
    have hepoch : e + 2 ≤ compute_epoch_at_slot cfg (E.slot_at cfg m) := by
      rw [hmEpoch]; exact hlate
    simpa only [compute_start_slot_at_epoch] using
      (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hepoch
  have hstrict : compute_start_slot_at_epoch cfg (e + 1) <
      compute_start_slot_at_epoch cfg (e + 2) := by
    simp only [compute_start_slot_at_epoch]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self (e + 1))
      (le_refl cfg.slots_per_epoch) cfg.slots_per_epoch_pos
  intro w' hw' m' hm' hslotCap hm'H
  refine hcanonical w' hw' m' ?_ ?_ hm'H
  · exact E.query_slot_start_le_of_slot_ge_minimal cfg ext hA
      (E.slot_at_mono cfg hm')
  · exact Nat.lt_of_le_of_lt hslotCap (Nat.lt_of_lt_of_le hstrict hboundary)

/-- If the executable current target is the trusted anchor, a current-epoch
selected block is itself the required early A3.2 carrier.  This is the anchor
arm of the actual gate's anchor-or-quorum split; it does not consult the global
unrealized-checkpoint origin. -/
theorem selectedEarlyA32Carrier_of_currentTarget_eq_anchor
    (hA : SelectedMarginAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    (htargetAnchor : get_current_target cfg (E.store cfg ext v q) = anchor) :
    E.SelectedEarlyA32CarrierAt cfg ext anchor S v q selected e := by
  have htargetC :=
    E.currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor cfg ext hA
      hboundary hcoh hanchor hv hqH hselected hheadSelected
      hselectedEpoch heCurrent
  have hCAnchor : S.C selected e = anchor :=
    htargetC.symm.trans htargetAnchor
  have hanchorEpoch : e = anchor.epoch := by
    have h := congrArg Checkpoint.epoch hCAnchor
    simpa only [S.checkpoint_epoch] using h
  have hselectedAt : E.BlockAt selected
      ((E.store cfg ext v q).blocks selected) :=
    E.blockAt_of_store_known cfg ext hselected
  have hselectedRoot : E.ExecutionRoot selected :=
    ⟨(E.store cfg ext v q).blocks selected, hselectedAt⟩
  have hgjAnchor : S.GJ selected = anchor := by
    rcases S.gj_anchor_or_before hselectedAt with hgj | hbefore
    · exact hgj
    · obtain ⟨hgjCert⟩ := S.certifiedJustified_of_AU cfg
        (S.gj_AU cfg selected hselectedRoot)
      have hanchorLe : anchor.epoch ≤ (S.GJ selected).epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg) hgjCert
      have hblockEpoch : compute_epoch_at_slot cfg
          ((E.store cfg ext v q).blocks selected).slot = e := by
        simpa only [get_block_epoch] using hselectedEpoch
      rw [hblockEpoch, hanchorEpoch] at hbefore
      exact False.elim ((Nat.not_lt_of_ge hanchorLe) hbefore)
  have hAUSelected : S.AU cfg selected (S.C selected e) := by
    have hgjC : S.GJ selected = S.C selected e :=
      hgjAnchor.trans hCAnchor.symm
    exact hgjC ▸ S.gj_AU cfg selected hselectedRoot
  have hselectedBefore :
      get_block_epoch cfg (E.store cfg ext v q) selected < e + 2 := by
    rw [hselectedEpoch]
    exact Nat.lt_add_of_pos_right (by decide)
  exact ⟨selected, hselected, RootDescends.refl selected,
    hselectedBefore, hAUSelected⟩

/-- In the equality branch, concrete global-UJ history either produces the
required selected carrier or exposes one concrete carrier for which the only
additional fact needed is `RootDescends carrier selected`. -/
theorem selectedEarlyA32Carrier_or_placementResidual_of_currentTarget_eq_unrealized
    (hA : SelectedMarginAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    (hequality : get_current_target cfg (E.store cfg ext v q) =
      (E.store cfg ext v q).unrealized_justified_checkpoint) :
    E.SelectedEarlyA32CarrierAt cfg ext anchor S v q selected e ∨
      E.SelectedEarlyA32PlacementResidualAt cfg ext anchor S
        v q selected e := by
  have htargetC :=
    E.currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor cfg ext hA
      hboundary hcoh hanchor hv hqH hselected hheadSelected
      hselectedEpoch heCurrent
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot := ⟨ast, ablk, hgenEq, hgenSlot⟩
  have hCeqUJ : S.C selected e =
      (E.store cfg ext v q).unrealized_justified_checkpoint :=
    htargetC.symm.trans hequality
  rcases E.globalUnrealizedJustified_anchor_or_known_AU cfg ext hcoh
      hgen hanchor v q with hUJAnchor | ⟨carrier, hcarrier, hAU⟩
  · have hCAnchor : S.C selected e = anchor := hCeqUJ.trans hUJAnchor
    have hanchorEpoch : e = anchor.epoch := by
      have h := congrArg Checkpoint.epoch hCAnchor
      simpa only [S.checkpoint_epoch] using h
    have hselectedAt : E.BlockAt selected
        ((E.store cfg ext v q).blocks selected) :=
      E.blockAt_of_store_known cfg ext hselected
    have hselectedRoot : E.ExecutionRoot selected :=
      ⟨(E.store cfg ext v q).blocks selected, hselectedAt⟩
    have hgjAnchor : S.GJ selected = anchor := by
      rcases S.gj_anchor_or_before hselectedAt with hgj | hbefore
      · exact hgj
      · obtain ⟨hgjCert⟩ := S.certifiedJustified_of_AU cfg
          (S.gj_AU cfg selected hselectedRoot)
        have hanchorLe : anchor.epoch ≤ (S.GJ selected).epoch :=
          CertifiedJustified.anchor_epoch_le (cfg := cfg) hgjCert
        have hblockEpoch : compute_epoch_at_slot cfg
            ((E.store cfg ext v q).blocks selected).slot = e := by
          simpa only [get_block_epoch] using hselectedEpoch
        rw [hblockEpoch, hanchorEpoch] at hbefore
        exact False.elim ((Nat.not_lt_of_ge hanchorLe) hbefore)
    have hAUSelected : S.AU cfg selected (S.C selected e) := by
      have hgjC : S.GJ selected = S.C selected e :=
        hgjAnchor.trans hCAnchor.symm
      exact hgjC ▸ S.gj_AU cfg selected hselectedRoot
    have hselectedBefore :
        get_block_epoch cfg (E.store cfg ext v q) selected < e + 2 := by
      rw [hselectedEpoch]
      exact Nat.lt_add_of_pos_right (by decide)
    exact Or.inl ⟨selected, hselected, RootDescends.refl selected,
      hselectedBefore, hAUSelected⟩
  · have hAUC : S.AU cfg carrier (S.C selected e) := by
      rw [hCeqUJ]
      exact hAU
    have hcheckpointOnChain : E.RootDescends carrier
        (S.C selected e).root := by
      obtain ⟨formedAt, hcarrierFormed, hevidence⟩ :=
        ChainFFGState.AU.evidence (cfg := cfg) S hAUC
      exact Execution.RootDescends.trans E hcarrierFormed hevidence.on_chain
    have hcarrierSlotLe :
        ((E.store cfg ext v q).blocks carrier).slot ≤
          get_current_slot cfg (E.store cfg ext v q) :=
      E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgen
        v q carrier hcarrier
    have hcarrierEpochLe :
        get_block_epoch cfg (E.store cfg ext v q) carrier ≤ e := by
      have hle := ce_mono cfg hcarrierSlotLe
      change get_block_epoch cfg (E.store cfg ext v q) carrier ≤
        get_current_store_epoch cfg (E.store cfg ext v q) at hle
      rw [← heCurrent] at hle
      exact hle
    have hcarrierBefore :
        get_block_epoch cfg (E.store cfg ext v q) carrier < e + 2 := by
      exact hcarrierEpochLe.trans_lt
        (Nat.lt_add_of_pos_right (by decide))
    by_cases habove : E.RootDescends carrier selected
    · exact Or.inl ⟨carrier, hcarrier, habove, hcarrierBefore, hAUC⟩
    · exact Or.inr ⟨carrier, hcarrier, hcheckpointOnChain,
        hcarrierBefore, hAUC, habove⟩

/-- Complete current-epoch reduction of the refactored fixed-source gate.
The anchor arm uses the selected block itself as an early carrier.  Every
non-anchor arm, including equality with a non-anchor global UJ checkpoint,
contains the concrete fixed-source quorum and hence supplies the full paper
A3.2 antecedent. -/
theorem selectedA32Semantic_of_fixedSourceGate_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m)
    (hgate : E.FixedSourceCurrentTargetA32GateRealization cfg ext
      anchor S (E.store cfg ext v q) selected) :
    E.SelectedA32SemanticRealizationAt cfg ext anchor S
      v q selected e := by
  have htargetC :=
    E.currentTarget_eq_selectedCheckpoint_of_currentEpochAncestor cfg ext hA
      hboundary hcoh hanchor hv hqH hselected hheadSelected
      hselectedEpoch heCurrent
  have hbranch := hgate.support_branch
  rw [htargetC] at hbranch
  have hCEpoch : (S.C selected e).epoch = e := S.checkpoint_epoch selected e
  rw [hCEpoch] at hbranch
  rcases hbranch with hCAnchor | ⟨_hne, Q, hsource⟩
  · have htargetAnchor : get_current_target cfg
        (E.store cfg ext v q) = anchor := htargetC.trans hCAnchor
    exact Or.inl
      (E.selectedEarlyA32Carrier_of_currentTarget_eq_anchor cfg ext hA
        hboundary hcoh hanchor hv hqH hselected hheadSelected
        hselectedEpoch heCurrent htargetAnchor)
  · have hcanonicalFull :=
      E.canonicalThroughoutNextEpoch_of_selectedCanonical_currentEpoch
        cfg ext hA hv hqH hselected heCurrent hlate hcanonical
    have hsupport := E.paperA32SupportThroughoutEpoch_of_concreteQuorum
      cfg ext hA.wellFormed hA.honest_behavior hA.synchrony
      hA.externals_coherence hA.whole_seconds hA.genesis hwalkDomain
      hv hqH hselected hselectedEpoch hcanonicalFull Q hsource
    exact Or.inr ⟨hcanonicalFull, hsupport⟩

/-- End-to-end current-epoch actual-call bridge.  The only call-site inputs are
the executable boolean and its normative honest-target-support proviso; the
signer set, concrete votes, common source, certificate, and anchor-or-quorum
split are all reconstructed by the state-semantics producer. -/
theorem selectedA32Semantic_of_actualCurrentTargetGate_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hboundaryPhase : Phase0BoundarySourceCoherence cfg ext)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {state : BeaconState Root}
    (hstate : state = get_pulled_up_head_state cfg ext query.store)
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg query.store))
    (hnextH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg
        ((get_current_target cfg query.store).epoch + 1))))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m)
    (hgate : will_current_target_be_justified cfg ext query.store = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg query.store) q) :
    E.SelectedA32SemanticRealizationAt cfg ext anchor S
      v q selected e := by
  have hselectedQ : selected ∈ query.store.block_roots := by
    simpa only [hquery] using hselected
  have hheadSelectedQ : is_ancestor query.store
      (get_head cfg query.store) (get_node_for_root selected) = true := by
    simpa only [hquery] using hheadSelected
  have hselectedCurrentQ : get_block_epoch cfg query.store selected =
      get_current_store_epoch cfg query.store := by
    simpa only [hquery] using hselectedEpoch.trans heCurrent
  have hfixedQ :=
    (E.fixedSourceCurrentTargetA32GateRealizationProducerAt_of_stateSemantics
      cfg ext (hA.toNoConflictPinningAssumptions cfg ext) hA.synchrony
      hboundary hcoh hhistory hphase hboundaryPhase hanchor hv hqH hquery
      hstate hval htab hendH hnextH hanchorH hfloor hselectedQ
      hheadSelectedQ hselectedCurrentQ) hgate hsupport
  have hfixed : E.FixedSourceCurrentTargetA32GateRealization cfg ext
      anchor S (E.store cfg ext v q) selected := by
    simpa only [hquery] using hfixedQ
  exact E.selectedA32Semantic_of_fixedSourceGate_currentEpoch cfg ext hA
    hwalkDomain hboundary hcoh hanchor hv hqH hselected hheadSelected
    hselectedEpoch heCurrent hlate hcanonical hfixed

/-- Weaker disjunctive form for the global-UJ-only analysis. The fixed-source
gate theorem above always discharges the left side. -/
theorem selectedA32Semantic_or_placementResidual_of_fixedSourceGate_currentEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {selected : Root} {e : Epoch}
    (hselected : selected ∈ (E.store cfg ext v q).block_roots)
    (hheadSelected : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q))
      (get_node_for_root selected) = true)
    (hselectedEpoch :
      get_block_epoch cfg (E.store cfg ext v q) selected = e)
    (heCurrent :
      e = get_current_store_epoch cfg (E.store cfg ext v q))
    {w : ValidatorIndex} {m : ℕ}
    (hlate : e + 2 ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hcanonical : E.SelectedCanonicalBeforeEndpointAt cfg ext q selected m)
    (hgate : E.FixedSourceCurrentTargetA32GateRealization cfg ext
      anchor S (E.store cfg ext v q) selected) :
    E.SelectedA32SemanticRealizationAt cfg ext anchor S
        v q selected e ∨
      E.SelectedEarlyA32PlacementResidualAt cfg ext anchor S
        v q selected e := by
  exact Or.inl
    (E.selectedA32Semantic_of_fixedSourceGate_currentEpoch cfg ext hA
      hwalkDomain hboundary hcoh hanchor hv hqH hselected hheadSelected
      hselectedEpoch heCurrent hlate hcanonical hgate)

end Execution

end FastConfirmation.Spec

end
