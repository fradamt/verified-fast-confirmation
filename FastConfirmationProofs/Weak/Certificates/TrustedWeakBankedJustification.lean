module
public import FastConfirmationProofs.Weak.Certificates.WeakBankedJustification
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {trusted : Store Root → Prop}

private theorem trusted_unrealizedJustified_anchor_or_AUEvidence {E : Execution Root}
    {anchor : Checkpoint Root} {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {store : Store Root} (h : TrustedAcceptedFFGGlobalCheckpointOrigins S store) :
    store.unrealized_justified_checkpoint = anchor ∨
      TrustedAcceptedSelectorAUEvidence S store store.unrealized_justified_checkpoint := by
  rcases h.unrealized_justified with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · right
    apply TrustedAcceptedSelectorAUEvidence.of_AU hr
    rw [hgu]
    exact S.gu_mem _ hr.acceptedRoot

/-- **The boundary walk of an accepted AU tip, at a possibly-Byzantine
observer.** The tip's chain is known all the way down to the first slot of the
checkpoint's epoch: the trusted anchor is a known block at or below that
boundary (`TrustedAnchorBoundaryAligned` plus `anchor.epoch ≤ c.epoch`, which
the accepted formation evidence certifies), and `store_walkKnownK` walks any
known root down to any known block's slot. This is the step every consumer of
`TrustedAcceptedSelectorAUCarrier.checkpointRoot_known` has to supply; factored out
here so the knownness and the ancestry consumers share it. -/
private theorem trusted_auTip_walkKnown
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [Execution.TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  obtain ⟨carr, _hdesc, hformed⟩ := hAU
  obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
  have hcertified : CertifiedJustified cfg E B.anchor c :=
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      B.state.includedAttestations.relation hincluded
  have hanchorEpochLe : B.anchor.epoch ≤ c.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
  have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
      compute_start_slot_at_epoch cfg c.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks B.anchor.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
      B.anchor.root hanchorMem tip htip
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary'.trans hstartLe

/-- **Accepted-origin checkpoint roots are known in the observer's own
store.** The observer-side restatement of the knownness half of
`AcceptedCurrentTargetLowerContracts.justifiedRootKnown_of_acceptedGlobalTrajectory`,
generalized from the store's justified checkpoint to *any* checkpoint with an
accepted origin at that store. -/
theorem trusted_acceptedOriginRoot_known_at_observer
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {c : Checkpoint Root}
    (horigin : c = B.anchor ∨
      TrustedAcceptedSelectorAUEvidence B.state (E.store cfg ext obs n) c) :
    c.root ∈ (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  rcases horigin with hcAnchor | hevidence
  · rw [hcAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots
      (Weak.trusted_auTip_walkKnown cfg ext B hT hanchor hboundary obs n
        carrier.tip_carrier.known carrier.au)

/-- **The observer's own unrealized-justified root is known in its own
store.** `trusted_acceptedOriginRoot_known_at_observer` at the store-global
unrealized-justified field, whose accepted origin is
`trusted_unrealizedJustified_anchor_or_AUEvidence`. -/
theorem trusted_unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).unrealized_justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  exact Weak.trusted_acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (trusted_unrealizedJustified_anchor_or_AUEvidence cfg ext
      ((B.causalStoreGlobalProjection ⟨ast, ablk, hgenEq, hslot⟩ hanchor
        (E.store_causal cfg ext obs n)).storeGlobal))

/-- **The observer's own justified root is known in its own store.**
`trusted_acceptedOriginRoot_known_at_observer` at the store-global justified field. -/
theorem trusted_justifiedRoot_known_at_observer
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis_structure
  exact Weak.trusted_acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (B.globalJustified_anchor_or_AUEvidence ⟨ast, ablk, hgenEq, hslot⟩ hanchor
      (E.store_causal cfg ext obs n))

/-- **The observer's own fork-choice head is a known block.** `get_head`'s
GHOST descent either lands on a block of the filtered tree or degenerates to
the justified root; both are known in the observer's own store, the latter by
`trusted_justifiedRoot_known_at_observer`. This is `supplier_known` for the revised
rule delta 5. -/
theorem trusted_head_known_at_observer
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (get_head cfg (E.store cfg ext obs n)).root ∈ (E.store cfg ext obs n).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext obs n) with hmem | heq
  · exact hmem
  · rw [heq]
    exact Weak.trusted_justifiedRoot_known_at_observer cfg ext B hT hanchor hboundary obs n

/-! ### The chain-intrinsic ancestry of an accepted AU checkpoint -/

/-- **An accepted AU checkpoint sits on its tip's own chain.** The accepted
bundle's `au_checkpoint_of_known` (causal-store quantified, honesty-free)
identifies the checkpoint's root with `get_checkpoint_block store tip c.epoch`,
i.e. with the block the store's own ancestor walk from `tip` lands on at the
first slot of `c.epoch`. Knownness is then `get_ancestor_spec` (this is
`TrustedAcceptedSelectorAUCarrier.checkpointRoot_known`), and ancestry is the walk
composition that knownness proof derives and discards: walking from `tip` down
to the landed block's own slot lands on that block, which is precisely
`is_ancestor`.

This is the lemma that makes the revised rule delta 5 work — with the banked
value read out of the head's own `unrealized_justifications` entry, coverage of
the banked root by the head certificate is a consequence of the FFG contracts,
not an extra hypothesis. -/
theorem trusted_auCheckpoint_known_and_below_tip
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) :
    c.root ∈ (E.store cfg ext obs n).block_roots ∧
      is_ancestor (E.store cfg ext obs n) (get_node_for_root tip)
        (get_node_for_root c.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  have hwalk : WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip :=
    Weak.trusted_auTip_walkKnown cfg ext B hT hanchor hboundary obs n htip hAU
  have hcheckpoint := B.coherence.au_checkpoint_of_known hstore tip htip c hAU
  have hroot : c.root = (get_ancestor (E.store cfg ext obs n)
      (ForkChoiceNode.mk tip .pending) (compute_start_slot_at_epoch cfg c.epoch)).root := by
    have hr := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block, get_checkpoint_block] using hr
  obtain ⟨hknown, hslotLe⟩ := get_ancestor_spec hparentSlots hwalk
  have hcKnown : c.root ∈ (E.store cfg ext obs n).block_roots := by
    rw [hroot]; exact hknown
  have hcSlot : ((E.store cfg ext obs n).blocks c.root).slot ≤
      compute_start_slot_at_epoch cfg c.epoch := by
    rw [hroot]; exact hslotLe
  have hback : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks c.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n c.root hcKnown tip htip
  have hcomp := get_ancestor_comp_root hparentSlots hcSlot hback
  rw [← hroot, get_ancestor_stop (le_refl _)] at hcomp
  refine ⟨hcKnown, ?_⟩
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
  exact hcomp.symm

/-- A known block's own unrealized justification is known and lies on its
ancestry. This applies to the selected certified carrier as well as the actual
fork-choice head. No observer-honesty assumption is used. -/
theorem trusted_blockUnrealizedJustification_known_and_below
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) (supplier : Root)
    (hhead : supplier ∈ (E.store cfg ext obs n).block_roots) :
    ((E.store cfg ext obs n).unrealized_justifications
        supplier).root ∈
      (E.store cfg ext obs n).block_roots ∧
      is_ancestor (E.store cfg ext obs n)
        (get_node_for_root supplier)
        (get_node_for_root ((E.store cfg ext obs n).unrealized_justifications
          supplier).root) = true := by
  have hgu : (E.store cfg ext obs n).unrealized_justifications
      supplier =
      B.state.GU supplier :=
    E.trusted_accepted_unrealized_justification_eq
      B.coherence.toTrustedFFGSelectorsMatchBeaconStates obs n hhead
  have hAU : B.state.AU cfg ext supplier
      ((E.store cfg ext obs n).unrealized_justifications
        supplier) := by
    rw [hgu]
    exact B.state.gu_mem _
      (E.acceptedRoot_of_causal_known cfg ext (E.store_causal cfg ext obs n) hhead)
  exact Weak.trusted_auCheckpoint_known_and_below_tip cfg ext B hT hanchor hboundary obs n
    hhead hAU

/-! ### The fork-choice reduction, retained

No longer on rule delta 5's path (the revised rule's coverage is intrinsic to
the head's own `unrealized_justifications` entry), but a true and reusable
fork-choice fact at a possibly-Byzantine observer: anything on the store's
*justified* root's chain is on the head's chain. -/

/-- **`get_head` descends from the store's justified root.** `get_head` starts
its GHOST descent at `store.justified_checkpoint.root` and only ever steps into
the filtered block tree rooted there, so any block on the justified root's
chain is on the head's chain (`E5Filter.head_ge_of_justified_ge_K`). All three
of that lemma's domain conditions are node-generic and hold at the (possibly
Byzantine) observer: `store_parentSlotLt`, `store_walkKnownK`, and
`trusted_justifiedRoot_known_at_observer` above. -/
theorem trusted_bankedBelowHead_of_bankedBelowJustified
    {E : Execution Root} (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {b : Root}
    (hb : b ∈ (E.store cfg ext obs n).block_roots)
    (hjb : is_ancestor (E.store cfg ext obs n)
      (get_node_for_root (E.store cfg ext obs n).justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext obs n)
      (get_head cfg (E.store cfg ext obs n)) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
  exact head_ge_of_justified_ge_K cfg
    (E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n)
    (E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n)
    (Weak.trusted_justifiedRoot_known_at_observer cfg ext B hT hanchor hboundary obs n)
    hb hjb

/-! ## The input invariant -/


theorem trusted_bankedSupplier_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    h.supplier ∈ (E.store cfg ext w m).block_roots ∧
      fcr_store.current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  -- Unfold the gate to a plain certificate on the supplier.
  have hcert' : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs h.second)
      h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1) = true := by
    have hc := h.certificate
    -- The certificate names the supplier directly.
    exact hc
  -- Same-slot-capable timing: end_slot + 1 = current_slot = E.slot_at second ≤ E.slot_at m.
  have hend1 : get_current_slot cfg (E.store cfg ext obs h.second) - 1 + 1 =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    Nat.sub_add_cancel h.second_pos
  have hslotEq : E.slot_at cfg h.second =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    (E.store_current_slot cfg ext obs h.second).symm
  have htiming : (get_current_slot cfg (E.store cfg ext obs h.second) - 1) + 1 ≤
      E.slot_at cfg m := by
    rw [hend1, ← hslotEq]; exact hgate
  have hsupplier : h.supplier ∈ (E.store cfg ext w m).block_roots :=
    E.certificate_dissemination cfg ext hA.wellFormed hA.honest_behavior hsync
      hA.externals_coherence hA.byzantine_bound hA ⟨ast, ablk, hgeq, hslot, hparent⟩
      obs h.second h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1)
      h.second_within h.start_within h.end_within h.start_anchor
      h.balance_registry h.balance_total (hcomm h.second h.second_within)
      h.supplier_known hcert' w hw m hmH htiming
  -- The chain-intrinsic ancestry: the banked value *is* the supplier's own
  -- unrealized justification, which the accepted contracts place on the
  -- supplier's chain.
  obtain ⟨hbankedKnown, hbelow⟩ :=
    Weak.trusted_blockUnrealizedJustification_known_and_below cfg ext B hT hanchor hboundary
      obs h.second h.supplier h.supplier_known
  rw [← h.banked_eq] at hbankedKnown hbelow
  have hanchorBanked : ablk.message.slot ≤
      ((E.store cfg ext obs h.second).blocks
        fcr_store.current_epoch_observed_justified_checkpoint.root).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence hgeq hslot hparent
      obs h.second fcr_store.current_epoch_observed_justified_checkpoint.root hbankedKnown
  have hbanked : fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence hgeq hslot
      hparent hanchorBanked h.supplier_known hsupplier hbankedKnown hbelow
  exact ⟨hsupplier, hbanked⟩

/-- **The consumption lemma, both arms**: the banked root is known at every
honest endpoint past the gate whether it is the trusted anchor or a certified
installation — no scoping and no side condition on the anchor arm. The anchor
arm needs only `Execution.store_storeLE` from genesis; the certified arm
routes through `trusted_bankedSupplier_known_at_all_honest_endpoints_at_observer`
above (there is no supplier in the anchor arm, so only the banked-root
conjunct is stated here, universally over whichever certificate witnesses the
invariant's second disjunct). -/
theorem trusted_bankedRoot_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : ∀ h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store,
      E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  rcases hinv with hanchorArm | hne
  · exact (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorArm
  · obtain ⟨h⟩ := hne
    exact (Weak.trusted_bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync  hgen hcomm h hw hmH (hgate h)).2


theorem trusted_weakFcr_previousGreatest_known {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) {n m : ℕ} (hnm : n ≤ m) :
    ((E.weakFcr cfg ext obs n
        ).previous_epoch_greatest_unrealized_checkpoint).root ∈
      (E.store cfg ext obs m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  obtain ⟨k, hk, hfield⟩ :=
    Weak.weakFcr_previousGreatest_origin cfg ext ⟨ast, ablk, hgenEq⟩ obs n
  rw [hfield]
  exact (E.store_storeLE cfg ext obs (hk.trans hnm)).1
    (Weak.trusted_unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary obs k)

/-! ### `banked_known`, discharged -/

/-- **`banked_known`, discharged for the whole weak trajectory.** Whatever the
revised rule delta 5 has banked in `current_epoch_observed_justified_checkpoint`
at any second is a known block in the observer's own store at that second — the
initialisation value is the trusted anchor, and every later value is either
carried (`store_storeLE`) or a gate-passing installation of the head's own
unrealized justification, which
`trusted_blockUnrealizedJustification_known_and_below` covers. Proved outright, with no
honesty hypothesis anywhere. -/
theorem trusted_weakFcr_observed_known {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ,
      ((E.weakFcr cfg ext obs n
          ).current_epoch_observed_justified_checkpoint).root ∈
        (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  intro n
  induction n with
  | zero =>
      change E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots
      rw [hgenEq]
      simp only [get_forkchoice_store, List.mem_singleton]
  | succ n ih =>
      by_cases hadv : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (Weak.update_fast_confirmation_variables cfg ext
              { E.weakFcr cfg ext obs n with
                store := E.store cfg ext obs (n + 1) }
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_pos hadv, Weak.on_fast_confirmation]
        rw [hstep, Weak.update_fcv_observed_exact]
        split_ifs
        · exact (Weak.trusted_blockUnrealizedJustification_known_and_below cfg ext B hT
            hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.trusted_head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
        · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (E.weakFcr cfg ext obs n
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_neg hadv]
        rw [hstep]
        exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih

/-- `banked_known` at the speculative query store `E.weakFcrStep`, the shape
the maintenance lemma needs at `second := n + 1`. -/
theorem trusted_weakFcrStep_observed_known {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    ((E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint).root ∈
      (E.store cfg ext obs (n + 1)).block_roots := by
  rw [Execution.weakFcrStep, Weak.update_fcv_observed_exact]
  split_ifs
  · exact (Weak.trusted_blockUnrealizedJustification_known_and_below cfg ext B hT
      hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.trusted_head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
  · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
      (Weak.trusted_weakFcr_observed_known cfg ext B hT hanchor hboundary obs n)


noncomputable def trusted_bankedJustificationCertificate_of_gate
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_carrier_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    Weak.BankedJustificationCertificate cfg ext E obs (n + 1)
      { Weak.update_fast_confirmation_variables cfg ext fcr_store with
        current_epoch_observed_justified_checkpoint :=
          fcr_store.store.unrealized_justifications
            (Weak.get_certified_head cfg ext fcr_store.store
              (get_current_balance_source fcr_store)) } := by
  -- `hA.genesis` is an `Exists`, so it may only be destructed *inside* the
  -- `Prop`-valued fields: a `Classical.choice` at the head of this
  -- `Type`-valued definition would block the two `rfl` projections below.
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hA.genesis
    exact ⟨ast, ablk, hgeq⟩
  have hbanked :
      ({ Weak.update_fast_confirmation_variables cfg ext fcr_store with
        current_epoch_observed_justified_checkpoint :=
          fcr_store.store.unrealized_justifications
            (Weak.get_certified_head cfg ext fcr_store.store
              (get_current_balance_source fcr_store)) } :
        FastConfirmationStore Root).current_epoch_observed_justified_checkpoint =
      (E.store cfg ext obs (n + 1)).unrealized_justifications
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := by
    change fcr_store.store.unrealized_justifications _ = _
    rw [hstore]
  have hheadKnown : (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ∈
      (E.store cfg ext obs (n + 1)).block_roots :=
    Weak.get_certified_head_known cfg ext _ _
      (Weak.trusted_head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1))
  have hcertStore : Weak.has_carrier_broadcast_certificate cfg ext
      (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store) = true := by
    rw [← hstore]; exact hgate.2
  have hcertPlain : Weak.has_broadcast_certificate cfg ext
      (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      (get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)))
      (get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1) = true := by
    simpa only [Weak.has_carrier_broadcast_certificate] using hcertStore
  have hbseq : get_current_balance_source fcr_store =
      (E.store cfg ext obs (n + 1)).checkpoint_states
        fcr_store.current_epoch_observed_justified_checkpoint := by
    simp only [get_current_balance_source]
    rw [hstore]
  have hkey : fcr_store.current_epoch_observed_justified_checkpoint ∈
      (E.store cfg ext obs (n + 1)).checkpoint_state_keys := by
    refine Weak.checkpoint_state_key_of_broadcast_certificate cfg ext E hgen0 obs (n + 1)
      _ (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      (get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)))
      (get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1) ?_
    rw [← hbseq]
    exact hcertPlain
  -- Slot arithmetic for the span side conditions.
  have hpos : 1 ≤ get_current_slot cfg (E.store cfg ext obs (n + 1)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hcall
  have hslotNow : get_current_slot cfg (E.store cfg ext obs (n + 1)) =
      E.slot_at cfg (n + 1) := E.store_current_slot cfg ext obs (n + 1)
  have hspan : get_block_slot (E.store cfg ext obs (n + 1))
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ≤
      get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1 :=
    Weak.has_broadcast_certificate_span_nonempty cfg ext hcertPlain
  have hendLe : get_current_slot cfg (E.store cfg ext obs (n + 1)) - 1 ≤
      E.slot_at cfg (n + 1) := by
    rw [← hslotNow]; exact Nat.sub_le _ _
  have hstartAnchor : E.slot_at cfg 0 ≤
      get_block_slot (E.store cfg ext obs (n + 1))
        (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := by
    obtain ⟨ast, ablk, hgeq, hslotEq, hparentNe⟩ := hA.genesis
    have hanchorHead : ablk.message.slot ≤
        ((E.store cfg ext obs (n + 1)).blocks
          (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))).slot :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence hgeq hslotEq
        hparentNe obs (n + 1) _ hheadKnown
    have hslot0 : E.slot_at cfg 0 = ablk.message.slot := by
      have ht := E.store_current_slot cfg ext obs 0
      rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
        get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
      rw [← ht, hslotEq]
    rw [hslot0]
    exact hanchorHead
  exact
    { second := n + 1
      second_le := Nat.le_refl _
      second_within := hH
      second_pos := hpos
      second_epoch_start := by rw [← hstore]; exact hgate.1
      supplier := (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store))
      supplier_known := hheadKnown
      banked_known := by
        rw [hbanked]
        exact (Weak.trusted_blockUnrealizedJustification_known_and_below cfg ext B hT
          hanchor hboundary obs (n + 1) _
            (Weak.get_certified_head_known cfg ext _ _
              (Weak.trusted_head_known_at_observer cfg ext B hT hanchor hboundary obs (n + 1)))).1
      banked_eq := hbanked
      balance_source := get_current_balance_source fcr_store
      balance_registry := by
        rw [hbseq]
        exact (E.registryConstant cfg ext hA.externals_coherence hgen0
          obs (n + 1)).2 _ hkey
      balance_total := by
        rw [hbseq]
        exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
          hA.externals_coherence (hdiv := hA.whole_seconds) (hgen := hgen0)
          obs (n + 1) _ hkey hH
      certificate := hcertPlain
      start_anchor := hstartAnchor
      start_within :=
        E.slotWithinHorizon_of_le cfg (hspan.trans hendLe) hH
      end_within := E.slotWithinHorizon_of_le cfg hendLe hH }

/-- The gate certificate's second is the call's own boundary second. -/
theorem trusted_bankedJustificationCertificate_of_gate_second
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_carrier_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    (Weak.trusted_bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
      hboundary hH hcall hstore hgate).second = n + 1 := rfl

/-- The gate certificate's supplier is that second's selected certified carrier. -/
theorem trusted_bankedJustificationCertificate_of_gate_supplier
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_carrier_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true) :
    (Weak.trusted_bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
        hboundary hH hcall hstore hgate).supplier =
      (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) := rfl

/-- **The certified carrier of a gate-passing epoch-start call is disseminated.**

The banked twin of `Execution.confirmed_known_at_all_honest_endpoints_at_observer`
applied to the *supplier* half of
`bankedSupplier_known_at_all_honest_endpoints_at_observer`, using this call's
supplier certificate. The strict-newer guard need not permit a checkpoint
write for this certificate to establish dissemination. This is the epoch-start
replacement for stage S3's
`Weak.headSeed_known_at_all_honest_endpoints_at_observer`: at an epoch start
the tentative-entry gate takes the uncertified escape, so no *entry* head
certificate is available, but rule delta 5's own banking gate carries one
whenever it fires. -/
theorem trusted_gatedHead_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hgate : is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
      Weak.has_carrier_broadcast_certificate cfg ext fcr_store.store
        (get_current_balance_source fcr_store) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m) :
    (Weak.get_certified_head cfg ext (E.store cfg ext obs (n + 1)) (get_current_balance_source fcr_store)) ∈
      (E.store cfg ext w m).block_roots := by
  have hknown :=
    (Weak.trusted_bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync  hA.genesis hcomm
      (Weak.trusted_bankedJustificationCertificate_of_gate cfg ext hA B hT hanchor
        hboundary hH hcall hstore hgate)
      hw hmH (by
        rw [Weak.trusted_bankedJustificationCertificate_of_gate_second]
        exact hslot)).1
  rwa [Weak.trusted_bankedJustificationCertificate_of_gate_supplier] at hknown

/-- **Rule delta 5 preserves its own input invariant.** At an epoch start,
a passing certificate gate and a strictly newer checkpoint install the
supplier's checkpoint. The exact write equation transports the supplier
certificate to the actual output. In every other case the banked field is
unchanged and the incoming witness re-indexes through
`BankedJustificationCertificate.transport`.

No ancestry obligation arises here: under the revised rule it is a theorem
about the banked value (`trusted_blockUnrealizedJustification_known_and_below`),
deferred to consumption. -/
theorem trusted_certifiedBankedJustification_update
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsScheduledFCRCallAt cfg ext obs n)
    {fcr_store : FastConfirmationStore Root}
    (hstore : fcr_store.store = E.store cfg ext obs (n + 1))
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store) :
    Weak.CertifiedBankedJustification cfg ext E obs (n + 1)
      (Weak.update_fast_confirmation_variables cfg ext fcr_store) := by
  by_cases hgate :
      (is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
        Weak.has_carrier_broadcast_certificate cfg ext fcr_store.store
          (get_current_balance_source fcr_store) = true) ∧
        (fcr_store.store.unrealized_justifications
          (Weak.get_certified_head cfg ext fcr_store.store
            (get_current_balance_source fcr_store))).epoch >
          fcr_store.current_epoch_observed_justified_checkpoint.epoch
  · -- The supplier checkpoint passes both the certificate and epoch guards.
    refine Or.inr ⟨(Weak.trusted_bankedJustificationCertificate_of_gate cfg ext hA B hT
      hanchor hboundary hH hcall hstore hgate.1).transport cfg ext
        (Nat.le_refl _) ?_⟩
    change (Weak.update_fast_confirmation_variables cfg ext
      fcr_store).current_epoch_observed_justified_checkpoint =
        fcr_store.store.unrealized_justifications
          (Weak.get_certified_head cfg ext fcr_store.store
            (get_current_balance_source fcr_store))
    rw [Weak.update_fcv_observed_exact, if_pos hgate]
  · -- No write: retain the previous checkpoint and its certificate.
    have heq : (Weak.update_fast_confirmation_variables cfg ext
        fcr_store).current_epoch_observed_justified_checkpoint =
        fcr_store.current_epoch_observed_justified_checkpoint := by
      rw [Weak.update_fcv_observed_exact, if_neg hgate]
    exact hinv.transport cfg ext (Nat.le_succ n) heq

/-- **The invariant holds along the whole actual weak trajectory.** Induction
on the second: the seed is the genesis initializer, which banks the anchor
store's `finalized_checkpoint` — in `E.genesis_store.block_roots`, hence the
anchor arm; the step is `trusted_certifiedBankedJustification_update` at a real slot
advance, and a pure re-index otherwise. No honesty hypothesis and no call
predicate beyond the slot advance `E.weakFcr` itself branches on. -/
theorem trusted_weakFcr_certifiedBankedJustification
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      Weak.CertifiedBankedJustification cfg ext E obs n (E.weakFcr cfg ext obs n) := by
  obtain ⟨ast, ablk, hgeq, _hslotEq, _hparentNe⟩ := hA.genesis
  intro n
  induction n with
  | zero =>
      intro _
      left
      change E.genesis_store.finalized_checkpoint.root ∈ E.genesis_store.block_roots
      rw [hgeq]
      simp only [get_forkchoice_store, List.mem_singleton]
  | succ n ih =>
      intro hH
      have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg (Nat.le_succ n) hH
      by_cases hadv : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hseat : Weak.CertifiedBankedJustification cfg ext E obs n
            { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) } :=
          (ih hHn).transport cfg ext (Nat.le_refl n) rfl
        have hupd := Weak.trusted_certifiedBankedJustification_update cfg ext hA B hT hanchor
          hboundary (obs := obs) (n := n) hH hadv (fcr_store :=
            { E.weakFcr cfg ext obs n with store := E.store cfg ext obs (n + 1) })
          rfl hseat
        refine hupd.transport cfg ext (Nat.le_refl (n + 1)) ?_
        simp only [Execution.weakFcr, if_pos hadv, Weak.on_fast_confirmation]
      · refine (ih hHn).transport cfg ext (Nat.le_succ n) ?_
        simp only [Execution.weakFcr, if_neg hadv]


end Weak
end FastConfirmation.Spec
end
