module
public import FastConfirmation.Spec.Proof.AcceptedResetCheckpointClassification
public import FastConfirmation.Spec.Proof.FFGCheckpointEpochOrder
public import FastConfirmation.Spec.Proof.SelectedFFGRealization
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Accepted dynamic finalized placement at a retained tip

The accepted global checkpoint trajectory remembers the concrete carrier which
installed a store-global `GF` or `GUF`.  A historical retained tip is a
different object, so that existential origin does not by itself identify the
global finalized field with `GF retained` or `GUF retained`.

That equality is stronger than the executable finalized leaf needs.  If the
endpoint's realized justified checkpoint is visible in the retained tip's
voting source, accepted block-local projection identifies that voting source
with `GJ retained` or `GU retained`.  Handler-derived checkpoint order then
puts the global finalized epoch below that retained, included-justified AU
target.  Exact cross-carrier certificate accountability supplies the semantic
prefix, and one boundary walk reflects it directly at the retained tip.

Thus finalization and source are merged without a free AU, filter, safety,
head-takeover, or same-origin premise.  The last section records the two exact
interface obstructions: an existential global origin does not name an
arbitrary retained tip, and source recency alone does not imply finalized
epoch dominance.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact voting-source projection -/

namespace AcceptedFFGStoreProjection

/-- On the accepted causal-store projection, the executable voting-source
read is exactly the retained root's realized `GJ` or eager `GU` selector. -/
theorem getVotingSource_eq_gj_or_gu
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store : Store Root}
    (h : AcceptedFFGStoreProjection S store)
    {tip : Root} (htip : tip ∈ store.block_roots) :
    get_voting_source cfg store tip = S.GJ tip ∨
      get_voting_source cfg store tip = S.GU tip := by
  simp only [get_voting_source]
  split_ifs
  · exact Or.inr (h.unrealized_justification tip htip)
  · exact Or.inl (h.block_state_gj tip htip)

end AcceptedFFGStoreProjection

/-! ## Consumer-shaped same-tip target -/

/-- The narrow dynamic placement needed for finalized-prefix reflection.

The global finalized field need not equal a block-local finalized selector at
`tip`.  It is enough to retain one included-justified AU target at that exact
tip whose epoch dominates the field. -/
structure AcceptedDynamicFinalizedPlacementAt
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (tip : Root) : Prop where
  tip_known : tip ∈ store.block_roots
  tip_accepted : E.AcceptedRoot cfg ext tip
  target : ∃ target : Checkpoint Root,
    (target = S.GJ tip ∨ target = S.GU tip) ∧
      S.AU cfg ext tip target ∧
      Nonempty (IncludedCertifiedJustified cfg E
        S.includedAttestations.Included anchor tip target) ∧
      store.finalized_checkpoint.epoch ≤ target.epoch

namespace ExactPrefixAcceptedFFGSemantics

/-- Visibility of the endpoint justified epoch at one retained tip produces
the exact consumer-shaped finalized placement.  Global field order is
handler-derived, while the retained target and its certificate come from the
same preselected accepted semantic state. -/
theorem dynamicFinalizedPlacementAt_of_sourceVisible
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {tip : Root} (htip : tip ∈ store.block_roots)
    (hvisible : SourceVisibleAtTip cfg store tip) :
    AcceptedDynamicFinalizedPlacementAt cfg ext B.state store tip := by
  have htipAccepted : E.AcceptedRoot cfg ext tip :=
    E.acceptedRoot_of_causal_known cfg ext hstore htip
  have hfinalizedLeJustified :
      store.finalized_checkpoint.epoch ≤
        store.justified_checkpoint.epoch :=
    B.globalFinalizedEpoch_le_justified cfg ext hgen hanchor hstore
  have hprojection :=
    (B.causalStoreGlobalProjection hgen hanchor hstore).blockLocal
  rcases hprojection.getVotingSource_eq_gj_or_gu cfg ext htip with
    hsourceGJ | hsourceGU
  · have hfinalizedLeGJ : store.finalized_checkpoint.epoch ≤
        (B.state.GJ tip).epoch := by
      apply hfinalizedLeJustified.trans
      calc
        store.justified_checkpoint.epoch ≤
            (get_voting_source cfg store tip).epoch :=
          hvisible.justified_epoch_le_source
        _ = (B.state.GJ tip).epoch :=
          congrArg Checkpoint.epoch hsourceGJ
    have hAU := B.state.gj_AU cfg ext htipAccepted
    exact {
      tip_known := htip
      tip_accepted := htipAccepted
      target := ⟨B.state.GJ tip, Or.inl rfl, hAU,
        B.state.includedJustifiedAtTip_of_AU cfg ext hAU,
        hfinalizedLeGJ⟩
    }
  · have hfinalizedLeGU : store.finalized_checkpoint.epoch ≤
        (B.state.GU tip).epoch := by
      apply hfinalizedLeJustified.trans
      calc
        store.justified_checkpoint.epoch ≤
            (get_voting_source cfg store tip).epoch :=
          hvisible.justified_epoch_le_source
        _ = (B.state.GU tip).epoch :=
          congrArg Checkpoint.epoch hsourceGU
    have hAU := B.state.gu_AU cfg ext htipAccepted
    exact {
      tip_known := htip
      tip_accepted := htipAccepted
      target := ⟨B.state.GU tip, Or.inr rfl, hAU,
        B.state.includedJustifiedAtTip_of_AU cfg ext hAU,
        hfinalizedLeGU⟩
    }

/-- `SourceAvailableAtTip` closes dynamic finalized placement exactly in its
visibility branch.  Its recency branch remains explicit rather than being
silently strengthened to finalized dominance. -/
theorem dynamicFinalizedPlacementAt_or_recent_of_sourceAvailable
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {tip : Root} (htip : tip ∈ store.block_roots)
    (havailable : SourceAvailableAtTip cfg store tip) :
    AcceptedDynamicFinalizedPlacementAt cfg ext B.state store tip ∨
      (get_voting_source cfg store tip).epoch + 2 ≥
        get_current_store_epoch cfg store := by
  rcases havailable with hvisible | hrecent
  · exact Or.inl (B.dynamicFinalizedPlacementAt_of_sourceVisible cfg ext
      hgen hanchor hstore htip hvisible)
  · exact Or.inr hrecent

end ExactPrefixAcceptedFFGSemantics

namespace AcceptedDynamicFinalizedPlacementAt

/-- Exact finalized leaf reflection from the dynamic retained target.

The accepted global field supplies either the trusted anchor or a concrete
included finalization certificate on its historical installer carrier.  The
target certificate is on `tip`; exact accountability is deliberately
cross-carrier, so no equality between those two carriers is assumed. -/
theorem finalizedRoot_eq_checkpointBlock_at_tip
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    {tip : Root}
    (h : AcceptedDynamicFinalizedPlacementAt cfg ext B.state store tip)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch)
      tip) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store tip
        store.finalized_checkpoint.epoch := by
  obtain ⟨target, _htargetSelector, htargetAU,
      ⟨hjustified⟩, hfinalizedLeTarget⟩ := h.target
  have hprefix : ExactCheckpointPrefix B.state.C
      store.finalized_checkpoint target := by
    rcases E.acceptedGlobalFinalized_anchor_or_includedCertificate
        cfg ext B hgen hanchor hstore with hfinalizedAnchor |
        ⟨_carrier, _hcarrier, hfinalized⟩
    · rw [hfinalizedAnchor]
      exact IncludedCertifiedJustified.anchor_prefix
        (cfg := cfg) P V hanchorExact hjustified
    · obtain ⟨hfinalized⟩ := hfinalized
      exact B.state.exactFinalizedPrefix_of_accountable cfg P V
        hanchorExact hacc hfinalized hjustified
          hfinalizedLeTarget
  exact exactCheckpointPrefix_root_eq_at_sameTip cfg ext B.coherence hstore
    hparent h.tip_known hprefix htargetAU hfinalizedLeTarget hwalk

end AcceptedDynamicFinalizedPlacementAt

namespace RetainedFilterTipPlacement

/-- Dynamic F2 at the exact filter-placement consumer.  The placement already
owns the finalized-boundary walk; source visibility derives the retained
accepted target, and accepted global provenance supplies finalization. -/
theorem finalizedRoot_eq_checkpointBlock_of_acceptedVisible
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    (hanchorExact : B.anchor =
      B.state.C B.anchor.root B.anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E B.anchor)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    {child : Root} (hplace : RetainedFilterTipPlacement cfg store child)
    (hvisible : SourceVisibleAtTip cfg store hplace.tip) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store hplace.tip
        store.finalized_checkpoint.epoch := by
  have hdynamic := B.dynamicFinalizedPlacementAt_of_sourceVisible cfg ext
    hgen hanchor hstore hplace.tip_known hvisible
  exact hdynamic.finalizedRoot_eq_checkpointBlock_at_tip cfg ext B hgen
    hanchor P V hanchorExact hacc hstore hparent
      hplace.finalized_walk_known

end RetainedFilterTipPlacement

/-! ## Checked interface obstructions -/

/-- An existential selector origin carries no equality at an independently
chosen retained tip.  This is the logical shape of
`AcceptedGlobalFinalizedOrigin`; additional history must relate the tips or,
as above, derive a dominating retained target instead. -/
theorem existentialOrigin_does_not_identify_retainedSelector :
    ∃ (selector : Bool → Nat) (field : Nat) (origin retained : Bool),
      field = selector origin ∧ origin ≠ retained ∧
        field ≠ selector retained := by
  refine ⟨fun b => if b then 1 else 0, 0, false, true, ?_⟩
  decide

/-- The recency disjunct of `SourceAvailableAtTip` is arithmetically too weak
to place finality.  Even with `F ≤ J ≤ current`, a source satisfying
`source + 2 ≥ current` may still be older than `F`. -/
theorem sourceRecency_does_not_imply_finalizedDominance :
    ∃ finalized justified source current : Nat,
      finalized ≤ justified ∧ justified ≤ current ∧
        source + 2 ≥ current ∧ ¬ finalized ≤ source := by
  exact ⟨5, 5, 4, 6, by omega⟩


end FastConfirmation.Spec

end
