module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetGateGeometry
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.FFG.SelectedSource.SelectedFFGRealization
public import FastConfirmationProofs.FFG.SelectedSource.FFGEndpointRealization

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted phase-source carriers

This module keeps an actual accepted source carrier on a concrete retained
endpoint tip without assuming the result it is used to prove.
It does not assume `SourceVisibleAtTip`, filter membership, `SafeFrom`, or a
safety conclusion.

The historical paper lemmas still have to produce a recent seed in the two
current-result early phases.  Once such a seed is produced, the constructors
below perform fixed-root cross-store transport, descendant persistence, and
finite retained-tip selection without strengthening that historical input.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Accepted selector monotonicity -/

namespace AcceptedChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Every accepted `GJ` value has its concrete included certificate. -/
theorem gj_certified
    (S : AcceptedChainFFGState cfg ext E anchor)
    {tip : Root} (htip : E.AcceptedRoot cfg ext tip) :
    Nonempty (CertifiedJustified cfg E anchor (S.GJ tip)) := by
  obtain ⟨carrier, _hdesc, hformed⟩ := S.gj_mem tip htip
  obtain ⟨hincluded⟩ := (S.formed_evidence hformed).certified
  exact ⟨IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) S.includedAttestations.relation hincluded⟩

/-- Accepted `GU` epochs are monotone along semantic block descent. -/
theorem gu_epoch_le_of_descends
    (S : AcceptedChainFFGState cfg ext E anchor)
    {seed tip : Root}
    (hseed : E.AcceptedRoot cfg ext seed)
    (htip : E.AcceptedRoot cfg ext tip)
    (hdesc : E.RootDescends tip seed) :
    (S.GU seed).epoch ≤ (S.GU tip).epoch := by
  apply S.gu_max htip
  exact AcceptedChainFFGState.AU.mono (cfg := cfg) (ext := ext) S hdesc
    (S.gu_AU cfg ext hseed)

/-- Accepted `GJ` epochs are monotone along a nondecreasing-epoch semantic
descent. -/
theorem gj_epoch_le_of_descends
    (S : AcceptedChainFFGState cfg ext E anchor)
    {seed tip : Root} {seedBlock tipBlock : BeaconBlock Root}
    (hseed : E.AcceptedBlockAt cfg ext seed seedBlock)
    (htip : E.AcceptedBlockAt cfg ext tip tipBlock)
    (hdesc : E.RootDescends tip seed)
    (hepoch : compute_epoch_at_slot cfg seedBlock.slot ≤
      compute_epoch_at_slot cfg tipBlock.slot) :
    (S.GJ seed).epoch ≤ (S.GJ tip).epoch := by
  rcases S.gj_anchor_or_before hseed with hanchor | hbefore
  · rw [hanchor]
    obtain ⟨htipCertified⟩ := S.gj_certified cfg ext htip.acceptedRoot
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg) htipCertified
  · apply S.gj_max htip
      (AcceptedChainFFGState.AU.mono (cfg := cfg) (ext := ext) S hdesc
        (S.gj_AU cfg ext hseed.acceptedRoot))
    exact hbefore.trans_le hepoch

/-- An old accepted `GU` source is below the realized `GJ` of a strictly
later-epoch descendant. -/
theorem gu_epoch_le_gj_of_descends
    (S : AcceptedChainFFGState cfg ext E anchor)
    {seed tip : Root} {tipBlock : BeaconBlock Root}
    (hseed : E.AcceptedRoot cfg ext seed)
    (htip : E.AcceptedBlockAt cfg ext tip tipBlock)
    (hdesc : E.RootDescends tip seed)
    (hbefore : (S.GU seed).epoch <
      compute_epoch_at_slot cfg tipBlock.slot) :
    (S.GU seed).epoch ≤ (S.GJ tip).epoch := by
  exact S.gj_max htip
    (AcceptedChainFFGState.AU.mono (cfg := cfg) (ext := ext) S hdesc
      (S.gu_AU cfg ext hseed)) hbefore

end AcceptedChainFFGState

namespace Execution

variable {E : Execution Root}

/-- Read the executable voting source at any exact causal store through the
one accepted semantic state selected outside the store. -/
theorem CausalStore.getVotingSource_eq_acceptedSelector
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {r : Root} (hr : r ∈ store.block_roots) :
    get_voting_source cfg store r =
      if get_current_store_epoch cfg store > get_block_epoch cfg store r then
        B.state.GU r
      else B.state.GJ r := by
  have hprojection :=
    Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection B hstore
  simp only [get_voting_source, get_block_epoch]
  split_ifs
  · exact hprojection.unrealized_justification r hr
  · exact hprojection.block_state_gj r hr

/-- The executable voting source of a known root owns positive accepted AU
evidence at that same root. -/
theorem CausalStore.getVotingSource_AU
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {r : Root} (hr : r ∈ store.block_roots) :
    B.state.AU cfg ext r (get_voting_source cfg store r) := by
  have haccepted := E.acceptedRoot_of_causal_known cfg ext hstore hr
  rw [hstore.getVotingSource_eq_acceptedSelector cfg ext B hr]
  split_ifs
  · exact B.state.gu_AU cfg ext haccepted
  · exact B.state.gj_AU cfg ext haccepted

/-- Fixed-root source epochs cannot decrease between two causal stores whose
clocks are epoch-ordered.  Accepted block uniqueness identifies the root's
block epoch; the only selector change is `GJ → GU`. -/
theorem acceptedVotingSource_epoch_le_of_currentEpoch_le
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    {query endpoint : Store Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext endpoint)
    {r : Root} (hrQ : r ∈ query.block_roots)
    (hrM : r ∈ endpoint.block_roots)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg endpoint) :
    (get_voting_source cfg query r).epoch ≤
      (get_voting_source cfg endpoint r).epoch := by
  have hqueryAt : E.AcceptedBlockAt cfg ext r (query.blocks r) :=
    E.acceptedBlockAt_of_causal_known cfg ext hquery hrQ
  have hendpointAt : E.AcceptedBlockAt cfg ext r (endpoint.blocks r) :=
    E.acceptedBlockAt_of_causal_known cfg ext hendpoint hrM
  have hblock : query.blocks r = endpoint.blocks r :=
    hqueryAt.unique cfg ext E hwf hendpointAt
  have hblockEpoch : get_block_epoch cfg query r =
      get_block_epoch cfg endpoint r := by
    simp only [get_block_epoch, hblock]
  have haccepted := hqueryAt.acceptedRoot
  rw [hquery.getVotingSource_eq_acceptedSelector cfg ext B hrQ,
    hendpoint.getVotingSource_eq_acceptedSelector cfg ext B hrM]
  by_cases hqOld : get_current_store_epoch cfg query >
      get_block_epoch cfg query r
  · have hmOld : get_current_store_epoch cfg endpoint >
        get_block_epoch cfg endpoint r := by
      rw [← hblockEpoch]
      exact hqOld.trans_le hclock
    rw [if_pos hqOld, if_pos hmOld]
  · by_cases hmOld : get_current_store_epoch cfg endpoint >
        get_block_epoch cfg endpoint r
    · rw [if_neg hqOld, if_pos hmOld]
      exact B.state.gj_epoch_le_gu cfg ext haccepted
    · rw [if_neg hqOld, if_neg hmOld]

/-- Complete accepted voting-source epoch persistence in one causal store.
All required path/domain facts are explicit operational geometry; there is no
source-visibility or filter premise. -/
theorem acceptedVotingSourceEpochChainPersistence
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (hprovenance : BlockProvenance E store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hnonfuture : BlocksSlotLe (get_current_slot cfg store) store) :
    VotingSourceEpochChainPersistence cfg store := by
  constructor
  intro seed tip hseed htip htipSeed
  have hwalk : WalkKnown store (store.blocks seed).slot tip :=
    hwalkK seed hseed tip htip
  have hslotLe : (store.blocks seed).slot ≤ (store.blocks tip).slot :=
    ancestor_slot_le hparent hwalk htipSeed
  have hepochLe : get_block_epoch cfg store seed ≤
      get_block_epoch cfg store tip := by
    exact ce_mono cfg hslotLe
  have hseedEpochCurrent : get_block_epoch cfg store seed ≤
      get_current_store_epoch cfg store := by
    exact ce_mono cfg (hnonfuture seed hseed)
  have htipEpochCurrent : get_block_epoch cfg store tip ≤
      get_current_store_epoch cfg store := by
    exact ce_mono cfg (hnonfuture tip htip)
  have hsemantic : E.RootDescends tip seed :=
    E.rootDescends_of_store_ancestor hprovenance hparent hwalk htipSeed
  have hseedAt : E.AcceptedBlockAt cfg ext seed (store.blocks seed) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hseed
  have htipAt : E.AcceptedBlockAt cfg ext tip (store.blocks tip) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore htip
  rw [hstore.getVotingSource_eq_acceptedSelector cfg ext B hseed,
    hstore.getVotingSource_eq_acceptedSelector cfg ext B htip]
  by_cases hseedOld : get_current_store_epoch cfg store >
      get_block_epoch cfg store seed
  · rw [if_pos hseedOld]
    by_cases htipOld : get_current_store_epoch cfg store >
        get_block_epoch cfg store tip
    · rw [if_pos htipOld]
      exact B.state.gu_epoch_le_of_descends cfg ext hseedAt.acceptedRoot
        htipAt.acceptedRoot hsemantic
    · rw [if_neg htipOld]
      have htipCurrent : get_block_epoch cfg store tip =
          get_current_store_epoch cfg store :=
        Nat.le_antisymm htipEpochCurrent (Nat.le_of_not_gt htipOld)
      have hguSeedBlock : (B.state.GU seed).epoch ≤
          get_block_epoch cfg store seed := by
        exact B.state.au_epoch_le_block hseedAt
          (B.state.gu_AU cfg ext hseedAt.acceptedRoot)
      have hguBeforeTip : (B.state.GU seed).epoch <
          get_block_epoch cfg store tip := by
        rw [htipCurrent]
        exact hguSeedBlock.trans_lt hseedOld
      exact B.state.gu_epoch_le_gj_of_descends cfg ext
        hseedAt.acceptedRoot htipAt hsemantic hguBeforeTip
  · rw [if_neg hseedOld]
    by_cases htipOld : get_current_store_epoch cfg store >
        get_block_epoch cfg store tip
    · rw [if_pos htipOld]
      have hcurrentSeed : get_current_store_epoch cfg store ≤
          get_block_epoch cfg store seed := Nat.le_of_not_gt hseedOld
      exact False.elim ((Nat.not_lt_of_ge
        (hcurrentSeed.trans hepochLe)) htipOld)
    · rw [if_neg htipOld]
      exact B.state.gj_epoch_le_of_descends cfg ext hseedAt htipAt
        hsemantic hepochLe

/-! ## Consumer-shaped retained source tips -/

/-- A recent voting source with positive accepted AU evidence, placed on a
concrete childless descendant of the selected block in the endpoint store.

This is the S1 carrier consumed before source/finality merging.  It contains
no finalized compatibility or filter conclusion. -/
structure AcceptedRetainedPhaseSourceCarrierAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (store : Store Root) (selected : Root) where
  store_causal : E.CausalStore cfg ext store
  tip : Root
  selected_known : selected ∈ store.block_roots
  tip_known : tip ∈ store.block_roots
  tip_descends_selected : is_ancestor store (get_node_for_root tip)
    (get_node_for_root selected) = true
  tip_is_leaf : store.block_roots.filter
    (fun r => (store.blocks r).parent_root = tip) = []
  source_au : B.state.AU cfg ext tip (get_voting_source cfg store tip)
  source_recent : (get_voting_source cfg store tip).epoch + 2 ≥
    get_current_store_epoch cfg store

namespace AcceptedRetainedPhaseSourceCarrierAt



end AcceptedRetainedPhaseSourceCarrierAt

/-- A recent seed on the selected branch extends mechanically to a retained
childless tip.  Accepted selector semantics supplies positive AU at the new
tip and source-epoch persistence transports recency. -/
theorem acceptedRetainedPhaseSourceCarrier_of_recentSeed_nonempty
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (hprovenance : BlockProvenance E store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hnonfuture : BlocksSlotLe (get_current_slot cfg store) store)
    {selected seed : Root}
    (hselected : selected ∈ store.block_roots)
    (hseed : seed ∈ store.block_roots)
    (hseedSelected : is_ancestor store (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hrecent : (get_voting_source cfg store seed).epoch + 2 ≥
      get_current_store_epoch cfg store) :
    Nonempty
      (E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected) := by
  let hpersistence := E.acceptedVotingSourceEpochChainPersistence cfg ext B
    hstore hparent hprovenance hwalkK hnonfuture
  obtain ⟨tip, htip, _htipWalk, htipSeed, hleaf⟩ :=
    exists_store_leaf_extension hparent hseed
  have htipSelected : is_ancestor store (get_node_for_root tip)
      (get_node_for_root selected) = true :=
    is_ancestor_trans (a := get_node_for_root tip) (b := get_node_for_root seed)
      (c := get_node_for_root selected) hparent
      (hwalkK selected hselected tip htip)
      (hwalkK selected hselected seed hseed)
      htipSeed hseedSelected
  have hsourceMono : (get_voting_source cfg store seed).epoch ≤
      (get_voting_source cfg store tip).epoch :=
    hpersistence.source_epoch_le_of_descends hseed htip htipSeed
  exact ⟨{
    store_causal := hstore
    tip := tip
    selected_known := hselected
    tip_known := htip
    tip_descends_selected := htipSelected
    tip_is_leaf := hleaf
    source_au := hstore.getVotingSource_AU cfg ext B htip
    source_recent := hrecent.trans (Nat.add_le_add_right hsourceMono 2)
  }⟩

/-- Choice-valued form of
`acceptedRetainedPhaseSourceCarrier_of_recentSeed_nonempty`.  The only
noncomputability is finite retained-leaf selection. -/
noncomputable def acceptedRetainedPhaseSourceCarrier_of_recentSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hparent : ParentSlotLt store)
    (hprovenance : BlockProvenance E store)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hnonfuture : BlocksSlotLe (get_current_slot cfg store) store)
    {selected seed : Root}
    (hselected : selected ∈ store.block_roots)
    (hseed : seed ∈ store.block_roots)
    (hseedSelected : is_ancestor store (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hrecent : (get_voting_source cfg store seed).epoch + 2 ≥
      get_current_store_epoch cfg store) :
    E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B store selected :=
  Classical.choice
    (E.acceptedRetainedPhaseSourceCarrier_of_recentSeed_nonempty cfg ext B
      hstore hparent hprovenance hwalkK hnonfuture hselected hseed
      hseedSelected hrecent)

/-- Query-local recency for a fixed seed transports to a later causal
endpoint and then extends to a retained endpoint tip.  The seed's endpoint
knownness/descent are ordinary relay/path facts, not source or safety
premises. -/
noncomputable def acceptedRetainedPhaseSourceCarrier_of_queryRecentSeed
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    {query endpoint : Store Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext endpoint)
    (hparent : ParentSlotLt endpoint)
    (hprovenance : BlockProvenance E endpoint)
    (hwalkK : ∀ t ∈ endpoint.block_roots,
      ∀ r ∈ endpoint.block_roots,
        WalkKnown endpoint (endpoint.blocks t).slot r)
    (hnonfuture : BlocksSlotLe (get_current_slot cfg endpoint) endpoint)
    {selected seed : Root}
    (hselected : selected ∈ endpoint.block_roots)
    (hseedQ : seed ∈ query.block_roots)
    (hseedM : seed ∈ endpoint.block_roots)
    (hseedSelected : is_ancestor endpoint (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg endpoint)
    (hrecentQ : (get_voting_source cfg query seed).epoch + 2 ≥
      get_current_store_epoch cfg endpoint) :
    E.AcceptedRetainedPhaseSourceCarrierAt cfg ext B endpoint selected := by
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hwf hquery hendpoint hseedQ hseedM hclock
  have hrecentM : (get_voting_source cfg endpoint seed).epoch + 2 ≥
      get_current_store_epoch cfg endpoint :=
    hrecentQ.trans (Nat.add_le_add_right hsourceMono 2)
  exact E.acceptedRetainedPhaseSourceCarrier_of_recentSeed cfg ext B
    hendpoint hparent hprovenance hwalkK hnonfuture hselected hseedM
      hseedSelected hrecentM

/-! ## Early phase matrix -/

/-- The three arithmetic cells below the late `e+2` A3.2 threshold. -/
inductive EarlySelectedEndpointPhase (e queryEpoch endpointEpoch : Epoch) :
    Prop where
  | previous
      (hquery : e + 1 = queryEpoch)
      (hendpoint : endpointEpoch = e + 1)
  | currentSame
      (hquery : e = queryEpoch)
      (hendpoint : endpointEpoch = e)
  | currentNext
      (hquery : e = queryEpoch)
      (hendpoint : endpointEpoch = e + 1)


/-! ## Historical A3.2 source placement -/




end Execution

end FastConfirmation.Spec

end
