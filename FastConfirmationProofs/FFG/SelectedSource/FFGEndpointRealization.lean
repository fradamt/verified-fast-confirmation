module
public import FastConfirmationProofs.FFG.State.ScheduledFFGStateTrajectory
public import FastConfirmationProofs.FFG.SelectedSource.SelectedFFGRealization
public import FastConfirmationProofs.FFG.Certificates.PaperCheckpointInclusionStoreProjection
public import FastConfirmationProofs.FCRRule.MinimalSelectedDomain
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-!
# Endpoint facts derivable from the block-local FFG projection

This module records the endpoint-facing consequences which really follow from
`ChainFFGState`, `FFGTransitionCoherence`, and the reachable-store trajectory.
It deliberately does not fill the remaining endpoint records with free
assumptions.

What is derivable:

* every `GJ`, `GU`, and executable voting-source read has a concrete
  `CertifiedJustified` certificate;
* executable store ancestry induces ancestry in the concrete execution parent
  graph; and
* AU monotonicity/maximality proves `VotingSourceEpochChainPersistence` at
  every reachable store.

What is not derivable from the current projection is documented at the end:
the store-global justified/finalized checkpoints do not retain which block
state or eager pull-up installed them.  Consequently the second field of
`EndpointSelectorRealization` and both fields of
`FinalizedBoundaryRealization` still need historical/global-checkpoint
producers.  A sound finalized-boundary constructor below exposes the exact
AU/carrier/walk data which would suffice.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Certificates inherited from AU -/

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Every available/unrealized checkpoint has a concrete global certificate.
The proof only forgets carrier-local block-body inclusion from the stronger
certificate already stored in `FormedCheckpointEvidence`. -/
theorem certifiedJustified_of_AU
    (S : ChainFFGState cfg E anchor)
    {tip : Root} {c : Checkpoint Root}
    (hAU : S.AU cfg tip c) :
    Nonempty (CertifiedJustified cfg E anchor c) := by
  obtain ⟨carrier, _hdesc, hevidence⟩ :=
    ChainFFGState.AU.evidence (cfg := cfg) S hAU
  obtain ⟨hcertified⟩ := hevidence.certified
  exact ⟨IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) S.includedAttestations hcertified⟩

/-- The realized selector is concretely certified. -/
theorem gj_certified
    (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    Nonempty (CertifiedJustified cfg E anchor (S.GJ r)) :=
  S.certifiedJustified_of_AU cfg (S.gj_AU cfg r hr)

/-- The eager/unrealized selector is concretely certified. -/
theorem gu_certified
    (S : ChainFFGState cfg E anchor) (r : Root)
    (hr : E.ExecutionRoot r) :
    Nonempty (CertifiedJustified cfg E anchor (S.GU r)) :=
  S.certifiedJustified_of_AU cfg (S.gu_AU cfg r hr)

end ChainFFGState

namespace Execution

variable (E : Execution Root)


/-! ## Executable ancestry projected to the execution parent graph -/

/-- Every known store edge is a concrete execution parent edge. -/
theorem parentEdge_of_store_known
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    {r : Root} (hr : r ∈ store.block_roots) :
    E.ParentEdge r (store.blocks r).parent_root := by
  rcases hprovenance r hr with hgen | hsched
  · obtain ⟨hrGenesis, hblock⟩ := hgen
    exact Or.inl ⟨r, hrGenesis, rfl,
      congrArg BeaconBlock.parent_root hblock⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hblock⟩ := hsched
    exact Or.inr ⟨w, n, sb, hscheduled, hroot.symm,
      congrArg BeaconBlock.parent_root hblock⟩

/-- A known fork-choice walk which lands on `ancestor` is the same parent
chain in the concrete execution graph.  This is the missing direction needed
to apply AU monotonicity to an executable `is_ancestor` fact. -/
theorem rootDescends_of_getAncestor
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    (hwf : ParentSlotLt store)
    {tip ancestor : Root}
    (hwalk : WalkKnown store (store.blocks ancestor).slot tip)
    (hlands : (get_ancestor store (ForkChoiceNode.mk tip .pending)
      (store.blocks ancestor).slot).root = ancestor) :
    E.RootDescends tip ancestor := by
  induction hwalk with
  | @stop r hr hle =>
      rw [get_ancestor_stop hle] at hlands
      have hre : r = ancestor := hlands
      subst r
      exact .refl ancestor
  | @step r hr hgt hp ih =>
      rw [get_ancestor_step hwf hr hgt hp] at hlands
      exact .step (E.parentEdge_of_store_known hprovenance hr) (ih hlands)

/-- Boolean store ancestry implies semantic execution ancestry on the known
walk domain. -/
theorem rootDescends_of_store_ancestor
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    (hwf : ParentSlotLt store)
    {tip ancestor : Root}
    (hwalk : WalkKnown store (store.blocks ancestor).slot tip)
    (hancestor : is_ancestor store (get_node_for_root tip)
      (get_node_for_root ancestor) = true) :
    E.RootDescends tip ancestor := by
  apply E.rootDescends_of_getAncestor hprovenance hwf hwalk
  simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hancestor

end Execution

/-! ## AU selector monotonicity -/

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}




end ChainFFGState

namespace Execution

variable (E : Execution Root)


/-! ## The exact finalized-boundary projection which would suffice -/







end Execution

end FastConfirmation.Spec

end
