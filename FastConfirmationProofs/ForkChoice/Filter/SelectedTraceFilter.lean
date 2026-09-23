module
public import FastConfirmationProofs.FCRRule.SelectedTraceCoverage
public import FastConfirmationProofs.FCRRule.SelectedEdgeGeometry
public import FastConfirmationProofs.ForkChoice.Filter.SelectedFilterChainGeometry

public import FastConfirmationStatements.Premises.FCRCallPremises
@[expose] public section

/-!
# Complete retained-trace FFG/filter contract

The executable selector can retain several previous- and tentative-loop edges.
Filtered membership is needed for every strict selected edge not already below
the endpoint justified root, not merely for the final result or for a tentative
edge which crosses epochs.

The state transition and justification functions in the transcribed execution
remain opaque, so their concrete certificate/source visibility cannot be
derived internally.  `SelectedTraceFFGPipeline` states exactly that missing
boundary for every retained edge.  The spec's `HonestVotesSupportTarget`
provisos are kept separately and indexed only by helper calls which the
executable path actually relies on.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)


/-- Exact opaque-state-transition boundary for all retained selector edges.

The endpoint certificate pipeline is concrete and uses the explicit
`FFGAccountabilityAssumptions`.  The
last field supplies only a known common-descendant leaf, the finalized-boundary
walk to it, and its voting-source freshness, which the current abstract state
transition cannot connect to the executable store.  The ancestor list,
`ChainDown` proof, selected-child list membership, parent-slot discipline, and
ordinary known-root walk domain are constructed internally.  It is conditional
on lack of direct justified coverage and on the spec's actual helper provisos;
it contains no head-safety or margin conclusion.
-/
structure SelectedTraceFFGPipeline (E : Execution Root)
    (anchor : Checkpoint Root)
    (v : ValidatorIndex) (q : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  query_store_eq : fcrStore.store = E.store cfg ext v q
  accountability_assumptions : FFGAccountabilityAssumptions cfg ext E
  endpoint : ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    EndpointFFGPipeline cfg E anchor (E.store cfg ext w m)
  retained_edge_tip_source :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys →
      ∀ a c : Root,
      (PreviousEpochSelectedEdge cfg ext fcrStore latestConfirmedRoot a c ∨
        (a, c) ∈
          (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) →
      FCRPredictionSupportAt cfg ext E v q fcrStore latestConfirmedRoot →
      ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg q ≤ E.slot_at cfg m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root c) ≠ true →
      ∃ hplace : RetainedFilterTipPlacement cfg (E.store cfg ext w m) c,
        TipSourceFresh cfg (E.store cfg ext w m) hplace.tip



namespace Execution

variable (E : Execution Root)


end Execution

end FastConfirmation.Spec

end
