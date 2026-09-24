module
public import FastConfirmationProofs.FFG.SelectedSource.EarlyPhaseSource
public import FastConfirmationProofs.FFG.SelectedSource.TrustedPhaseSourceCarriers

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hgenSlot : ast.slot = ablk.message.slot)
    (hgenParent : ablk.message.parent_root ≠ ablk.root)
    {query : Store Root} {w : ValidatorIndex} {m : Nat}
    {selected seed : Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext (E.store cfg ext w m))
    (hqueryParent : ParentSlotLt query)
    (hqueryProvenance : BlockProvenance E query)
    (hqueryWalk : WalkKnown query (query.blocks selected).slot seed)
    (hselectedQ : selected ∈ query.block_roots)
    (hseedQ : seed ∈ query.block_roots)
    (hseedM : seed ∈ (E.store cfg ext w m).block_roots)
    (hseedSelectedQ : is_ancestor query (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query)
    (hrecentQ : (get_voting_source cfg query seed).epoch + 2 ≥
      get_current_store_epoch cfg query) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      hqueryWalk hseedSelectedQ
  have hselectedRoot : E.ExecutionRoot selected := by
    refine ⟨query.blocks selected, ?_⟩
    rcases hqueryProvenance selected hselectedQ with hgenesis | hsched
    · exact Or.inl ⟨hgenesis.1, hgenesis.2⟩
    · obtain ⟨sb, ⟨u, k, hscheduled⟩, hroot, hmessage⟩ := hsched
      exact Or.inr ⟨u, k, sb, hscheduled, hroot, hmessage.symm⟩
  obtain ⟨_hselectedM, hseedSelectedM⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hwf hec hgen hgenSlot hgenParent hseedM hselectedRoot hsemantic
  have hsourceMono := E.trusted_acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hwf hquery hendpoint hseedQ hseedM hclock
  refine ⟨seed, hseedM, hseedSelectedM, ?_⟩
  rw [hsameEpoch]
  exact hrecentQ.trans (Nat.add_le_add_right hsourceMono 2)

end Execution
end FastConfirmation.Spec
end
