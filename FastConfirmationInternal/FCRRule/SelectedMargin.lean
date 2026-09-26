module
public import FastConfirmationInternal.Network.VotePathAdmissibility
public import FastConfirmationInternal.Legacy.Vocabulary

@[expose] public section

/-! Defines the selected margin domain and its lower execution premises. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- Local cache facts and the derived G4 paths used by the selected-result proof. -/
structure SelectedMarginDomain (E : Execution Root) : Prop where
  honest_head_paths : HonestHeadPathAdmissibility cfg ext E
  justified_root_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots
  justified_checkpoint_cached : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint ∈
      (E.store cfg ext w m).checkpoint_state_keys

/-- The lower protocol assumptions used by the selected-margin proof, with
`JustificationInterface` replaced by `SelectedMarginDomain`. -/
structure SelectedMarginAssumptions (E : Execution Root) : Prop where
  genesis : ∃ (anchor_state : BeaconState Root) (anchor_block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
    anchor_state.slot = anchor_block.message.slot ∧
    anchor_block.message.parent_root ≠ anchor_block.root
  wellFormed : WellFormedExecution E
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  honest_behavior : HonestBehavior cfg ext E
  synchrony : NextSlotSynchronyPremises cfg ext E
  externals_coherence : BeaconExternalsPremises cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineWeightPremises cfg E
  domain : SelectedMarginDomain cfg ext E


end FastConfirmation.Spec

end
