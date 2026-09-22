module
public import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
public import FastConfirmation.Spec.Proof.SelectedJustifiedCompatibility
public import FastConfirmation.Spec.Proof.SelectedPreQueryAnchor
public import FastConfirmation.Spec.Proof.CausalCheckpointEpochBound
public import FastConfirmation.Spec.Proof.SelectedFFGRealization
public import FastConfirmation.Spec.Proof.PaperA32Projection

@[expose] public section


/-!
# Selected-call A3.2 semantics vocabulary

The contract records which once stood here — the proviso-conditional
`SelectedTraceFFGStateRealizationFor` state realization and its two filter
consequences — were deleted with the rest of the
`SelectedHelperProvisosAt` surface; see `docs/weak-final-wave.md` §8.1.

What remains are the shared A3.2 vocabulary pieces used by the live selected
and weak trunks:

* the earlier-slot canonicality window available at one endpoint of the
  coupled selected-result induction;
* the explicit early query carrier for an already-available selected
  checkpoint, and the semantic split which either propagates that carrier or
  supplies the paper's full A3.2 antecedents; and
* the projection of the selected-margin bundle onto concrete Casper
  accountability, so no duplicate economic assumption is requested.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The exact earlier-slot canonicality window available at one endpoint of
the coupled selected-result induction. -/
def SelectedCanonicalBeforeEndpointAt (q : ℕ) (glc : Root) (m : ℕ) : Prop :=
  ∀ w' ∈ E.honest, ∀ m' : ℕ,
    E.slot_start cfg (E.slot_at cfg q) ≤ m' →
    E.slot_at cfg m' < E.slot_at cfg m →
    E.WithinHorizon cfg m' →
    is_ancestor (E.store cfg ext w' m')
      (get_head cfg (E.store cfg ext w' m'))
      (get_node_for_root glc) = true

/-- An already-available query carrier for the selected checkpoint.  Keeping
the carrier explicit avoids the invalid backward inference from AU at a later
head to AU at `selected`.  The carrier is relayed to later endpoints before
its AU fact is projected into the executable unrealized map. -/
def SelectedEarlyA32CarrierAt
    (anchor : Checkpoint Root) (state : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ) (selected : Root)
    (baseEpoch : Epoch) : Prop :=
  ∃ carrier : Root,
    carrier ∈ (E.store cfg ext v q).block_roots ∧
    E.RootDescends carrier selected ∧
    get_block_epoch cfg (E.store cfg ext v q) carrier < baseEpoch + 2 ∧
    state.AU cfg carrier (state.C selected baseEpoch)

/-- Exact semantic split for the late selected-carrier argument.

If the target is already AU on a concrete query carrier above `selected`, it
is propagated directly and paper A3.2 is not invoked.  Otherwise the paper's
full canonicality and fixed-source support antecedents are supplied together.
The executable `A32IncludedAtTip` projection is not a field in either branch. -/
def SelectedA32SemanticRealizationAt
    (anchor : Checkpoint Root) (state : ChainFFGState cfg E anchor)
    (v : ValidatorIndex) (q : ℕ) (selected : Root)
    (baseEpoch : Epoch) : Prop :=
  E.SelectedEarlyA32CarrierAt cfg ext anchor state v q selected baseEpoch ∨
    (E.CanonicalThroughoutEpoch cfg ext selected (baseEpoch + 1) ∧
      PaperA32SupportThroughoutEpoch cfg ext state selected baseEpoch)

/-- The selected-margin bundle already contains every premise used by
concrete Casper accountability; the FFG realization must not ask for a
duplicate economic assumption. -/
def SelectedMarginAssumptions.toFFGAccountabilityAssumptions
    (hA : SelectedMarginAssumptions cfg ext E) :
    FFGAccountabilityAssumptions cfg ext E where
  genesis_store := by
    obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hA.genesis
    exact ⟨ast, ablk, hgen⟩
  whole_seconds := hA.whole_seconds
  honest_behavior := hA.honest_behavior
  externals_coherence := hA.externals_coherence
  static_validator_set := hA.static_validators
  byzantine_bound := hA.byzantine_bound

end Execution

end FastConfirmation.Spec

end
