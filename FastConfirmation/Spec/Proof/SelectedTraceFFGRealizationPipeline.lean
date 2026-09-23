module
public import FastConfirmation.Spec.Proof.SelectedTraceFilterPipeline
public import FastConfirmation.Spec.Proof.SelectedJustifiedCompatibility
public import FastConfirmation.Spec.Proof.SelectedPreQueryAnchor
public import FastConfirmation.Spec.Proof.CausalCheckpointEpochBound
public import FastConfirmation.Spec.Proof.SelectedFFGRealization
public import FastConfirmation.Spec.Proof.PaperA32Projection

@[expose] public section

/-!
# Non-circular selected-trace FFG realization

This module replaces the legacy `SelectedTraceFFGPipeline` boundary with the
causal/state-facing pieces actually used by the coupled proof.  The contract is
indexed by the exact selected call.  It does not contain filter membership,
`TipSourceFresh`, a leaf, a common-descendant placement, or a future head/safety
conclusion.

The remaining semantic fields have deliberately different roles:

* endpoint certificate, selector, finalized-boundary, and source-persistence
  realization describe concrete values read from honest endpoint stores;
* pre-query result/checkpoint comparability is the initial SIR / helper-gate
  soundness boundary;
* every non-anchor endpoint justification exposes a causal honest target vote;
  votes at or after the query are discharged by the actual head induction; and
* source availability exposes the paper's early-recency / later-inclusion
  alternative at a **seed** below an already-compatible selected result.
  Finite leaf selection, availability propagation, filter placement, and
  filtered membership are then proved mechanically.
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
