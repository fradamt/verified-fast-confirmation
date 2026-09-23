module
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationModel.Execution.PayloadFrame

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / FFGStateTrajectory

Handler induction for the block-local FFG projection.  The model-level
coherence record states only genesis and successful-transition equations.
This file proves that every root in every reachable store carries the exact
projected post-state and eager-pull-up values, including the value written to
`unrealized_justifications`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {E : Execution Root} {anchor : Checkpoint Root}


/-- Exact correspondence between a fork-choice store and the block-local FFG
projection at every root in the store's finite block domain. -/
structure FFGStoreProjection (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop where
  block_state_gj : ∀ r ∈ store.block_roots,
    (store.block_states r).current_justified_checkpoint = S.GJ r
  block_state_gf : ∀ r ∈ store.block_roots,
    (store.block_states r).finalized_checkpoint = S.GF r
  pulled_up_gu : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint = S.GU r
  pulled_up_guf : ∀ r ∈ store.block_roots,
    (ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint = S.GUF r
  unrealized_justification : ∀ r ∈ store.block_roots,
    store.unrealized_justifications r = S.GU r

namespace FFGStoreProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}



end FFGStoreProjection

namespace FFGBlockStateProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}


end FFGBlockStateProjection

variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-! ## Block-identity-preserving helpers -/












/-! ## Event handlers -/




/-! ## Ticks and execution induction -/





namespace Execution









end Execution

end FastConfirmation.Spec

end
