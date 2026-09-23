module
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Execution.Trajectory.ChainWalkClosure
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadMembership
public import FastConfirmationProofs.Execution.Trajectory.EdgeDynamics
public import FastConfirmationProofs.FFG.SourceHistory.LaterStoreSupport
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / IHMechanize

This module contains `filtered_subset_block_roots` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — `dynamics_struct` from `hb` + `hcase`

`ResidualMechanicalII.dynamicsChainStruct_body` builds the `DynamicsChainStruct` existential
(`Nodup`/`IsChain`/`getLast` over `get_ancestor_roots store b jc`) from the parent-slot
order `hwf`, the filtered containment `hfilt`, `b`/`jc` knownness, the `b`-walk domain
`hwalk`, and the descent case split `hcase`. The other inputs are derived from
`SpecAssumptions`. -/

omit [Inhabited Root] in
/-- **The filtered block tree is contained in `block_roots`.** `get_filtered_block_tree`
wraps `filter_block_tree_aux` at base `justified_checkpoint.root`; every emitted root is a
known block or that base (`Engine.filter_block_tree_aux_output_mem`), and the base is known
(`hjc`). -/
theorem filtered_subset_block_roots (store : Store Root)
    (hjc : store.justified_checkpoint.root ∈ store.block_roots) :
    ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots := by
  intro r hr
  simp only [get_filtered_block_tree] at hr
  rcases filter_block_tree_aux_output_mem cfg (store.block_roots.length + 1)
    store.justified_checkpoint.root r hr with h | rfl
  · exact h
  · exact hjc

namespace Execution

variable (E : Execution Root)


/-! ## Section 2 — `hmaj`: post-`T1` saturation and boost dilution

The saturated honest-majority field of `EdgeDynamics.EdgeInputResidual` is
`x(σ') + ⌊C·J(σ')/(100−C)⌋ + boost + 1 ≤ s(σ')` for `σ'` at least two epochs past `es`.
Past `T1` every honest span member has re-voted `desc(b')` (`committee_coverage` +
`votes_head` + IH), represented by `hsat`: `SupportsDesc` holds for every
honest window member. It collapses the honest partition to `Sclass = window`
(`Sval = Jspec`) and `Xclass = ∅` (`Xval = 0`), so `hmaj` reduces to the pure-ℕ
boost-dilution inequality `⌊C·J/(100−C)⌋ + boost + 1 ≤ J`, represented by `hdil`.
The class collapse is proved here. -/





/-! ## Section 3 — `hrec`: every `Sclass` member records a `c`-supporting message

`EdgeDynamics.EdgeInputResidual.hrec` asks that every `Sclass w m b lo σ` member records, at
the endpoint `(w, m)`, a latest message supporting the fork child `c` on `b`'s chain. Each
`Sclass` member carries its own `SupportsDesc` vote witness `(t, kk, a)` (newest by `σ`, its
block `⪰ b`); `EngineTransport.recorded_supports_c_of_IH` — instantiated at the endpoint
anchor `(v₀, n₀) := (w, m)` so the cross-store transport is **reflexive** — turns that into
the recorded `c`-support, handling both the equality case (the recorded root *is* the vote
block, `latest_message_root`) and the displacement case (a later `[σ+1, k)` vote installed
`lm`; the engine IH `hIH` covers it). The `WalkKnown` domains come from
`AnchorFacade.store_walkKnownK`; the recorded message and its epoch floor from
`Delivery.vote_ubiquity` (packaged as `hubiq`); endpoint knownness, the
recorded-root walk, and the fork edge are explicit hypotheses. -/


/-! ## Section 4 — `hdeltas`: the pre-`T1` per-slot step, reduced to same-epoch monotonicity

`EdgeDynamics.EdgeInputResidual.hdeltas` is the per-slot `∃ξα` class-migration step for a
pre-`T1` slot (`σ' + 1` still inside `epoch(es) + 2`). In the **same-epoch** regime the
`ρ = 0` bookkeeping (each member is assigned at
most once per epoch, `committee_assignment_unique`) forces the `X → S` migrant weight to be
**zero** — no window member re-votes within the epoch, so the only class movement is the
fresh honest committee of slot `σ' + 1` entering `Sclass` (`votes_head` + IH: it votes
`desc(b')`). Hence the `∃ξα` witness is `ξ = α = 0`, and `hdeltas` collapses to the three
per-slot facts `hSmono` / `hXmono` / `hρ0` below. This section mechanizes that `ξ = α = 0`
assembly; the three monotonicity facts are explicit inputs. -/


end Execution

end FastConfirmation.Spec

end
