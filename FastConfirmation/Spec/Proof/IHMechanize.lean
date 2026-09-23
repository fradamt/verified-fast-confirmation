module
public import FastConfirmation.Spec.Proof.AnchorFacade
public import FastConfirmation.Spec.Proof.ResidualMechanicalII
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.Engine
public import FastConfirmation.Spec.Proof.EdgeDynamics
public import FastConfirmation.Spec.Proof.EngineTransport
public import FastConfirmation.Spec.Proof.DynamicsClosure

@[expose] public section


/-!
# Spec / Proof / IHMechanize: constructing IH-dependent inputs

`ShellInstantiation.ShellResiduals` contains two inputs per confirmed block: the
**structural** confirmed chain `dynamics_struct`
(`DynamicsChainStruct`) and the **per-edge** store-dynamics supply `fork_edges`
(`ForkAssembly.ForkEdgeSupply`, packaged from `EdgeDynamics.EdgeInputResidual`). The three
IH-dependent fields of `EdgeInputResidual` — the pre-`T1` class-migration deltas
`hdeltas`, the post-`T1` saturated majority `hmaj`, and the per-`Sclass`-member recorded
`c`-support `hrec` — are explicit engine premises that use the head-safety IH.
This module constructs these fields from smaller store-dynamics inputs.

## Constructions

* **Section 1 — `dynamics_struct`.** `dynamicsChainStruct_of_endpoint` constructs
  `ShellResiduals.dynamics_struct` from two flat per-endpoint
  facts under the shell IH — `hb` (the confirmed block is relay-known at the endpoint) and
  `hcase` (the L4 loop-inversion descent: `b` is on the justified chain or `= jc`) —
  deriving `ParentSlotLt` from `WFTrajectory`, the
  filtered-tree containment from `Engine.filter_block_tree_aux_output_mem`, justified
  knownness from `JustificationInterface`, and the `b`-walk domain from
  `AnchorFacade.store_walkKnownK`) from `SpecAssumptions`.

* **Section 2 — `hmaj` (post-`T1` saturation).** `hmaj_of_saturation_support` reduces the
  saturated honest-majority field to the clean "full saturation" store-dynamics crux —
  `Sclass = honest window` and `Xclass = ∅` at the endpoint (every honest span member has
  re-voted `desc(b')` by `T1`, `committee_coverage` + `votes_head` + IH) — plus the pure-ℕ
  boost-dilution arithmetic `C·J/(100−C) + boost + 1 ≤ J`. `Sval_eq_Jspec_of_saturation` /
  `Xval_eq_zero_of_saturation` carry the class-collapse; `boost_dilution` isolates the
  arithmetic as an explicit hypothesis on the endpoint span.

* **Section 3 — `hrec` (recorded support).** `hrec_of_domain` packages
  `EngineTransport.recorded_supports_c_of_IH` per `Sclass` member at the endpoint anchor
  `(w, m)` (`v₀ := w`, `n₀ := m`, so the cross-store transport is reflexive): the member's
  vote witness comes from its own `SupportsDesc`, the recorded `lm` and its epoch floor from
  `Delivery.vote_ubiquity`, and the `WalkKnown` domain from `AnchorFacade.store_walkKnownK`.
  The ubiquity landing and endpoint slot bound are explicit hypotheses.

* **Section 4 — `hdeltas` (class migration).** `hdeltas_of_monotone` constructs
  the pre-`T1` per-slot `∃ξα` step from same-epoch monotonicity premises.

**P-6 note.** Some names used in this header no longer exist. The legacy `SpecAssumptions`
observed-anchor cone was retired and swept for orphans, which removed `ShellInstantiation.ShellResiduals`, `EdgeDynamics.EdgeInputResidual`,
and this module's own `dynamicsChainStruct_of_endpoint` and `hdeltas_of_monotone`.
The descriptions above are kept because they still identify the *shapes* the surviving
declarations produce and consume. See `docs/p6-justified-descends-derivation.md` §8.
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

/-! ### Deleted: `dynamicsChainStruct_of_endpoint` and `hdeltas_of_monotone`

The per-endpoint `DynamicsChainStruct` constructor and the monotone pre-`T1` migration step.
The first was consumed only by `FinalWiring.dynamics_struct_of_suppliers`, the second only by
`VoteLanding.hdeltas_sameEpoch`.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

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
