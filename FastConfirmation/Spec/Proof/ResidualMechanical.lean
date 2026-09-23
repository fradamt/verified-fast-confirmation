module
public import FastConfirmation.Spec.Proof.ResidualDischarge
public import FastConfirmation.Spec.Proof.WFTrajectory

@[expose] public section

/-!
# Spec / Proof / ResidualMechanical

This module contains `DynamicsChainSupply`, `MechanicalResiduals` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)




/-! ## Section 2 — finalized tracking from one cross-store residual

`genesis_fin_track` and `finalized_track` are the same statement at two anchors:
each honest store's finalized block is known and descends from an earlier honest
finalized root. Both collapse onto one cross-store finalized-descent residual
`hfin_descent` (`finalized(w, m) ⪰ finalized(v, k)` whenever `k ≤ m`) plus
finalized-knownness `hfin_known`. The genesis anchor `(E.store v 0)` is
`E.genesis_store` by definition — `hfin_descent … 0 …` (with `0 ≤ m`) supplies it,
`hfin_descent … (n+1) …` (with `n+1 ≤ m`) supplies the update anchor. This is the
Casper cross-store finalization-consistency fact represented by
`finalized_descent`. -/





/-- **The same-epoch dynamics-chain supply.** `LedgerChainInputCert`'s shape with
each edge's `LedgerCertInput` replaced by the more primitive same-epoch
`DynamicsResidual`. At every honest endpoint `(w, m)` past `n₀`, given head safety
at strictly earlier slots (the strong-induction hypothesis), the confirmed chain
from the justified root to `b` presents as a `List.IsChain DynamicsResidual` with
the fork-choice domain facts. The certificate seed the L4 chain fold supplies per
confirmed block. -/
def DynamicsChainSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∃ ds : List Root,
      (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
        r ∈ (E.store cfg ext w m).block_roots) ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      ds.Nodup ∧
      List.IsChain (E.DynamicsResidual cfg ext w m)
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b




/-- **The mechanical input bundle** produced by the `ResidualMechanical` reductions. Seven named
store-dynamics / FFG residuals, each in an existing shape:

* `anchor_unscheduled` — the `WFTrajectory` genesis anchor guard (no scheduled block's root
  is a genesis block's dangling parent pointer; a `WellFormedExecution`-shaped
  fact) that `store_parentSlotLt` consumes;
* `walk_domain` — the `WalkKnown` ancestor-closure walk domain per honest store;
* `justified_known` / `finalized_known` — the justified/finalized checkpoint roots
  are known per honest store;
* `finalized_descent` — cross-store finalized descent (Casper finalization
  consistency), used by both finalized-tracking fields;
* `observed_dom` — observed-justified justified-dominance;
* `dynamics_chain` — the per-confirmed-block same-epoch `DynamicsChainSupply`
  (the per-edge `DynamicsResidual` seeds plus the chain structure). -/
structure MechanicalResiduals (E : Execution Root) : Prop where
  /-- `WFTrajectory`: no scheduled block's root equals a genesis block's dangling parent. -/
  anchor_unscheduled : ∀ r ∈ E.genesis_store.block_roots, ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n → b.root ≠ (E.genesis_store.blocks r).parent_root
  /-- the `WalkKnown` walk domain over all known roots per honest store. -/
  walk_domain : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ t r : Root,
    r ∈ (E.store cfg ext w m).block_roots →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r
  /-- justified-knownness per honest store. -/
  justified_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- finalized-knownness per honest store. -/
  finalized_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- cross-store finalized descent (Casper): each honest store's finalized block
      descends from any earlier honest finalized root. -/
  finalized_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true
  /-- The rotated observed-justified anchor is on every honest justified
      chain (verbatim `L4ResidualHyps.observed_dom`). -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- Every `is_one_confirmed` block at an update store carries a
      same-epoch `DynamicsChainSupply` (the per-edge `DynamicsResidual` seeds). -/
  dynamics_chain : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainSupply cfg ext b (n + 1)


end Execution




end FastConfirmation.Spec

end
