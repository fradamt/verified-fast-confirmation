module
public import FastConfirmationProofs.FFG.SourceHistory.StoreDynamicsInputs
public import FastConfirmationProofs.Execution.Trajectory.WFTrajectory

@[expose] public section

/-!
# Execution / Trajectory / ChainWalkClosure

Proves chain-walk closure and store dynamics from scheduled handler steps.

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

/-!
# Spec / Proof / ResidualMechanicalII

This module contains `isChain_imp_of_mem`, `WalkClosure`, `walkKnown_of_closure` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section 0 — two reusable helpers

A member-restricted `List.IsChain` lift (mathlib's `IsChain.imp` is blanket), and
the generic `WalkKnown`-from-closure construction that discharges `walk_domain`'s
inductive obligation. -/

/-- **Member-restricted `IsChain` lift.** `List.IsChain.imp` requires the edge
implication for *all* pairs; this variant only needs it on pairs of list members —
enough to keep the per-edge residual scoped to the chain. -/
theorem isChain_imp_of_mem {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, List.IsChain R l →
      (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) → List.IsChain S l := by
  intro l p
  induction p with
  | nil => intro _; exact .nil
  | singleton a => intro _; exact .singleton a
  | @cons_cons a b rest hr _ ih =>
    intro h
    refine .cons_cons (h a (by simp) b (by simp) hr) (ih ?_)
    intro x hx y hy hxy
    exact h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy

/-- **A flat ancestor-closure store predicate.** Every known block strictly above
the target slot `sl` has a known parent — the first-order fact that makes the
`WalkKnown` walk toward `sl` stay inside the store. -/
def WalkClosure (store : Store Root) (sl : Slot) : Prop :=
  ∀ r ∈ store.block_roots, sl < (store.blocks r).slot →
    (store.blocks r).parent_root ∈ store.block_roots

/-- **`WalkKnown` from the parent-slot order + the flat closure.** Strong
induction on the block's slot: at or below `sl` the walk stops; above `sl` the
closure hands a known parent whose slot strictly drops (`ParentSlotLt`), so the
induction hypothesis walks it the rest of the way. Thus `ParentSlotLt` and
`WalkClosure` imply the required `WalkKnown` property. -/
theorem walkKnown_of_closure {store : Store Root} (sl : Slot)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hclosure : WalkClosure store sl) :
    ∀ r ∈ store.block_roots, WalkKnown store sl r := by
  have key : ∀ N r, (store.blocks r).slot = N → r ∈ store.block_roots →
      WalkKnown store sl r := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro r hs hr
      by_cases hle : (store.blocks r).slot ≤ sl
      · exact WalkKnown.stop hr hle
      · have hlt : sl < (store.blocks r).slot := not_le.mp hle
        have hpar_in : (store.blocks r).parent_root ∈ store.block_roots :=
          hclosure r hr hlt
        have hpar_lt := hwf r hr hpar_in
        exact WalkKnown.step hr hlt (ih _ (hs ▸ hpar_lt) _ rfl hpar_in)
  intro r hr
  exact key _ r rfl hr

/-- **A parent-linked chain of known roots is `Nodup`.** Along a parent-link chain
`(blocks c).parent_root = a`, the parent-slot order makes slots strictly increase
(oldest→newest), so all elements are distinct. Discharges the `Nodup` obligation of
the structural confirmed chain. -/
theorem parentLinkChain_nodup {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {l : List Root} (hmem : ∀ x ∈ l, x ∈ store.block_roots)
    (hchain : List.IsChain (fun a b => (store.blocks b).parent_root = a) l) :
    l.Nodup := by
  have hslt : List.IsChain
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot) l := by
    refine isChain_imp_of_mem hchain ?_
    intro a ha b hb hlink
    have hpin : (store.blocks b).parent_root ∈ store.block_roots := hlink ▸ hmem a ha
    have hlt := hwf b (hmem b hb) hpin
    rwa [hlink] at hlt
  have _htrans : Trans
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot) :=
    ⟨fun h1 h2 => lt_trans h1 h2⟩
  have hpair := (List.isChain_iff_pairwise
    (R := fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)).mp hslt
  exact hpair.imp (fun {a b} h (heq : a = b) => absurd (heq ▸ h) (lt_irrefl _))

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)




namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `walk_domain` from the flat closure `WalkClosure`

`MechanicalResiduals.walk_domain` asks for a `WalkKnown` walk domain over every
known root and every target slot. `walkKnown_of_closure` builds each `WalkKnown`
from the Layer-0 parent-slot order (`ParentSlotLt`, delivered at the trajectory
level by `WFTrajectory.store_parentSlotLt`) and the flat closure `WalkClosure` at
the target slot. So `walk_domain` reduces to `WalkClosure` at every honest store —
the `WalkKnown` inductive obligation is discharged; only the first-order closure
remains. -/




/-- **The structural confirmed-chain residual.** `DynamicsChainSupply`'s shape with
the `DynamicsResidual` edges replaced by the purely structural parent-link
`(blocks c).parent_root = a`, and carrying membership of every chain element in
`block_roots` (so the per-edge lift is member-scoped). This is the
`AncestryRoots.get_ancestor_roots` chain from the justified root to `b`; it
contains no `DynamicsResidual` assumptions. -/
def DynamicsChainStruct (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
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
      (∀ r ∈ (E.store cfg ext w m).justified_checkpoint.root :: ds,
        r ∈ (E.store cfg ext w m).block_roots) ∧
      List.IsChain
        (fun a c => ((E.store cfg ext w m).blocks c).parent_root = a)
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **The per-edge dynamics residual supply.** At every honest endpoint `(w, m)`
past `n₀` (given the strong-induction head-safety hypothesis), every real parent
edge `a ← c` of known blocks carries a `DynamicsResidual w m a c` — the engine's
per-fork content (`ResidualDischarge.DynamicsResidual`). The chain structure is
separated out so this predicate is required only on confirmed-chain edges. -/
def DynamicsEdgeSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
        E.DynamicsResidual cfg ext w m a c





/-- **The reduced residual bundle** (`ResidualMechanicalII`). Relative to
`MechanicalResiduals`, `anchor_unscheduled` comes from `WellFormedExecution`,
`walk_domain` is represented by `walk_closure`, and `dynamics_chain` is split
into structural and per-edge inputs. -/
structure MechanicalResidualsII (E : Execution Root) : Prop where
  /-- The flat ancestor-closure at every honest store and every target slot;
      together with `ParentSlotLt`, it implies `walk_domain`'s `WalkKnown`
      property. -/
  walk_closure : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
    WalkClosure (E.store cfg ext w m) sl
  /-- Justified-knownness per honest store. -/
  justified_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- Finalized-knownness per honest store. -/
  finalized_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- Cross-store finalized descent (Casper finalization consistency). -/
  finalized_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true
  /-- The observed-justified anchor lies on every later honest justified chain. -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- The structural confirmed-chain per `is_one_confirmed` block (the
      `get_ancestor_roots` parent-link chain — fork-choice-mechanical). -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- The per-edge `DynamicsResidual` supply. -/
  dynamics_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsEdgeSupply cfg ext b (n + 1)


end Execution




end FastConfirmation.Spec

end
