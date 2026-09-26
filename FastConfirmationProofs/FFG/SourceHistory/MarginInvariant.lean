module
public import FastConfirmationProofs.Discount.GroundWeightTransport
public import FastConfirmationProofs.Checkpoints.CheckpointMarginInputs
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.Execution.Trajectory.InductionHypothesis
public import FastConfirmationProofs.Checkpoints.CheckpointEquivalence
public import FastConfirmationProofs.Safety.ConfirmedPrefixSafety

@[expose] public section

/-!
# Spec / Proof / INVstarTrack

Connects FFG source-history edges to the recorded fork-choice margin invariant.

This module contains `ForkEdgeGroundInputs`, `mem_isAncestor_of_parentChain` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the σ-general endpoint strip and the `INVstar` maintenance

`GroundBeta.bval_endpoint_strip_of_transport` transports the `INVstar` strip at the
**base** window end `es` (σ = es). At a later endpoint the relevant window end is the
current σ ≥ es, so this section re-states the strip transport at a general window end
σ, and delivers the `INVstar` maintenance that lifts the base `INVstar(es)` to
`INVstar(σ)` at the confirming anchor. -/



/-! ## Section 2 — the `hBb`-free per-edge bundle and its `DescendStep`

`ForkEdgeGroundInputs` is the `hBb`-free mirror of `ShellCompose.ForkEdgeEngineInputs`:
the base is `INVstar` at the confirming anchor `(vc, nc)` over `[lo, σ]` (the v1 invariant
over the store-independent `Bval`) instead of `INV2`, and there is **no** `hBb` field. Its
fields are exactly the inputs `GroundBeta.ledger_descendStep` consumes at window end σ: the
honest descent transports `hSt`/`hAt`, the invariant `hinv`, the filtered child `hchild`, the
`b`-side lower bound `hbside`, and the `Bval` sibling upper bound `hsib`. -/








omit [Inhabited Root] in
/-- **Chain members are ancestors of the chain's last block.** Along a parent-linked
chain of known roots ending at `b` (`getLast? = some b`), every member `c` is an ancestor of `b`
(`is_ancestor store b c`): the suffix from `c` to `b` composes single parent steps
(`is_ancestor_of_parent`) by transitivity (`is_ancestor_trans`, walk domains from the blanket
`hwalk`). This lets the ground per-edge supply be
demanded **only** for the `b`-chain edges the `DescendStep` chain walks — the `c` of each
`ForkEdgeGroundInputs` is always a `b`-ancestor (a winning child), so the off-`b`-chain losing
siblings appear only as `hsib` recorded-bound objects, never as harm-carrying subjects. -/
theorem mem_isAncestor_of_parentChain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {b : Root} (hb : b ∈ store.block_roots) :
    ∀ {L : List Root}, List.IsChain (fun a c => (store.blocks c).parent_root = a) L →
      (∀ x ∈ L, x ∈ store.block_roots) → L.getLast? = some b →
      ∀ c ∈ L, is_ancestor store (get_node_for_root b) (get_node_for_root c) = true := by
  intro L hchain
  induction hchain with
  | nil => intro _ hlast; simp at hlast
  | singleton a =>
    intro _ hlast c hc
    rw [List.getLast?_singleton, Option.some_inj] at hlast
    rw [List.mem_singleton] at hc
    subst hc; subst hlast
    exact is_ancestor_refl store _
  | @cons_cons a d rest hr _ ih =>
    intro hmem hlast c hc
    rw [List.getLast?_cons_cons] at hlast
    have hmem' : ∀ x ∈ d :: rest, x ∈ store.block_roots :=
      fun x hx => hmem x (List.mem_cons_of_mem _ hx)
    have hdmem : d ∈ store.block_roots := hmem' d (by simp)
    have hamem : a ∈ store.block_roots := hmem a (by simp)
    have ihd := ih hmem' hlast
    rcases List.mem_cons.mp hc with rfl | hc'
    · have hbd := ihd d (by simp)
      have hda := is_ancestor_of_parent hwf hdmem hamem hr
      exact is_ancestor_trans (a := get_node_for_root b) (b := get_node_for_root d)
        (c := get_node_for_root c) hwf (hwalk _ hamem b hb) (hwalk _ hamem d hdmem) hbd hda
    · exact ihd c hc'









end Execution

/-! ## Section 5 — the `hBb`-free safety headlines -/



end FastConfirmation.Spec

end
