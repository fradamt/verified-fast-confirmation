module
public import FastConfirmation.Spec.Proof.WeakAncestryTransport

@[expose] public section

/-!
# Spec / Proof / WeakAncestryEndpoint: cross-store `is_ancestor` replay

`WeakAncestryTransport.lean`'s `Execution.is_ancestor_transport_closed` replays
an `is_ancestor` walk computed at `(v, n)` into a foreign store `(w, k)` and
concludes only *membership*: the ancestor `b` lands in `(w, k)`'s block roots.
Several downstream obligations need the stronger fact — that `is_ancestor`
itself, recomputed at `(w, k)`, is still `true` — since `is_ancestor` is what
feeds fork-choice predicates such as `filter_block_tree` and the FFG helpers
directly, rather than raw membership.

This module supplies that companion, `Execution.is_ancestor_replay_closed`,
built from the same containment-free ingredients as `WeakAncestryTransport`:
block-root injectivity at commonly-known roots (`WellFormedExecution.blocks_agree`)
and each store's own parent-closure/walk-domain facts
(`Execution.store_parentClosedAbove`, `Execution.store_walkKnown_ge`,
`Execution.store_walkKnownK`). No store containment is assumed in either
direction.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable (E : Execution Root)

/-- **Containment-free `is_ancestor` replay.** If `d` descends from `b` in
`(v, n)`'s store (as witnessed by `is_ancestor`) and `d` is known at a foreign
store `(w, k)`, then `is_ancestor` recomputed at `(w, k)` for the same pair
`(d, b)` is still `true` — not just `b ∈ (w, k)`'s block roots.

The proof composes:
* `Execution.is_ancestor_transport_closed` for the membership fact `b ∈ (w, k)`'s
  block roots (everything it needs is already in the hypothesis set here);
* `WellFormedExecution.blocks_agree` at `b`, now known to both stores, to
  identify the two `is_ancestor` wrappers' target-slot expressions;
* the same walk replay (`get_ancestor_aux_congr_closed`, fed by
  `store_walkKnownK`/`store_walkKnown_ge`/`store_parentClosedAbove`) used by
  `is_ancestor_transport_closed`, to carry the `(v, n)`-side landing fact on
  `d`'s walk to `b`'s slot into `(w, k)`. -/
theorem Execution.is_ancestor_replay_closed (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot) (hparent : ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} {n k : ℕ} {d b : Root}
    (hanchor : ablk.message.slot ≤ ((E.store cfg ext v n).blocks b).slot)
    (hd_v : d ∈ (E.store cfg ext v n).block_roots)
    (hd_w : d ∈ (E.store cfg ext w k).block_roots)
    (hb_v : b ∈ (E.store cfg ext v n).block_roots)
    (hanc : is_ancestor (E.store cfg ext v n) (get_node_for_root d) (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext w k) (get_node_for_root d) (get_node_for_root b) = true := by
  -- `b` is known at `(w, k)` too, via the membership transport.
  have hb_w : b ∈ (E.store cfg ext w k).block_roots :=
    E.is_ancestor_transport_closed cfg ext hwf hec hgeq hslot hparent hanchor hd_v hd_w hb_v hanc
  -- cross-store agreement at the commonly-known roots (no containment)
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots, x ∈ (E.store cfg ext w k).block_roots →
      (E.store cfg ext v n).blocks x = (E.store cfg ext w k).blocks x := fun x hxv hxw =>
    hwf.blocks_agree (E.blockProvenance cfg ext v n) (E.blockProvenance cfg ext w k) hxv hxw
  -- `b`'s block agrees between the two stores, now that it is known to both
  have hbb : (E.store cfg ext v n).blocks b = (E.store cfg ext w k).blocks b := hagree b hb_v hb_w
  -- the two walk domains at the target slot `(blocks b).slot` (`v`-side expression),
  -- and `w`'s closure there
  have hclosed := E.store_parentClosedAbove cfg ext hwf hgeq hanchor w k
  have hwalk_v : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks b).slot d :=
    E.store_walkKnownK cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩ v n b hb_v d hd_v
  have hwalk_w : WalkKnown (E.store cfg ext w k)
      ((E.store cfg ext v n).blocks b).slot d :=
    E.store_walkKnown_ge cfg ext hwf hec hgeq hslot hparent hanchor w k d hd_w
  -- the walk at `(v, n)` lands on `b`
  have hlands_v : get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d)
      ((E.store cfg ext v n).blocks b).slot = ForkChoiceNode.mk b := by
    simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hanc
  -- replay it at `(w, k)`: same fuel (agreement at `d`), same walk
  have hgw : get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d)
        ((E.store cfg ext v n).blocks b).slot
      = get_ancestor (E.store cfg ext w k) (ForkChoiceNode.mk d)
        ((E.store cfg ext v n).blocks b).slot := by
    simp only [get_ancestor]
    rw [hagree d hd_v hd_w]
    exact get_ancestor_aux_congr_closed hagree hclosed hwalk_v hd_w _
  -- so the walk at `(w, k)` also lands on `b`, still at the `v`-side slot expression
  have hlands_w : get_ancestor (E.store cfg ext w k) (ForkChoiceNode.mk d)
      ((E.store cfg ext v n).blocks b).slot = ForkChoiceNode.mk b := by
    rw [← hgw]; exact hlands_v
  -- transport the slot expression to the `w`-side via block agreement at `b`,
  -- and conclude `is_ancestor` at `(w, k)`
  simp only [is_ancestor, get_node_for_root, decide_eq_true_eq]
  rw [← hbb]
  exact hlands_w

end FastConfirmation.Spec

end
