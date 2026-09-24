module
public import FastConfirmationProofs.Weak.Selection.WeakAncestryTransport
public import FastConfirmationProofs.Execution.Delivery.VoteDeadlineOrigin
public import FastConfirmationStatements.Premises.SelectedMargin

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
    (hec : BeaconExternalsPremises cfg ext E)
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
  have hlands_v : (get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d .pending)
      ((E.store cfg ext v n).blocks b).slot).root = b := by
    simpa only [is_ancestor_get_node_for_root, decide_eq_true_eq] using hanc
  -- replay it at `(w, k)`: same fuel (agreement at `d`), same walk
  have hgw : (get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d .pending)
        ((E.store cfg ext v n).blocks b).slot).root
      = (get_ancestor (E.store cfg ext w k) (ForkChoiceNode.mk d .pending)
        ((E.store cfg ext v n).blocks b).slot).root := by
    simp only [get_ancestor]
    rw [hagree d hd_v hd_w]
    exact get_ancestor_aux_congr_closed hagree hclosed hwalk_v hd_w _ _ _
  -- so the walk at `(w, k)` also lands on `b`, still at the `v`-side slot expression
  have hlands_w : (get_ancestor (E.store cfg ext w k) (ForkChoiceNode.mk d .pending)
      ((E.store cfg ext v n).blocks b).slot).root = b := by
    rw [← hgw]; exact hlands_v
  -- transport the slot expression to the `w`-side via block agreement at `b`,
  -- and conclude `is_ancestor` at `(w, k)`
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
  rw [← hbb]
  exact hlands_w


/-- A root reached by an admissible known walk is not permanently excluded. -/
theorem VotePathAdmissible.ancestor_not_excluded
    {v w : ValidatorIndex} {n boundary : ℕ} {slot : Slot} {d b : Root}
    (hparent : ParentSlotLt (E.store cfg ext v n))
    (hpath : VotePathAdmissible cfg ext E v n w boundary slot d)
    (hlands : (get_ancestor (E.store cfg ext v n)
      (ForkChoiceNode.mk d .pending) slot).root = b) :
    ¬ PermanentBlockExclusion cfg ext E v n b w boundary := by
  induction hpath with
  | @stop r hr hnot hle =>
    rw [get_ancestor_stop hle] at hlands
    simpa only using hlands ▸ hnot
  | @step r hr hnot hgt hp ih =>
    rw [get_ancestor_step hparent hr hgt hp.walkKnown] at hlands
    exact ih hlands

/-- Relay one known ancestor of an honest signed head from its vote deadline. -/
theorem Execution.honest_head_ancestor_known_at_endpoint_weak
    (hA : SelectedMarginAssumptions cfg ext E)
    {u w : ValidatorIndex} {n m : ℕ} {b : Root}
    (hu : u ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hb : b ∈ (E.store cfg ext u n).block_roots)
    (hanc : is_ancestor (E.store cfg ext u n)
      (get_node_for_root (get_head cfg (E.store cfg ext u n)).root)
      (get_node_for_root b) = true)
    (hslot : E.slot_at cfg n < E.slot_at cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hA.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]; simp only [get_forkchoice_store]; omega
  obtain ⟨hnext, hlt⟩ := E.past_slot_deadline_target_gate cfg
    hA.whole_seconds hgenTime hslot
  have hhead : (get_head cfg (E.store cfg ext u n)).root ∈
      (E.store cfg ext u n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext u n) with h | h
    · exact h
    · rw [h]
      exact hA.domain.justified_root_known u hu n hHn
  have hwalk : WalkKnown (E.store cfg ext u n)
      ((E.store cfg ext u n).blocks b).slot
      (get_head cfg (E.store cfg ext u n)).root :=
    E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ u n b hb _ hhead
  have hHnext : E.WithinHorizon cfg
      (E.slot_start cfg (E.slot_at cfg n + 1)) :=
    E.withinHorizon_mono cfg hnext hHm
  have hpath := hA.domain.honest_head_paths u hu n hHn w
    ((E.store cfg ext u n).blocks b).slot hHnext hwalk
  have hparent : ParentSlotLt (E.store cfg ext u n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled u n
  have hlands : (get_ancestor (E.store cfg ext u n)
      (ForkChoiceNode.mk (get_head cfg (E.store cfg ext u n)).root .pending)
      ((E.store cfg ext u n).blocks b).slot).root = b := by
    simpa only [is_ancestor_get_node_for_root, decide_eq_true_eq] using hanc
  have hnot := VotePathAdmissible.ancestor_not_excluded cfg ext E
    hparent hpath hlands
  exact (hA.synchrony.deadline_block_relay u hu n b hHn hb hdue
    w hw m hHm hnext hlt).resolve_right hnot

end FastConfirmation.Spec

end
