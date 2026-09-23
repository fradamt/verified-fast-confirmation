module
public import FastConfirmation.Spec.Proof.FilterFuel
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / Descent

Gloas head descent follows nodes identified by a root and a payload status.
A beacon edge has two steps: select EMPTY or FULL at the parent root, then
select a pending beacon child of that resolved node.

`NodeDescendsTo` records actual selections under the full weight/root/status
key. `DescendsTo` is its root-facing form and counts beacon edges. The payload
selection is explicit: strict beacon-child weight domination alone does not
choose the parent's payload branch. Previous-slot payload selections have
zero weight and can depend on the status tie-breaker.

The conclusion concerns the target's pending node, so it proves beacon-root
ancestry without requiring a particular payload status at the target root.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Actual Gloas node paths -/

/-- An actual `get_head` path to beacon root `b`, counted in node steps.
Each step selects the complete Gloas key, including payload tie-breaking. -/
inductive NodeDescendsTo (cfg : Config) (store : Store Root) (blocks : List Root)
    (b : Root) : ℕ → ForkChoiceNode Root → Prop
  | here (status : PayloadStatus) (hb : b ∈ store.block_roots) :
      NodeDescendsTo cfg store blocks b 0 (ForkChoiceNode.mk b status)
  | step {n : ℕ} {head best : ForkChoiceNode Root}
      (hbest : (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) = some best)
      (hrec : NodeDescendsTo cfg store blocks b n best) :
      NodeDescendsTo cfg store blocks b (n + 1) head

namespace NodeDescendsTo

variable {cfg : Config}

/-- Strict weight domination is sufficient for one actual node selection. -/
theorem step_of_dominant {store : Store Root} {blocks : List Root}
    {b : Root} {n : ℕ} {head best : ForkChoiceNode Root}
    (hchild : best ∈ get_node_children store blocks head)
    (hdom : ∀ child ∈ get_node_children store blocks head, child ≠ best →
      get_weight cfg store child < get_weight cfg store best)
    (hrec : NodeDescendsTo cfg store blocks b n best) :
    NodeDescendsTo cfg store blocks b (n + 1) head :=
  NodeDescendsTo.step (get_head_argmax_dominant cfg hchild hdom) hrec

end NodeDescendsTo

/-- Root-facing Gloas descent. Each of the `n` beacon edges has a payload
resolution followed by a beacon-child selection, hence `2 * n` node steps. -/
def DescendsTo (cfg : Config) (store : Store Root) (blocks : List Root)
    (b : Root) (n : ℕ) (h : Root) : Prop :=
  NodeDescendsTo cfg store blocks b (2 * n) (ForkChoiceNode.mk h .pending)

namespace DescendsTo

variable {cfg : Config}

/-- The pending target root already reaches the target beacon block. -/
theorem here {store : Store Root} {blocks : List Root} {b : Root}
    (hb : b ∈ store.block_roots) : DescendsTo cfg store blocks b 0 b :=
  NodeDescendsTo.here .pending hb

/-- One beacon-edge step includes an actual parent payload selection. The
second selection uses strict weight domination among that resolved node's
pending beacon children. This replaces the impossible pending-to-pending
child step from the phase0 statement. -/
theorem step {store : Store Root} {blocks : List Root}
    {b h c : Root} {n : ℕ} {status : PayloadStatus}
    (hresolve : (get_node_children store blocks (ForkChoiceNode.mk h .pending)).argmax
      (fun child => toLex (get_weight cfg store child,
        toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
      some (ForkChoiceNode.mk h status))
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store blocks (ForkChoiceNode.mk h status))
    (hdom : ∀ child ∈ get_node_children store blocks (ForkChoiceNode.mk h status),
      child ≠ ForkChoiceNode.mk c .pending →
        get_weight cfg store child < get_weight cfg store (ForkChoiceNode.mk c .pending))
    (hrec : DescendsTo cfg store blocks b n c) :
    DescendsTo cfg store blocks b (n + 1) h := by
  have hp : NodeDescendsTo cfg store blocks b (2 * n + 2)
      (ForkChoiceNode.mk h .pending) :=
    NodeDescendsTo.step hresolve (NodeDescendsTo.step_of_dominant hchild hdom hrec)
  change NodeDescendsTo cfg store blocks b (2 * (n + 1)) _
  convert hp using 1 <;> omega

end DescendsTo

/-! ## Continued descent preserves beacon ancestry -/

/-- Once a node descends from beacon root `b`, all further head-loop steps
stay below that root. Payload resolution keeps the root; a beacon-child step
strictly increases its slot and continues the same beacon ancestry. -/
theorem get_head_aux_stays_below {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) {b : Root} :
    ∀ (fuel : ℕ) {head : ForkChoiceNode Root},
      WalkKnown store (store.blocks b).slot head.root →
      (get_ancestor store head (store.blocks b).slot).root = b →
      (get_ancestor store (get_head_aux cfg store blocks fuel head)
        (store.blocks b).slot).root = b := by
  intro fuel
  induction fuel with
  | zero => intro head _ hanc; exact hanc
  | succ fuel ih =>
    intro head hwalk hanc
    rw [get_head_aux_succ]
    cases hbest : (get_node_children store blocks head).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) with
    | none => exact hanc
    | some best =>
      have hmem : best ∈ get_node_children store blocks head := List.argmax_mem hbest
      rcases mem_get_node_children.mp hmem with hpending | hresolved
      · have hroot : best.root = head.root := hpending.2.1
        apply ih
        · rw [hroot]
          exact hwalk
        · exact (get_ancestor_root_eq_of_root_eq (a := best) (b := head)
            hroot (store.blocks b).slot).trans hanc
      · obtain ⟨_, _, hbestmem, hparent, _⟩ := hresolved
        have hbestknown : best.root ∈ store.block_roots := hsub _ hbestmem
        have hparent_lt : (store.blocks head.root).slot < (store.blocks best.root).slot := by
          have h := hwf best.root hbestknown (by rw [hparent]; exact hwalk.root_mem)
          rwa [hparent] at h
        have hb_le_head : (store.blocks b).slot ≤ (store.blocks head.root).slot := by
          have h := get_ancestor_slot_le_status hwf hwalk head.payload_status
          change (store.blocks (get_ancestor store head (store.blocks b).slot).root).slot ≤
            (store.blocks head.root).slot at h
          rwa [hanc] at h
        have hgt : (store.blocks b).slot < (store.blocks best.root).slot :=
          lt_of_le_of_lt hb_le_head hparent_lt
        have hparentwalk : WalkKnown store (store.blocks b).slot
            (store.blocks best.root).parent_root := by
          rw [hparent]
          exact hwalk
        have hbestwalk : WalkKnown store (store.blocks b).slot best.root :=
          WalkKnown.step hbestknown hgt hparentwalk
        apply ih hbestwalk
        rw [get_ancestor_step_status hwf hbestknown hgt hparentwalk]
        exact (get_ancestor_root_eq_of_root_eq
          (a := ForkChoiceNode.mk (store.blocks best.root).parent_root
            (get_parent_payload_status store (store.blocks best.root)))
          (b := head) hparent (store.blocks b).slot).trans hanc

/-! ## Following certified selections -/

/-- Enough fuel follows every actual Gloas selection in a node path and
then remains below the target's pending node. -/
theorem get_head_descends_node {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots)
    {b : Root} {n : ℕ} {head : ForkChoiceNode Root}
    (hdesc : NodeDescendsTo cfg store blocks b n head) :
    ∀ fuel, n ≤ fuel →
      (get_ancestor store (get_head_aux cfg store blocks fuel head)
        (store.blocks b).slot).root = b := by
  induction hdesc with
  | here status hb =>
    intro fuel _
    apply get_head_aux_stays_below cfg hwf hsub fuel (WalkKnown.stop hb (le_refl _))
    rw [get_ancestor_stop_status (le_refl _)]
  | @step n head best hbest hrec ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [get_head_aux_step cfg store blocks fuel head best hbest]
      exact ih fuel (by omega)

/-- A root path of `n` beacon edges needs at least `2 * n` node steps. The
result is beacon-root equality; the final payload status can be resolved. -/
theorem get_head_descends {store : Store Root} {blocks : List Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ blocks, r ∈ store.block_roots) {b : Root} {n : ℕ} {h : Root}
    (hdesc : DescendsTo cfg store blocks b n h) :
    ∀ fuel, 2 * n ≤ fuel →
      (get_ancestor store (get_head_aux cfg store blocks fuel (ForkChoiceNode.mk h .pending))
        (store.blocks b).slot).root = b :=
  get_head_descends_node cfg hwf hsub hdesc

/-- Root-path head safety. The existing beacon-depth bound supplies twice as
much node fuel through the Gloas head wrapper. -/
theorem is_ancestor_get_head {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {n : ℕ}
    (hdesc : DescendsTo cfg store (get_filtered_block_tree cfg store) b n
      store.justified_checkpoint.root)
    (hfuel : n ≤ (get_filtered_block_tree cfg store).length + 1) :
    is_ancestor store (get_head cfg store) (ForkChoiceNode.mk b .pending) = true := by
  rw [is_ancestor_pending, decide_eq_true_eq]
  exact get_head_descends cfg hwf hsub hdesc
    (2 * (get_filtered_block_tree cfg store).length + 2) (by omega)

end FastConfirmation.Spec

end
