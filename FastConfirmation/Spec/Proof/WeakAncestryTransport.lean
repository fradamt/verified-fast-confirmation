module
public import FastConfirmation.Spec.Proof.AnchorFacade
public import FastConfirmation.Spec.Proof.BlockAgreement

@[expose] public section

/-!
# Spec / Proof / WeakAncestryTransport: containment-free `is_ancestor` transport

`Knownness.mem_of_honest_past_descendant` replays an `is_ancestor` walk from one
store into another through a **store containment** (`Synchrony.block_relay` into
the confirming node), which the weak-synchrony model (`Model/WeakSynchrony.lean`)
cannot supply: its confirming observer is not a member of `E.honest`, so no
relay law applies to it in either direction.

This module rebuilds the transport with **no containment hypothesis at all**.
The only cross-store input is block-root injectivity
(`WellFormedExecution.blocks_agree` at *commonly*-known roots) plus each store's
own parent-closure; both are Layer-0 facts available at every node, honest or
not. Nothing here mentions the `Weak` namespace — these are pure
fork-choice/store lemmas.

## What is delivered

* **`get_ancestor_aux_congr_closed`** — the walk-restricted congruence.
  `BlockAgreement.get_ancestor_aux_congr` demands *blanket* agreement
  `∀ x ∈ s.block_roots, s.blocks x = t.blocks x` (only available under
  `s.block_roots ⊆ t.block_roots`). Here agreement is required only at roots
  known to **both** stores, and membership in `t.block_roots` is carried as an
  invariant along the walk: it is re-established at each step by `t`'s
  parent-closure above the target slot (`hclosed`), which applies exactly
  because the recursion continues only while the target slot is below the
  current block's slot.
* **`Execution.store_parentClosedAbove`** — the parent-closure input, at every
  node and second: above the anchor slot every known block has a known parent
  (`store_nonAnchorParentKnown`; the anchor branch is excluded since the anchor
  sits *at* `ablk.message.slot`, not above the target slot).
* **`Execution.store_walkKnown_ge`** — `store_walkKnownK` with the target slot
  freed from "the slot of a known block" to any `sl ≥ ablk.message.slot`
  (`E5Filter.walkKnown_of_anchorSlot` takes the anchor-slot lower bound
  directly).
* **`Execution.is_ancestor_transport_closed`** — the assembled transport: an
  `is_ancestor` fact computed at `(v, n)` for a descendant `d` known at a
  *foreign* `(w, k)` places the ancestor `b` in `(w, k)`'s block roots, with no
  containment in either direction.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## The walk-restricted `get_ancestor_aux` congruence

`get_ancestor_aux` reads `blocks` only at the roots it walks through. On the
`WalkKnown s slot r` domain those roots are known to `s`; if the *starting* root
is also known to `t` and `t` is parent-closed above `slot`, then every walked
root is known to `t` as well, so the two stores agree on all of them and compute
the same ancestor — no containment between the stores is needed. -/

/-- **Walk-restricted congruence (the containment-free replacement for
`BlockAgreement.get_ancestor_aux_congr`).** Agreement is assumed only at
*commonly* known roots (`hagree`), and `r ∈ t.block_roots` is carried as an
invariant along the walk: the recursion steps only while `slot < (blocks r).slot`,
exactly where `t`'s parent-closure (`hclosed`) hands the invariant to the parent. -/
theorem get_ancestor_aux_congr_closed [LinearOrder Root] [Inhabited Root] {s t : Store Root} {slot : Slot}
    (hagree : ∀ x ∈ s.block_roots, x ∈ t.block_roots → s.blocks x = t.blocks x)
    (hclosed : ∀ x ∈ t.block_roots, slot < (t.blocks x).slot →
      (t.blocks x).parent_root ∈ t.block_roots)
    {r : Root} (hw : WalkKnown s slot r) (hrt : r ∈ t.block_roots) :
    ∀ statusS statusT : PayloadStatus, ∀ fuel : ℕ,
      (get_ancestor_aux s slot fuel (ForkChoiceNode.mk r statusS)).root =
        (get_ancestor_aux t slot fuel (ForkChoiceNode.mk r statusT)).root := by
  revert hrt
  induction hw with
  | @stop r hr hle =>
    intro hrt statusS statusT fuel
    cases fuel with
    | zero => rfl
    | succ f =>
      simp only [get_ancestor_aux]
      rw [if_neg (by simpa using hle),
        if_neg (by rw [← hagree r hr hrt]; simpa using hle)]
  | @step r hr hgt hp ih =>
    intro hrt statusS statusT fuel
    have hb : s.blocks r = t.blocks r := hagree r hr hrt
    have hpt : (s.blocks r).parent_root ∈ t.block_roots := by
      rw [hb]; exact hclosed r hrt (by rw [← hb]; exact hgt)
    cases fuel with
    | zero => rfl
    | succ f =>
      simp only [get_ancestor_aux]
      rw [if_pos (by simpa using hgt), if_pos (by rw [← hb]; simpa using hgt), ← hb]
      exact ih hpt _ _ f

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)
variable (E : Execution Root)

/-! ## The two store-side inputs

Both are read off the Layer-0 anchor facade (`AnchorFacade`), at **every** node
and second — no honesty, no relay. -/

/-- **Parent-closure above the anchor slot.** At any target slot `sl` at or above
the anchor's slot, every known block strictly above `sl` has a known parent:
`NonAnchorParentKnown` leaves only the anchor as a possible exception, and
`store_anchor_block` pins the anchor's slot to `ablk.message.slot ≤ sl`,
contradicting `sl < slot`. This is `get_ancestor_aux_congr_closed`'s `hclosed`. -/
theorem Execution.store_parentClosedAbove (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    {sl : Slot} (hsl : ablk.message.slot ≤ sl) (w : ValidatorIndex) (k : ℕ) :
    ∀ x ∈ (E.store cfg ext w k).block_roots, sl < ((E.store cfg ext w k).blocks x).slot →
      ((E.store cfg ext w k).blocks x).parent_root ∈ (E.store cfg ext w k).block_roots := by
  intro x hx hlt
  rcases E.store_nonAnchorParentKnown cfg ext hgeq w k x hx with heq | hin
  · subst heq
    rw [E.store_anchor_block cfg ext hwf hgeq w k hx] at hlt
    exact absurd hlt (Nat.not_lt.mpr hsl)
  · exact hin

/-- **The walk domain at any target slot at or above the anchor slot.**
`store_walkKnownK` with its target freed from "the slot of a known block":
`E5Filter.walkKnown_of_anchorSlot` consumes the anchor-slot lower bound `hsl`
directly, so no anchor-minimal-slot instance at a known target is needed. -/
theorem Execution.store_walkKnown_ge (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot) (hparent : ablk.message.parent_root ≠ ablk.root)
    {sl : Slot} (hsl : ablk.message.slot ≤ sl) (w : ValidatorIndex) (k : ℕ) :
    ∀ r ∈ (E.store cfg ext w k).block_roots, WalkKnown (E.store cfg ext w k) sl r := by
  have hpsl : ParentSlotLt (E.store cfg ext w k) :=
    E.store_parentSlotLt cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w k
  have hQ : ParentInRootsOr ablk.message.parent_root (E.store cfg ext w k) := by
    intro r hr
    rcases E.store_nonAnchorParentKnown cfg ext hgeq w k r hr with heq | hin
    · right; subst heq; rw [E.store_anchor_block cfg ext hwf hgeq w k hr]
    · left; exact hin
  exact walkKnown_of_anchorSlot hpsl hQ
    (E.store_anchor_guard cfg ext hwf hgeq hparent w k) hsl

/-! ## The containment-free transport

The replacement for `Knownness.mem_of_honest_past_descendant`'s geometric core:
an `is_ancestor` fact computed at `(v, n)` about a descendant `d` that some
*other* store `(w, k)` also knows lands its ancestor `b` in `(w, k)`'s block
roots. Neither store is assumed to contain the other; the only cross-store input
is `blocks_agree` at the commonly-known roots, which `WellFormedExecution`
supplies through block-root injectivity at every node. -/

/-- **Containment-free `is_ancestor` transport.** If `d` descends from `b` in
`(v, n)`'s store and `d` is known at `(w, k)`, then `b` is known at `(w, k)`.
The `b`-slot walk from `d` is known in both stores (`store_walkKnownK` at `v`,
`store_walkKnown_ge` at `w`), the two `get_ancestor` wrappers get the same fuel
(`hagree` at the commonly-known `d`), and `get_ancestor_aux_congr_closed`
replays the walk verbatim into `(w, k)`; `get_ancestor_spec` then puts its
endpoint — which is `b` — in `(w, k)`'s block roots. -/
theorem Execution.is_ancestor_transport_closed (hwf : WellFormedExecution E)
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
    b ∈ (E.store cfg ext w k).block_roots := by
  -- cross-store agreement at the commonly-known roots (no containment)
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots, x ∈ (E.store cfg ext w k).block_roots →
      (E.store cfg ext v n).blocks x = (E.store cfg ext w k).blocks x := fun x hxv hxw =>
    hwf.blocks_agree (E.blockProvenance cfg ext v n) (E.blockProvenance cfg ext w k) hxv hxw
  -- the two walk domains at the target slot `(blocks b).slot`, and `w`'s closure there
  have hclosed := E.store_parentClosedAbove cfg ext hwf hgeq hanchor w k
  have hwalk_v : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks b).slot d :=
    E.store_walkKnownK cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩ v n b hb_v d hd_v
  have hwalk_w : WalkKnown (E.store cfg ext w k)
      ((E.store cfg ext v n).blocks b).slot d :=
    E.store_walkKnown_ge cfg ext hwf hec hgeq hslot hparent hanchor w k d hd_w
  have hpsl_w : ParentSlotLt (E.store cfg ext w k) :=
    E.store_parentSlotLt cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w k
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
  have hspec := (get_ancestor_spec hpsl_w hwalk_w).1
  rw [← hgw, hlands_v] at hspec
  exact hspec

end FastConfirmation.Spec

end
