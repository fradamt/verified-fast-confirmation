module
public import FastConfirmation.Spec.Proof.ObservedDom
public import FastConfirmation.Spec.Proof.L4Fold

@[expose] public section

/-!
# Spec / Proof / MicroSteps: structural reductions

This module supplies two reductions used by `ResidualMechanicalII` and
`ObservedDom`:

* **`walk_closure` from an anchor-minimum guard.** `ResidualMechanicalII.WalkClosure`
  asks every known block above the target slot to have a *known* parent. Its
  "parent is known **or** the anchor's dangling pointer `P`" half is Layer-0:
  `Execution.store_parentInRootsOr` re-exposes the `ParentInRootsOr P` component of
  `WFTrajectory.WFPlus` at the trajectory level (the same induction as
  `store_parentSlotLt`, extracting `.2.2.1`). `walkClosure_of_min` then derives
  `WalkClosure` from `ParentInRootsOr P` plus the flat
  **anchor/minimal-slot guard** `∀ r, parent = P → slot ≤ sl` (only the anchor's own
  dangling edge, not every block). So `walk_closure` shrinks to `anchor_slot_guard`.

* **The confirming-store descent used by `dynamics_struct`.** The loops in
  inversions (`L4Fold.find_latest_confirmed_descendant_spec` /
  `get_latest_confirmed_spec`) already expose that the confirmed block is a reset
  anchor or passed `is_one_confirmed`; strengthened here to `..._mem`, they also
  expose that a non-anchor result is a **member of `get_ancestor_roots store head r₀`**
  — i.e. it descends from the reset anchor `r₀` *at the confirming store*. This is the
  loop-structural half of `hcase`. Lifting it to the arbitrary endpoint `(w, m)` of
  `DynamicsChainStruct` uses an explicit cross-store transport premise.

A third reduction — the on-boundary source for `prev_greatest_justifiedIn`
(`update_fcv_observed_boundary`, `fcrStep_observed_boundary`,
`prev_greatest_justifiedIn_of_boundarySource`) — stood here too. It unfolded
`update_fast_confirmation_variables`' epoch-boundary rotation of
`current_epoch_observed_justified_checkpoint` for the observed-anchor filter bundle, and is
deleted with the legacy `SpecAssumptions` observed-anchor cone's orphan sweep (P-6; see the
section note below and `docs/p6-justified-descends-derivation.md` §8). The off-boundary
`fcrStep_observed_else` is unaffected.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section 1 — `walk_closure` from the anchor-minimum guard

`WalkClosure store sl` (`∀ r ∈ block_roots, sl < (blocks r).slot →
(blocks r).parent_root ∈ block_roots`) classifies *every* block above `sl`. Under
`ParentInRootsOr P store` each block's parent is already known **or** the anchor's
dangling `P`; parent-`P` blocks are guarded by the flat
minimal-slot fact `parent = P → slot ≤ sl`. -/

/-- **`WalkClosure` from `ParentInRootsOr` + the anchor-min guard.** For a block `r`
above `sl`, `ParentInRootsOr` gives its parent known (done) or `= P`; in the `= P`
case the guard forces `slot ≤ sl`, contradicting `sl < slot`. So the full closure
reduces to constraining only the parent-`P` blocks — the anchor's own edge. -/
theorem walkClosure_of_min {store : Store Root} {P : Root} {sl : Slot}
    (hQ : ParentInRootsOr P store)
    (hguard : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ sl) :
    WalkClosure store sl := by
  intro r hr hlt
  rcases hQ r hr with hin | hP
  · exact hin
  · exact absurd hlt (Nat.not_lt.mpr (hguard r hr hP))

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 2 — confirming-store descent from the loop inversions

`L4Fold.find_latest_confirmed_descendant_spec` shows the confirmed result is the input
`lcr` or passed `is_one_confirmed`. This strengthening additionally exposes the
loop-structural certificate: a non-`lcr` result is a **member of
`get_ancestor_roots store head base`** for the loop base — the
ascending chain from `base` toward the head — so it descends from a reset anchor *at
the confirming store*. The lift to an arbitrary endpoint `(w, m)` is represented by the
`DynamicsChainStruct` endpoint premise. -/

/-- **`find_latest_confirmed_descendant` on the head chain.** The result
is the input `lcr`, or it passed `is_one_confirmed` *and* lies on
`get_ancestor_roots store head base` for a loop base `base` — the ascending canonical
segment from `base` toward the head. Mirrors `find_latest_confirmed_descendant_spec`'s
`P`-closure structure with the loop membership (`prev_epoch_loop_spec` /
`tentative_loop_spec` already return `r ∈ roots`) threaded through both advancement
stages, so every advance witnesses a concrete base. -/
theorem find_latest_confirmed_descendant_mem (fcr_store : FastConfirmationStore Root)
    (lcr : Root) :
    find_latest_confirmed_descendant cfg ext fcr_store lcr = lcr ∨
    (is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store)
        (find_latest_confirmed_descendant cfg ext fcr_store lcr) = true ∧
      ∃ base : Root,
        find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
          get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base) := by
  set P : Root → Prop := fun r => r = lcr ∨
    (is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) r = true ∧
      ∃ base : Root, r ∈
        get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base)
    with hP
  have hprev : ∀ (ce : Epoch) (base acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base) acc) := by
    intro ce base acc hacc
    rcases prev_epoch_loop_spec cfg ext fcr_store ce
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base) acc with
      h | ⟨r, hr, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ ⟨hc, base, hr⟩)
  have htent : ∀ (base acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base) acc) := by
    intro base acc hacc
    rcases tentative_loop_spec cfg ext fcr_store
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root base) acc with
      h | ⟨r, hr, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ ⟨hc, base, hr⟩)
  change P (find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact Or.inl rfl
      | (apply htent; first | exact Or.inl rfl | exact hprev _ _ _ (Or.inl rfl))
      | exact hprev _ _ _ (Or.inl rfl)

/-! ## Section 3 — the source of `prev_greatest_justifiedIn`

`ObservedDom`'s sole corner (`is_start_slot_at_epoch = true`, no slot advance) has the
`fcrStep`-observed checkpoint set by `update_fast_confirmation_variables`' rotation.
`update_fcv_observed_boundary` computes that rotation **on** the epoch boundary: the
observed checkpoint becomes the store's `unrealized_justified_checkpoint` (when the
next slot is also an epoch start — only possible for `slots_per_epoch = 1`) or the
carried `previous_epoch_greatest_unrealized_checkpoint`. Both are greatest-unrealized
/ unrealized-justified checkpoints supplied by the boundary-source premise. -/

/-! ### Deleted: the epoch-boundary observed-rotation micro-steps

`update_fcv_observed_boundary`, `fcrStep_observed_boundary` and
`prev_greatest_justifiedIn_of_boundarySource` stood here. They unfolded the on-boundary
rotation of `current_epoch_observed_justified_checkpoint` for the observed-anchor filter
bundle's `observed_known` / `prev_greatest_justifiedIn` fields. The off-boundary
`fcrStep_observed_else` and the rest of the module are unaffected.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

namespace Execution

variable (E : Execution Root)

/-- **`ParentInRootsOr` at every node and second (Layer 0).** The `ParentInRootsOr P`
component of `WFTrajectory.WFPlus`, delivered at the trajectory level by exactly the
`store_parentSlotLt` induction (base: the `get_forkchoice_store` anchor's single
dangling edge; step: `WFPlus_foldl` over the scheduled events). `P` is the anchor's
dangling parent `ablk.message.parent_root`, uniform over `(v, n)`. This is the Layer-0
half of `WalkClosure` — every known block's parent is a known root or `P`. -/
theorem store_parentInRootsOr
    (hwf : WellFormedExecution E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hanchor : ∀ r ∈ E.genesis_store.block_roots, ∀ w n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n → b.root ≠ (E.genesis_store.blocks r).parent_root) :
    ∃ P : Root, ∀ (v : ValidatorIndex) (n : ℕ), ParentInRootsOr P (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]; exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  have hanchorP : ∀ w m (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w m → b.root ≠ ablk.message.parent_root := by
    intro w m b hb
    have hmem : ablk.root ∈ E.genesis_store.block_roots := by
      rw [hgeq]; simp [get_forkchoice_store]
    have hpeq : (E.genesis_store.blocks ablk.root).parent_root = ablk.message.parent_root := by
      rw [hgeq]; simp [get_forkchoice_store]
    rw [← hpeq]; exact hanchor ablk.root hmem w m b hb
  refine ⟨ablk.message.parent_root, fun v n => ?_⟩
  suffices key : ∀ k, WFPlus ablk.message.parent_root E (E.store cfg ext v k) from
    (key n).2.2.1
  intro k
  induction k with
  | zero =>
    refine ⟨hgws.core, hgws.parentSlotLt, ?_, E.blockProvenance cfg ext v 0⟩
    change ParentInRootsOr ablk.message.parent_root E.genesis_store
    rw [hgeq]
    intro r hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    subst hr
    right
    simp [get_forkchoice_store]
  | succ k ih =>
    change WFPlus ablk.message.parent_root E
      ((E.schedule v (k + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v k) (E.time_at (k + 1))))
    refine WFPlus_foldl cfg ext ablk.message.parent_root hwf
      hec.state_transition_slot hec.state_transition_pre_slot_lt hanchorP
      _ _ (fun b hb => ⟨v, k + 1, hb⟩) ?_
    exact on_tick_WFPlus cfg ablk.message.parent_root _ _ ih

/-- **`walk_closure` from the anchor-min guard.** Given the
`ParentInRootsOr P` at every honest store (`store_parentInRootsOr`, `P` explicit) and
the flat anchor-min guard `∀ r, parent = P → slot ≤ sl`, every `WalkClosure`
obligation follows by `walkClosure_of_min`. -/
theorem walkClosure_of_anchorGuard {P : Root}
    (hP : ∀ w ∈ E.honest, ∀ m : ℕ, ParentInRootsOr P (E.store cfg ext w m))
    (hguard : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root = P →
          ((E.store cfg ext w m).blocks r).slot ≤ sl) :
    ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot, WalkClosure (E.store cfg ext w m) sl :=
  fun w hw m sl => walkClosure_of_min (hP w hw m) (hguard w hw m sl)

end Execution

end FastConfirmation.Spec

end
