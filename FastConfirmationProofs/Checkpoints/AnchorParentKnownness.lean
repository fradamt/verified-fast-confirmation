module
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability
public import FastConfirmationProofs.Execution.Trajectory.WFTrajectory

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Checkpoints / AnchorParentKnownness

Proves that non-anchor parent blocks are known in stores used by ancestry arguments.

This module contains `NonAnchorParentKnown`, `SameBlocks.nonAnchorParentKnown`, `nonAnchorParentKnown_insert` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section 1 — the parent-known companion `NonAnchorParentKnown`

Every known block either *is* the genesis anchor `aRoot` or has a parent that is
itself a known root. This is strictly stronger than `WFTrajectory.ParentInRootsOr`
(which lets a *non-anchor* block name the dangling parent `P`): it captures
`on_block`'s guard `block.parent_root ∈ block_roots`, so the only block ever naming
the dangling `P` is the anchor. It reads only `block_roots` + `blocks`, so it is a
standalone fold (no `WellFormedStoreCore`), and rides across every block-set-
preserving helper by `SameBlocks`. -/

/-- Every known block is the anchor `aRoot`, or its parent pointer is a known
root. The `on_block`-guard companion to `WFTrajectory.ParentInRootsOr`. -/
def NonAnchorParentKnown (aRoot : Root) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots,
    r = aRoot ∨ (store.blocks r).parent_root ∈ store.block_roots

/-- `SameBlocks` carries `NonAnchorParentKnown` across: it reads only
`block_roots` and `blocks`. -/
theorem SameBlocks.nonAnchorParentKnown {s t : Store Root} (h : SameBlocks s t)
    (aRoot : Root) (hs : NonAnchorParentKnown aRoot s) : NonAnchorParentKnown aRoot t := by
  obtain ⟨hbr, hb, _⟩ := h
  simp only [NonAnchorParentKnown, ← hbr, ← hb]
  exact hs

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
/-- Block insertion preserves `NonAnchorParentKnown`. The new block's parent was
checked known by `on_block`'s first guard (`hpar_in`), so it lands in the
parent-known branch; every older block keeps its classification. -/
theorem nonAnchorParentKnown_insert (aRoot : Root) (store : Store Root) (block_root : Root)
    (block : BeaconBlock Root) (state : BeaconState Root) (br : List Root)
    (hsub : ∀ r ∈ store.block_roots, r ∈ br)
    (hbr : ∀ r ∈ br, r = block_root ∨ r ∈ store.block_roots)
    (hQ : NonAnchorParentKnown aRoot store)
    (hpar_in : block.parent_root ∈ store.block_roots) :
    NonAnchorParentKnown aRoot { store with
      block_roots := br
      blocks := Function.update store.blocks block_root block
      block_states := Function.update store.block_states block_root state } := by
  intro r hr
  dsimp only at hr ⊢
  by_cases hrb : r = block_root
  · subst hrb
    rw [Function.update_self]
    exact Or.inr (hsub _ hpar_in)
  · rw [Function.update_of_ne hrb]
    have hrin : r ∈ store.block_roots := (hbr r hr).resolve_left hrb
    rcases hQ r hrin with heq | hin
    · exact Or.inl heq
    · exact Or.inr (hsub _ hin)

/-- `on_block` preserves `NonAnchorParentKnown`: the new edge is guard-checked
(`nonAnchorParentKnown_insert`), and the four post-helpers are block-identity-
preserving (`SameBlocks`). -/
theorem on_block_nonAnchorParentKnown (aRoot : Root) {store store' : Store Root}
    {sb : SignedBeaconBlock Root} (hQ : NonAnchorParentKnown aRoot store)
    (hh : on_block cfg ext store sb = some store') :
    NonAnchorParentKnown aRoot store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact hQ
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh with hp hpayload hslot hfin hfc
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      let added : Store Root :=
        { store with
          block_roots := store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state
          payload_timeliness_vote := Function.update store.payload_timeliness_vote
            sb.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update store.payload_data_availability_vote
            sb.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added state sb.message.payload_attestations with
        | none => none
        | some notified => some (compute_pulled_up_tip cfg ext
            (update_checkpoints
              (update_proposer_boost_root cfg
                (record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              state.current_justified_checkpoint state.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added state sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).nonAnchorParentKnown aRoot ?_
        refine (update_checkpoints_sameBlocks _ _ _).nonAnchorParentKnown aRoot ?_
        refine (update_proposer_boost_root_sameBlocks cfg _ _ _).nonAnchorParentKnown aRoot ?_
        refine (record_block_timeliness_sameBlocks cfg _ _).nonAnchorParentKnown aRoot ?_
        refine (notify_ptc_messages_sameBlocks cfg ext hn).nonAnchorParentKnown aRoot ?_
        refine nonAnchorParentKnown_insert aRoot store sb.root sb.message state
          (store.block_roots ++ [sb.root]) ?_ ?_ hQ hp
        · intro r hr
          exact List.mem_append_left _ hr
        · intro r hr
          rw [List.mem_append, List.mem_singleton] at hr
          exact hr.symm

omit [LinearOrder Root] in
/-- `on_tick` preserves `NonAnchorParentKnown` (block-identity-preserving). -/
theorem on_tick_nonAnchorParentKnown (aRoot : Root) (store : Store Root) (time : ℕ)
    (h : NonAnchorParentKnown aRoot store) :
    NonAnchorParentKnown aRoot (on_tick cfg store time) :=
  (on_tick_sameBlocks cfg store time).nonAnchorParentKnown aRoot h

/-- One dispatched event preserves `NonAnchorParentKnown`. -/
theorem apply_event_nonAnchorParentKnown (aRoot : Root) {store store' : Store Root}
    {event : Event Root} (h : NonAnchorParentKnown aRoot store)
    (he : apply_event cfg ext store event = some store') :
    NonAnchorParentKnown aRoot store' := by
  cases event with
  | block b =>
    simp only [apply_event] at he
    exact on_block_nonAnchorParentKnown cfg ext aRoot h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact (on_attestation_sameBlocks cfg ext he).nonAnchorParentKnown aRoot h
  | attester_slashing sl =>
    simp only [apply_event] at he
    exact (on_attester_slashing_sameBlocks ext he).nonAnchorParentKnown aRoot h
  | execution_payload_envelope envelope observation =>
    exact (on_execution_payload_envelope_frame ext he).sameBlocks.nonAnchorParentKnown aRoot h
  | payload_attestation_message message ifb =>
    exact (on_payload_attestation_message_frame cfg ext he).sameBlocks.nonAnchorParentKnown aRoot h

/-- Folding a second's scheduled events preserves `NonAnchorParentKnown`. -/
theorem nonAnchorParentKnown_foldl (aRoot : Root) :
    ∀ (l : List (Event Root)) (s : Store Root), NonAnchorParentKnown aRoot s →
      NonAnchorParentKnown aRoot
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons e l ih =>
    intro s h
    rw [List.foldl_cons]
    apply ih
    cases he : apply_event cfg ext s e with
    | none => simpa [he] using h
    | some s' =>
      simp only [Option.getD_some]
      exact apply_event_nonAnchorParentKnown cfg ext aRoot h he

/-- **`NonAnchorParentKnown` at every node and second (Layer 0).** From the
`get_forkchoice_store` genesis base (`block_roots = [anchor_root]`, the anchor is
`aRoot`) via the standalone fold. -/
theorem Execution.store_nonAnchorParentKnown (E : Execution Root)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    NonAnchorParentKnown ablk.root (E.store cfg ext v n) := by
  induction n with
  | zero =>
    change NonAnchorParentKnown ablk.root E.genesis_store
    rw [hgeq]
    intro r hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    exact Or.inl hr
  | succ n ih =>
    change NonAnchorParentKnown ablk.root
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    exact nonAnchorParentKnown_foldl cfg ext ablk.root _ _
      (on_tick_nonAnchorParentKnown cfg ablk.root _ _ ih)

/-! ## Section 2 — the two Layer-0 anchor facts and the target-known walk domain

The genesis anchor `ablk` seeds `block_roots = [ablk.root]` with
`blocks ablk.root = ablk.message`; its dangling parent `P := ablk.message.parent_root`
is never a known root (`BlockProvenance` + `anchor_parent_unscheduled`). With
`NonAnchorParentKnown` (Section 1) and `ParentSlotLt` (`WFTrajectory`) this pins the
anchor as the unique minimal-slot block, giving the two facts on `E5Filter`'s dropped
list — from which `walkKnown_of_anchorSlot` composes the target-known walk domain
`hwalkK` at every honest store, with **no** `anchor_guard` residual. -/

/-- The anchor's recorded block is its genesis block (`ablk.message`), at every
store that knows the anchor root. `BlockProvenance`: the genesis case is direct;
the scheduled case is pinned by `genesis_blocks_agree`. -/
theorem Execution.store_anchor_block (E : Execution Root) (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (hr : ablk.root ∈ (E.store cfg ext v n).block_roots) :
    (E.store cfg ext v n).blocks ablk.root = ablk.message := by
  have hmemg : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]; simp [get_forkchoice_store]
  have hgb : E.genesis_store.blocks ablk.root = ablk.message := by
    rw [hgeq]; simp [get_forkchoice_store]
  rcases E.blockProvenance cfg ext v n _ hr with ⟨_, hb⟩ | ⟨b, hsched, hbr, hb⟩
  · rw [hb, hgb]
  · obtain ⟨w, m, hbm⟩ := hsched
    have hbmsg : b.message = E.genesis_store.blocks b.root :=
      hwf.genesis_blocks_agree w m b hbm (hbr ▸ hmemg)
    rw [hb, hbmsg, hbr, hgb]

/-- **`P ∉ block_roots`.** The anchor's dangling parent `P := ablk.message.parent_root`
is never a known block: `BlockProvenance`'s genesis case forces `P = ablk.root`
(excluded by `hparent`), and its scheduled case makes `P` a scheduled block root
(excluded by `anchor_parent_unscheduled`). -/
theorem Execution.store_dangling_parent_unknown (E : Execution Root)
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) (v : ValidatorIndex) (n : ℕ) :
    ablk.message.parent_root ∉ (E.store cfg ext v n).block_roots := by
  intro hmem
  have hmemg : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]; simp [get_forkchoice_store]
  have hpeq : (E.genesis_store.blocks ablk.root).parent_root = ablk.message.parent_root := by
    rw [hgeq]; simp [get_forkchoice_store]
  rcases E.blockProvenance cfg ext v n _ hmem with ⟨hg, _⟩ | ⟨b, hsched, hbr, _⟩
  · rw [hgeq] at hg
    simp only [get_forkchoice_store, List.mem_singleton] at hg
    exact hparent hg
  · obtain ⟨w, m, hb⟩ := hsched
    exact hwf.anchor_parent_unscheduled ablk.root hmemg w m b hb (hbr.trans hpeq.symm)

/-- **(b) the fixed-slot anchor guard.** Every known block
naming the dangling parent `P` is the anchor itself (`NonAnchorParentKnown` +
`P ∉ block_roots`), hence has slot `= anchorSlot := ablk.message.slot`. This is the
sound replacement for the `∀ sl` `anchor_guard` residual. -/
theorem Execution.store_anchor_guard (E : Execution Root) (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) (v : ValidatorIndex) (n : ℕ) :
    ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root = ablk.message.parent_root →
        ((E.store cfg ext v n).blocks r).slot ≤ ablk.message.slot := by
  intro r hr hpar
  rcases E.store_nonAnchorParentKnown cfg ext hgeq v n r hr with heq | hin
  · subst heq
    rw [E.store_anchor_block cfg ext hwf hgeq v n hr]
  · rw [hpar] at hin
    exact absurd hin (E.store_dangling_parent_unknown cfg ext hwf hgeq hparent v n)

/-- **(a) anchor-minimal-slot.** The anchor's slot is a
lower bound on every known block's slot. Strong induction on the block's slot at a
fixed store: `NonAnchorParentKnown` bottoms the walk at the anchor
(`slot = anchorSlot`), and every non-anchor block's parent (known, `ParentSlotLt`)
has a strictly smaller slot bounded below by the induction hypothesis. -/
theorem Execution.store_anchor_min_slot (E : Execution Root) (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgeq : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot) (hparent : ablk.message.parent_root ≠ ablk.root)
    (v : ValidatorIndex) (n : ℕ) :
    ∀ r ∈ (E.store cfg ext v n).block_roots,
      ablk.message.slot ≤ ((E.store cfg ext v n).blocks r).slot := by
  have hpsl : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled v n
  have hnak := E.store_nonAnchorParentKnown cfg ext hgeq v n
  have key : ∀ N r, ((E.store cfg ext v n).blocks r).slot = N →
      r ∈ (E.store cfg ext v n).block_roots →
      ablk.message.slot ≤ ((E.store cfg ext v n).blocks r).slot := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro r hs hr
      rcases hnak r hr with heq | hin
      · subst heq
        rw [E.store_anchor_block cfg ext hwf hgeq v n hr]
      · have hlt := hpsl r hr hin
        have hle := ih _ (hs ▸ hlt) _ rfl hin
        exact le_trans hle (le_of_lt hlt)
  intro r hr
  exact key _ r rfl hr

/-- **The target-known walk domain `hwalkK`, Layer-0 discharged.** For every *known*
target `t` and known root `r`, the walk from `r` toward `(blocks t).slot` stays
known — via `E5Filter.walkKnown_of_anchorSlot` fed by the anchor guard (b), the
anchor-minimal-slot fact (a) at `t`, `ParentSlotLt`, and `ParentInRootsOr P`
(recovered from `NonAnchorParentKnown` + the anchor's own dangling edge). This
discharges the `_K` descent lemmas' walk domain with **no** `anchor_guard`. -/
theorem Execution.store_walkKnownK (E : Execution Root) (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (v : ValidatorIndex) (n : ℕ) :
    ∀ t ∈ (E.store cfg ext v n).block_roots, ∀ r ∈ (E.store cfg ext v n).block_roots,
      WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks t).slot r := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hpsl : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwf hec ⟨ast, ablk, hgeq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled v n
  have hQ : ParentInRootsOr ablk.message.parent_root (E.store cfg ext v n) := by
    intro r hr
    rcases E.store_nonAnchorParentKnown cfg ext hgeq v n r hr with heq | hin
    · right; subst heq; rw [E.store_anchor_block cfg ext hwf hgeq v n hr]
    · left; exact hin
  intro t ht r hr
  exact walkKnown_of_anchorSlot hpsl hQ
    (E.store_anchor_guard cfg ext hwf hgeq hparent v n)
    (E.store_anchor_min_slot cfg ext hwf hec hgeq hslot hparent v n t ht) r hr

/-! ## Checkpoint-state key membership at genesis

The stronger trajectory property
`justified_checkpoint ∈ checkpoint_state_keys` would make
`Registry.registryConstant`'s `checkpoint_states` clause apply to the justified
source, yielding `(checkpoint_states justified).validators = E.registry`. It is
not preserved by this model: `update_checkpoints`
(`Model/Handlers.lean`) bumps `justified_checkpoint` to `state.current_justified_checkpoint`
(a block **post-state** checkpoint) whenever its epoch is higher, and does **not**
insert that checkpoint into `checkpoint_state_keys`; only `store_target_checkpoint_state`
(reached from `on_attestation`) ever keys a checkpoint. So `on_block`
(`update_checkpoints` + `compute_pulled_up_tip`) and `on_tick_per_slot`'s
epoch-boundary branch (`update_checkpoints store.unrealized_justified_checkpoint …`)
both move `justified_checkpoint` to an **unkeyed** checkpoint. No
`ExternalsCoherence` / `JustificationInterface` field guarantees a keyed justified
checkpoint (the closest, `state_transition_checkpoint_epoch`, bounds epochs only).

Deriving the trajectory property would require either a behavioral premise
("every checkpoint that becomes
justified via `update_checkpoints` was previously target-cached" — an
`ExternalsCoherence`-family fact, absent) or a `Model/` change to `on_block`
(cache the justified checkpoint state, as newer deployed fork-choice does). This
module proves the genesis instance that follows from the current interface. -/




/-- **The target-known fork-choice domain** — `ResidualDischarge.StoreDomain` with the
blanket `hwalk` replaced by the Section-2 `hwalkK`. Unlike the blanket form this is
Layer-0 dischargeable (`store_domainK`). -/
def Execution.StoreDomainK (E : Execution Root) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks
              ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r) ∧
      (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots


namespace Execution

variable (E : Execution Root)

/-- **`SafeFrom` from `StoreDomainK` + reset-anchor dominance (`_K`).** The `_K`
counterpart of `L4Fold.safeFrom_of_justified_dom`: `r₀` is safe from `n₀` if it is
known and on the justified chain at every honest store past `n₀`, via
`E5Filter.head_ge_of_justified_ge_K` (target-known walk, no blanket domain). -/
theorem safeFrom_of_justified_dom_K (hdomK : E.StoreDomainK cfg ext) {r₀ : Root} {n₀ : ℕ}
    (hdom : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      r₀ ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root r₀) = true) :
    E.SafeFrom cfg ext r₀ n₀ := by
  intro w hw m hm hH
  obtain ⟨hwf, hwalkK, hjust⟩ := hdomK w hw m hH
  obtain ⟨hr0, hjb⟩ := hdom w hw m hm hH
  exact head_ge_of_justified_ge_K cfg hwf hwalkK hjust hr0 hjb





end Execution


end FastConfirmation.Spec

end
