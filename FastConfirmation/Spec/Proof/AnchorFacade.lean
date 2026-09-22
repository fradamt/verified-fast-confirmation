module
public import FastConfirmation.Spec.Proof.E5Filter
public import FastConfirmation.Spec.Proof.WFTrajectory

@[expose] public section

/-!
# Spec / Proof / AnchorFacade: Layer-0 anchor facts and the safety interface

This module builds on the interface reduction in `E5Filter.lean` §3.
`E5Filter` reshaped the fork-choice head lemma onto the **target-known**
walk domain `hwalkK` (`walkKnown_of_anchorSlot` / `head_ge_of_justified_ge_K`),
replacing the stronger `∀ sl` `anchor_guard` (false for checkpoint-sync anchors).
This module proves the two Layer-0 anchor facts that discharge `hwalkK` and uses
them in the safety interface.

## What is delivered

* **Section 1 — the parent-known companion `NonAnchorParentKnown`.** Every known
  block either *is* the genesis anchor or has a **known** parent (`on_block`'s
  parent guard). A standalone trajectory fold (no `WellFormedStoreCore` needed —
  the guard is handler-local), mirroring `WFTrajectory.on_block_parentInRootsOr`.

* **Section 2 — the two Layer-0 anchor facts:**
  * **(a) anchor-minimal-slot** `store_anchor_min_slot` — `∀ t ∈ block_roots,
    anchorSlot ≤ (blocks t).slot` (`anchorSlot := anchor block's slot`). Strong
    induction on the block's slot at a *fixed* store: `ParentSlotLt` drops the
    parent's slot, `NonAnchorParentKnown` bottoms the walk at the anchor.
  * **(b) the fixed-slot anchor guard** `store_anchor_guard` — `∀ r ∈ block_roots,
    parent = P → slot ≤ anchorSlot` (`P := anchor's dangling parent`). Only the
    anchor names `P`: `NonAnchorParentKnown` + `P ∉ block_roots`
    (`BlockProvenance` + `anchor_parent_unscheduled`), then `BlockProvenance`
    pins the anchor's block.

  `store_walkKnownK` composes them through `E5Filter.walkKnown_of_anchorSlot` into
  the **target-known** walk domain at every honest store — `hwalkK` is Layer-0, no
  `anchor_guard` residual.

* **Section 3 — the safety interface.** `store_domainK` supplies the
  `_K` fork-choice domain (`hwf`/`hwalkK`/`hjust`) at every honest store from
  `SpecAssumptions` (the Layer-0 facts + `JustificationInterface.checkpoint_known`).
  `safeFrom_of_justified_dom_K` / the observed + finalized reset-anchor lifts are
  re-proved on the `_K` head lemmas (`E5Filter.head_ge_of_justified_ge_K`,
  `head_ge_of_justifiedIn_le_K`), so the reset anchors are safe with **no** blanket
  walk domain and **no** `∀ sl` anchor guard. `SoundResiduals` is the resulting
  input bundle — the observed filter route (`ObservedFilterResiduals`),
  the finalized tracks, and the engine `advance_cert` — with the anchor/walk domain
  discharged internally. `spec_safety_sound_residuals` is the end-to-end headline.

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
    split_ifs at hh with hp hslot hfin hfc
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      cases hh
      refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).nonAnchorParentKnown aRoot ?_
      refine (update_checkpoints_sameBlocks _ _ _).nonAnchorParentKnown aRoot ?_
      refine (update_proposer_boost_root_sameBlocks cfg _ _ _).nonAnchorParentKnown aRoot ?_
      refine (record_block_timeliness_sameBlocks cfg _ _).nonAnchorParentKnown aRoot ?_
      refine nonAnchorParentKnown_insert aRoot store sb.root sb.message state _ ?_ ?_ hQ hp
      · intro r hr
        first
          | exact hr
          | exact List.mem_append_left _ hr
      · intro r hr
        first
          | exact Or.inr hr
          | · rw [List.mem_append, List.mem_singleton] at hr
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

/-- **Genesis base for `hval`'s key-membership.** `get_forkchoice_store` seeds
`checkpoint_state_keys = {justified_checkpoint}` with the store's own
`justified_checkpoint` as the single key, so the membership holds at genesis. -/
theorem get_forkchoice_store_justified_keyed (ast : BeaconState Root)
    (ablk : SignedBeaconBlock Root) :
    (get_forkchoice_store cfg ast ablk).justified_checkpoint ∈
      (get_forkchoice_store cfg ast ablk).checkpoint_state_keys := by
  simp [get_forkchoice_store]

/-! ## Section 3 — safety interface with the target-known domain

`E5Filter`'s `spec_safety_of_hypsFilter` and `ForkAssembly`'s `spec_safety_final_residuals`
each carry an over-strong field: the former's `L4ResidualHypsFilter.store_domain`
uses the **blanket** walk domain `∀ t r` (false for checkpoint-sync anchors, `E5Filter`
§3), while the latter's `FinalResidualsER.observed_dom` assumes the invalid-in-general
relation `obs ⪯ jc`. This section omits both: the observed anchor uses
`E5Filter`'s sound filter route (`ObservedFilterResiduals`), and the walk domain is the
**target-known** `StoreDomainK`, discharged from the Section-2 anchor facts — no blanket
walk, no `∀ sl` anchor guard. -/

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

/-- **`StoreDomainK` is Layer-0 discharged.** `ParentSlotLt` (`store_parentSlotLt`),
the target-known walk domain (`store_walkKnownK` — Section 2), and justified-knownness
(`JustificationInterface.checkpoint_known`) at every honest store. This is the whole
content of the removed `anchor_guard` / blanket-`hwalk` residual. -/
theorem Execution.store_domainK (E : Execution Root) (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hji : JustificationInterface cfg ext E) :
    E.StoreDomainK cfg ext := by
  intro w hw m hH
  refine ⟨E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled w m,
    E.store_walkKnownK cfg ext hwf hec hgen w m, (hji.checkpoint_known w hw m).1⟩

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

/-- **Filter-route head domination (`_K`, both regimes).** `E5Filter.head_ge_of_justifiedIn`
on the target-known walk domain: the `≤`-epoch case through the filter
(`head_ge_of_justifiedIn_le_K`), the ahead case through `hahead`. -/
theorem head_ge_of_justifiedIn_K (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
          < ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
    (c : Checkpoint Root) (hc_just : JustifiedIn (E.store cfg ext w m) c)
    (hc_known : c.root ∈ (E.store cfg ext w m).block_roots)
    (hahead : (E.store cfg ext w m).justified_checkpoint.epoch < c.epoch →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root c.root) = true) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true := by
  by_cases hle : c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch
  · exact E.head_ge_of_justifiedIn_le_K cfg ext hji w hw m hH
      hwf hwalkK hjust c hc_just hc_known hle
  · exact hahead (not_le.mp hle)

/-- **`SafeFrom(observed-root)` via the sound filter route (`_K`).** `E5Filter`'s
`safeFrom_observed_of_filter` on the target-known walk domain: the observed anchor is
`JustifiedIn` everywhere (`fcrStep_observed_justifiedIn`, using `hprev`), known
(`hknown`), so `head_ge_of_justifiedIn_K` dominates it — sound `obs ⪯ jc` where it
holds, `hahead` above. No blanket walk, no `anchor_guard`. -/
theorem safeFrom_observed_of_filter_K (hji : JustificationInterface cfg ext E)
    (hdomK : E.StoreDomainK cfg ext)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint))
    (hknown : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots)
    (hahead : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.epoch <
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root
          (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1) := by
  intro w hw m hm hH
  obtain ⟨hwf, hwalkK, hjust⟩ := hdomK w hw m hH
  exact E.head_ge_of_justifiedIn_K cfg ext hji w hw m hH hwf hwalkK hjust
    ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
    (E.fcrStep_observed_justifiedIn cfg ext hji hprev v hv n w hw m hm hH)
    (hknown v hv n w hw m hm hH) (hahead v hv n w hw m hm hH)

/-- **The sound input bundle** (`AnchorFacade`). This bundle omits two over-strong
inputs:

* the fork-choice **walk domain is discharged internally** (`store_domainK` from the
  Section-2 anchor facts + `JustificationInterface.checkpoint_known`) — no blanket
  `hwalk`, no `∀ sl` `anchor_guard`;
* the observed anchor uses the **sound filter route** (`observed_filter`) rather than
  the invalid-in-general relation `obs ⪯ jc`.

The reset (finalized/genesis) anchors carry their *sound* justified dominance
`jc ⪰ r₀` with knownness (`jc ⪰ finalized` always holds — E5 cross-store descent +
`finalized_justified_ancestry`); the engine leg is the certificate `advance_cert`. -/
structure SoundResiduals (E : Execution Root) : Prop where
  /-- E5: the genesis finalized reset anchor is known and justified-dominated at every
      honest store. -/
  genesis_dom : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext v 0).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true
  /-- E5: each update's finalized reset anchor is known and justified-dominated at
      every honest store past `n+1`. -/
  finalized_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true
  /-- **E5 (sound filter route)**: the observed-anchor filter inputs replace the
      invalid-in-general `observed_dom` premise. -/
  observed_filter : E.ObservedFilterResiduals cfg ext
  /-- engine: every `is_one_confirmed` block at an update store carries a
      `LedgerChainInputCert`. -/
  advance_cert : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    LedgerChainInputCert cfg ext E b (n + 1)

/-- **`L4Residual` from the sound bundle.** `StoreDomainK` is discharged from
`SpecAssumptions` (`store_domainK`); the finalized/genesis anchors go through
`safeFrom_of_justified_dom_K`, the observed anchor through the sound filter route
`safeFrom_observed_of_filter_K`, the advance through `L4Fold.safeFrom_of_certificates`.
No blanket walk domain, no `∀ sl` anchor guard, no `obs ⪯ jc`. -/
theorem l4Residual_of_soundResiduals (hSA : SpecAssumptions cfg ext E)
    (h : E.SoundResiduals cfg ext) : E.L4Residual cfg ext := by
  obtain ⟨hgen, hwf, _, _, _, hec, _, _, hji⟩ := hSA
  have hdomK := E.store_domainK cfg ext hwf hec hgen hji
  exact
    { genesis_safe := fun v hv =>
        E.safeFrom_of_justified_dom_K cfg ext hdomK
          (fun w hw m (_hm : 0 ≤ m) (hH : E.WithinHorizon cfg m) =>
            h.genesis_dom v hv w hw m hH)
      finalized_safe := fun v hv n => by
        rw [E.fcrStep_store]
        exact E.safeFrom_of_justified_dom_K cfg ext hdomK (h.finalized_dom v hv n)
      observed_safe := fun v hv n =>
        E.safeFrom_observed_of_filter_K cfg ext hji hdomK
          h.observed_filter.prev_greatest_justifiedIn h.observed_filter.observed_known
          h.observed_filter.observed_head_ahead v hv n
      advance_safe := fun v hv n b hconf =>
        E.safeFrom_of_certificates cfg ext (h.advance_cert v hv n b hconf) }

end Execution

/-- **`Spec_Safety` from the sound input bundle** (`AnchorFacade`). FCR safety
follows when every execution's `SpecAssumptions`
supplies `SoundResiduals`. The exactly-enumerated residual bundle:

* `genesis_dom` / `finalized_dom` `[E5-reset]` — the finalized reset anchors are known
  and on every honest justified chain (`jc ⪰ finalized`, sound; cross-store finalized
  descent + `finalized_justified_ancestry`);
* `observed_filter` `[E5/E6]` — the observed-anchor filter inputs
  (`ObservedFilterResiduals`: boundary-source justification, observed-anchor
  knownness, and the ahead-regime head domination), used instead of the
  invalid-in-general relation `obs ⪯ jc`;
* `advance_cert` `[E-engine]` — the per-confirmed-block `LedgerChainInputCert` (the §8
  certificate boundary; its accounting uses the explicit `Arms` premises, and the crossing
  tax-arm is supplied separately by `Crossing.lean` — both outside this bundle).

The fork-choice **walk domain** and **anchor guard** are discharged rather than assumed:
`StoreDomainK` is proved from Layer-0 facts
(`store_domainK` ← the Section-2 anchor facts + `checkpoint_known`), so neither the
blanket `∀ t r` `hwalk` of `L4ResidualHypsFilter.store_domain` nor the `∀ sl`
`anchor_guard` of `FinalResidualsER` appears. -/
theorem spec_safety_sound_residuals
    (h : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.SoundResiduals cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_residual cfg ext
    (fun E hSA => E.l4Residual_of_soundResiduals cfg ext hSA (h E hSA))

end FastConfirmation.Spec

end
