module
public import FastConfirmation.Spec.Proof.Shrink

@[expose] public section

/-!
# Spec / Proof / Structural: the disjunctive `hcase` and shared-anchor knownness

This module addresses the
two structural residuals the final shrink (`Shrink.Spec_Safety_shrunk`) still carries:

* **(a) the disjunctive `hcase`.** The `dynamics_struct` leg reduces
  (`IHMechanize.dynamicsChainStruct_of_endpoint`) to `hb` + `hcase`, where the old `hcase` demands,
  at every honest endpoint `(w, m)`, that the confirmed block `b` **descends from** the store's
  justified checkpoint `jc(w,m)` (`get_ancestor_roots b jc ≠ [] ∨ b = jc`, i.e. `b ⪰ jc`). That is
  **false** once `jc(w,m)` has advanced *above* `b` (`jc ⪰ b`): then there is no chain from `jc`
  down to `b`, and the `DynamicsChainStruct` route stalls. Section 1 reframes the obligation as a
  **disjunction** — at each `(w, m)`, `jc ⪰ b` (**advance**) or `b ⪰ jc` (**chain**) — and splits:
  the advance branch discharges the head descent `head ⪰ b` **outright, with no engine**, via
  `E5Filter.head_ge_of_justified_ge_K` (`head ⪰ jc ⪰ b`); the chain branch delegates to the engine
  supplier in its delivered shape. The wrapper `safeFrom_of_disjunctive` accepts the disjunctive
  supply and yields the head-descent (`SafeFrom`) conclusion in **either** branch.

  The disjunction itself is derived from `justified_ancestry` where it is clean
  (`chain_of_covering`: if `b ⪰ jcb` for a justified `jcb` at `(w, m)` and `jc.epoch ≤ jcb.epoch`,
  then `b ⪰ jc`). The remaining premise is the `jc.epoch > jcb.epoch` sub-case, where `jc` outran `b`'s
  covering justified checkpoint and the disjunction's *advance* side (`jc ⪰ b`) must hold because
  `jc` advanced **along** `b`'s chain — is exactly the engine's head-safety content (the honest
  majority kept `b` canonical through `jc`'s epoch). The interface states this premise precisely.

* **(b) `SameSlotFinalizedRootKnownNonGenesis` via the shared anchor.** Section 2 wires the intended
  shared-anchor route: all honest stores share the genesis anchor (`store w 0 = genesis_store`, the
  anchor root known at every `(w, m)` by `StoreLE`); `finalized_descent` puts the confirming node's
  reset root `fv := (store v (n+1)).finalized` **below** `w`'s own finalized root `fw`
  (`checkpoint_known`); the descent walk from `fw` stays in known roots
  (`AnchorFacade.store_walkKnownK`), so `LastCruxes.mem_of_is_ancestor_above_anchor` concludes `fv`
  is a known block **at `w`, with no relay** — *provided the boundary* `hab : anchorSlot ≤
  (store w m).blocks fv.slot` holds. Section 2 delivers the full reduction to `hab`
  (`finalized_cross_known_of_boundary`) and closes it **outright for the genesis-start regime**
  (`anchorSlot = GENESIS_SLOT = 0`, `sameSlotFinalizedRootKnown_of_genesis_start`), where `hab` is `0 ≤ _`.

  **The genuine obstruction (checkpoint-sync, stated exactly).** At a checkpoint-sync anchor
  (`anchorSlot > 0`) the boundary `hab` is *not* derivable from the available assumptions at the
  same-slot regime: if `fv ∉ (store w m).block_roots` the totalized lookup `(store w m).blocks fv`
  is the `Inhabited` default (slot `0 < anchorSlot`), so `is_ancestor (store w m) fw fv` — the
  `finalized_descent` assertion — is satisfied **vacuously** with `fv` = the anchor's dangling
  parent `ablk.message.parent_root` (also `∉ block_roots`, also `∉ (store w 0).block_roots`, so the
  non-genesis guard does **not** exclude it). No assumption forces `(store w m).blocks fv.slot ≥
  anchorSlot` for an unknown `fv`; the missing export is "finalized blocks are old, hence already
  gossiped" — exactly `block_relay`'s `+1` gate, which the same-slot regime is past. This is the
  same-slot knownness condition represented by `SameSlotFinalizedRootKnownNonGenesis`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the disjunctive `hcase`: advance (free) ∨ chain (engine)

At an honest endpoint `(w, m)` the confirmed block `b` and the store's justified checkpoint `jc`
are related in one of two ways: `jc ⪰ b` (**advance** — `jc` has moved to at-or-above `b`) or
`b ⪰ jc` (**chain** — `b` descends from `jc`). The advance branch needs **no engine**: the filter
alone puts `head ⪰ jc ⪰ b`. Only the chain branch runs the LMD margin engine. -/

/-- **Advance branch (fully proved).** If the store's justified checkpoint `jc` is at or above `b`
(`hadv : jc ⪰ b`, `is_ancestor jc.root b`), the fork-choice head descends from `b` outright —
`E5Filter.head_ge_of_justified_ge_K` (`head ⪰ jc ⪰ b`), with the fork-choice domain conditions
Layer-0 discharged (`AnchorFacade.store_domainK`). No LMD margin, no engine: the FFG takeover. -/
theorem head_ge_of_advance (hSA : SpecAssumptions cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) {b : Root}
    (hH : E.WithinHorizon cfg m)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hadv : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root b) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨hwf, hwalkK, hjust⟩ := E.store_domainK cfg ext hwfE hec hgen hji w hw m hH
  exact head_ge_of_justified_ge_K cfg hwf hwalkK hjust hb hadv

/-- **The per-endpoint case-split wrapper.** Given, at `(w, m)`, the disjunction `jc ⪰ b ∨ b ⪰ jc`
(`hdisj`) and the engine supplier for the chain branch (`heng : b ⪰ jc → head ⪰ b`), the head
descends from `b` in **either** case: the advance branch closes by `head_ge_of_advance` (no
engine), the chain branch by `heng`. This is the patch the `DynamicsChainStruct`-consuming path
needs — it no longer demands the (false-under-advance) `b ⪰ jc` unconditionally. -/
theorem head_descent_of_disjunction (hSA : SpecAssumptions cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) {b : Root}
    (hH : E.WithinHorizon cfg m)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hdisj : is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true)
    (heng : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root b) = true := by
  rcases hdisj with hadv | hchain
  · exact E.head_ge_of_advance cfg ext hSA w hw m hH hb hadv
  · exact heng hchain

/-- **The disjunctive `SafeFrom` wrapper.** Lifts `head_descent_of_disjunction`
across every endpoint past `n₀`: `SafeFrom b n₀` follows from per-endpoint `b`-knownness (`hbk`),
the disjunction supply (`hdisj`), and the chain-branch engine supplier (`heng`). The advance side
is fully discharged; the chain side is the engine in its delivered `SafeFrom`-endpoint shape. This
is the disjunctive replacement of the `dynamics_struct`/`L4Fold` head-descent obligation: the
`jc`-advance case is closed here, off the engine. -/
theorem safeFrom_of_disjunctive (hSA : SpecAssumptions cfg ext E) {b : Root} {n₀ : ℕ}
    (hbk : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.WithinHorizon cfg m →
      b ∈ (E.store cfg ext w m).block_roots)
    (hdisj : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root b) = true ∨
        is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true)
    (heng : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true) :
    E.SafeFrom cfg ext b n₀ :=
  fun w hw m hm hH =>
    E.head_descent_of_disjunction cfg ext hSA w hw m hH (hbk w hw m hm hH)
      (hdisj w hw m hm hH) (heng w hw m hm hH)

/-- **Chain branch from a covering justified checkpoint.** The derivation of
`b ⪰ jc` from `justified_ancestry`: if `jcb` is a justified checkpoint at `(w, m)` that `b`
descends from (`hb_ge_jcb : b ⪰ jcb`, the confirming-store balance-source descent transported) and
the store's justified `jc` is at **no higher** epoch (`hle : jc.epoch ≤ jcb.epoch`), then FFG
cross-epoch coherence puts `jcb ⪰ jc`, so `b ⪰ jcb ⪰ jc` — the chain case. Uses
`justified_ancestry` (`jc` justified in its own store by `Or.inl rfl`) + `is_ancestor_trans` on the
target-known walk domain (`store_walkKnownK`). -/
theorem chain_of_covering (hSA : SpecAssumptions cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) {b : Root} {jcb : Checkpoint Root}
    (hH : E.WithinHorizon cfg m)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hjcb_just : JustifiedIn (E.store cfg ext w m) jcb)
    (hjcb_known : jcb.root ∈ (E.store cfg ext w m).block_roots)
    (hb_ge_jcb : is_ancestor (E.store cfg ext w m)
      (get_node_for_root b) (get_node_for_root jcb.root) = true)
    (hle : (E.store cfg ext w m).justified_checkpoint.epoch ≤ jcb.epoch) :
    is_ancestor (E.store cfg ext w m) (get_node_for_root b)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨hwf, hwalkK, hjust⟩ := E.store_domainK cfg ext hwfE hec hgen hji w hw m hH
  -- `jcb ⪰ jc` from FFG cross-epoch coherence
  have hjcb_ge_jc := hji.justified_ancestry w hw m
    (E.store cfg ext w m).justified_checkpoint jcb hH
    (Or.inl rfl) hjcb_just hle hjust hjcb_known
  -- `b ⪰ jcb ⪰ jc`
  simp only [get_node_for_root] at hb_ge_jcb hjcb_ge_jc ⊢
  exact is_ancestor_trans hwf
    (hwalkK _ hjust _ hb) (hwalkK _ hjust _ hjcb_known) hb_ge_jcb hjcb_ge_jc

/-- **The disjunction from a covering justified checkpoint.** Assembles the full
`jc ⪰ b ∨ b ⪰ jc` supply: on `jc.epoch ≤ jcb.epoch` the chain side (`chain_of_covering`); on
`jcb.epoch < jc.epoch` the advance side — where `jc` outran `b`'s covering justified checkpoint, so
`jc ⪰ b` **must** hold because `jc` advanced *along* `b`'s chain — supplied by `hadv_hi`, the engine
head-safety content for exactly that strict sub-case. This localizes the engine residual to
`jcb.epoch < jc.epoch`: everything else is closed from `justified_ancestry`. -/
theorem disjunction_of_covering (hSA : SpecAssumptions cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) {b : Root} {jcb : Checkpoint Root}
    (hH : E.WithinHorizon cfg m)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hjcb_just : JustifiedIn (E.store cfg ext w m) jcb)
    (hjcb_known : jcb.root ∈ (E.store cfg ext w m).block_roots)
    (hb_ge_jcb : is_ancestor (E.store cfg ext w m)
      (get_node_for_root b) (get_node_for_root jcb.root) = true)
    (hadv_hi : jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true := by
  by_cases hle : (E.store cfg ext w m).justified_checkpoint.epoch ≤ jcb.epoch
  · exact Or.inr (E.chain_of_covering cfg ext hSA w hw m hH
      hb hjcb_just hjcb_known hb_ge_jcb hle)
  · exact Or.inl (hadv_hi (not_le.mp hle))

/-! ## Section 2 — `SameSlotFinalizedRootKnownNonGenesis` via the shared genesis anchor

The `mem_of_is_ancestor_above_anchor` transport instantiated at the finalized reset anchor, with
its walk domain / parent-order / knownness premises discharged from `SpecAssumptions` and only the
boundary `hab` (the reset root sits at or above the anchor slot in `w`'s store) left as input. -/

/-- **The reset root is known at `w`, from the boundary `hab`.** For honest `v`, `w`, times with
`n + 1 ≤ m`, the confirming node's finalized reset root `fv := (store v (n+1)).finalized` is a known
block at `(w, m)` provided it sits at or above the anchor slot in `w`'s store (`hab`). The transport
is `LastCruxes.mem_of_is_ancestor_above_anchor` on `a := fw := (store w m).finalized` (known,
`checkpoint_known`) with the anchor-slot walk from `AnchorFacade.store_walkKnownK` and the descent
`fw ⪰ fv` from `finalized_descent`; every premise but `hab` is Layer-0 / interface-mechanical.
`hab` is quantified over the anchor decomposition (`hgen` supplies the unique one). -/
theorem finalized_cross_known_of_boundary (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m)
    (hab : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk →
      ablk.message.slot ≤ ((E.store cfg ext w m).blocks
        (E.store cfg ext v (n + 1)).finalized_checkpoint.root).slot) :
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  -- the anchor root is known at `(w, m)` (shared genesis + `StoreLE`)
  have hanchor_mem0 : ablk.root ∈ (E.store cfg ext w 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]; simp [get_forkchoice_store]
  have hanchor_mem : ablk.root ∈ (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchor_mem0
  -- Layer-0 parent-slot order and the target-known walk domain at `(w, m)`
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled w m
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec hgen' w m
  -- `fw` is a known block; the walk `fw ↓ anchorSlot` stays known
  have hfw_known : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := (hji.checkpoint_known w hw m).2
  have hanchor_slot : ((E.store cfg ext w m).blocks ablk.root).slot = ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq w m hanchor_mem]
  have hwa : WalkKnown (E.store cfg ext w m) ablk.message.slot
      (E.store cfg ext w m).finalized_checkpoint.root := by
    have := hwalkK ablk.root hanchor_mem _ hfw_known
    rwa [hanchor_slot] at this
  -- the descent `fw ⪰ fv` and the boundary
  have hanc : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk (E.store cfg ext w m).finalized_checkpoint.root)
      (ForkChoiceNode.mk (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true := by
    have := hji.finalized_descent v hv (n + 1) w hw m
      (E.withinHorizon_mono cfg hm hH) hH hm
    simpa only [get_node_for_root] using this
  exact mem_of_is_ancestor_above_anchor hpsl hwa (hab ast ablk hgeq) hanc

/-- **`SameSlotFinalizedRootKnownNonGenesis` for the genesis-start regime.** When the anchor
block sits at `GENESIS_SLOT` (`hanchor0`, a genesis start, as opposed to a checkpoint-sync
anchor), the boundary `hab` of `finalized_cross_known_of_boundary` is `0 ≤ _` — trivially true — so
the confirming node's finalized reset root is known at **every** honest `(w, m)` with `n + 1 ≤ m`,
**same-slot included, non-genesis included, with no relay**. This closes the same-slot reset corner
outright under genesis-start (hence also `SameSlotFinalizedRootKnownNonGenesis`, whose non-genesis
guard is not needed here). -/
theorem sameSlotFinalizedRootKnown_of_genesis_start (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := by
  intro v hv n w hw m hm hH
  refine E.finalized_cross_known_of_boundary cfg ext hSA v hv n w hw m hm hH ?_
  intro ast ablk hgeq
  rw [hanchor0 ast ablk hgeq, GENESIS_SLOT]
  exact Nat.zero_le _

/-- **`SameSlotFinalizedRootKnownNonGenesis` from genesis-start.** The guarded field is
discharged under the genesis-start hypothesis: `sameSlotFinalizedRootKnown_of_genesis_start` establishes the
reset-root knownness for every `(w, m)` regardless of the same-slot / non-genesis guards, so the
guarded `SameSlotFinalizedRootKnownNonGenesis` follows by dropping its two extra hypotheses. -/
theorem sameSlotFinalizedRootKnownNonGenesis_of_genesis_start (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT) :
    E.SameSlotFinalizedRootKnownNonGenesis cfg ext :=
  fun v hv n w hw m hm hH _hgate _hng =>
    E.sameSlotFinalizedRootKnown_of_genesis_start cfg ext hSA hanchor0 v hv n w hw m hm hH

end Execution

end FastConfirmation.Spec

end
