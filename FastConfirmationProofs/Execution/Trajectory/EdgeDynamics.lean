module
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / EdgeDynamics

This module contains `blockRoots_subset_of_relay`, `equiv_subset_of_relay`, `EdgeInputResidual` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — relay containments (`hsub`, `hequiv`) -/

/-- **`hsub` — block-root containment from `block_relay`.** Every root known at the
confirming anchor `(vc, nc)` is known at the endpoint `(w, m)`, provided the endpoint is at
least one slot past the anchor (`slot_at nc + 1 ≤ slot_at (m + 1)`). This is the block
propagation deadline `Synchrony.block_relay` for each root, packaged as a set containment;
it feeds both `is_ancestor` transports so they carry no raw containment premise. -/
theorem blockRoots_subset_of_relay (hsync : PaperSafetySynchrony cfg ext E)
    {vc w : ValidatorIndex} {nc m : ℕ}
    (hvc : vc ∈ E.honest) (hw : w ∈ E.honest)
    (hHnc : E.WithinHorizon cfg nc) (hHm : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg nc + 1 ≤ E.slot_at cfg (m + 1)) :
    (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots :=
  fun r hr => hsync.block_relay vc hvc nc r hHnc hr w hw m hHm hslot


/-- **`hequiv` — equivocator containment from `attester_slashing_relay`.** Every equivocator
known at the confirming anchor `(vc, nc)` is known at the endpoint `(w, m)`, under the
one-slot ordering `slot_at nc + 1 ≤ slot_at m`. This supplies
`ForkEdgeInput`'s `hequiv` field. -/
theorem equiv_subset_of_relay (hsync : PaperSafetySynchrony cfg ext E)
    {vc w : ValidatorIndex} {nc m : ℕ}
    (hvc : vc ∈ E.honest) (hw : w ∈ E.honest)
    (hHnc : E.WithinHorizon cfg nc) (hHm : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg nc + 1 ≤ E.slot_at cfg m) :
    (E.store cfg ext vc nc).equivocating_indices ⊆
      (E.store cfg ext w m).equivocating_indices :=
  fun i hi => hsync.attester_slashing_relay vc hvc nc i hHnc hi w hw m hHm hslot

/-! ## Section 2 — the `is_ancestor` transports (`htS`, `htA`)

The forward transport is `EngineTransport.is_ancestor_transport` (walk from `r` toward
`b`'s slot); the reverse transport (needed for `AncestorOrVoteless`'s `b ⪯ r` orientation)
is the same `BlockAgreement.is_ancestor_congr` with the walk from `b` toward `r`'s slot.
Both consume only the block relay containment (Section 1) and the per-root `WalkKnown`
domain conditions. -/






/-- **The per-edge residual bundle.** Its fields supply the store-dynamics facts
used to construct `ForkEdgeInput`:

* `hbase` — `DynamicsClosure.INV2_base_of_confirmed` (through the `Arms` accounting);
* `hdeltas` — `StepDischargeII` / `DynamicsClosure.INV2_pre_step_of_deltas` (IH-shaped);
* `hmaj` — `DynamicsClosure.hsat_functional`'s `hmaj` (IH-shaped);
* `hval` — `Registry.registryConstant` (modulo the checkpoint-key membership);
* `hchild` — `FilterViability.chain_mem_get_filtered_block_tree`;
* `hrec` — `EngineTransport.recorded_supports_c_of_IH` (IH-shaped);
* `hHon`/`hByz` — the sibling confinements (`Forks.siblings_incompatible` + provenance +
  the `BbadSet`/`SpentSet` dichotomy).

`hdomS`/`hdomA` are the per-root walk-domain conditions the two transports need; the block
relay containment and equivocator containment are derived from `Synchrony` in
`forkEdgeInput_of_residual`. -/
structure EdgeInputResidual (E : Execution Root) (w : ValidatorIndex) (m : ℕ)
    (b h c : Root) (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot) : Prop where
  /-- The window start lies in the finite verification segment. -/
  hloH : E.SlotWithinHorizon cfg lo
  /-- The window endpoint lies in the finite verification segment. -/
  hσH : E.SlotWithinHorizon cfg σ
  /-- `hbase` — `INV2(es)` at the confirming anchor (boost = the endpoint proposer score). -/
  hbase : E.INV2 cfg ext vc nc b lo es es (get_proposer_score cfg (E.store cfg ext w m))
  /-- the forward walk-domain condition feeding `htS`. -/
  hdomS : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
      (get_node_for_root r) (get_node_for_root b) = true →
    r ∈ (E.store cfg ext vc nc).block_roots ∧
      WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks b).slot r
  /-- the reverse walk-domain condition feeding `htA`. -/
  hdomA : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
      (get_node_for_root b) (get_node_for_root r) = true →
    r ∈ (E.store cfg ext vc nc).block_roots ∧
      WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks r).slot b
  /-- `hBb` — the recorded base-enemy weight movement `(vc, nc) → (w, m)`, carried as an
  explicit input. The relay-based implication is invalid because the
  recorded-`BbadSet` subset is unprovable across epochs once `recorded_conflict_slashed`
  carries its same-target-epoch guard. The accepted route is `GroundBeta`'s
  store-independent ground-truth-`Bval` endpoint strip (`ledger_descendStep_groundBeta`),
  which needs **no** `hBb`. -/
  hBb : E.BbadVal cfg ext w m b lo es ≤ E.BbadVal cfg ext vc nc b lo es
  /-- `hdeltas` — the per-slot pre-`T1` class-migration deltas. -/
  hdeltas : ∀ σ' : Slot, es ≤ σ' →
    E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
    compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
    ∃ ξ α : ℕ,
      (E.Sval cfg ext w m b lo σ' + ξ + α +
          E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
            (fun i => i ∈ E.honest))
        ≤ E.Sval cfg ext w m b lo (σ' + 1)) ∧
      (E.Xval cfg ext w m b lo (σ' + 1) + ξ ≤ E.Xval cfg ext w m b lo σ') ∧
      (E.weight ((E.span_committee (σ' + 1) (σ' + 1)).filter (fun i => i ∈ E.honest)) ≤
        E.weight (E.Unrec cfg ext w m b lo es σ' \ E.Unrec cfg ext w m b lo es (σ' + 1))
          + ξ + α +
          E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
            (fun i => i ∈ E.honest)))
  /-- `hmaj` — the post-`T1` saturated honest majority. -/
  hmaj : ∀ σ' : Slot, es ≤ σ' →
    compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
    E.SlotWithinHorizon cfg σ' →
    E.Xval cfg ext w m b lo σ'
        + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
            / (100 - cfg.confirmation_byzantine_threshold)
        + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤ E.Sval cfg ext w m b lo σ'
  /-- `hval` — the registry-constant justified balance source. -/
  hval : ((E.store cfg ext w m).checkpoint_states
    (E.store cfg ext w m).justified_checkpoint).validators = E.registry
  /-- The justified balance source lies in the finite activity-constancy segment. -/
  hbsH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
    (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon
  /-- `hchild` — the fork-choice child membership of `c` under `h`. -/
  hchild : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk h
          (get_parent_payload_status (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks c)))
  /-- `hrec` — every `Sclass` member records a `c`-supporting latest message. -/
  hrec : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
    ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
      is_ancestor (E.store cfg ext w m)
        (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true
  /-- `hHon` — honest supporters of any sibling are confined to `Xclass`. -/
  hHon : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈
        get_node_children (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m))
            (ForkChoiceNode.mk h
              (get_parent_payload_status (E.store cfg ext w m)
                ((E.store cfg ext w m).blocks c))) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo σ
  /-- `hByz` — byz supporters of any sibling are confined to `BbadSet ∪ SpentSet`. -/
  hByz : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈
        get_node_children (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m))
            (ForkChoiceNode.mk h
              (get_parent_payload_status (E.store cfg ext w m)
                ((E.store cfg ext w m).blocks c))) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ




end Execution

end FastConfirmation.Spec

end
