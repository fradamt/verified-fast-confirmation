module
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.DynamicsClosure

@[expose] public section

/-!
# Spec / Proof / EdgeDynamics: constructing `ForkEdgeInput`

`ForkAssembly.ForkEdgeInput` is the per-edge store-dynamics bundle that
`ForkAssembly.dynamicsResidual_of_forkEdgeInput` converts to a
`DynamicsResidual`. This module derives its relay, ancestry-transport, and boost
fields, and packages the other fields in `EdgeInputResidual`.

## Relay and transport fields

* **`hequiv`** — `equivocating@(vc,nc) ⊆ equivocating@(w,m)` from
  `Synchrony.attester_slashing_relay` under the one-slot ordering
  `slot_at nc + 1 ≤ slot_at m` (`equiv_subset_of_relay`).
* **`hsub`** — `block_roots@(vc,nc) ⊆ block_roots@(w,m)` from `Synchrony.block_relay`
  under `slot_at nc + 1 ≤ slot_at (m+1)` (`blockRoots_subset_of_relay`);
  it feeds the two transports so they no longer carry a raw containment premise.
* **`htS`/`htA`** — the forward and reverse `is_ancestor` transports `(vc,nc) → (w,m)`,
  via `EngineTransport.is_ancestor_transport` (forward) and `BlockAgreement.is_ancestor_congr`
  (reverse). Reduced to the block relay (above) + per-root `WalkKnown` domain conditions —
  the standard Layer-0 shapes (`SupportsDesc_transport` / `AncestorOrVoteless_transport`).
* **`hboost`** — `boost = get_proposer_score cfg (store w m)`: definitional once `boost` is
  taken as that value.

## IH-dependent and accounting inputs

`EdgeInputResidual` bundles the fields supplied by the head-safety induction or
by accounting lemmas:

* **`hbase`** — `INV2(es)` at the confirming anchor: `DynamicsClosure.INV2_base_of_confirmed`
  reduces it to `Arms.arms_of_confirmed`'s accessor bridges (`Bridge.weak_base_discharged`
  + `Discount` + `HonestWeight` + the class-decomposition identities), whose accounting is
  the accounting inputs stated in `Arms.lean`.
* **`hdeltas`** — the per-slot pre-`T1` class-migration deltas `hs'`/`hx'`/`hρ`
  (`votes_head` + engine IH + `Delivery` + the `ρ = 0` same-epoch assignment bookkeeping,
  `StepDischargeII`).
* **`hmaj`** — the post-`T1` saturated honest majority (`committee_coverage` + `votes_head`
  + engine IH).
* **`hrec`** — per-`Sclass`-member recorded `c`-support at `(w,m)`
  (`Delivery.vote_ubiquity` + `Bridge.recorded_lm_is_newest` + the epoch-cased root
  identification, `EngineTransport.recorded_supports_c_of_IH`).
* **`hHon`/`hByz`** — the sibling confinements (provenance slot-confinement +
  `Forks.siblings_incompatible` + the `BbadSet`/`SpentSet` dichotomy).
* **`hval`** — the registry-constant justified source (`Registry.registryConstant` modulo
  `justified_checkpoint ∈ checkpoint_state_keys`).
* **`hchild`** — the fork-choice child membership `c ∈ get_node_children … h`
  (`FilterViability.chain_mem_get_filtered_block_tree`).

`forkEdgeInput_of_residual` assembles these fields into a `ForkEdgeInput`.


**P-6 note.** Some names used in this header no longer exist. The legacy `SpecAssumptions`
observed-anchor cone was retired and swept for orphans, which removed this module's own `EdgeInputResidual` and `forkEdgeInput_of_residual`.
The descriptions above are kept because they still identify the *shapes* the surviving
declarations produce and consume. See `docs/p6-justified-descends-derivation.md` §8.
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




/-! ## Section 3 — `EdgeInputResidual` and assembly

`EdgeInputResidual` is exactly the facts that stay after Sections 1–2: the `INV2` base,
the per-slot pre-`T1` deltas, the saturated majority, the registry source, the child
membership, the recorded `c`-support, and the two sibling confinements — plus the per-root
`WalkKnown` domain functions the transports consume. `boost` is fixed to
`get_proposer_score cfg (store w m)`, so `ForkEdgeInput`'s `hboost` field is definitional. -/

/-! ### Deleted: `EdgeInputResidual` and `forkEdgeInput_of_residual`

The per-edge residual bundle and its lift to a `ForkAssembly.ForkEdgeInput`. Both were
consumed only by `ShellCompose`'s engine composition. The per-field reductions of Sections 1-2,
and `ForkEdgeInput` itself, are unaffected; docstrings elsewhere that name
`EdgeInputResidual.<field>` still identify the field *shapes*, which are unchanged.


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
