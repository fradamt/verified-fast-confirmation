module
public import FastConfirmation.Spec.Proof.ForkAssembly

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

/-- **The reverse `is_ancestor` transport.** For known `b`, `r` at the confirming anchor
with the walk from `b` toward `r`'s slot known, a `b ⪯ r` fact transports `(vc,nc) → (w,m)`.
Mirrors `EngineTransport.is_ancestor_transport` in the opposite orientation via
`is_ancestor_congr`. -/
theorem is_ancestor_transport_rev (hwf : WellFormedExecution E)
    {vc w : ValidatorIndex} {nc m : ℕ} {r b : Root}
    (hsub : (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hr : r ∈ (E.store cfg ext vc nc).block_roots)
    (hb : b ∈ (E.store cfg ext vc nc).block_roots)
    (hw : WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks r).slot b)
    (hanc : is_ancestor (E.store cfg ext vc nc)
      (get_node_for_root b) (get_node_for_root r) = true) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root b) (get_node_for_root r) = true := by
  have hagree : ∀ x ∈ (E.store cfg ext vc nc).block_roots,
      (E.store cfg ext vc nc).blocks x = (E.store cfg ext w m).blocks x := fun x hx =>
    hwf.blocks_agree (E.blockProvenance cfg ext vc nc) (E.blockProvenance cfg ext w m)
      hx (hsub hx)
  simp only [get_node_for_root] at hanc ⊢
  rwa [← is_ancestor_congr hagree hb hr hw]

/-- **`htS` — the forward transport, quantified.** From the block relay containment `hsub`,
`b`-knownness, and the per-root forward walk-domain function `hdomS`, every `r ⪯ b` fact at
`(vc, nc)` transports to `(w, m)`. Exactly `ForkEdgeInput`'s `htS` argument, in the shape
`SupportsDesc_transport_of_anc` consumes. -/
theorem htS_of_walk (hwf : WellFormedExecution E)
    {vc w : ValidatorIndex} {nc m : ℕ} {b : Root}
    (hsub : (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext vc nc).block_roots)
    (hdomS : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root r) (get_node_for_root b) = true →
      r ∈ (E.store cfg ext vc nc).block_roots ∧
        WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks b).slot r) :
    ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root r) (get_node_for_root b) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root r) (get_node_for_root b) = true := by
  intro r hanc
  obtain ⟨hr, hwalk⟩ := hdomS r hanc
  exact is_ancestor_transport cfg ext hwf hsub hr hb hwalk hanc

/-- **`htA` — the reverse transport, quantified.** From the block relay containment `hsub`,
`b`-knownness, and the per-root reverse walk-domain function `hdomA`, every `b ⪯ r` fact at
`(vc, nc)` transports to `(w, m)`. Exactly `ForkEdgeInput`'s `htA` argument, in the shape
`AncestorOrVoteless_transport_of_anc` consumes. -/
theorem htA_of_walk (hwf : WellFormedExecution E)
    {vc w : ValidatorIndex} {nc m : ℕ} {b : Root}
    (hsub : (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb : b ∈ (E.store cfg ext vc nc).block_roots)
    (hdomA : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root b) (get_node_for_root r) = true →
      r ∈ (E.store cfg ext vc nc).block_roots ∧
        WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks r).slot b) :
    ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root b) (get_node_for_root r) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r) = true := by
  intro r hanc
  obtain ⟨hr, hwalk⟩ := hdomA r hanc
  exact E.is_ancestor_transport_rev cfg ext hwf hsub hr hb hwalk hanc

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

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-- **`hval` from the justification interface.** The `EdgeInputResidual.hval`
field states that the justified balance-source state carries the ground registry.
It follows from
`JustificationInterface.justified_cached`: the justified checkpoint is a
*keyed* checkpoint state because the real pipeline justifies only ≥2/3-attested targets that
`on_attestation`'s `store_target_checkpoint_state` cached) together with
`Registry.registryConstant`'s checkpoint-state clause (every keyed checkpoint state at an
honest store carries `validators = E.registry`, from the trusted genesis initialization +
`ExternalsCoherence`). -/
theorem hval_of_interface (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hji : JustificationInterface cfg ext E) (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m) :
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
  (E.registryConstant cfg ext hec hgen w m).2 _
    (hji.justified_cached w hw m hH)

/-- The cached justified balance source is no later than the endpoint execution
slot, hence its current epoch is below the endpoint's verification horizon. -/
theorem justified_balance_source_epoch_lt_horizon
    (hec : ExternalsCoherence cfg ext E) (hji : JustificationInterface cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hH : E.WithinHorizon cfg m) :
    get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon := by
  have hcached := hji.justified_cached w hw m hH
  have hslot := (E.stateSlotsLE cfg ext hdiv hec hgen w m).2 _ hcached
  exact lt_of_le_of_lt (Nat.div_le_div_right hslot) hH.2.2

end Execution

end FastConfirmation.Spec

end
