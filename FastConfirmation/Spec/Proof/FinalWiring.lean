import FastConfirmation.Spec.Proof.ExportWiring
import FastConfirmation.Spec.Proof.IHMechanize

/-!
# Spec / Proof / FinalWiring: residual wiring

The `unrealized_justified` export is wired here into the `StrongPrefixSafetyInputs`
constituents, and the two mechanical E5-reset anchor obligations are closed outright.

## What is delivered

* **`prev_greatest_of_interface`** — the boundary-source justification field
  is closed **outright** from the export `JustificationInterface.unrealized_justified`.
  `MicroSteps.prev_greatest_justifiedIn_of_boundarySource` reduces it to `JustifiedIn` of the
  boundary rotation source (`(store v (n+1)).unrealized_justified_checkpoint` or
  `(fcr v n).previous_epoch_greatest_unrealized_checkpoint`); those are exactly the two
  conjuncts of `unrealized_justified`, which supplies the boundary-source premise.

* **`genesis_dom_of_interface`** — the E5-reset field `StrongPrefixSafetyInputs.genesis_dom` is
  closed **outright**. The genesis finalized root is the anchor (`get_forkchoice_store`), known
  at every honest store by within-node `StoreLE` monotonicity from the shared genesis; the
  ancestry `jc(w,m) ⪰ finalized(v,0)` composes `finalized_justified_ancestry` (finalized ⪯ jc)
  with `finalized_descent` (finalized(v,0) ⪯ finalized(w,m)) through `is_ancestor_trans` on the
  target-known walk domain (`store_walkKnownK`, the anchor target known).

* **`finalized_dom_of_known` / `finalized_root_relay_known`** — the reset field
  `StrongPrefixSafetyInputs.finalized_dom`. `finalized_dom_of_known` closes **both** conjuncts given
  the finalized-root knownness at `(w, m)` (its ancestry leg is the same `is_ancestor_trans`
  composition as `genesis_dom`); `finalized_root_relay_known` discharges that knownness from
  `Synchrony.block_relay` at the later-slot regime. The **same-slot cross-node** membership is
  outside the block-relay guarantee because `block_relay` has a `+1`-slot gate.

* **`dynamics_struct_of_hcase`** — the structural field `StrongPrefixSafetyInputs.dynamics_struct`
  via `IHMechanize.dynamicsChainStruct_of_endpoint`, with the endpoint knownness `hb`
  discharged from the confirming-store knownness by `HeadStack.b_known_of_relay` (later-slot),
  with the L4 loop-inversion descent `hcase` represented as the cross-store E5 input.

* **base-enemy transport (`hBb`).** `GroundBeta`'s store-independent ground-truth-`Bval` endpoint strip
  (`ledger_descendStep_groundBeta`, no relay, no `hBb`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `prev_greatest` from `unrealized_justified` -/

/-- **`prev_greatest` from `unrealized_justified`.** The `StrongPrefixSafetyInputs.prev_greatest` field
`StrongPrefixSafetyInputs.prev_greatest` (on an epoch boundary with no slot advance, the re-rotated
`fcrStep`-observed checkpoint is `JustifiedIn` in every honest view later) closes **outright**.
`MicroSteps.prev_greatest_justifiedIn_of_boundarySource` reduces it to `JustifiedIn (store w m)`
of the boundary rotation source

    if is_start_slot_at_epoch (cur+1) then (store v (n+1)).unrealized_justified_checkpoint
    else (fcr v n).previous_epoch_greatest_unrealized_checkpoint,

and both branches are conjuncts of the `unrealized_justified` export: the `then` branch is its
first conjunct at `(v, n+1)`, the `else` branch its second at `(v, n)`. The synchrony premise
`slot_at _ ≤ slot_at m` comes from `n + 1 ≤ m` by `slot_at_mono`. -/
theorem prev_greatest_of_interface (hji : JustificationInterface cfg ext E) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint) := by
  refine E.prev_greatest_justifiedIn_of_boundarySource cfg ext ?_
  intro v hv n w hw m hm hH _hstart
  have hHn1 := E.withinHorizon_mono cfg hm hH
  have hnm : n ≤ m := Nat.le_trans (Nat.le_succ n) hm
  have hHn := E.withinHorizon_mono cfg hnm hH
  split_ifs with hnext
  · exact (hji.unrealized_justified v hv (n + 1) w hw m
      hHn1 hH (E.slot_at_mono cfg hm)).1
  · exact (hji.unrealized_justified v hv n w hw m
      hHn hH (E.slot_at_mono cfg hnm)).2

/-! ## Section 2 — the E5 reset anchors: `genesis_dom` and `finalized_dom`

Both reset fields carry two conjuncts: the anchor root is known at `(w, m)`, and the store's
justified checkpoint dominates it (`jc(w,m) ⪰ r₀`). The dominance is the same composition for
both: `finalized_justified_ancestry` puts the store's own finalized block on its justified
chain (`finalized(w,m) ⪯ jc(w,m)`), and `finalized_descent` puts the reset anchor below the
store's finalized (`r₀ ⪯ finalized(w,m)`); `is_ancestor_trans` on the target-known walk domain
(`store_walkKnownK`, `r₀` the known target) composes them. -/

/-- **Justified dominance of a known reset anchor.** For any honest `(w, m)` and any root `r₀`
that is known at `(w, m)` and below the store's own finalized checkpoint
(`hdescent : finalized(w,m) ⪰ r₀`, the `finalized_descent` output), the store's justified
checkpoint dominates `r₀`. Composes `finalized_justified_ancestry` (finalized ⪯ jc) with
`hdescent` (r₀ ⪯ finalized) via `is_ancestor_trans`; the two walk witnesses come from
`store_walkKnownK` with `r₀` the known target and `jc(w,m).root` / `finalized(w,m).root` the
walked roots (both known by `checkpoint_known`). -/
theorem justified_dom_of_descent (hwfE : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hji : JustificationInterface cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} {r₀ : Root}
    (hH : E.WithinHorizon cfg m)
    (hr0known : r₀ ∈ (E.store cfg ext w m).block_roots)
    (hdescent : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root r₀) = true) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root r₀) = true := by
  have hpsl := E.store_parentSlotLt cfg ext hwfE hec hgen hwfE.anchor_parent_unscheduled w m
  have hjc := (hji.checkpoint_known w hw m).1
  have hfin := (hji.checkpoint_known w hw m).2
  have hwalk := E.store_walkKnownK cfg ext hwfE hec hgen w m r₀ hr0known
  exact is_ancestor_trans hpsl
    (hwalk _ hjc) (hwalk _ hfin)
    (hji.finalized_justified_ancestry w hw m hH hfin hjc) hdescent

/-- **`genesis_dom` closed.** The genesis reset field of
`StrongPrefixSafetyInputs`. The genesis finalized root is the anchor `ablk.root`
(`get_forkchoice_store`), which is known at every honest store by `StoreLE` monotonicity from
the shared genesis (`store v 0 = genesis_store = store w 0`); the dominance is
`justified_dom_of_descent` fed by `finalized_descent v 0 w m` (`0 ≤ m`). No residual. -/
theorem genesis_dom_of_interface (hSA : SpecAssumptions cfg ext E) :
    ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      (E.store cfg ext v 0).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  intro v _hv w hw m hH
  -- the genesis finalized root is the anchor root, known at `(w, m)`
  have hroot0 : (E.store cfg ext v 0).finalized_checkpoint.root = ablk.root := by
    change (E.genesis_store).finalized_checkpoint.root = ablk.root
    rw [hgeq]; simp [get_forkchoice_store]
  have hmem0 : (E.store cfg ext v 0).finalized_checkpoint.root ∈
      (E.store cfg ext w 0).block_roots := by
    rw [hroot0]
    change ablk.root ∈ (E.genesis_store).block_roots
    rw [hgeq]; simp [get_forkchoice_store]
  have hknown : (E.store cfg ext v 0).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hmem0
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  refine ⟨hknown, ?_⟩
  exact E.justified_dom_of_descent cfg ext hwfE hec hgen' hji hw hH hknown
    (hji.finalized_descent v _hv 0 w hw m hsv.genesis_within_horizon hH (Nat.zero_le m))

/-- **`finalized_dom` given the reset-anchor knownness.** The per-update reset
field of `StrongPrefixSafetyInputs`, reduced to the finalized-root knownness `hknown` at `(w, m)`:
its dominance leg is `justified_dom_of_descent` fed by `finalized_descent v (n+1) w m`. The
knownness itself is `finalized_root_relay_known` at strictly-later slot; the **same-slot
cross-node** case lies outside `block_relay`'s `+1`-slot guarantee. -/
theorem finalized_dom_of_known (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m)
    (hknown : (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots) :
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  refine ⟨hknown, ?_⟩
  exact E.justified_dom_of_descent cfg ext hwfE hec hgen hji hw hH hknown
    (hji.finalized_descent v hv (n + 1) w hw m
      (E.withinHorizon_mono cfg hm hH) hH hm)

/-- **The reset-anchor knownness via block relay.** The finalized root of
`(v, n+1)` is known at that store (`JustificationInterface.checkpoint_known`), so
`Synchrony.block_relay` lands it at every honest `(w, m)` past the block-relay slot gate
`slot_at (n+1) + 1 ≤ slot_at (m+1)` — the strictly-later regime. The same-slot cross-node case
(the whole window `[n+1, m+1]` inside one slot) is the documented block-relay reach limit. -/
theorem finalized_root_relay_known
    (hji : JustificationInterface cfg ext E) (hsyn : Synchrony cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hHm : E.WithinHorizon cfg m)
    (hgap : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) :
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots :=
  hsyn.block_relay v hv (n + 1) _ hHn1
    (hji.checkpoint_known v hv (n + 1)).2 w hw m hHm hgap

/-! ## Section 3 — `dynamics_struct` from the two per-endpoint suppliers

`IHMechanize.dynamicsChainStruct_of_endpoint` reduces `DynamicsChainStruct b (n+1)` to `hb`
(the confirmed `b` is relay-known at each honest endpoint under the shell IH) and `hcase` (the
L4 loop-inversion descent). `dynamics_struct_of_suppliers` lifts that to the field shape of
`StrongPrefixSafetyInputs.dynamics_struct` — per `is_one_confirmed` block, apply the endpoint lemma
to the two supplied families. `hb_of_confirming` discharges `hb` at the later-slot regime from
the confirming-store knownness via `HeadStack.b_known_of_relay`; the same-slot cross-node case
and `hcase` are supplied explicitly as cross-store inputs. -/

/-- **`dynamics_struct` from per-confirmed-block `hb`/`hcase` suppliers.** The
structural field of `StrongPrefixSafetyInputs` reduces to a per-confirmed-block endpoint-knownness
supplier `hb` and loop-inversion-descent supplier `hcase`, via
`IHMechanize.dynamicsChainStruct_of_endpoint`. This is the field-level wiring; the two
suppliers are the genuine residuals (`hb` relay-closable at later slot, `hcase` the cross-store
descent). -/
theorem dynamics_struct_of_suppliers (hSA : SpecAssumptions cfg ext E)
    (hb : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
          is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
            (get_node_for_root b) = true) →
        b ∈ (E.store cfg ext w m).block_roots)
    (hcase : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
        E.WithinHorizon cfg m →
        (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
          is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
            (get_node_for_root b) = true) →
        get_ancestor_roots (E.store cfg ext w m) b
            (E.store cfg ext w m).justified_checkpoint.root ≠ [] ∨
          b = (E.store cfg ext w m).justified_checkpoint.root) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
      is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
      E.DynamicsChainStruct cfg ext b (n + 1) :=
  fun v hv n b hconf =>
    E.dynamicsChainStruct_of_endpoint cfg ext hSA
      (hb v hv n b hconf) (hcase v hv n b hconf)

/-- **`hb`, later-slot, from confirming-store knownness.** Given the confirmed
`b` is a known block at its confirming store `(v, n+1)` (`hbconf`), `HeadStack.b_known_of_relay`
lands it at every honest endpoint `(w, m)` at the later-slot regime `slot_at (n+1) + 1 ≤
slot_at (m+1)`. This discharges `dynamics_struct_of_suppliers`' `hb` off the same-slot corner;
the same-slot cross-node case is the documented block-relay reach limit. -/
theorem hb_of_confirming (hsyn : Synchrony cfg ext E)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {n m : ℕ} {b : Root} (hbconf : b ∈ (E.store cfg ext v (n + 1)).block_roots)
    (hHn1 : E.WithinHorizon cfg (n + 1)) (hHm : E.WithinHorizon cfg m)
    (hgap : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) :
    b ∈ (E.store cfg ext w m).block_roots :=
  E.b_known_of_relay cfg ext hsyn hv hw hbconf hHn1 hHm hgap

/-! ## Section 4 — ground-truth base-enemy bounds

The base transport routes through `FastConfirmation/Spec/Proof/GroundBeta.lean`:
`bval_endpoint_strip_of_transport` / `ledger_descendStep_groundBeta` bound the endpoint enemy
by the **store-independent** ground-truth window weight `Bval(es)` (`span_fraction`-budgeted at
the endpoint directly — no relay, no subset, no `hBb`), closing the per-fork descent at every
slot regime with only the honest transports. -/

end Execution

end FastConfirmation.Spec
