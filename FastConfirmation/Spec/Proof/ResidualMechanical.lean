import FastConfirmation.Spec.Proof.ResidualDischarge
import FastConfirmation.Spec.Proof.WFTrajectory

/-!
# Spec / Proof / ResidualMechanical: deriving `L4ResidualHyps`

`ResidualDischarge.l4Residual_of_hyps` reduces `Spec_Safety` to the six-field
bundle `L4ResidualHyps`. This module derives its store-structural fields from
`SpecAssumptions` and the trajectory invariants, and packages the additional
store-dynamics and FFG inputs as `MechanicalResiduals`.

The reductions follow the fields of `L4ResidualHyps`:

* **`interface`** — a `SpecAssumptions` component; wired directly.

* **`store_domain`** — the shared per-honest-store fork-choice
  `StoreDomain` (parent-slot order + `WalkKnown` walk domain + justified-known).
  Its `parent_slot_lt` conjunct follows from
  `WFTrajectory.store_parentSlotLt` (Layer 0, under the `WFTrajectory` anchor guard). The
  other two conjuncts (`WalkKnown`-forall — the ancestor-closure store
  invariant — and justified-knownness) are supplied by the named
  `walk_domain` and `justified_known` inputs.

* **`genesis_fin_track` + `finalized_track`** — both are instances
  of one cross-store finalized-descent residual `finalized_descent` (each honest
  store's finalized block descends from any earlier honest finalized root — the
  Casper cross-store finalization-consistency fact) plus finalized-knownness. The
  genesis anchor identity (`E.store v 0 = E.genesis_store`, shared across honest
  `v`) is derived here, so both fields use the same residual.

* **`observed_dom`** — the rotated observed-justified anchor is on every
  honest justified chain, using `observed_justified`, `justified_unique`, and
  `gate_sound`, together with `HonestVotesSupportTarget` at the
  `will_current_target_be_justified` gate.

* **`advance_cert`** — the per-confirmed-block
  `LedgerChainInputCert`. `ledgerChainInputCert_of_dynamicsChain` **builds** it:
  from a per-honest-endpoint ascending chain of same-epoch `DynamicsResidual`
  edges (`ResidualDischarge.DynamicsResidual`, the certificate seed the L4 loop
  inversions expose) plus the endpoint domain facts, the `List.IsChain
  DynamicsResidual` lifts edge-wise to `List.IsChain LedgerCertInput`
  (`ledgerCertInput_of_dynamicsResidual` + `List.IsChain.imp`). The per-edge
  `DynamicsResidual` supply and the epoch-crossing prev-epoch tax-arm stay named
  (`dynamics_chain`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `StoreDomain` from Layer 0 + two named invariants

`StoreDomain` bundles three per-honest-store conditions. The parent-slot order is
the Layer-0 `ParentSlotLt`, derived by `WFTrajectory.store_parentSlotLt` under the
`SpecAssumptions` genesis form and the `WFTrajectory` anchor guard. The
`WalkKnown` walk domain and justified-knownness enter through the two named
inputs. -/

/-- **`StoreDomain` from the Layer-0 parent-slot order + the two named invariants.**
The `parent_slot_lt` conjunct is `store_parentSlotLt` (Layer 0); `hwalk` /
`hjust` supply the `WalkKnown` walk domain and justified-knownness. The `hgen` /
`hanchor` hypotheses are `SpecAssumptions`' genesis form and the `WFTrajectory` anchor guard
that `store_parentSlotLt` consumes. -/
theorem storeDomain_of_layer0
    (hwf : WellFormedExecution E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hanchor : ∀ r ∈ E.genesis_store.block_roots, ∀ w n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n → b.root ≠ (E.genesis_store.blocks r).parent_root)
    (hwalk : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ t r : Root,
      r ∈ (E.store cfg ext w m).block_roots →
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots) :
    E.StoreDomain cfg ext := by
  intro w hw m hH
  exact ⟨E.store_parentSlotLt cfg ext hwf hec hgen hanchor w m,
    hwalk w hw m, hjust w hw m hH⟩

/-! ## Section 2 — finalized tracking from one cross-store residual

`genesis_fin_track` and `finalized_track` are the same statement at two anchors:
each honest store's finalized block is known and descends from an earlier honest
finalized root. Both collapse onto one cross-store finalized-descent residual
`hfin_descent` (`finalized(w, m) ⪰ finalized(v, k)` whenever `k ≤ m`) plus
finalized-knownness `hfin_known`. The genesis anchor `(E.store v 0)` is
`E.genesis_store` by definition — `hfin_descent … 0 …` (with `0 ≤ m`) supplies it,
`hfin_descent … (n+1) …` (with `n+1 ≤ m`) supplies the update anchor. This is the
Casper cross-store finalization-consistency fact represented by
`finalized_descent`. -/

/-- **`genesis_fin_track` from the finalized-descent residual.** The genesis anchor
`(E.store v 0).finalized_checkpoint.root` is reached at `k = 0` (`0 ≤ m`). -/
theorem genesisFinTrack_of_descent
    (hfin_known : ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
    (hfin_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true) :
    ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true :=
  fun v hv w hw m hH =>
    ⟨hfin_known w hw m hH, hfin_descent v hv 0 w hw m (Nat.zero_le m) hH⟩

/-- **`finalized_track` from the finalized-descent residual.** The update anchor
`(E.store v (n+1)).finalized_checkpoint.root` is reached at `k = n+1` (`n+1 ≤ m`). -/
theorem finalizedTrack_of_descent
    (hfin_known : ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
    (hfin_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true :=
  fun v hv n w hw m hm hH =>
    ⟨hfin_known w hw m hH, hfin_descent v hv (n + 1) w hw m hm hH⟩

/-! ## Section 3 — the certificate chain assembly

`advance_cert` needs a `LedgerChainInputCert` per confirmed block `b`: at every
honest endpoint `(w, m)`, an ascending chain from the justified root to `b` whose
every edge is a `LedgerCertInput`. `DynamicsChainSupply` is the same shape with the
edges the more primitive same-epoch `DynamicsResidual` (`ResidualDischarge`) — the
certificate seed the L4 loop inversions (`get_ancestor_roots` ascending chain)
expose per fork edge. `ledgerChainInputCert_of_dynamicsChain` **builds** the
`LedgerChainInputCert` from it: the `List.IsChain DynamicsResidual` lifts edge-wise
to `List.IsChain LedgerCertInput` via `ledgerCertInput_of_dynamicsResidual` (the
per-edge closure, needing the `hec`/`hsv` coherence records) and `List.IsChain.imp`;
the domain facts pass through unchanged. The per-edge `DynamicsResidual` supply and
the epoch-crossing previous-epoch tax arm stay inside `DynamicsChainSupply`. -/

/-- **The same-epoch dynamics-chain supply.** `LedgerChainInputCert`'s shape with
each edge's `LedgerCertInput` replaced by the more primitive same-epoch
`DynamicsResidual`. At every honest endpoint `(w, m)` past `n₀`, given head safety
at strictly earlier slots (the strong-induction hypothesis), the confirmed chain
from the justified root to `b` presents as a `List.IsChain DynamicsResidual` with
the fork-choice domain facts. The certificate seed the L4 chain fold supplies per
confirmed block. -/
def DynamicsChainSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∃ ds : List Root,
      (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
        r ∈ (E.store cfg ext w m).block_roots) ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      ds.Nodup ∧
      List.IsChain (E.DynamicsResidual cfg ext w m)
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **`LedgerChainInputCert` from the dynamics-chain supply.** The
per-edge `DynamicsResidual` chain lifts to a `LedgerCertInput` chain
(`ledgerCertInput_of_dynamicsResidual` + `List.IsChain.imp`); the domain facts pass
through unchanged. The chain-assembly result — everything below the per-edge
certificate boundary is `DynamicsChainSupply`, the named residual. -/
theorem ledgerChainInputCert_of_dynamicsChain
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    {b : Root} {n₀ : ℕ} (hsupply : E.DynamicsChainSupply cfg ext b n₀) :
    LedgerChainInputCert cfg ext E b n₀ := by
  intro w hw m hm hH hIH
  obtain ⟨ds, hwf, hsub, hb, hnd, hdchain, hlast⟩ := hsupply w hw m hm hH hIH
  exact ⟨ds, hwf, hsub, hb, hnd,
    hdchain.imp (fun _ _ hab => E.ledgerCertInput_of_dynamicsResidual cfg ext hec hsv hab),
    hlast⟩

/-! ## Section 4 — the residual bundle and the `L4ResidualHyps` assembly

`MechanicalResiduals` collects the seven named residuals this module reduces
`L4ResidualHyps` to, with each input retained in its existing shape.
`l4ResidualHyps_of_mechanical` discharges all six `L4ResidualHyps` fields from
`SpecAssumptions` (`interface`, plus the `hwf`/`hec`/`hsv`/`hgen` records the
mechanical reductions consume) and this bundle. -/

/-- **The mechanical input bundle** produced by the `ResidualMechanical` reductions. Seven named
store-dynamics / FFG residuals, each in an existing shape:

* `anchor_unscheduled` — the `WFTrajectory` genesis anchor guard (no scheduled block's root
  is a genesis block's dangling parent pointer; a `WellFormedExecution`-shaped
  fact) that `store_parentSlotLt` consumes;
* `walk_domain` — the `WalkKnown` ancestor-closure walk domain per honest store;
* `justified_known` / `finalized_known` — the justified/finalized checkpoint roots
  are known per honest store;
* `finalized_descent` — cross-store finalized descent (Casper finalization
  consistency), used by both finalized-tracking fields;
* `observed_dom` — observed-justified justified-dominance;
* `dynamics_chain` — the per-confirmed-block same-epoch `DynamicsChainSupply`
  (the per-edge `DynamicsResidual` seeds plus the chain structure). -/
structure MechanicalResiduals (E : Execution Root) : Prop where
  /-- `WFTrajectory`: no scheduled block's root equals a genesis block's dangling parent. -/
  anchor_unscheduled : ∀ r ∈ E.genesis_store.block_roots, ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n → b.root ≠ (E.genesis_store.blocks r).parent_root
  /-- the `WalkKnown` walk domain over all known roots per honest store. -/
  walk_domain : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ t r : Root,
    r ∈ (E.store cfg ext w m).block_roots →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r
  /-- justified-knownness per honest store. -/
  justified_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- finalized-knownness per honest store. -/
  finalized_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- cross-store finalized descent (Casper): each honest store's finalized block
      descends from any earlier honest finalized root. -/
  finalized_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true
  /-- The rotated observed-justified anchor is on every honest justified
      chain (verbatim `L4ResidualHyps.observed_dom`). -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- Every `is_one_confirmed` block at an update store carries a
      same-epoch `DynamicsChainSupply` (the per-edge `DynamicsResidual` seeds). -/
  dynamics_chain : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainSupply cfg ext b (n + 1)

/-- **`L4ResidualHyps` from `SpecAssumptions` + `MechanicalResiduals`.** All six
`L4ResidualHyps` fields: `interface` from `SpecAssumptions`; `store_domain` from the
Layer-0 parent-slot order + `walk_domain`/`justified_known`; the two finalized
tracks from `finalized_known`/`finalized_descent`; `observed_dom` verbatim; and
`advance_cert` from the chain assembly `ledgerChainInputCert_of_dynamicsChain`
applied to `dynamics_chain`. This is `ResidualMechanical`'s contract — `L4ResidualHyps` reduces to
exactly the `MechanicalResiduals` list. -/
theorem l4ResidualHyps_of_mechanical (hSA : SpecAssumptions cfg ext E)
    (hmech : E.MechanicalResiduals cfg ext) : E.L4ResidualHyps cfg ext := by
  obtain ⟨hgen, hwf, _hdiv, _hbeh, _hsync, hec, hsv, _hbb, hji⟩ := hSA
  exact
    { interface := hji
      store_domain := E.storeDomain_of_layer0 cfg ext hwf hec hgen hmech.anchor_unscheduled
        hmech.walk_domain hmech.justified_known
      genesis_fin_track := E.genesisFinTrack_of_descent cfg ext hmech.finalized_known
        hmech.finalized_descent
      finalized_track := E.finalizedTrack_of_descent cfg ext hmech.finalized_known
        hmech.finalized_descent
      observed_dom := hmech.observed_dom
      advance_cert := fun v hv n b hconf =>
        E.ledgerChainInputCert_of_dynamicsChain cfg ext hec hsv
          (hmech.dynamics_chain v hv n b hconf) }

end Execution

/-! ## Section 5 — the headline: `Spec_Safety` from `MechanicalResiduals`

Composing `l4ResidualHyps_of_mechanical` with `ResidualDischarge.spec_safety_of_residualHyps`:
if `SpecAssumptions` supplies `MechanicalResiduals` for every execution, the FCR
safety guarantee holds. `MechanicalResiduals` is the input bundle produced by
this reduction. -/

/-- **`Spec_Safety` from the mechanical residuals.** The final reduction: the FCR
safety guarantee follows from a proof that every execution's `SpecAssumptions`
supplies `MechanicalResiduals`. -/
theorem spec_safety_of_mechanical
    (hmech : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.MechanicalResiduals cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_residualHyps cfg ext
    (fun E hSA => E.l4ResidualHyps_of_mechanical cfg ext hSA (hmech E hSA))

end FastConfirmation.Spec
