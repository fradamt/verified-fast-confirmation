import FastConfirmation.Spec.Proof.Remainder
import FastConfirmation.Spec.Proof.FinalWiring
import FastConfirmation.Spec.Proof.Identities
import FastConfirmation.Spec.Proof.StrongPrefixSafety

/-!
# Spec / Proof / ShellCompose: the shell-IH composition

This module threads the shell's head-safety induction hypothesis (the IH of
`HeadSafetyEngine.spec_head_safety_engine`, carried through `ForkAssembly.ForkEdgeSupply`)
into the IH-functional store-dynamics families, machine-checking that the per-edge engine
bundle `EdgeDynamics.EdgeInputResidual` — hence `ForkAssembly.ForkEdgeInput` and
`fork_edges` — reduces to exactly the **enumerated engine residuals + same-slot availability**.

## What this module composes

`EdgeDynamics.forkEdgeInput_of_residual` already turns an `EdgeInputResidual` into a
`ForkEdgeInput`. This module reduces the **IH-functional** fields of `EdgeInputResidual`
one level further, wiring the committed suppliers so the residual is a transparent bundle
`ForkEdgeEngineInputs` of the genuinely-open engine facts:

* **`hdeltas` (pre-`T1` class migration)** ⟵ `Remainder.hSmono_of_engine` /
  `hXmono_of_engine` (each per pre-`T1` slot) composed through
  `VoteLanding.hdeltas_sameEpoch`. Its sole store-dynamics input is the per-slot
  `Remainder.FreshEngineInputs` — the head-safety IH at the fresh voters' stores plus the
  `Synchrony.block_relay` domain conditions — together with the same-epoch structure. The
  IH regime is `slot(voter) < slot(m)`; the `slot(voter) = slot(m)` corner is **same-slot availability**.
* **`hmaj` (post-`T1` saturated majority)** ⟵ `VoteLanding.hmaj_of_saturation_lb` fed
  `Identities.hspan_of_coverage`. Its inputs are the full-saturation support crux `hsat`
  (`committee_coverage` + `votes_head` + IH) and the explicit tiny-`TAB` nondegeneracy /
  coverage `hnondeg`/`hcov`.
* **`hrec` (recorded `c`-support)** ⟵ `IHMechanize.hrec_of_domain` — the per-endpoint
  domain package (`Delivery.vote_ubiquity` + `store_walkKnownK` + the engine IH).
* **`hval`** — discharged outright from `SpecAssumptions` (`EdgeDynamics.hval_of_interface`).

Carried verbatim as genuine per-edge residuals: `hbase` (the confirming-anchor `INV2(es)`,
further reduced by `Identities.INV2_base_bridged_instantiated` to the `VpreIdentities`
class-decomposition identities), the two `is_ancestor` walk domains `hdomS`/`hdomA`, the
recorded base-enemy movement `hBb` (the ground-truth route
`GroundBeta.ledger_descendStep_groundBeta` avoids this assumption), the fork-choice
child membership `hchild`, and the sibling confinements
`hHon`/`hByz` (the `Xclass`-antitone reconciliation at general `σ` is the deepest residue —
`VoteLanding.hHon_of_confinement`/`hByz_of_confinement` discharge the base slice `σ = es`).

The net statement — `forkEdgeInput_of_engineInputs` — is that the whole per-edge engine
composes from `SpecAssumptions` down to `ForkEdgeEngineInputs`, whose fields are the named
engine residuals the shell threads its IH into. Consequently, there is
**no** reduction to same-slot availability alone (the engine's base mechanization — `hsat`,
`VpreIdentities`, the block-relay `FreshEngineInputs` — remains open at every slot regime),
so this composition does not yield an outright next-slot-weakened `Spec_Safety`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the IH-functional field reductions

The two reductions that genuinely thread the shell's head-safety induction hypothesis:
`hdeltas` (via the per-slot `FreshEngineInputs`) and `hmaj` (via the saturation crux). Both
are produced in `EdgeDynamics.EdgeInputResidual`'s exact field shapes. -/

/-- **`EdgeInputResidual.hdeltas` from the per-slot engine inputs.** Each pre-`T1`
slot's honest-support growth `hSmono` and sibling-stuck antitonicity `hXmono`
(`Remainder.hSmono_of_engine`/`hXmono_of_engine`) is produced from the fresh-voter engine
inputs `FreshEngineInputs` (the head-safety IH + `Synchrony.block_relay` domains) and the
same-epoch structure; `VoteLanding.hdeltas_sameEpoch` then assembles the migration deltas.
This is the shell-IH composition of the hardest IH-functional family. -/
theorem hdeltas_of_engineInputs (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hwf : WellFormedExecution E)
    (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot)
    (hlo : lo ≤ es + 1)
    (hin : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.FreshEngineInputs cfg ext w m b lo σ' ∧
        (∀ t : Slot, lo ≤ t → t ≤ σ' →
          compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1)) ∧
        E.slot_at cfg 0 ≤ σ' + 1) :
    ∀ σ' : Slot, es ≤ σ' →
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
              (fun i => i ∈ E.honest))) := by
  refine E.hdeltas_sameEpoch cfg ext hec w m b lo es hlo ?_ ?_ ?_
  · intro σ' h1 hσH hσ1H h2
    obtain ⟨hfresh, hsame, hs0⟩ := hin σ' h1 hσH hσ1H h2
    exact E.hSmono_of_engine cfg ext hhb hec hwf w m b lo σ' hσ1H hs0 hsame hfresh
  · intro σ' h1 hσH hσ1H h2
    obtain ⟨hfresh, hsame, hs0⟩ := hin σ' h1 hσH hσ1H h2
    exact E.hXmono_of_engine cfg ext hhb hec hwf w m b lo σ' hσ1H hs0 hsame hfresh
  · intro σ' h1 hσH hσ1H h2
    exact (hin σ' h1 hσH hσ1H h2).2.1

/-- **`EdgeInputResidual.hmaj` from the saturation crux and coverage.** The post-`T1`
saturated honest majority from the full-saturation support crux `hsat` (every honest window
member re-votes `desc(b)`, `committee_coverage` + IH) and the explicit saturated-`Jspec`
lower bound produced by `Identities.hspan_of_coverage` (tiny-`TAB` nondegeneracy `hnondeg` +
full-epoch honest coverage `hcov`), via `VoteLanding.hmaj_of_saturation_lb`. `boost` is
pinned to the endpoint proposer score, matching `EdgeInputResidual.hmaj`. -/
theorem hmaj_of_engineInputs (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
        E.SupportsDesc cfg ext w m b σ' i)
    (hnondeg : 4 * (get_proposer_score cfg (E.store cfg ext w m) + 1) ≤ E.total_active cfg)
    (hcov : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.total_active cfg ≤ 2 * E.Jspec lo σ') :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b lo σ'
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
              / (100 - cfg.confirmation_byzantine_threshold)
          + get_proposer_score cfg (E.store cfg ext w m) + 1 ≤ E.Sval cfg ext w m b lo σ' :=
  E.hmaj_of_saturation_lb cfg ext w m b lo es (get_proposer_score cfg (E.store cfg ext w m))
    hsat (hspan_of_coverage E cfg lo es (get_proposer_score cfg (E.store cfg ext w m))
      hnondeg hcov)

/-! ## Section 2 — the transparent engine-residual bundle and the per-edge composition

`ForkEdgeEngineInputs` is `EdgeDynamics.EdgeInputResidual` with the IH-functional fields
`hdeltas`/`hmaj`/`hrec` replaced by their genuine engine inputs (the shell-IH families) and
`hval` dropped (interface-derivable). `forkEdgeInput_of_engineInputs` composes the suppliers
into a `ForkEdgeInput`, so `fork_edges` reduces exactly to this bundle under `SpecAssumptions`. -/

/-- **The per-edge engine-residual bundle.** The store-dynamics assumptions
per confirmed edge `a ← c` at honest endpoint `(w, m)`, with the IH-functional families
exposed as their engine inputs: `hdeltaIn` (the per-slot `FreshEngineInputs` = the shell
head-safety IH + `block_relay` domains + same-epoch structure) feeds `hdeltas`;
`hsat`/`hnondeg`/`hcov` feed `hmaj`; the domain package `hb_wm`…`hwalk_wm` feeds `hrec`. The
non-IH residues `hbase` (⟶ `VpreIdentities`), the transports `hdomS`/`hdomA`, the base-enemy
movement `hBb`, the child membership `hchild`, and the sibling confinements `hHon`/`hByz`
(the deepest residue) are carried verbatim. -/
structure ForkEdgeEngineInputs (E : Execution Root) (w : ValidatorIndex) (m : ℕ)
    (b h c : Root) (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot) : Prop where
  /-- the confirming anchor is honest. -/
  hvc : vc ∈ E.honest
  /-- the confirming anchor lies in the verified execution prefix. -/
  hHnc : E.WithinHorizon cfg nc
  /-- the endpoint lies in the verified execution prefix. -/
  hHm : E.WithinHorizon cfg m
  /-- the block-relay slot gate confirming-anchor → endpoint. -/
  hslotS : E.slot_at cfg nc + 1 ≤ E.slot_at cfg (m + 1)
  /-- window end past the cutoff. -/
  hσ : es ≤ σ
  /-- window start lies in the finite verification segment. -/
  hloH : E.SlotWithinHorizon cfg lo
  /-- window endpoint lies in the finite verification segment. -/
  hσH : E.SlotWithinHorizon cfg σ
  /-- window start no later than one past the cutoff. -/
  hlo : lo ≤ es + 1
  /-- `b` is known at the confirming anchor. -/
  hb : b ∈ (E.store cfg ext vc nc).block_roots
  /-- `hbase` — `INV2(es)` at the confirming anchor (⟶ `VpreIdentities`). -/
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
  /-- `hBb` — recorded base-enemy weight movement. The store-independent
      ground-truth-`Bval` endpoint strip (`GroundBeta.ledger_descendStep_groundBeta`)
      provides an alternative route that does not require this field. -/
  hBb : E.BbadVal cfg ext w m b lo es ≤ E.BbadVal cfg ext vc nc b lo es
  /-- `hdeltas` inputs — the per-slot `FreshEngineInputs` (shell IH + relay) + same-epoch. -/
  hdeltaIn : ∀ σ' : Slot, es ≤ σ' →
    E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
    compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
    E.FreshEngineInputs cfg ext w m b lo σ' ∧
      (∀ t : Slot, lo ≤ t → t ≤ σ' →
        compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1)) ∧
      E.slot_at cfg 0 ≤ σ' + 1
  /-- `hmaj` input — the post-`T1` full-saturation support crux. -/
  hsat : ∀ σ' : Slot, es ≤ σ' →
    compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
    E.SlotWithinHorizon cfg σ' →
    ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext w m b σ' i
  /-- `hmaj` input — tiny-`TAB` nondegeneracy (explicit). -/
  hnondeg : 4 * (get_proposer_score cfg (E.store cfg ext w m) + 1) ≤ E.total_active cfg
  /-- `hmaj` input — full-epoch honest coverage floor (explicit). -/
  hcov : ∀ σ' : Slot, es ≤ σ' →
    compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
    E.SlotWithinHorizon cfg σ' →
    E.total_active cfg ≤ 2 * E.Jspec lo σ'
  /-- `hrec` domain — `b`/`c` known and edge at the endpoint. -/
  hb_wm : b ∈ (E.store cfg ext w m).block_roots
  hc_wm : c ∈ (E.store cfg ext w m).block_roots
  hbc_wm : is_ancestor (E.store cfg ext w m)
    (get_node_for_root b) (get_node_for_root c) = true
  /-- `hrec` domain — the engine IH at later `[σ+1, slot m)` votes (shell-threaded). -/
  hIH : ∀ j ∈ E.honest, ∀ t' : Slot, σ + 1 ≤ t' → t' < E.slot_at cfg m →
    ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true
  /-- `hrec` domain — the ubiquity landing (`Delivery.vote_ubiquity`). -/
  hubiq : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
    E.vote i t = some (kk, a) →
    ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
      compute_epoch_at_slot cfg t ≤ lm.epoch
  /-- `hrec` domain — vote-block knownness. -/
  hbbr_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
    ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
    E.vote i t = some (kk, a) → a.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots
  /-- `hrec` domain — recorded-root walk domain. -/
  hwalk_wm : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ lm,
    (E.store cfg ext w m).latest_messages i = some lm →
    WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root
  /-- `hchild` — the fork-choice child membership of `c` under `h`. -/
  hchild : ForkChoiceNode.mk c ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h)
  /-- `hHon` — honest supporters of any sibling are confined to `Xclass` (carried). -/
  hHon : ∀ c' : Root,
    ForkChoiceNode.mk c' ∈
        get_node_children (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo σ
  /-- `hByz` — byz supporters of any sibling are confined to `BbadSet ∪ SpentSet` (carried). -/
  hByz : ∀ c' : Root,
    ForkChoiceNode.mk c' ∈
        get_node_children (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ

/-- **`ForkEdgeEngineInputs ⟹ ForkEdgeInput`.** The per-edge shell-IH composition:
the IH-functional families are reduced by the suppliers (`hdeltas_of_engineInputs`,
`hmaj_of_engineInputs`, `IHMechanize.hrec_of_domain`), `hval` is discharged from the
interface (`EdgeDynamics.hval_of_interface`), and the non-IH residues are carried into an
`EdgeInputResidual`, which `EdgeDynamics.forkEdgeInput_of_residual` lifts to a `ForkEdgeInput`.
This machine-checks that the whole per-edge engine composes down to `ForkEdgeEngineInputs`. -/
theorem forkEdgeInput_of_engineInputs (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b h c : Root} {vc : ValidatorIndex} {nc : ℕ} {lo es σ : Slot}
    (hw : w ∈ E.honest)
    (hin : E.ForkEdgeEngineInputs cfg ext w m b h c vc nc lo es σ) :
    E.ForkEdgeInput cfg ext w m b h c := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E := ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, heq, _, _⟩ := hgen
    exact ⟨ast, ablk, heq⟩
  have hres : E.EdgeInputResidual cfg ext w m b h c vc nc lo es σ :=
    { hloH := hin.hloH
      hσH := hin.hσH
      hbase := hin.hbase
      hdomS := hin.hdomS
      hdomA := hin.hdomA
      hBb := hin.hBb
      hdeltas := E.hdeltas_of_engineInputs cfg ext hhb hec hwfE w m b lo es hin.hlo hin.hdeltaIn
      hmaj := E.hmaj_of_engineInputs cfg ext w m b lo es hin.hsat hin.hnondeg hin.hcov
      hval := E.hval_of_interface cfg ext hec hgen' hji w hw m hin.hHm
      hbsH := E.justified_balance_source_epoch_lt_horizon cfg ext hec hji hdiv hgen'
        w hw m hin.hHm
      hchild := hin.hchild
      hrec := E.hrec_of_domain cfg ext hSA hw hin.hb_wm hin.hc_wm hin.hbc_wm hin.hIH
        hin.hubiq hin.hbbr_known hin.hwalk_wm
      hHon := hin.hHon
      hByz := hin.hByz }
  exact E.forkEdgeInput_of_residual cfg ext hwfE hsync hin.hvc hw hin.hHnc hin.hHm
    hin.hslotS hin.hσ hin.hlo hin.hb hres

/-! ## Section 3 — the endpoint/edge lift and the final facade

`ForkEdgeEngineSupply` is `ForkAssembly.ForkEdgeSupply`'s endpoint/edge quantification with
the per-edge `ForkEdgeInput` replaced by the transparent `ForkEdgeEngineInputs`;
`forkEdgeSupply_of_engineSupply` lifts it back, so `fork_edges` reduces to it. -/

/-- **The per-block engine supply.** `ForkAssembly.ForkEdgeSupply`'s shape with the
per-edge `ForkEdgeInput` replaced by the transparent engine bundle `ForkEdgeEngineInputs`
(the certificate coordinates existentially supplied per edge). This is the exact functional
the `HeadSafetyEngine` shell instantiates — its strong induction supplies the head-safety IH
`hIH`, which the `hdeltaIn`/`hIH` fields of `ForkEdgeEngineInputs` thread through. -/
def ForkEdgeEngineSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
        ∃ (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot),
          E.ForkEdgeEngineInputs cfg ext w m b a c vc nc lo es σ

/-- **`ForkEdgeEngineSupply ⟹ ForkEdgeSupply`.** The endpoint/edge quantification and
the shell head-safety IH pass through unchanged; each edge's existential engine bundle is
composed to a `ForkEdgeInput` by `forkEdgeInput_of_engineInputs`. -/
theorem forkEdgeSupply_of_engineSupply (hSA : SpecAssumptions cfg ext E)
    {b : Root} {n₀ : ℕ} (hsupply : E.ForkEdgeEngineSupply cfg ext b n₀) :
    E.ForkEdgeSupply cfg ext b n₀ := by
  intro w hw m hm hHm hIH a c ha hc hlink
  obtain ⟨vc, nc, lo, es, σ, hin⟩ := hsupply w hw m hm hHm hIH a c ha hc hlink
  exact E.forkEdgeInput_of_engineInputs cfg ext hSA hw hin

/-- **The engine-reduced safety residual bundle.** `StrongPrefixSafetyInputs`
with the opaque `fork_edges` (`ForkEdgeSupply`) replaced by the transparent engine supply
`fork_edges_engine` (`ForkEdgeEngineSupply` per confirmed block). The same-slot reset corner
`finalized_dom_sameslot` and the structural chain `dynamics_struct` pass through verbatim. -/
structure EngineSafetyResiduals (E : Execution Root) : Prop where
  /-- `[E5-reset / same-slot availability]` — verbatim `StrongPrefixSafetyInputs.finalized_dom_sameslot`. -/
  finalized_dom_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- `[E-struct]` — verbatim `StrongPrefixSafetyInputs.dynamics_struct`. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E-edges]` — the transparent per-edge engine supply per confirmed block: the
      shell-IH families `hdeltaIn`/`hsat`/`hIH`, plus the
      carried `hbase`/`hHon`/`hByz`/`hchild`/transports/`hBb`). -/
  fork_edges_engine : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeEngineSupply cfg ext b (n + 1)

/-- **`StrongPrefixSafetyInputs` from `EngineSafetyResiduals` + `SpecAssumptions`.** The two
carried fields pass through; `fork_edges` is rebuilt per confirmed block from
`fork_edges_engine` via `forkEdgeSupply_of_engineSupply`. -/
theorem specSafetyResiduals_of_engine (hSA : SpecAssumptions cfg ext E)
    (h : E.EngineSafetyResiduals cfg ext) : E.StrongPrefixSafetyInputs cfg ext :=
  { finalized_dom_sameslot := h.finalized_dom_sameslot
    dynamics_struct := h.dynamics_struct
    fork_edges := fun v hv n b hconf =>
      E.forkEdgeSupply_of_engineSupply cfg ext hSA (h.fork_edges_engine v hv n b hconf) }

end Execution

/-! ## Section 4 — deleted: `Spec_Safety_of_engineResiduals`

The engine-reduced safety headline stood here: `Spec_Safety` from `EngineSafetyResiduals`, via
`specSafetyResiduals_of_engine` and `StrongPrefixSafety.Spec_Safety_of_strongPrefix_inputs`.
It carried the unproduced ahead-regime head-tracking premise `htracks` and is deleted with the rest of the legacy
`SpecAssumptions` observed-anchor cone (P-6). `specSafetyResiduals_of_engine` and the per-edge
engine composition above are unaffected. See `docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
