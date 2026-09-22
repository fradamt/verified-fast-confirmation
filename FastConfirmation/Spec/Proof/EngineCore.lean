module
public import FastConfirmation.Spec.Proof.Closing
public import FastConfirmation.Spec.Proof.INVstarTrack
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Spec / Proof / EngineCore: the `hadv_hi` geometric core and per-edge assembly

`Closing.EngineAdvanceCore` reduces the
public `Spec_Safety` to four localized per-confirmed-block fields, of which two are the substantive
engine content: `hcov`'s strict-epoch advance sub-case `hadv_hi`, and the chain-branch engine
`heng`. This module attacks both.

## Section 1 — `hadv_hi` (the geometric core)

`Structural.disjunction_of_covering` localizes the `jc ⪰ b ∨ b ⪰ jc` disjunction's open content to
exactly the strict sub-case `hadv_hi`: when the store's justified checkpoint `jc(w,m)` sits at a
**strictly higher** epoch than `b`'s covering justified checkpoint `jcb` (`jcb.epoch < jc.epoch`),
the advance side `jc ⪰ b` must hold — `jc` advanced *along* `b`'s chain.

`hadv_hi_of_head` mechanizes the **geometry** of that advance, reducing `hadv_hi` to the head-safety
inputs the shell IH supplies. The intended source of those inputs is that `jc(w,m)` is
justified above `jcb`, so (`justified_requires_targets`) two-thirds of its epoch's committee named
`jc` as their attestation target; an honest such voter's head — under the shell's safety IH at that
earlier slot — descended from `b` (`head ⪰ b`), and its target root `jc.root` is that head's
epoch-boundary block (`Delivery.honest_attestation_data_target_root`, the `get_checkpoint_block` on
the head chain). So there is a known head `H` at the endpoint with `H ⪰ b` and
`get_checkpoint_block H jc.epoch = jc.root`; and because `b` sits at or below the epoch boundary
(`b.slot ≤ compute_start_slot_at_epoch jc.epoch`, `b` in `jcb`'s epoch, strictly below `jc`'s), the
boundary block `jc.root` is at or above `b` on `H`'s chain — i.e. `jc.root ⪰ b` (`jc ⪰ b`).

The geometry is `AncestryRoots.get_ancestor_comp`: `get_ancestor (get_ancestor H boundary) b.slot =
get_ancestor H b.slot`, i.e. walking to `b.slot` through the boundary block gives the same node as
walking directly, so `b` (= `get_ancestor H b.slot`) is an ancestor of `jc.root`
(= `get_ancestor H boundary`). The three inputs `H`/`hckpt`/`hbslot` express honest-voter
extraction, cross-store head transport, and the epoch bound.

## Section 2 — the per-edge `ForkEdgeGroundInputs` assembly scaffold (`heng` part 1)

`heng` runs `INVstarTrack.spec_head_safety_engine_ground`, whose per-block supply
`ForkEdgeGroundSupply` presents, per real parent edge `a ← c` of known blocks at the endpoint
`(w, m)`, a `ForkEdgeGroundInputs` carrying the `INVstar` certificate at the confirming anchor over
`[lo, σ]`. `invstar_sigma_of_deltas` threads the **maintenance** leg coordinate-by-coordinate: from
the base `INVstar(es)` and a per-slot class-delta supplier it iterates `Ledger.INVstar_step` to any
window end `σ ≥ es` (via `INVstarTrack.INVstar_maintained`); `forkEdgeGroundInputs_of` bundles the
maintained `INVstar` with the honest transports and endpoint fork data into the per-edge structure,
aligning the boost coordinate to `get_proposer_score cfg (E.store cfg ext w m)` as the
per-edge structure requires. The base producer (`Identities.INV2_base_bridged_instantiated` +
`LastAlgebra.vpreIdentities_of` + `Cruxes.hPS_crux`, bridged to `INVstar`), the delta producers
(`StepDischargeII`/`Remainder`), and the far-`σ` saturation handoff
(`Cruxes.hsat_crux`/`hcov_crux` via `LastAlgebra.saturated_majority_of_crux`) provide the remaining
inputs.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hadv_hi`: the advance side from an honest head descending from `b` -/

/-- **`hadv_hi` geometric core.** At an honest endpoint `(w, m)`, if there is a known
block `H` whose chain descends from `b` (`hHb`, the shell IH's `head ⪰ b` at the honest voter's
head, transported to `(w, m)`) and whose epoch-boundary block for the store's justified epoch is the
store's justified root (`hckpt`, `get_checkpoint_block H jc.epoch = jc.root` — the honest voter's
target root is `jc`, `Delivery.honest_attestation_data_target_root`), and `b` sits at or below that
epoch boundary (`hbslot`), then the store's justified checkpoint descends from `b`: `jc ⪰ b`, the
advance side of `Structural.disjunction_of_covering`.

The domain conditions (`ParentSlotLt`, the target-known walk `WalkKnown S (blocks b).slot H`) are
Layer-0 discharged (`AnchorFacade.store_domainK`). The geometry is one `get_ancestor_comp` step:
`b = get_ancestor H (blocks b).slot = get_ancestor (get_ancestor H boundary) (blocks b).slot =
get_ancestor jc.root (blocks b).slot`, so `is_ancestor jc.root b`. -/
theorem hadv_hi_of_head (hSA : SpecAssumptions cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) {b H : Root}
    (hHm : E.WithinHorizon cfg m)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hH : H ∈ (E.store cfg ext w m).block_roots)
    (hHb : is_ancestor (E.store cfg ext w m)
      (get_node_for_root H) (get_node_for_root b) = true)
    (hckpt : get_checkpoint_block cfg (E.store cfg ext w m) H
        (E.store cfg ext w m).justified_checkpoint.epoch =
      (E.store cfg ext w m).justified_checkpoint.root)
    (hbslot : ((E.store cfg ext w m).blocks b).slot ≤
      compute_start_slot_at_epoch cfg (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root b) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨hwf, hwalkK, _hjust⟩ := E.store_domainK cfg ext hwfE hec hgen hji w hw m hHm
  set S := E.store cfg ext w m with hSdef
  -- unfold the two `is_ancestor` booleans to the `get_ancestor` equalities
  simp only [is_ancestor, get_node_for_root, decide_eq_true_eq] at hHb ⊢
  -- zeta-reduce `get_checkpoint_block`'s `let`s: `(get_ancestor S (mk H) boundary).root = jc.root`
  simp only [get_checkpoint_block] at hckpt
  -- structure eta: the boundary node IS `mk jc.root`
  have eta : get_ancestor S (ForkChoiceNode.mk H)
      (compute_start_slot_at_epoch cfg S.justified_checkpoint.epoch)
      = ForkChoiceNode.mk S.justified_checkpoint.root := by rw [← hckpt]
  -- the composition step: walk to `b.slot` through the boundary block
  have key := get_ancestor_comp (store := S) hwf hbslot (hwalkK b hb H hH)
  rw [eta, hHb] at key
  exact key

/-! ## Section 2 — the per-edge `ForkEdgeGroundInputs` producer (`heng` part 1) -/

/-- **`INVstar` maintained from the base and a per-slot delta supplier.** From the base
`INVstar(es)` at the confirming anchor and a supplier that, at every window end
`σ ≥ es`, exhibits the per-slot class deltas `ξ`/`α`/`φ`/`β`/`σt` (the `x→s`/`a→s`/fresh honest
migrants, the new byz, and the base-supporter recurrers leaving `Unrec`) satisfying the six
`Ledger.INVstar_step` relations from `σ` to `σ + 1`, `INVstar(σ)` holds for every `σ ≥ es`.
Threads `INVstarTrack.INVstar_maintained` over `Ledger.INVstar_step`: the enemy leg is the
store-independent `Bval` (monotone), so the step needs no arrival/relay accounting — only the honest
class deltas and the per-slot `span_fraction` funding `hF3`. The delta supplier follows from
`StepDischargeII`/`Remainder` (votes-land + IH +
`committee_assignment_unique`); here it enters as the shell-shaped hypothesis. -/
theorem invstar_sigma_of_deltas (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hbase : E.INVstar cfg ext v₀ n₀ b' lo es es boost)
    (hdelta : ∀ σ : Slot, es ≤ σ →
      ∃ ξ α φ β σt : ℕ,
        E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α + φ ≤ E.Sval cfg ext v₀ n₀ b' lo (σ + 1) ∧
        E.Xval cfg ext v₀ n₀ b' lo (σ + 1) + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ ∧
        E.Bval lo (σ + 1) ≤ E.Bval lo σ + β ∧
        E.Jspec lo (σ + 1) = E.Jspec lo σ + φ ∧
        E.Uval cfg ext v₀ n₀ b' lo es (σ + 1) + σt ≤ E.Uval cfg ext v₀ n₀ b' lo es σ ∧
        (100 - cfg.confirmation_byzantine_threshold) * β ≤
          cfg.confirmation_byzantine_threshold * (σt + ξ + α + φ)) :
    ∀ σ : Slot, es ≤ σ → E.SlotWithinHorizon cfg σ →
      E.INVstar cfg ext v₀ n₀ b' lo es σ boost := by
  intro σ hσ hσH
  induction σ, hσ using Nat.le_induction with
  | base => exact hbase
  | succ σ hσ ih =>
    obtain ⟨ξ, α, φ, β, σt, hs', hx', hB', hJ', hUσt, hF3⟩ := hdelta σ hσ
    have hσH' : E.SlotWithinHorizon cfg σ :=
      E.slotWithinHorizon_mono cfg (Nat.le_succ σ) hσH
    exact E.INVstar_step cfg ext hbb v₀ n₀ b' lo es hloH hσH' hσH
      boost ξ α φ β σt hs' hx' hB' hJ' hUσt hF3 (ih hσH')

/-- **The per-edge `ForkEdgeGroundInputs` producer, maintenance threaded.** Assembles
the per-edge ground bundle at the endpoint `(w, m)` for the confirmed edge `h ← c`, over the
certificate window `[lo, σ]` at the confirming anchor `(vc, nc)`. The `INVstar` certificate `hinv`
is produced by `invstar_sigma_of_deltas` — the base `INVstar(es)` lifted to the window end `σ` —
with the boost coordinate aligned to `get_proposer_score cfg (E.store cfg ext w m)` exactly as
`ForkEdgeGroundInputs` requires; the honest descent transports `hSt`/`hAt`, the filtered child
`hchild`, the `b`-side lower bound `hbside` and the `Bval` sibling upper bound `hsib` enter in their
delivered shapes. The base `INVstar(es)` (`Identities.INV2_base_bridged_instantiated` +
`LastAlgebra.vpreIdentities_of` + `Cruxes.hPS_crux`, bridged to `INVstar`), the delta supplier
(`StepDischargeII`/`Remainder`), and the far-`σ` saturation handoff provide the remaining inputs. -/
theorem forkEdgeGroundInputs_of_base (hbb : ByzantineBound cfg E)
    {w : ValidatorIndex} {m : ℕ} {b h c : Root} {vc : ValidatorIndex} {nc : ℕ} {lo es σ : Slot}
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ)
    (hσ : es ≤ σ)
    (hSt : ∀ i, E.SupportsDesc cfg ext vc nc b σ i → E.SupportsDesc cfg ext w m b σ i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext vc nc b σ i →
      E.AncestorOrVoteless cfg ext w m b σ i)
    (hbase : E.INVstar cfg ext vc nc b lo es es
      (get_proposer_score cfg (E.store cfg ext w m)))
    (hdelta : ∀ σ' : Slot, es ≤ σ' →
      ∃ ξ α φ β σt : ℕ,
        E.Sval cfg ext vc nc b lo σ' + ξ + α + φ ≤ E.Sval cfg ext vc nc b lo (σ' + 1) ∧
        E.Xval cfg ext vc nc b lo (σ' + 1) + ξ ≤ E.Xval cfg ext vc nc b lo σ' ∧
        E.Bval lo (σ' + 1) ≤ E.Bval lo σ' + β ∧
        E.Jspec lo (σ' + 1) = E.Jspec lo σ' + φ ∧
        E.Uval cfg ext vc nc b lo es (σ' + 1) + σt ≤ E.Uval cfg ext vc nc b lo es σ' ∧
        (100 - cfg.confirmation_byzantine_threshold) * β ≤
          cfg.confirmation_byzantine_threshold * (σt + ξ + α + φ))
    (hchild : ForkChoiceNode.mk c ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h))
    (hbside : E.Sval cfg ext w m b lo σ ≤ get_attestation_score cfg (E.store cfg ext w m)
      (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint))
    (hsib : ∀ c' : Root, ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
      c' ≠ c →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint)
        ≤ E.Xval cfg ext w m b lo σ + E.Bval lo σ) :
    E.ForkEdgeGroundInputs cfg ext w m b h c vc nc lo es σ :=
  { hSt := hSt
    hAt := hAt
    hinv := E.invstar_sigma_of_deltas cfg ext hbb vc nc b lo es
      (get_proposer_score cfg (E.store cfg ext w m)) hloH hbase hdelta σ hσ hσH
    hchild := hchild
    hbside := hbside
    hsib := hsib }

end Execution

end FastConfirmation.Spec

end
