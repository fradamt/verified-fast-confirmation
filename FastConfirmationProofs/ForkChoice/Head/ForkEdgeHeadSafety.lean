module
public import FastConfirmationProofs.Checkpoints.CheckpointMarginInputs
public import FastConfirmationProofs.FFG.SourceHistory.ConfirmationMarginInputs
public import FastConfirmationProofs.Checkpoints.CheckpointEquivalence
public import FastConfirmationProofs.Safety.ConfirmedPrefixSafety

@[expose] public section

/-!
# Spec / Proof / ShellCompose

This module contains `ForkEdgeEngineInputs` and related declarations.
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
      compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)
  /-- `hrec` domain — vote-block knownness. -/
  hbbr_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
    ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
    E.vote i t = some (kk, a) → a.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots
  /-- `hrec` domain — recorded-root walk domain. -/
  hwalk_wm : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ lm,
    (E.store cfg ext w m).latest_messages i = some lm →
    WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root
  /-- `hchild` — the fork-choice child membership of `c` under `h`. -/
  hchild : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk h
          (get_parent_payload_status (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks c)))
  /-- `hstatus` — the pending-parent status contest selects the status of `c`. -/
  hstatus : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) h
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  /-- `hHon` — honest supporters of any sibling are confined to `Xclass` (carried). -/
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
  /-- `hByz` — byz supporters of any sibling are confined to `BbadSet ∪ SpentSet` (carried). -/
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

/-! ## Section 4 — the engine-reduced safety headline -/


end FastConfirmation.Spec

end
