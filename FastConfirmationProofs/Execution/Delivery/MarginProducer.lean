module
public import FastConfirmationProofs.Monotonicity.Growth
public import FastConfirmationProofs.Checkpoints.SlotClock
public import FastConfirmationProofs.Handlers.Dominance
public import FastConfirmationProofs.Checkpoints.AnchorChainSafety
public import FastConfirmationProofs.FFG.Certificates.CertExtract
public import FastConfirmationProofs.Discount.FutureCrossingMargin
public import FastConfirmationProofs.Execution.StoreInvariants.CheckpointDomain
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Discount.SupportDiscount
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Handlers.HandlerStepFacts

@[expose] public section

/-!
# Execution / Delivery / MarginProducer

The fresh-voter producer and the growth package starting at the confirming
cutoff `es`.  The equality-slot voter-index argument closes the former
`es → es+1` boundary split.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Restricting an endpoint chain fact to an earlier relayed store -/

omit [Inhabited Root] in
/-- If all blocks of `source` occur in `target`, a chain segment `b ⪰ c` known
at `target` can be recovered at `source` once `source` already knows `b` and a
descendant `a ⪰ b`. The source walk starts at its actual trusted-anchor slot
`sa`; the endpoint lower bound extends that walk far enough to land `c` in
`source`. -/
theorem chain_descent_restrict (hwfE : WellFormedExecution E)
    {source target : Store Root} {a b c : Root} {sa : Slot}
    (hsource : BlockProvenance E source) (htarget : BlockProvenance E target)
    (hparent : ∀ r ∈ source.block_roots,
      (source.blocks r).parent_root ∈ source.block_roots →
        (source.blocks (source.blocks r).parent_root).slot < (source.blocks r).slot)
    (hwalkA : ∀ r ∈ source.block_roots, WalkKnown source sa r)
    (hsa_c : sa ≤ (target.blocks c).slot)
    (hsub : source.block_roots ⊆ target.block_roots)
    (ha : a ∈ source.block_roots)
    (hb : b ∈ source.block_roots)
    (hab : is_ancestor source (get_node_for_root a) (get_node_for_root b) = true)
    (hbc : is_ancestor target (get_node_for_root b) (get_node_for_root c) = true) :
    c ∈ source.block_roots ∧
      is_ancestor source (get_node_for_root a) (get_node_for_root c) = true := by
  have hagree : ∀ r ∈ source.block_roots, source.blocks r = target.blocks r :=
    fun r hr => hwfE.blocks_agree hsource htarget hr (hsub hr)
  have hwalk_b_target : WalkKnown source (target.blocks c).slot b :=
    (hwalkA b hb).mono hsa_c
  have hget_target :
      (get_ancestor target (ForkChoiceNode.mk b .pending) (target.blocks c).slot).root = c := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hbc
  have hget_source :
      (get_ancestor source (ForkChoiceNode.mk b .pending) (target.blocks c).slot).root = c := by
    rw [get_ancestor_congr hagree hb hwalk_b_target]
    exact hget_target
  have hc_source : c ∈ source.block_roots := by
    have hmem := (get_ancestor_spec hparent hwalk_b_target).1
    rw [hget_source] at hmem
    exact hmem
  have hc_agree : source.blocks c = target.blocks c := hagree c hc_source
  have hbc_source :
      is_ancestor source (get_node_for_root b) (get_node_for_root c) = true := by
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
    rw [hc_agree]
    exact hget_source
  have hwalk_a_c : WalkKnown source (source.blocks c).slot a :=
    (hwalkA a ha).mono (by rwa [hc_agree])
  have hwalk_b_c : WalkKnown source (source.blocks c).slot b := by
    rwa [hc_agree]
  exact ⟨hc_source,
    is_ancestor_trans (a := get_node_for_root a) (b := get_node_for_root b)
      (c := get_node_for_root c) hparent hwalk_a_c hwalk_b_c hab hbc_source⟩

/-! ## Fresh engine inputs from the confirming cutoff onward -/


/-! ## Growth from `es` -/



/-! ## Complete same-epoch endpoint strip -/


end Execution

end FastConfirmation.Spec

/-!
# Spec / Proof / MarginProducer

This module contains `SameEpochSelectedMarginInputs`, `epoch_eq_of_between`, `CrossingSelectedMarginInputs` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## The same-epoch producer boundary -/

/-- The residual inputs for one same-epoch selected-chain edge `a <- c`.

The confirming endpoint is `(v,n+1)` and the consuming fork-choice endpoint is
`(w,m)`.  The window geometry is explicit.  The three aggregate growth facts
are intentionally absent: `sameEpoch_descendStep_of_selectedInputs` derives
them from the shell IH through `FreshProducer`.
-/
structure SameEpochSelectedMarginInputs
    (E : Execution Root) (glc a c : Root) (v : ValidatorIndex) (n : ℕ)
    (w : ValidatorIndex) (m : ℕ) (lo es σ : Slot) : Prop where
  /-- The confirming cutoff is the slot immediately before `(v,n+1)`. -/
  confirming_cutoff : E.slot_at cfg (n + 1) = es + 1
  /-- The selecting step really advanced the execution clock. -/
  selecting_advance : E.slot_at cfg n < E.slot_at cfg (n + 1)
  /-- The edge window begins no later than the confirming cutoff. -/
  lo_le_es : lo ≤ es
  /-- The endpoint window extends the confirming window. -/
  es_le_σ : es ≤ σ
  /-- The trusted execution start is no later than the confirming cutoff. -/
  start_le_es : E.slot_at cfg 0 ≤ es
  /-- The endpoint has passed the complete vote window. -/
  σ_lt_endpoint : σ < E.slot_at cfg m
  /-- The complete contest window is contained in one epoch. -/
  same_epoch : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ
  /-- Past supporting votes transport from the confirming store to the endpoint. -/
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.SupportsDesc cfg ext v (n + 1) c es i →
      E.SupportsDesc cfg ext w m c es i
  /-- Past ancestor/voteless votes transport from the confirming store. -/
  ancestor_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.AncestorOrVoteless cfg ext v (n + 1) c es i →
      E.AncestorOrVoteless cfg ext w m c es i
  /-- The ordinary confirmation-rule margin at the confirming store. -/
  base_strip :
    E.Xval cfg ext v (n + 1) c lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext v (n + 1) c lo es
  /-- The selected child survives the endpoint filter. -/
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  /-- The required payload status wins the pending-parent contest. -/
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  /-- Every honest support-class member is recorded on the selected side. -/
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  /-- Honest recorded supporters of a competing child are confined to `Xclass`. -/
  honest_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∈ E.honest → i ∈ E.Xclass cfg ext w m c lo σ
  /-- Byzantine recorded supporters of a competing child lie in the window budget. -/
  byzantine_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∉ E.honest → i ∈ E.Bwin lo σ

omit [Inhabited Root] in
/-- Epoch equality at the endpoints makes every intermediate slot share that
epoch. -/
theorem epoch_eq_of_between {lo t σ : Slot}
    (htlo : lo ≤ t) (htσ : t ≤ σ)
    (heq : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ) :
    compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo := by
  apply le_antisymm
  · rw [heq]
    exact Nat.div_le_div_right htσ
  · exact Nat.div_le_div_right htlo


/-! ## Crossing producer boundary -/

/-- The exact re-anchored endpoint certificate still needed for a crossing
edge.  Unlike the legacy supply this is horizon-neutral data only after it has
been produced at an in-horizon endpoint; the surrounding functional below
performs that scoping.
-/
structure CrossingSelectedMarginInputs
    (E : Execution Root) (glc a c : Root) (v : ValidatorIndex) (n : ℕ)
    (w : ValidatorIndex) (m : ℕ) (lo σ : Slot)
    (oldSiblingHonest oldSiblingByzantine : ℕ) : Prop where
  child_filtered : ForkChoiceNode.mk c .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
  status_margin : PendingStatusMargin cfg (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) a
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
  selected_score : E.Sval cfg ext v (n + 1) c lo σ ≤
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  endpoint_margin : oldSiblingHonest
      + E.Xval cfg ext v (n + 1) c lo σ
      + oldSiblingByzantine + E.Bval lo σ
      + get_proposer_score cfg (E.store cfg ext w m) + 1
    ≤ E.Sval cfg ext v (n + 1) c lo σ
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c))) →
    c' ≠ c →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)
      ≤ oldSiblingHonest + E.Xval cfg ext v (n + 1) c lo σ
        + oldSiblingByzantine + E.Bval lo σ



/-! ## Horizon-scoped selected-result supply and chain lift -/



/-! ## Anchor charge without a genesis-start specialization -/


end Execution

end FastConfirmation.Spec

end
