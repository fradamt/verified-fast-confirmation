module
public import FastConfirmation.Spec.Proof.Growth
public import FastConfirmation.Spec.Proof.Clock
public import FastConfirmation.Spec.Proof.Dominance

@[expose] public section

/-!
# Spec / Proof / Fresh Producer

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



/-- The same-epoch aggregate Byzantine budget from `es`. -/
theorem hbudget_sameEpoch_of_IH (hbb : ByzantineBound cfg E)
    (hec : ExternalsCoherence cfg ext E) {lo es σ : Slot}
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo) :
    (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold *
        (E.Jspec lo σ - E.Jspec lo es) :=
  E.hbudget_sameEpoch cfg ext hbb hec hlo hbase hσH hsame

/-! ## Complete same-epoch endpoint strip -/


end Execution

end FastConfirmation.Spec

end
