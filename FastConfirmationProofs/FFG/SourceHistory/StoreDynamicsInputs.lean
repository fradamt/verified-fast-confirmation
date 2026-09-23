module
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant
public import FastConfirmationProofs.Discount.ByzantineBudgetLedger

@[expose] public section

/-!
# Spec / Proof / ResidualDischarge

This module contains `DynamicsResidual` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)












/-- **The per-edge dynamics residual.** For one fork `(h, c)` at the honest
endpoint `(w, m)`, the `ledgerCertInput_of_endpoint` hypotheses, existentially
quantified over the certificate `(vc, nc, b', lo, es, σ, boost)`: the base honest
transports `hSt`/`hAt`, recorded enemy movement `hBb`, base `hbase`, the per-slot
step `hpre`, saturation `hsat`, and the
endpoint data `hval`/`hboost`/`hchild` + recorded-support bridges
`hSmem`/`hHon`/`hByz`. -/
def DynamicsResidual (w : ValidatorIndex) (m : ℕ) (h c : Root) : Prop :=
  ∃ (vc : ValidatorIndex) (nc : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ),
    es ≤ σ ∧
    E.SlotWithinHorizon cfg lo ∧
    E.SlotWithinHorizon cfg σ ∧
    (∀ i, E.SupportsDesc cfg ext vc nc b' es i → E.SupportsDesc cfg ext w m b' es i) ∧
    (∀ i, E.AncestorOrVoteless cfg ext vc nc b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i) ∧
    E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext vc nc b' lo es ∧
    E.INV2 cfg ext vc nc b' lo es es boost ∧
    (∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.INV2 cfg ext w m b' lo es σ' boost → E.INV2 cfg ext w m b' lo es (σ' + 1) boost) ∧
    (∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b' lo σ' + E.Enemy cfg ext w m b' lo es σ' + boost + 1
        ≤ E.Sval cfg ext w m b' lo σ') ∧
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry ∧
    boost = get_proposer_score cfg (E.store cfg ext w m) ∧
    ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))) ∧
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) ∧
    (∀ i ∈ E.Sclass cfg ext w m b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint)) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext w m b' lo σ) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b' lo es ∨ i ∈ E.SpentSet es σ)





end Execution


end FastConfirmation.Spec

end
