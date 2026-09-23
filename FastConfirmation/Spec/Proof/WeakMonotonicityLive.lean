module
public import FastConfirmation.Spec.Proof.WeakSelectorBetween
public import FastConfirmation.Spec.Proof.WeakDutyFreshness
public import FastConfirmation.Spec.Proof.WeakObservedResetSeedSafety
public import FastConfirmation.Spec.TheoremStatements

@[expose] public section

/-!
# Weak live monotonicity helpers

These facts isolate the parts of the strong live proof that carry over to
the weak selector and its support discount.
-/

namespace FastConfirmation.Spec.Weak

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The accepted FFG, observer, and call-contract premises of the weak
trajectory safety witness, collected without adding a liveness field. -/
def AcceptedWeakObserverLivePremises (E : Execution Root)
    (v : ValidatorIndex) : Prop :=
  ∃ B : ExactPrefixAcceptedFFGSemantics cfg ext E,
    JustificationInterface cfg ext E ∧
    B.anchor = E.genesis_store.justified_checkpoint ∧
    E.TrustedAnchorBoundaryAligned (cfg := cfg) (anchor := B.anchor) ∧
    E.AcceptedRealizedFinalizationDelay cfg ext B ∧
    B.state.PaperA32Inclusion cfg ext ∧
    (∃ P : AcceptedEpochCheckpointProjection B.anchor
        (E.AcceptedRoot cfg ext) B.state.C,
      B.state.ExactLinkValidity ∧
      E.WeakObserverAssumptions cfg ext v ∧
      E.AcceptedHistoricalA32CompletedPrefixCallSupplement cfg ext ∧
      EpochEndsFitUint64 cfg)

/-- The concrete weak accepted-observer specialization of the upstream
statement. Its accepted premises match the weak full-rule safety witness. -/
def AcceptedWeakSpec_Monotonicity_live : Prop :=
  WeakSpec_Monotonicity_live cfg ext
    (AcceptedWeakObserverLivePremises cfg ext)

/-- Consecutive parent and child slots make the weak empty-slot discount
zero, even with the duty-fresh and PENDING parent support rules. -/
theorem support_discount_zero_of_consecutive (store : Store Root)
    (source : BeaconState Root) (b : Root)
    (hparent : (store.blocks (store.blocks b).parent_root).slot + 1 =
      (store.blocks b).slot) :
    Weak.get_support_discount cfg ext store source b = 0 := by
  simp [Weak.get_support_discount, Weak.compute_empty_slot_support_discount,
    hparent]

/-- The weak selector preserves its input as an ancestor of its result.
Certificate guards may stop advancement, but do not reverse the walk. -/
theorem find_latest_confirmed_descendant_ge
    (fcr : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr.store.block_roots,
      (fcr.store.blocks r).parent_root ∈ fcr.store.block_roots →
        (fcr.store.blocks (fcr.store.blocks r).parent_root).slot <
          (fcr.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr.store.block_roots, ∀ r ∈ fcr.store.block_roots,
      WalkKnown fcr.store (fcr.store.blocks t).slot r)
    (hhead : (get_head cfg fcr.store).root ∈ fcr.store.block_roots)
    (input : Root) (hinput : input ∈ fcr.store.block_roots) :
    is_ancestor fcr.store
      (get_node_for_root (Weak.find_latest_confirmed_descendant cfg ext fcr input))
      (get_node_for_root input) = true :=
  (Weak.find_latest_confirmed_descendant_between cfg ext fcr hwf hwalk hhead
    input hinput).1

/-- Weak epoch-start chain safety reduces to a weak one-confirmation
certificate for each strict descendant of the observed checkpoint. -/
theorem is_confirmed_chain_safe_of_checkpoint_certificates
    (query : FastConfirmationStore Root) (c : Root)
    (hcheckpoint : query.current_epoch_observed_justified_checkpoint =
      get_checkpoint_for_block cfg query.store c
        query.current_epoch_observed_justified_checkpoint.epoch)
    (hepoch : query.current_epoch_observed_justified_checkpoint.epoch + 1 ≥
      get_current_store_epoch cfg query.store)
    (hcert : ∀ b ∈ get_ancestor_roots query.store c
        query.current_epoch_observed_justified_checkpoint.root,
      Weak.is_one_confirmed cfg ext query.store
        (get_previous_balance_source query) b = true) :
    Weak.is_confirmed_chain_safe cfg ext query c = true := by
  have hall : (get_ancestor_roots query.store c
      query.current_epoch_observed_justified_checkpoint.root).all
      (fun b => Weak.is_one_confirmed cfg ext query.store
        (get_previous_balance_source query) b) = true :=
    List.all_eq_true.mpr hcert
  simp only [Weak.is_confirmed_chain_safe]
  rw [if_neg (by intro hne; exact hne hcheckpoint)]
  rw [if_pos hepoch]
  exact hall

/-- When the cached root is the observed checkpoint, the strict chain is
empty and the weak boundary check succeeds. -/
theorem is_confirmed_chain_safe_at_observed_checkpoint
    (query : FastConfirmationStore Root)
    (hcheckpoint : query.current_epoch_observed_justified_checkpoint =
      get_checkpoint_for_block cfg query.store
        query.current_epoch_observed_justified_checkpoint.root
        query.current_epoch_observed_justified_checkpoint.epoch)
    (hepoch : query.current_epoch_observed_justified_checkpoint.epoch + 1 ≥
      get_current_store_epoch cfg query.store) :
    Weak.is_confirmed_chain_safe cfg ext query
      query.current_epoch_observed_justified_checkpoint.root = true := by
  apply is_confirmed_chain_safe_of_checkpoint_certificates cfg ext query _
    hcheckpoint hepoch
  intro b hb
  have hnil := get_ancestor_roots_stop (store := query.store)
    (block_root := query.current_epoch_observed_justified_checkpoint.root)
    (terminal_root := query.current_epoch_observed_justified_checkpoint.root) (le_refl _)
  rw [hnil] at hb
  cases hb

/-- Honest span growth preserves a strict weak margin when old support does
not disappear. The weak budget has no equivocation credit, so the conclusion
needs the score growth without a loss term. -/
private theorem margin_growth_without_support_loss
    (window boost adversarial score added honestAdded adversarialNew : ℕ)
    (hold : window + boost + 2 * adversarial < 2 * score)
    (hbudget : 4 * adversarialNew ≤ 4 * adversarial + added)
    (hhonest : 3 * added ≤ 4 * honestAdded) :
    window + added + boost + 2 * adversarialNew <
      2 * (score + honestAdded) := by
  omega

/-- The bare strong-rule loss argument is false for the weak budget: one
lost supporter can consume the entire strict margin with no new slot. This
is only an arithmetic witness, not an accepted execution. -/
private theorem support_loss_can_destroy_weak_margin :
    ∃ window boost adversarial oldScore newScore lost : ℕ,
      oldScore = newScore + lost ∧
      window + boost + 2 * adversarial < 2 * oldScore ∧
      ¬ (window + boost + 2 * adversarial < 2 * newScore) := by
  refine ⟨100, 0, 25, 76, 75, 1, rfl, ?_, ?_⟩ <;> decide

end FastConfirmation.Spec.Weak

end
