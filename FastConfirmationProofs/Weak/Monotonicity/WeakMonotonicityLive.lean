module
public import FastConfirmationProofs.Weak.Selection.WeakSelectorBetween
public import FastConfirmationProofs.Weak.Discount.WeakDutyFreshness
public import FastConfirmationProofs.Weak.Safety.WeakObservedResetSeedSafety
public import FastConfirmationProofs.Safety.NextSlotSafety
public import FastConfirmationProofs.Execution.History.CausalQueryTraceAdapter
public import FastConfirmationStatements.Weak.LiveMonotonicity

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

/-- The weak safety floor contains the strong accepted trajectory fields.
The strong record's additional epoch-length condition is explicit here. -/
theorem accepted_weak_observer_to_strong_bundle
    {E : Execution Root} {v : ValidatorIndex}
    (hW : AcceptedWeakObserverLivePremises cfg ext E v)
    (hslots : 1 < cfg.slots_per_epoch) :
    Nonempty (E.AcceptedActualFCRNextSlotSafetyAssumptions cfg ext) := by
  rcases hW with ⟨B, _hji, hanchor, hboundary, hDelay, hpaper,
    P, V, hObs, hCbase, hfit⟩
  let hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext :=
    Execution.ScheduledPrefixTrajectoryAssumptions.of_selectedMarginAssumptions
      cfg ext E hObs.base hObs.genesis
  let hC := Execution.AcceptedHistoricalA32CompletedPrefixCallSupplement.toCompletedPrefixCallAssumptions
    cfg ext E hCbase hObs.base
  exact ⟨{
    semantics := B
    trajectory := hT
    completed_calls := hC
    epoch_ends_fit := hfit
    anchor_eq := hanchor
    anchor_boundary := hboundary
    finalization_delay := hDelay
    slots_per_epoch_gt_one := hslots
    paper_a32 := hpaper
    checkpoint_projection := P
    exact_link_validity := V
  }⟩

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

/-- With no recorded equivocation, the weak and strong adversarial budgets
are equal on every slot span. -/
theorem adversarial_weight_eq_of_no_equivocations
    (store : Store Root) (source : BeaconState Root) (a b : Slot)
    (hno : store.equivocating_indices = ∅) :
    Weak.compute_adversarial_weight cfg store source a b =
      FastConfirmation.Spec.compute_adversarial_weight cfg ext store source a b := by
  simp only [Weak.compute_adversarial_weight,
    FastConfirmation.Spec.compute_adversarial_weight,
    FastConfirmation.Spec.get_equivocation_score, hno, Finset.inter_empty,
    Finset.filter_empty, Finset.sum_empty, Nat.sub_zero]
  by_cases hpos : 0 < estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg source) a b / 100 *
        cfg.confirmation_byzantine_threshold
  · simp [hpos]
  · have hz := Nat.eq_zero_of_not_pos hpos
    simp [hz]

/-- If every recorded supporter of this node passes the duty filter, the
weak and strong LMD scores agree. Unrelated old cells need not be fresh. -/
theorem attestation_score_eq_of_supporters_fresh
    (store : Store Root) (source : BeaconState Root)
    (node : ForkChoiceNode Root)
    (hfresh : ∀ i lm, store.latest_messages i = some lm →
      is_ancestor store (get_supported_node store lm) node = true →
      Weak.is_duty_fresh_message cfg ext store i lm = true) :
    Weak.get_duty_fresh_attestation_score cfg ext store node source =
      FastConfirmation.Spec.get_attestation_score cfg store node source := by
  simp only [Weak.get_duty_fresh_attestation_score,
    FastConfirmation.Spec.get_attestation_score]
  congr 1
  congr 1
  apply List.filter_congr
  intro i hi
  cases hmsg : store.latest_messages i with
  | none => simp [hmsg]
  | some lm =>
      by_cases ha : is_ancestor store (get_supported_node store lm) node = true
      · simp [hmsg, ha, hfresh i lm hmsg ha]
      · have haf : is_ancestor store (get_supported_node store lm) node = false := by
          cases h : is_ancestor store (get_supported_node store lm) node with
          | false => rfl
          | true => exact False.elim (ha h)
        simp [hmsg, haf]

/-- At a consecutive child, zero equivocation and duty freshness make the
weak and strong one-block checks agree. This is the conversion needed after
the strong numerical reconfirmation core. -/
theorem one_confirmed_of_strong_of_no_equiv_supporters_fresh_consecutive
    (store : Store Root) (source : BeaconState Root) (b : Root)
    (hno : store.equivocating_indices = ∅)
    (hfresh : ∀ i lm, store.latest_messages i = some lm →
      is_ancestor store (get_supported_node store lm) (get_node_for_root b) = true →
      Weak.is_duty_fresh_message cfg ext store i lm = true)
    (hparent : (store.blocks (store.blocks b).parent_root).slot + 1 =
      (store.blocks b).slot)
    (hstrong : FastConfirmation.Spec.is_one_confirmed cfg ext store source b = true) :
    Weak.is_one_confirmed cfg ext store source b = true := by
  have hscore := attestation_score_eq_of_supporters_fresh cfg ext store source
    (get_node_for_root b) hfresh
  have hadv : Weak.get_adversarial_weight cfg store source b =
      FastConfirmation.Spec.get_adversarial_weight cfg ext store source b := by
    unfold Weak.get_adversarial_weight FastConfirmation.Spec.get_adversarial_weight
    dsimp only
    split_ifs <;> exact adversarial_weight_eq_of_no_equivocations cfg ext
      store source _ _ hno
  have hweakDiscount : Weak.get_support_discount cfg ext store source b = 0 :=
    support_discount_zero_of_consecutive cfg ext store source b hparent
  have hstrongDiscount : FastConfirmation.Spec.get_support_discount cfg ext
      store source b = 0 := by
    simp [FastConfirmation.Spec.get_support_discount,
      FastConfirmation.Spec.compute_empty_slot_support_discount, hparent]
  have hthreshold : Weak.compute_safety_threshold cfg ext store b source =
      FastConfirmation.Spec.compute_safety_threshold cfg ext store b source := by
    simp only [Weak.compute_safety_threshold,
      FastConfirmation.Spec.compute_safety_threshold, hweakDiscount,
      hstrongDiscount, hadv]
  simpa only [Weak.is_one_confirmed, FastConfirmation.Spec.is_one_confirmed,
    hscore, hthreshold] using hstrong

/-- A recorded supporter cannot cast its vote before the block it
supports. This is the slot geometry needed to apply boundary freshness. -/
theorem supporter_vote_slot_ge_block
    (store : Store Root) (b : Root) (lm : LatestMessage Root)
    (hwf : ParentSlotLt store)
    (hwalk : WalkKnown store (store.blocks b).slot lm.root)
    (hanc : is_ancestor store (get_supported_node store lm)
      (get_node_for_root b) = true)
    (hmsgSlot : (store.blocks lm.root).slot ≤ lm.slot) :
    (store.blocks b).slot ≤ lm.slot := by
  have hancPending : is_ancestor store (get_node_for_root lm.root)
      (get_node_for_root b) = true := by
    simpa only [get_node_for_root, is_ancestor_supported_pending] using hanc
  have hroot : (get_ancestor store (get_node_for_root lm.root)
      (store.blocks b).slot).root = b := by
    simpa only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] using hancPending
  have hslot := get_ancestor_slot_le hwf hwalk
  change (store.blocks (get_ancestor store (get_node_for_root lm.root)
    (store.blocks b).slot).root).slot ≤ (store.blocks lm.root).slot at hslot
  rw [hroot] at hslot
  exact hslot.trans hmsgSlot

/-- Every recorded supporter of a block in the completed epoch is
duty-fresh at its boundary, provided the vote was cast before that boundary. -/
theorem boundary_supporter_is_duty_fresh
    (store : Store Root) (e : Epoch) (b : Root)
    (lm : LatestMessage Root) (i : ValidatorIndex)
    (hslot : get_current_slot cfg store =
      compute_start_slot_at_epoch cfg (e + 1))
    (hbstart : compute_start_slot_at_epoch cfg e ≤ (store.blocks b).slot)
    (hwf : ParentSlotLt store)
    (hwalk : WalkKnown store (store.blocks b).slot lm.root)
    (hanc : is_ancestor store (get_supported_node store lm)
      (get_node_for_root b) = true)
    (hmsgBlock : (store.blocks lm.root).slot ≤ lm.slot)
    (hmsgPast : lm.slot < get_current_slot cfg store) :
    Weak.is_duty_fresh_message cfg ext store i lm = true := by
  have hlow : compute_start_slot_at_epoch cfg e ≤ lm.slot :=
    hbstart.trans (supporter_vote_slot_ge_block store b lm
      hwf hwalk hanc hmsgBlock)
  exact duty_fresh_vote_slot_at_boundary cfg ext e hslot hlow
    (hslot ▸ hmsgPast)

end FastConfirmation.Spec.Weak

end
