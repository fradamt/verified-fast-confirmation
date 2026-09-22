module
public import FastConfirmation.Spec.Proof.WeakFreshSupport
public import FastConfirmation.Spec.Proof.HonestWeight
public import FastConfirmation.Spec.Proof.Preservation

@[expose] public section

/-!
# Spec / Proof / WeakQuorumAccounting

Margin-discharge wave, Stage G-c: the weak quorum arithmetic over the fresh
support sets of `WeakFreshSupport.lean` — verbatim `Quorum.lean` /
`QuorumAccounting.lean` Steps 1/3/4 restated over `Weak.is_one_confirmed`,
`Weak.get_duty_fresh_attestation_score`, `Weak.get_adversarial_weight`.

Step 3 (`fresh_byz_score_le_adversarial_weight`) is simpler than its strong
counterpart `HonestWeight.byz_score_le_adversarial_weight`: `Weak.
compute_adversarial_weight` has no equivocation subtraction (rule delta 1), so
there is no guard arithmetic to thread through — the fresh Byzantine
supporters' weight is bounded by the raw span estimate directly
(`ByzantineBound.span_bound`), and that raw estimate **is**
`Weak.compute_adversarial_weight`/`Weak.get_adversarial_weight`
(`compute_adversarial_weight_eq`, `rfl`). Consequently no `hne` (no honest
equivocator), no `HonestBehavior`/`ExternalsCoherence`/genesis hypotheses are
needed here at all.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Step 1 — the threshold arithmetic (`Quorum.is_one_confirmed_ineq`, weak twin) -/

/-- Pure form of the threshold inequality: `s > ⌊(X − d)/2⌋` (guarded) gives
`2s + d ≥ X + 1` in both guard branches. Restated locally: `Quorum.
threshold_arith` is `private`. -/
private theorem threshold_arith {s d X : ℕ}
    (h : s > if d < X then (X - d) / 2 else 0) : 2 * s + d ≥ X + 1 := by
  split_ifs at h <;> omega

/-- `Weak.is_one_confirmed`, resolved to a branch-free inequality: twice the
fresh support plus the fresh discount strictly exceeds the maximum-support +
boost + twice-adversarial budget. Verbatim `Quorum.is_one_confirmed_ineq`
proof over the weak scorer/discount/threshold. -/
theorem is_one_confirmed_ineq {store : Store Root} {bs : BeaconState Root}
    {b : Root} (h : Weak.is_one_confirmed cfg ext store bs b = true) :
    2 * Weak.get_duty_fresh_attestation_score cfg ext store (get_node_for_root b) bs
        + Weak.get_support_discount cfg ext store bs b
      ≥ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1)
        + compute_proposer_score cfg bs
        + 2 * Weak.get_adversarial_weight cfg store bs b + 1 := by
  have h' : Weak.get_duty_fresh_attestation_score cfg ext store (get_node_for_root b) bs >
      Weak.compute_safety_threshold cfg ext store b bs := by
    simpa [Weak.is_one_confirmed] using h
  have heq : Weak.compute_safety_threshold cfg ext store b bs =
      if Weak.get_support_discount cfg ext store bs b <
          estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b).parent_root).slot + 1)
            (get_current_slot cfg store - 1)
          + compute_proposer_score cfg bs
          + 2 * Weak.get_adversarial_weight cfg store bs b then
        (estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b).parent_root).slot + 1)
            (get_current_slot cfg store - 1)
          + compute_proposer_score cfg bs
          + 2 * Weak.get_adversarial_weight cfg store bs b
          - Weak.get_support_discount cfg ext store bs b) / 2
      else 0 := rfl
  rw [heq] at h'
  exact threshold_arith h'

/-! ## `get_adversarial_weight_eq` / `compute_adversarial_weight_eq` -/

omit [LinearOrder Root] [Inhabited Root] in
/-- `Weak.get_adversarial_weight` unfolded to its span. -/
theorem get_adversarial_weight_eq {store : Store Root} {bs : BeaconState Root} {b : Root} :
    Weak.get_adversarial_weight cfg store bs b =
      Weak.compute_adversarial_weight cfg store bs
        (if get_block_epoch cfg store b >
            get_block_epoch cfg store (store.blocks b).parent_root then
          compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
        else (store.blocks b).slot)
        (get_current_slot cfg store - 1) := by
  simp only [Weak.get_adversarial_weight]
  split_ifs <;> rfl

omit [LinearOrder Root] [Inhabited Root] in
/-- **The weak budget IS the raw estimate — the guard disappears.** -/
theorem compute_adversarial_weight_eq (store : Store Root) (bs : BeaconState Root)
    (a b : Slot) :
    Weak.compute_adversarial_weight cfg store bs a b =
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) a b / 100
        * cfg.confirmation_byzantine_threshold := rfl

/-! ## Step 3 — the fresh Byzantine budget, no equivocation term -/

private theorem fresh_byzantine_weight_le {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {sa es : Slot}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hsaH : E.SlotWithinHorizon cfg sa) (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa es
        / 100 * cfg.confirmation_byzantine_threshold := by
  set L := (Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
    (fun i => i ∉ E.honest) with hL
  have hLnodup : L.Nodup := (Weak.FreshAttSupporters_nodup cfg ext store _ bs).filter _
  have hmap : L.map (fun i => (bs.validators.getD i default).effective_balance)
      = L.map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  have hsub : L.toFinset ⊆ (E.span_committee sa es).filter (fun i => i ∉ E.honest) := by
    intro i hi
    rw [List.mem_toFinset, hL, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  rw [htab]
  calc (L.map (fun i => (bs.validators.getD i default).effective_balance)).sum
      = ∑ i ∈ L.toFinset, E.weight_of i := by
        rw [hmap]; exact (List.sum_toFinset E.weight_of hLnodup).symm
    _ ≤ ∑ i ∈ (E.span_committee sa es).filter (fun i => i ∉ E.honest), E.weight_of i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = E.weight ((E.span_committee sa es).filter (fun i => i ∉ E.honest)) := rfl
    _ ≤ estimate_committee_weight_between_slots cfg (E.total_active cfg) sa es / 100 *
          cfg.confirmation_byzantine_threshold := hbb.span_bound sa es hsaH hesH

/-- **Weak Step 3: no `hne`, no `byz_le_adv_arith`, no `hcomm`.** The fresh
Byzantine supporters' weight is within `Weak.get_adversarial_weight` directly:
`FreshAttSupporters` sublists into `AttSupporters`
(`mem_AttSupporters_of_mem_fresh`), so `supporter_mem_span_committee` confines
them to the span, and the weak budget *is* the raw span estimate
(`compute_adversarial_weight_eq`). -/
theorem fresh_byz_score_le_adversarial_weight {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root} (hwf : ParentSlotLt store) {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hbH : E.SlotWithinHorizon cfg (store.blocks b).slot)
    (hcurH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hwalk : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs, ∀ lm,
      store.latest_messages i = some lm → WalkKnown store (store.blocks b).slot lm.root) :
    (((Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ Weak.get_adversarial_weight cfg store bs b := by
  have hsa : (if get_block_epoch cfg store b >
        get_block_epoch cfg store (store.blocks b).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
      else (store.blocks b).slot) ≤ (store.blocks b).slot := by
    split_ifs
    · exact start_slot_at_block_epoch_le cfg store b
    · exact le_refl _
  have hspan : ∀ i ∈ Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs,
      i ∉ E.honest →
      i ∈ E.span_committee
        (if get_block_epoch cfg store b >
            get_block_epoch cfg store (store.blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
          else (store.blocks b).slot)
        (get_current_slot cfg store - 1) := by
    intro i hi _
    exact supporter_mem_span_committee cfg hwf hprov (Weak.mem_AttSupporters_of_mem_fresh cfg ext hi)
      (hwalk i (Weak.mem_AttSupporters_of_mem_fresh cfg ext hi)) hsa
  have hstartH : E.SlotWithinHorizon cfg
      (if get_block_epoch cfg store b >
          get_block_epoch cfg store (store.blocks b).parent_root then
          compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
        else (store.blocks b).slot) :=
    ⟨hsa.trans hbH.1, lt_of_le_of_lt (Nat.div_le_div_right hsa) hbH.2⟩
  have hendH : E.SlotWithinHorizon cfg (get_current_slot cfg store - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  rw [Weak.get_adversarial_weight_eq, Weak.compute_adversarial_weight_eq]
  exact fresh_byzantine_weight_le cfg ext hbb hval htab hstartH hendH hspan

/-! ## Step 4 — the honest-support majority (arithmetic assembly) -/

/-- Pure `ℕ` core of the assembly: cancel `2·A` against `2·z` in the
`Weak.is_one_confirmed` inequality once `z ≤ A`. Restated locally:
`QuorumAccounting.majority_arith` is `private`. -/
private theorem majority_arith {h z d ms ps a : ℕ}
    (hineq : 2 * (h + z) + d ≥ ms + ps + 2 * a + 1) (hbyz : z ≤ a) :
    2 * h + d ≥ ms + ps + 1 := by omega

/-- Step 4 (assembly): given `Weak.is_one_confirmed = true` and the fresh
Byzantine-supporter bound `hbyz : byz_score ≤ Weak.get_adversarial_weight`,
twice the fresh honest supporters' weight plus the fresh support discount
dominates `maximum_support + proposer_score + 1`. -/
theorem honest_support_majority_of_byz_le {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hconf : Weak.is_one_confirmed cfg ext store bs b = true)
    (hbyz : (((Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ Weak.get_adversarial_weight cfg store bs b) :
    2 * (((Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + Weak.get_support_discount cfg ext store bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1)
        + compute_proposer_score cfg bs + 1 := by
  have hineq := is_one_confirmed_ineq cfg ext hconf
  rw [Weak.fresh_attestation_score_honest_split cfg ext E store (get_node_for_root b) bs] at hineq
  exact majority_arith hineq hbyz

/-- Steps 3 + 4 composed: the unconditional weak headline over fresh support
at an arbitrary (not necessarily honest) observer's store. -/
theorem honest_support_majority_at_observer {E : Execution Root}
    (hbb : ByzantineBound cfg E) {store : Store Root} (hwf : ParentSlotLt store)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hbH : E.SlotWithinHorizon cfg (store.blocks b).slot)
    (hcurH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hconf : Weak.is_one_confirmed cfg ext store bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs, ∀ lm,
      store.latest_messages i = some lm → WalkKnown store (store.blocks b).slot lm.root) :
    2 * (((Weak.FreshAttSupporters cfg ext store (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + Weak.get_support_discount cfg ext store bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1)
        + compute_proposer_score cfg bs + 1 :=
  honest_support_majority_of_byz_le cfg ext hconf
    (fresh_byz_score_le_adversarial_weight cfg ext hbb hwf hval htab hbH hcurH hprov hwalk)

end Weak

end FastConfirmation.Spec

end
