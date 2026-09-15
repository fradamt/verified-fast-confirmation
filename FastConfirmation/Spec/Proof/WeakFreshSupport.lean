import FastConfirmation.Spec.Proof.QuorumAccounting
import FastConfirmation.Spec.Proof.WeakEconomicReadback
import FastConfirmation.Spec.Model.WeakSynchrony

/-!
# Spec / Proof / WeakFreshSupport

Margin-discharge wave, Stage G-a/G-b (`docs/weak-synchrony.md`'s rule delta 3
economic follow-through): the **fresh** twins of `QuorumAccounting.AttSupporters`
and `Discount.ParentSupport`/`ParentStuck`/`ParentStuckByz`, matching the exact
counted-cell filters of `Weak.get_epoch_fresh_attestation_score` /
`Weak.get_epoch_fresh_block_support_between_slots`.

Every lemma here is a named twin of an existing strong lemma with an extra
`Weak.is_epoch_fresh_message` conjunct threaded through; the twins are
strictly simpler where the strong originals needed the equivocation-score
apparatus (`EquivActive`, `hne`), because `Weak.compute_adversarial_weight`
has no equivocation subtraction at all (rule delta 1).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## `epoch_le_of_fresh_cell`

Epoch monotonicity turns a fresh cell into the `hdom` premise of
`Execution.recorded_lm_is_newest_in_store`, for every ground vote at or below
the cutoff. -/

omit [LinearOrder Root] [Inhabited Root] in
theorem epoch_le_of_fresh_cell {store : Store Root} {lm : LatestMessage Root}
    (hfresh : Weak.is_epoch_fresh_message cfg store lm = true)
    {es : Slot} (hes : es = get_current_slot cfg store - 1)
    {t : Slot} (ht : t ≤ es) :
    compute_epoch_at_slot cfg t ≤ lm.epoch := by
  have hcut : Weak.recorded_cutoff_epoch cfg store ≤ get_latest_message_epoch lm :=
    of_decide_eq_true hfresh
  have hmono : compute_epoch_at_slot cfg t ≤ compute_epoch_at_slot cfg es :=
    Nat.div_le_div_right ht
  have hcuteq : Weak.recorded_cutoff_epoch cfg store = compute_epoch_at_slot cfg es := by
    rw [Weak.recorded_cutoff_epoch, hes]
  rw [hcuteq] at hcut
  exact hmono.trans hcut

/-! ## `FreshAttSupporters` — the fresh counted-support list

Twin of `AttSupporters`, matching `Weak.get_epoch_fresh_attestation_score`'s
filter in the exact conjunct order `(equiv && fresh) && ancestor`. -/

/-- The **fresh supporter list** of `node` under `state`: the unslashed active
non-equivocating validators whose recorded latest message is epoch-fresh
(rule delta 3) and supports `node`. This is exactly the list
`Weak.get_epoch_fresh_attestation_score` maps to effective balances and sums. -/
def FreshAttSupporters (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) : List ValidatorIndex :=
  ((get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)).filter
    (fun i => match store.latest_messages i with
      | none => false
      | some lm =>
          decide (i ∉ store.equivocating_indices) &&
            Weak.is_epoch_fresh_message cfg store lm &&
            is_ancestor store (get_supported_node store lm) node)

omit [Inhabited Root] in
/-- `Weak.get_epoch_fresh_attestation_score` is the sum of effective balances
over the fresh supporter list (`rfl`: `FreshAttSupporters` is literally the
filtered list the score function computes and sums). -/
theorem get_epoch_fresh_attestation_score_eq_sum (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) :
    Weak.get_epoch_fresh_attestation_score cfg store node state =
      ((FreshAttSupporters cfg store node state).map
        (fun i => (state.validators.getD i default).effective_balance)).sum :=
  rfl

omit [Inhabited Root] in
/-- The fresh supporter list has no duplicates (it is a triple filter of
`List.range`, exactly as `AttSupporters_nodup`). -/
theorem FreshAttSupporters_nodup (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) : (FreshAttSupporters cfg store node state).Nodup := by
  simp only [FreshAttSupporters, get_active_validator_indices]
  exact (((List.nodup_range).filter _).filter _).filter _

omit [Inhabited Root] in
/-- A fresh supporter is unslashed-active-non-equivocating, has an epoch-fresh
recorded latest message, and that message supports the node. -/
theorem mem_FreshAttSupporters {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ FreshAttSupporters cfg store node state) :
    ∃ lm, store.latest_messages i = some lm ∧
      i ∉ store.equivocating_indices ∧
      Weak.is_epoch_fresh_message cfg store lm = true ∧
      is_ancestor store (get_supported_node store lm) node = true := by
  simp only [FreshAttSupporters, List.mem_filter] at hi
  obtain ⟨_, hQ⟩ := hi
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hQ; exact absurd hQ (by simp)
  | some lm =>
    rw [hlm] at hQ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
    exact ⟨lm, rfl, hQ.1.1, hQ.1.2, hQ.2⟩

/-- Generic helper: if `q` implies `p` on every element of `l`, filtering by
`q` is a sublist of filtering by `p`. Pure `List`/`Bool` fact, no honesty
content. -/
private theorem filter_sublist_of_imp {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, q x = true → p x = true) :
    List.Sublist (l.filter q) (l.filter p) := by
  have heq : List.filter (fun a => q a && p a) l = l.filter q := by
    apply List.filter_congr
    intro a ha
    rcases Bool.eq_false_or_eq_true (q a) with hqa | hqa
    · simp [hqa, h a ha hqa]
    · simp [hqa]
  have hstep : List.filter q (List.filter p l) = l.filter q := by
    rw [List.filter_filter]; exact heq
  rw [← hstep]
  exact List.filter_sublist

omit [Inhabited Root] in
/-- Sublist relation to the strong supporter list — the reuse hook for
`supporter_mem_span_committee` and `byzantine_supporter_weight_le`. -/
theorem FreshAttSupporters_sublist (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) :
    List.Sublist (FreshAttSupporters cfg store node state)
      (AttSupporters cfg store node state) := by
  simp only [FreshAttSupporters, AttSupporters]
  apply filter_sublist_of_imp
  intro i _ hq
  cases hlm : store.latest_messages i with
  | none => simp_all
  | some lm => simp_all only [Bool.and_eq_true]; tauto

omit [Inhabited Root] in
theorem mem_AttSupporters_of_mem_fresh {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ FreshAttSupporters cfg store node state) :
    i ∈ AttSupporters cfg store node state :=
  (FreshAttSupporters_sublist cfg store node state).subset hi

omit [Inhabited Root] in
/-- Split of the fresh score into the honest and non-honest sub-sums (mirror
of `attestation_score_honest_split`). -/
theorem fresh_attestation_score_honest_split (E : Execution Root)
    (store : Store Root) (node : ForkChoiceNode Root) (state : BeaconState Root) :
    Weak.get_epoch_fresh_attestation_score cfg store node state =
      (((FreshAttSupporters cfg store node state).filter (fun i => i ∈ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum +
      (((FreshAttSupporters cfg store node state).filter (fun i => i ∉ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum := by
  rw [get_epoch_fresh_attestation_score_eq_sum]
  exact (List.sum_map_filter_add_sum_map_filter_not (fun i => i ∈ E.honest)
    (fun i => (state.validators.getD i default).effective_balance)
    (FreshAttSupporters cfg store node state)).symm

omit [Inhabited Root] in
/-- The fresh honest-supporter list-sum equals the ground-truth weight of the
honest fresh supporters as a `Finset` (mirror of `FractionBase.honest_score_eq_weight`). -/
theorem fresh_honest_score_eq_weight {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry) :
    (((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map
      (fun i => (bs.validators.getD i default).effective_balance)).sum =
      E.weight (((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).toFinset) := by
  have hLnodup : ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
      (fun i => i ∈ E.honest)).Nodup := (FreshAttSupporters_nodup cfg store _ bs).filter _
  have hmap : ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map (fun i => (bs.validators.getD i default).effective_balance)
      = ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [hmap]
  exact (List.sum_toFinset E.weight_of hLnodup).symm

omit [Inhabited Root] in
/-- The fresh Byzantine-supporter list-sum equals the ground-truth weight of
its `toFinset` (mirror of `HonestWeight.byz_score_eq_weight`). -/
theorem fresh_byz_score_eq_weight {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry) :
    (((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map
      (fun i => (bs.validators.getD i default).effective_balance)).sum =
      E.weight (((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).toFinset) := by
  have hLnodup : ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).Nodup := (FreshAttSupporters_nodup cfg store _ bs).filter _
  have hmap : ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map (fun i => (bs.validators.getD i default).effective_balance)
      = ((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [hmap]
  exact (List.sum_toFinset E.weight_of hLnodup).symm

/-! ## `FreshParentSupport` — the fresh parent-stuck sets

Twin of `ParentSupport`/`ParentStuck`/`ParentStuckByz` (`Discount.lean`), gated
by freshness, matching `Weak.get_epoch_fresh_block_support_between_slots`'s
filter order. -/

/-- The fresh pre-region parent supporters over the ground-truth committee
union: unslashed-active validators of `[parent.slot + 1, b.slot − 1]` whose
latest message is exactly `b`'s parent root, epoch-fresh, and non-equivocating.
Mirrors `Weak.get_epoch_fresh_block_support_between_slots` with
`E.span_committee` in place of the store's `get_slot_committee` union. -/
def FreshParentSupport (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  ((E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1)).filter (fun i =>
      !(bs.validators.getD i default).slashed &&
        is_active_validator (bs.validators.getD i default) (get_current_epoch cfg bs))).filter
    (fun i => (store.latest_messages i).any (fun lm =>
      decide (lm.root = (store.blocks b).parent_root) &&
        Weak.is_epoch_fresh_message cfg store lm &&
        decide (i ∉ store.equivocating_indices)))

/-- The fresh honest parent-stuck weight source: the honest members of
`FreshParentSupport`. -/
def FreshParentStuck (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  (FreshParentSupport cfg E store bs b).filter (fun i => i ∈ E.honest)

/-- The fresh Byzantine parent-stuck slice: the non-honest members of
`FreshParentSupport`. -/
def FreshParentStuckByz (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  (FreshParentSupport cfg E store bs b).filter (fun i => i ∉ E.honest)

omit [Inhabited Root] in
/-- A fresh parent supporter is in the pre-region span committee, does not
equivocate, and has an epoch-fresh recorded latest message pointing at `b`'s
parent. -/
theorem mem_FreshParentSupport {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} {i : ValidatorIndex}
    (hi : i ∈ FreshParentSupport cfg E store bs b) :
    i ∈ E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1) ∧
      i ∉ store.equivocating_indices ∧
      ∃ lm, store.latest_messages i = some lm ∧
        lm.root = (store.blocks b).parent_root ∧
        Weak.is_epoch_fresh_message cfg store lm = true := by
  simp only [FreshParentSupport, Finset.mem_filter] at hi
  obtain ⟨⟨hspan, _⟩, hP2⟩ := hi
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hP2; simp at hP2
  | some lm =>
    rw [hlm] at hP2
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hP2
    exact ⟨hspan, hP2.2, lm, rfl, hP2.1.1, hP2.1.2⟩

omit [Inhabited Root] in
/-- The fresh parent-stuck set is a subset of the strong `ParentStuck`
(dropping the freshness conjunct). -/
theorem FreshParentStuck_subset_ParentStuck {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} :
    FreshParentStuck cfg E store bs b ⊆ ParentStuck cfg E store bs b := by
  intro i hi
  simp only [FreshParentStuck, FreshParentSupport, Finset.mem_filter] at hi
  obtain ⟨⟨⟨hspan, hact⟩, hP2⟩, hih⟩ := hi
  refine Finset.mem_filter.mpr ⟨?_, hih⟩
  simp only [ParentSupport, Finset.mem_filter]
  refine ⟨⟨hspan, hact⟩, ?_⟩
  cases hlm : store.latest_messages i with
  | none => simp_all
  | some lm => simp_all only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq]; tauto

/-! ## The weak-native parent-split and discount bound

Twins of `WeakEconomicReadback.get_block_support_eq_parent_split_of_prefix` /
`parentstuck_byz_plus_equiv_le_of_prefix` / `support_discount_le_parent_stuck_of_prefix`
— strictly simpler here: `Weak.compute_adversarial_weight` has no equivocation
subtraction (rule delta 1), so there is no `EquivActive` apparatus and no
`hne` (no-honest-equivocator) premise; the Byzantine budget bound is a pure
subset argument into the non-honest span committee. -/

/-- Store-generic clone of `get_block_support_eq_parent_split_of_prefix`, over
`Weak.get_epoch_fresh_block_support_between_slots` and `FreshParentStuck`/
`FreshParentStuckByz`. -/
theorem fresh_block_support_eq_parent_split_of_prefix {E : Execution Root}
    {v : ValidatorIndex} (n : ℕ)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot) :
    Weak.get_epoch_fresh_block_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (FreshParentStuck cfg E (E.store cfg ext v n) bs b)
        + E.weight (FreshParentStuckByz cfg E (E.store cfg ext v n) bs b) := by
  have hendH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks b).slot - 1) :=
    ⟨(Nat.sub_le _ _).trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hbH.2⟩
  have hce : (Finset.Icc
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)).biUnion
          (fun s => get_slot_committee cfg ext (E.store cfg ext v n) s) =
      (Finset.Icc
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)).biUnion E.committee := by
    apply Finset.biUnion_congr rfl
    intro s hs
    exact hcomm s
      ⟨(le_trans (Finset.mem_Icc.mp hs).2 hendH.1),
        lt_of_le_of_lt
          (Nat.div_le_div_right (Finset.mem_Icc.mp hs).2) hendH.2⟩
  have hA : Weak.get_epoch_fresh_block_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (FreshParentSupport cfg E (E.store cfg ext v n) bs b) := by
    simp only [Weak.get_epoch_fresh_block_support_between_slots, FreshParentSupport,
      Execution.span_committee, Execution.weight, Execution.weight_of, hce]
    exact Finset.sum_congr rfl (fun i _ => by rw [hval])
  rw [hA]
  simp only [FreshParentStuck, FreshParentStuckByz, Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not
    (FreshParentSupport cfg E (E.store cfg ext v n) bs b) (fun i => i ∈ E.honest) E.weight_of).symm

/-- The fresh Byzantine parent-stuck weight is within the raw (undiscounted)
budget — a pure subset argument (`FreshParentSupport ⊆ E.span_committee`, no
equivocation term to net against, hence no `hcomm`). -/
theorem freshParentStuckByz_le_budget {E : Execution Root} (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg) :
    E.weight (FreshParentStuckByz cfg E (E.store cfg ext v n) bs b)
      ≤ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          (((E.store cfg ext v n).blocks b).slot - 1) / 100
          * cfg.confirmation_byzantine_threshold := by
  have hendH : E.SlotWithinHorizon cfg (((E.store cfg ext v n).blocks b).slot - 1) :=
    ⟨(Nat.sub_le _ _).trans hbH.1, lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hbH.2⟩
  have hsub : FreshParentStuckByz cfg E (E.store cfg ext v n) bs b ⊆
      (E.span_committee (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)).filter (fun i => i ∉ E.honest) := by
    intro i hi
    simp only [FreshParentStuckByz, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨(mem_FreshParentSupport cfg hi.1).1, hi.2⟩
  have hmono : E.weight (FreshParentStuckByz cfg E (E.store cfg ext v n) bs b) ≤
      E.weight ((E.span_committee (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)).filter (fun i => i ∉ E.honest)) := by
    simp only [Execution.weight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [htab]
  exact hmono.trans (hbb.span_bound _ _ hstartH hendH)

/-- Pure `ℕ` guard core: from the split `Ppre = Hp + Bp` and the budget
`Bp ≤ budget`, the guarded empty-slot discount is within `Hp`. Simpler than
`Discount.discount_guard`: `Weak.compute_adversarial_weight` has no inner
`if budget > eq` guard to thread through. -/
private theorem weak_discount_guard {c : Prop} [Decidable c] {Ppre Hp Bp budget : ℕ}
    (hsplit : Ppre = Hp + Bp) (hbe : Bp ≤ budget) :
    (if c then 0 else if Ppre > budget then Ppre - budget else 0) ≤ Hp := by
  split_ifs <;> omega

/-- **Headline: the weak discount is covered by the FRESH parent-stuck honest
weight.** No `hne`, no equivocation score, no honesty of the store's owner. -/
theorem support_discount_le_fresh_parent_stuck_of_prefix {E : Execution Root}
    (hbb : ByzantineBound cfg E) {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg) :
    Weak.get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (FreshParentStuck cfg E (E.store cfg ext v n) bs b) := by
  simp only [Weak.get_support_discount, Weak.compute_empty_slot_support_discount,
    Weak.compute_adversarial_weight]
  exact weak_discount_guard
    (fresh_block_support_eq_parent_split_of_prefix cfg ext n hcomm hval hbH)
    (freshParentStuckByz_le_budget cfg ext hbb hval hstartH hbH htab)

end Weak

end FastConfirmation.Spec
