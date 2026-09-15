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

end Weak

end FastConfirmation.Spec
