module
public import FastConfirmation.Spec.Proof.Discount
public import FastConfirmation.Spec.Proof.CurrentTargetPrefixAccounting
public import FastConfirmation.Spec.Proof.WeakObserverValidity

@[expose] public section

/-!
# Spec / Proof / WeakEconomicReadback

Stage 2 of the weak-synchrony economic-core migration: store-generic clones of
seven `Discount` / `HonestWeight` lemmas whose only honesty dependency was
`ExternalsCoherence.committees_agree v hv n s hnH …` (i.e. the completed-store
committee readback fact, only ever available at an *honest* node's store).

The weak model's observer is not required to lie in `E.honest`, so its store
cannot supply `hv : v ∈ E.honest`. `CurrentTargetPrefixAccounting.lean`
introduces the store-generic replacement fact
`E.PrefixCommitteeAgreement cfg ext store` and already uses it to reprove the
completed-boundary `HonestWeight.get_equivocation_score_eq_weight` as
`get_equivocation_score_eq_weight_of_prefix` — over a fully abstract `store`,
which is strictly more general than the `E.store cfg ext v n` instance the
other six lemmas need. This file threads that same substitution through the
remaining six lemmas (`Discount`'s three, `HonestWeight`'s other three),
reusing `get_equivocation_score_eq_weight_of_prefix` itself rather than
re-deriving it.

Every clone drops exactly the hypotheses whose sole purpose was to supply
`v ∈ E.honest` / `E.WithinHorizon cfg n` to a `committees_agree` call, and
replaces them with a single `hcomm : E.PrefixCommitteeAgreement cfg ext
(E.store cfg ext v n)` premise; `v` and `n` are otherwise unconstrained. Every
other hypothesis — including honesty facts unrelated to committee readback,
such as `Execution.honest_not_equivocating`'s trajectory invariant, which
already holds at an arbitrary node's store — is carried over verbatim.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Local restatements of file-private helpers

`Discount.lean` and `HonestWeight.lean` each declare `private` arithmetic
helpers (`weight_add_le`, `discount_guard`, `byz_le_adv_arith`) that are
therefore invisible outside those files. They carry no honesty content at
all — pure `Finset`/`ℕ` facts — so they are simply restated here verbatim
(same pattern as `CurrentTargetPrefixAccounting.lean`'s local
`prefix_weight_add_le` / `prefix_byz_le_net_of_add`). -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight is superadditive-into a common superset over disjoint parts. -/
private theorem weight_add_le {E : Execution Root} {A B C : Finset ValidatorIndex}
    (hdisj : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAC hBC)
    (fun _ _ _ => Nat.zero_le _)

/-- Pure `ℕ` guard core: from the split `Ppre = Hp + Bp` and the budget
`Bp + eq ≤ budget`, the guarded empty-slot discount is within `Hp`, whatever the
adjacency guard `c` and the two underflow guards do. -/
private theorem discount_guard {c : Prop} [Decidable c] {Ppre Hp Bp eq budget : ℕ}
    (hsplit : Ppre = Hp + Bp) (hbe : Bp + eq ≤ budget) :
    (if c then 0 else if Ppre > (if budget > eq then budget - eq else 0)
       then Ppre - (if budget > eq then budget - eq else 0) else 0) ≤ Hp := by
  split_ifs <;> omega

private theorem payload_support_le_block_support
    (store : Store Root) (bs : BeaconState Root) (parent : Root)
    (status : PayloadStatus) (start_slot end_slot : Slot) :
    get_parent_payload_support_between_slots cfg ext store bs parent status start_slot end_slot
      ≤ get_block_support_between_slots cfg ext store bs parent start_slot end_slot := by
  unfold get_parent_payload_support_between_slots get_block_support_between_slots
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    cases hmsg : store.latest_messages i with
    | none => simp [hmsg] at hi
    | some msg =>
      simp only [hmsg, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hi ⊢
      exact hi.2.1
  · intro i _ _
    exact Nat.zero_le _

private theorem discount_guard_mono {c : Prop} [Decidable c]
    {P Q adv : ℕ} (hPQ : P ≤ Q) :
    (if c then 0 else if P > adv then P - adv else 0) ≤
      (if c then 0 else if Q > adv then Q - adv else 0) := by
  split_ifs <;> omega

/-- Pure `ℕ` core: `byz + equiv ≤ max_adv` gives `byz` within the
`compute_adversarial_weight` guard (both branches). -/
private theorem byz_le_adv_arith {byz equiv max_adv : ℕ} (h : byz + equiv ≤ max_adv) :
    byz ≤ if max_adv > equiv then max_adv - equiv else 0 := by
  split_ifs <;> omega

/-! ## Discount clone 1 — the honest / Byzantine split of the pre-region
support, at an arbitrary node's store. -/

/-- Store-generic clone of `get_block_support_eq_parent_split`. The original's
only use of `hv : v ∈ E.honest` / `hnH : E.WithinHorizon cfg n` was the
`hec.committees_agree v hv n s hnH …` call inside the `biUnion` congruence
step; that is replaced here by `hcomm : E.PrefixCommitteeAgreement cfg ext
(E.store cfg ext v n)`, which supplies the same committee equality directly
from the query slot's `SlotWithinHorizon`, with no honesty premise at all. -/
theorem get_block_support_eq_parent_split_of_prefix {E : Execution Root}
    {v : ValidatorIndex} (n : ℕ)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot) :
    get_block_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b)
        + E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) := by
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
  have hA : get_block_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (ParentSupport cfg E (E.store cfg ext v n) bs b) := by
    simp only [get_block_support_between_slots, ParentSupport, Execution.span_committee,
      Execution.weight, Execution.weight_of, hce]
    exact Finset.sum_congr rfl (fun i _ => by rw [hval])
  rw [hA]
  simp only [ParentStuck, ParentStuckByz, Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not
    (ParentSupport cfg E (E.store cfg ext v n) bs b) (fun i => i ∈ E.honest) E.weight_of).symm

/-! ## Discount clone 2 — the pre-region Byzantine budget, at an arbitrary
node's store. -/

/-- Store-generic clone of `parentstuck_byz_plus_equiv_le`. The original's
`hec`/`hv`/`hnH` fed only the `get_equivocation_score_eq_weight` call, which is
replaced by `Execution.get_equivocation_score_eq_weight_of_prefix` (already
store-generic, from `CurrentTargetPrefixAccounting.lean`) driven by the same
`hcomm`. -/
theorem parentstuck_byz_plus_equiv_le_of_prefix {E : Execution Root}
    (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest) :
    E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b)
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          (((E.store cfg ext v n).blocks b).slot - 1)
      ≤ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          (((E.store cfg ext v n).blocks b).slot - 1)
          / 100 * cfg.confirmation_byzantine_threshold := by
  have hendH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks b).slot - 1) :=
    ⟨(Nat.sub_le _ _).trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hbH.2⟩
  rw [E.get_equivocation_score_eq_weight_of_prefix cfg ext hcomm hval
      (((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
      (((E.store cfg ext v n).blocks b).slot - 1) hendH, htab]
  refine weight_add_le ?_ ?_ ?_ |>.trans (hbb.span_bound _ _ hstartH hendH)
  · rw [Finset.disjoint_left]
    intro i hiBz hiEA
    simp only [ParentStuckByz, Finset.mem_filter] at hiBz
    have hnoteq := (mem_ParentSupport cfg hiBz.1).2
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [ParentStuckByz, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨(mem_ParentSupport cfg hi.1).1, hi.2⟩
  · intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-! ## Discount clone 3 — the headline discount bound, at an arbitrary node's
store. -/

/-- Store-generic clone of `support_discount_le_parent_stuck`; threads
`hcomm` through clones 1 and 2 above via the same pure-`ℕ` guard core
(`discount_guard`, imported unchanged from `Discount.lean`). -/
theorem support_discount_le_parent_stuck_of_prefix {E : Execution Root}
    (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest) :
    get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) := by
  simp only [get_support_discount, compute_empty_slot_support_discount,
    compute_adversarial_weight]
  exact (discount_guard_mono
    (payload_support_le_block_support cfg ext _ _ _ _ _ _)).trans
    (discount_guard
      (get_block_support_eq_parent_split_of_prefix cfg ext n hcomm hval hbH)
      (parentstuck_byz_plus_equiv_le_of_prefix cfg ext hbb hcomm hval hstartH hbH htab hne))

/-! ## HonestWeight clone 4 — the equivocation-score readback, at an
arbitrary node's store.

`get_equivocation_score_eq_weight_of_prefix`, already proved in
`CurrentTargetPrefixAccounting.lean`, IS this clone: it is stated over a fully
abstract `store : Store Root` (strictly more general than the
`E.store cfg ext v n` instance below, which is recovered by simply choosing
`store := E.store cfg ext v n`), needs no `v`/`n` at all, and its conclusion is
verbatim the same equation as `HonestWeight.get_equivocation_score_eq_weight`
with `E.store cfg ext v n` in place of the abstract `store`. So it is reused
directly (see clones 2, 5 above/below) rather than duplicated here. -/

/-! ## HonestWeight clone 5 — Byzantine supporters plus equivocation score,
at an arbitrary node's store. -/

/-- Store-generic clone of `byz_plus_equiv_le`. As in Discount clone 2, the
original's `hec`/`hv`/`hnH` fed only the `get_equivocation_score_eq_weight`
call, replaced here by `Execution.get_equivocation_score_eq_weight_of_prefix`
driven by `hcomm`. -/
theorem byz_plus_equiv_le_of_prefix {E : Execution Root}
    (hbb : ByzantineBound cfg E) {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    {sa es : Slot}
    (hsaH : E.SlotWithinHorizon cfg sa) (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es
      ≤ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa es
          / 100 * cfg.confirmation_byzantine_threshold := by
  rw [byz_score_eq_weight cfg hval,
    E.get_equivocation_score_eq_weight_of_prefix cfg ext hcomm hval sa es hesH, htab]
  set BS := ((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
    (fun i => i ∉ E.honest)).toFinset with hBS
  set EA := EquivActive cfg E (E.store cfg ext v n) bs sa es with hEA
  refine weight_add_le ?_ ?_ ?_ |>.trans (hbb.span_bound sa es hsaH hesH)
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [hBS, List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨lm, _, hnoteq, _⟩ := mem_AttSupporters cfg hiBS.1
    simp only [hEA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [hBS, List.mem_toFinset, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  · intro i hi
    simp only [hEA, EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-! ## HonestWeight clone 6 — Byzantine supporters within the adversarial
weight, at an arbitrary node's store.

Unlike clones 1/2/3/5, this lemma's `hec`/`hhb`/`hgen` triple is *not* purely a
`committees_agree` vehicle: it also derives
`hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest` via
`Execution.honest_not_equivocating`, whose own `w : ValidatorIndex` node
argument is already unconstrained (only the *validator being shown
non-equivocating*, not the *node whose store is read*, needs to be honest).
So `hec`, `hhb`, `hgen` are kept verbatim; only the `hv : v ∈ E.honest` used
to specialize the (now replaced) `byz_plus_equiv_le` call is dropped, in
favor of `hcomm`. `hnH : E.WithinHorizon cfg n` is also kept: it is used
independently, via `Execution.store_current_slot`, to place the node's own
current slot within the horizon (unrelated to committee readback). -/
theorem byz_score_le_adversarial_weight_of_prefix {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (hvalid : E.ObserverValidity cfg ext v)
    (hnH : E.WithinHorizon cfg n)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b := by
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest := by
    intro i hi hih
    exact E.honest_not_equivocating_of_observer_validity cfg ext hhb hec hvalid hgen hih n hi
  have hsa : (if get_block_epoch cfg (E.store cfg ext v n) b >
        get_block_epoch cfg (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).parent_root then
        compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
      else ((E.store cfg ext v n).blocks b).slot) ≤ ((E.store cfg ext v n).blocks b).slot := by
    split_ifs
    · exact start_slot_at_block_epoch_le cfg (E.store cfg ext v n) b
    · exact le_refl _
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest →
      i ∈ E.span_committee
        (if get_block_epoch cfg (E.store cfg ext v n) b >
            get_block_epoch cfg (E.store cfg ext v n)
              ((E.store cfg ext v n).blocks b).parent_root then
            compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
          else ((E.store cfg ext v n).blocks b).slot)
        (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    fun i hi _ => supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) hsa
  have hstartH : E.SlotWithinHorizon cfg
      (if get_block_epoch cfg (E.store cfg ext v n) b >
          get_block_epoch cfg (E.store cfg ext v n)
            ((E.store cfg ext v n).blocks b).parent_root then
          compute_start_slot_at_epoch cfg (get_block_epoch cfg (E.store cfg ext v n) b)
        else ((E.store cfg ext v n).blocks b).slot) :=
    ⟨hsa.trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hsa) hbH.2⟩
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  rw [get_adversarial_weight_eq]
  exact byz_le_adv_arith
    (byz_plus_equiv_le_of_prefix cfg ext hbb hcomm hval htab hne hstartH hendH hspan)

/-! ## HonestWeight clone 7 — the headline honest-support majority, at an
arbitrary node's store. -/

/-- Store-generic clone of `honest_support_majority`. `hv` is dropped (its only
use fed `byz_score_le_adversarial_weight`, replaced below by `hcomm`);
`honest_support_majority_of_byz_le` itself is already fully store-generic
(no honesty hypothesis), so it is reused unchanged. -/
theorem honest_support_majority_of_prefix {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (hvalid : E.ObserverValidity cfg ext v)
    (hnH : E.WithinHorizon cfg n)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈ (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v n))
      (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root) :
    2 * (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          (((E.store cfg ext v n).blocks ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v n) - 1)
        + compute_proposer_score cfg bs + 1 :=
  honest_support_majority_of_byz_le cfg ext hconf
    (byz_score_le_adversarial_weight_of_prefix cfg ext hhb hec hbb hgen hvalid hnH hcomm hwf hbH
      hval htab hprov hwalk)

end FastConfirmation.Spec

end
