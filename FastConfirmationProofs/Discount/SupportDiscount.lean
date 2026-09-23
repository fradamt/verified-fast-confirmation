module
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Gloas.Payload.PayloadSupport

@[expose] public section

/-!
# Spec / Proof / Discount

`get_support_discount` (`= compute_empty_slot_support_discount`) is bounded by
honest weight: the weight of the validators whose latest message is **stuck on
`b`'s parent** in the empty pre-region `[parent.slot + 1, b.slot − 1]`. This is
the discount-aware engine's key structural fact: `d ≤ Hpar` unconditionally,
without an additional assumption.

The pre-region support (`get_block_support_between_slots` restricted to the
parent root) splits into an honest part `Hpar = E.weight (ParentStuck …)` and a
Byzantine part `Bpar`. The discount is `max(0, Ppre − advpre)` with `advpre`
guarded by the pre-region's `compute_adversarial_weight`; because the Byzantine
parent-stuck supporters are non-equivocating span members, `Bpar +
equivocation_score ≤ budget` (`span_bound`), so `advpre` (`= budget − equiv`,
guarded) absorbs `Bpar` and the surviving discount `Ppre − advpre ≤ Hpar`.

The four pieces mirror `HonestWeight`'s `byz_score_eq_weight` /
`byz_plus_equiv_le` and `FractionBase`'s `honest_score_eq_weight`:

* `ParentStuck` / `ParentStuckByz` — the honest / Byzantine slices of the
  pre-region parent supporters (ground-truth committees via `E.span_committee`).
* `get_block_support_eq_parent_split` — at an honest node the pre-region support
  is `E.weight (ParentStuck …) + E.weight (ParentStuckByz …)` (committees agree,
  registry constancy).
* `parentstuck_byz_plus_equiv_le` — `Bpar + equivocation_score ≤ budget`
  (parent-stuck Byzantine and active equivocators are disjoint non-honest span
  members; `span_bound`), verbatim after `byz_plus_equiv_le`.
* `support_discount_le_parent_stuck` — the headline `d ≤ Hpar`, closing on a
  pure-`ℕ` guard lemma.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The parent-stuck sets

`ParentSupport` is the pre-region parent-supporter set, matching the exact
filters of `get_block_support_between_slots` but over the ground-truth committee
union `E.span_committee [parent.slot + 1, b.slot − 1]`: unslashed active
validators whose recorded latest message is exactly `b`'s parent root and who do
not equivocate. `ParentStuck` / `ParentStuckByz` are its honest / non-honest
slices. -/

/-- The pre-region parent supporters over the ground-truth committee union: the
unslashed-active validators of `[parent.slot + 1, b.slot − 1]` whose latest
message is exactly `b`'s parent root (non-equivocating). Mirrors
`get_block_support_between_slots` with `E.span_committee` in place of the
store's `get_slot_committee` union. -/
def ParentSupport (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  ((E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1)).filter (fun i =>
      !(bs.validators.getD i default).slashed &&
        is_active_validator (bs.validators.getD i default)
          (get_current_epoch cfg bs))).filter
    (fun i => (store.latest_messages i).any (fun latest_message =>
      decide (latest_message.root = (store.blocks b).parent_root) &&
        decide (i ∉ store.equivocating_indices)))

/-- The honest parent-stuck weight source (`Hpar`): the honest members of
`ParentSupport`. This is what the headline discount bound is charged against. -/
def ParentStuck (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  (ParentSupport cfg E store bs b).filter (fun i => i ∈ E.honest)

/-- The Byzantine parent-stuck slice (`Bpar`): the non-honest members of
`ParentSupport`. -/
def ParentStuckByz (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) : Finset ValidatorIndex :=
  (ParentSupport cfg E store bs b).filter (fun i => i ∉ E.honest)

/-- Parent supporters whose vote selects the payload status required by `b`
or remains PENDING. These are the Gloas discount filter. -/
def ParentPayloadSupport (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (ParentSupport cfg E store bs b).filter (fun i =>
    (store.latest_messages i).any (fun lm =>
      decide ((get_supported_node store lm).payload_status =
        get_parent_payload_status store (store.blocks b) ∨
        (get_supported_node store lm).payload_status = .pending)))

/-- Honest matching or PENDING parent support that can fund the discount. -/
def ParentPayloadStuck (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (ParentPayloadSupport cfg E store bs b).filter (fun i => i ∈ E.honest)

/-- Non-honest matching or PENDING parent support. -/
def ParentPayloadStuckByz (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (ParentPayloadSupport cfg E store bs b).filter (fun i => i ∉ E.honest)







omit [Inhabited Root] in
/-- A parent supporter is in the pre-region span committee and does not
equivocate (its recorded latest message pins `i ∉ equivocating_indices`). -/
theorem mem_ParentSupport {E : Execution Root} {store : Store Root} {bs : BeaconState Root}
    {b : Root} {i : ValidatorIndex} (hi : i ∈ ParentSupport cfg E store bs b) :
    i ∈ E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1) ∧ i ∉ store.equivocating_indices := by
  simp only [ParentSupport, Finset.mem_filter] at hi
  obtain ⟨⟨hspan, _⟩, hP2⟩ := hi
  refine ⟨hspan, ?_⟩
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hP2; simp at hP2
  | some lm =>
    rw [hlm] at hP2
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hP2
    exact hP2.2

/-! ## Piece 2 — the honest / Byzantine split of the pre-region support -/

/-- **Piece 2.** At an honest node `(v, n)` on a registry-constant balance
source, the pre-region parent support splits into the honest parent-stuck weight
plus the Byzantine parent-stuck weight (committees agree, `hval`). -/
theorem get_block_support_eq_parent_split {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest) (n : ℕ)
    (hnH : E.WithinHorizon cfg n)
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
    exact hec.committees_agree v hv n s hnH
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

/-- The payload-aware parent support splits into matching honest and
non-honest votes. The opposing payload's parent votes are absent from both
terms. -/
theorem get_parent_payload_support_eq_split {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest)
    (n : ℕ) (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot) :
    get_parent_payload_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (get_parent_payload_status (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b))
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b)
        + E.weight (ParentPayloadStuckByz cfg E (E.store cfg ext v n) bs b) := by
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
    exact hec.committees_agree v hv n s hnH
      ⟨(le_trans (Finset.mem_Icc.mp hs).2 hendH.1),
        lt_of_le_of_lt
          (Nat.div_le_div_right (Finset.mem_Icc.mp hs).2) hendH.2⟩
  have hA : get_parent_payload_support_between_slots cfg ext (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (get_parent_payload_status (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b))
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (ParentPayloadSupport cfg E (E.store cfg ext v n) bs b) := by
    simp only [get_parent_payload_support_between_slots, ParentPayloadSupport,
      ParentSupport, Execution.span_committee, Execution.weight,
      Execution.weight_of, hce]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter]
      cases hmsg : (E.store cfg ext v n).latest_messages i with
      | none => simp
      | some msg =>
        simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    · intro i _
      rw [hval]
  rw [hA]
  simp only [ParentPayloadStuck, ParentPayloadStuckByz, Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not
    (ParentPayloadSupport cfg E (E.store cfg ext v n) bs b)
      (fun i => i ∈ E.honest) E.weight_of).symm

/-! ## Piece 3 — the Byzantine parent-stuck budget

Verbatim after `HonestWeight.byz_plus_equiv_le`: the Byzantine parent-stuck
supporters (`ParentStuckByz`) and the active equivocators (`EquivActive`) are
*disjoint* — parent supporters are non-equivocating (`mem_ParentSupport`),
equivocators equivocate — and both sit inside the non-honest pre-region span
committee (`ParentStuckByz` by construction, `EquivActive` by Step 1's `hne`), so
their combined weight is within `estimate // 100 *
CONFIRMATION_BYZANTINE_THRESHOLD` (`ByzantineWeightPremises.span_bound`). -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Weight is superadditive-into a common superset over disjoint parts. -/
private theorem weight_add_le {E : Execution Root} {A B C : Finset ValidatorIndex}
    (hdisj : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    E.weight A + E.weight B ≤ E.weight C := by
  simp only [Execution.weight]
  rw [← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAC hBC)
    (fun _ _ _ => Nat.zero_le _)

/-- **Piece 3.** At an honest node with no honest equivocators (`hne`, Step 1),
the Byzantine parent-stuck weight plus the pre-region equivocation score is
within `estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`. -/
theorem parentstuck_byz_plus_equiv_le {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) (hbb : ByzantineWeightPremises cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
  rw [get_equivocation_score_eq_weight cfg ext hec hv n hnH hval
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

/-! ## Piece 4 — the headline: the discount is covered by parent-stuck honest weight

`get_support_discount = compute_empty_slot_support_discount` is `0` when the
parent is adjacent (`parent.slot + 1 = b.slot`) and otherwise the guarded
`Ppre − advpre`, where `advpre` is the pre-region `compute_adversarial_weight
= budget − equiv` (guarded). Piece 2 splits `Ppre = Hpar + Bpar` and piece 3
gives `Bpar + equiv ≤ budget`, so `Bpar ≤ advpre` in every guard case and the
surviving discount `Ppre − advpre ≤ Hpar` — a pure-`ℕ` fact. -/

/-- Pure `ℕ` guard core: from the split `Ppre = Hp + Bp` and the budget
`Bp + eq ≤ budget`, the guarded empty-slot discount is within `Hp`, whatever the
adjacency guard `c` and the two underflow guards do. -/
private theorem discount_guard {c : Prop} [Decidable c] {Ppre Hp Bp eq budget : ℕ}
    (hsplit : Ppre = Hp + Bp) (hbe : Bp + eq ≤ budget) :
    (if c then 0 else if Ppre > (if budget > eq then budget - eq else 0)
       then Ppre - (if budget > eq then budget - eq else 0) else 0) ≤ Hp := by
  split_ifs <;> omega

/-- The Gloas payload filter only removes parent-root supporters. -/
private theorem parent_payload_support_le_block_support
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

/-- A smaller payload-filtered support produces no larger discount. -/
private theorem discount_guard_mono {c : Prop} [Decidable c]
    {P Q adv : ℕ} (hPQ : P ≤ Q) :
    (if c then 0 else if P > adv then P - adv else 0) ≤
      (if c then 0 else if Q > adv then Q - adv else 0) := by
  split_ifs <;> omega

/-- **Piece 4 (headline).** The support discount is covered by the parent-stuck
honest weight: `d ≤ Hpar`. Unconditional (no `hbyz`): the adjacency branch is
`0 ≤ _`, and the empty-slot branch closes on the split (piece 2), the pre-region
Byzantine budget (piece 3), and the guard arithmetic. `hne` (no honest
equivocators) is `HonestWeight.Execution.honest_not_equivocating`. -/
theorem support_discount_le_parent_stuck {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) (hbb : ByzantineWeightPremises cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
    (parent_payload_support_le_block_support cfg ext _ _ _ _ _ _)).trans
    (discount_guard (get_block_support_eq_parent_split cfg ext hec hv n hnH hval hbH)
      (parentstuck_byz_plus_equiv_le cfg ext hec hbb hv hnH hval hstartH hbH htab hne))

/-- The repaired discount is charged only to honest parent votes for the
child's required payload status. Opposite-status parent votes are not spent by
the discount and remain available to the opposing fork-choice branch. -/
theorem support_discount_le_matching_parent_stuck {E : Execution Root}
    (hec : BeaconExternalsPremises cfg ext E) (hbb : ByzantineWeightPremises cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest) :
    get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b) := by
  have hbyz : E.weight
      (ParentPayloadStuckByz cfg E (E.store cfg ext v n) bs b) ≤
      E.weight (ParentStuckByz cfg E (E.store cfg ext v n) bs b) := by
    simp only [Execution.weight]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [ParentPayloadStuckByz, ParentPayloadSupport,
        ParentStuckByz, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2⟩
    · intro i _ _
      exact Nat.zero_le _
  have hbudget := parentstuck_byz_plus_equiv_le cfg ext hec hbb hv hnH
    hval hstartH hbH htab hne
  have hbudget' := (Nat.add_le_add_right hbyz _).trans hbudget
  simp only [get_support_discount, compute_empty_slot_support_discount,
    compute_adversarial_weight]
  exact discount_guard
    (get_parent_payload_support_eq_split cfg ext hec hv n hnH hval hbH)
    hbudget'

end FastConfirmation.Spec

end
