module
public import FastConfirmationProofs.Discount.StatusMarginConstruction
public import FastConfirmationProofs.Weak.Selection.WeakSiblingScore

@[expose] public section

/-!
# Spec / Proof / WeakStatusMarginConstruction

The weak analogue of `StatusMarginConstruction` (G2-004). At an edge `a → c`
that an arbitrary weak observer `obs` confirms, the pending parent `(a,
PENDING)` at a later honest endpoint `(w, m)` selects the payload status that
`c` requires.

The strong construction reads the query store of an honest owner. The weak
construction reads only the recorded cells of the observer and places them
in the classes of the honest endpoint:

* The weak empty-slot discount counts only duty-fresh, non-equivocating
  parent votes whose payload status matches the status `c` requires. Its
  honest part is `FreshParentPayloadStuck`
  (`support_discount_le_fresh_parent_payload_stuck_of_prefix`).
* An honest endpoint supporter of the opposite resolved status of `a` is a
  sibling-stuck validator, or an old ancestor-class voter. For an old voter,
  duty freshness at the observer and the recorded-epoch bound at the honest
  endpoint give the same message at both stores
  (`old_window_latest_messages_agree`). That message selects the opposite
  status, so the observer discount does not use it
  (`endpoint_opposite_not_freshParentPayloadStuck`).
* The confirmation strip therefore keeps the debt
  `O = w(Aclass(W, lo, es) \ FreshParentPayloadStuck)`
  (`endpoint_status_strip_lo_at_observer`).
* The direct-window and same-epoch arms grow the strip from `es` to `σ` with
  committee support (`statusMargin_loWindow_at_observer`). The two crossing
  arms use the re-anchored full-span certificate with the debt `O`
  (`statusMargin_crossing_at_observer`). The weak budget has no
  equivocation subtraction, so both crossing arms have one shape.

The observer contributes only its own validated handler run
(`ObserverIndexedAttestationValidity`), its committee readback, and its recorded cells. No
delivery to the observer and no observer honesty is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## 1. Matching-payload fresh parent support -/

/-- The validators that fund the weak payload-aware empty-slot discount of
`b`: members of the empty-slot committees whose recorded message is exactly
for `b`'s parent, duty-fresh, non-equivocating, and selects the payload
status that `b` requires. Mirrors
`Weak.get_duty_fresh_parent_payload_support_between_slots` over the
ground-truth committee union. -/
def FreshParentPayloadSupport (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  ((E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1)).filter (fun i =>
      !(bs.validators.getD i default).slashed &&
        is_active_validator (bs.validators.getD i default) (get_current_epoch cfg bs))).filter
    (fun i => (store.latest_messages i).any (fun lm =>
      decide (lm.root = (store.blocks b).parent_root) &&
        Weak.is_duty_fresh_message cfg ext store i lm &&
        decide (i ∉ store.equivocating_indices) &&
        decide ((get_supported_node store lm).payload_status =
          get_parent_payload_status store (store.blocks b) ∨
          (get_supported_node store lm).payload_status = .pending)))

/-- The honest members of `FreshParentPayloadSupport`. -/
def FreshParentPayloadStuck (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (FreshParentPayloadSupport cfg ext E store bs b).filter (fun i => i ∈ E.honest)

/-- The non-honest members of `FreshParentPayloadSupport`. -/
def FreshParentPayloadStuckByz (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (FreshParentPayloadSupport cfg ext E store bs b).filter (fun i => i ∉ E.honest)

theorem mem_FreshParentPayloadSupport {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} {i : ValidatorIndex}
    (hi : i ∈ FreshParentPayloadSupport cfg ext E store bs b) :
    i ∈ E.span_committee ((store.blocks (store.blocks b).parent_root).slot + 1)
        ((store.blocks b).slot - 1) ∧
      i ∉ store.equivocating_indices ∧
      ∃ lm, store.latest_messages i = some lm ∧
        lm.root = (store.blocks b).parent_root ∧
        Weak.is_duty_fresh_message cfg ext store i lm = true ∧
        ((get_supported_node store lm).payload_status =
          get_parent_payload_status store (store.blocks b) ∨
         (get_supported_node store lm).payload_status = .pending) := by
  simp only [FreshParentPayloadSupport, Finset.mem_filter] at hi
  obtain ⟨⟨hspan, _⟩, hP2⟩ := hi
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hP2; simp at hP2
  | some lm =>
    rw [hlm] at hP2
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hP2
    obtain ⟨⟨⟨hroot, hfresh⟩, hne⟩, hstatus⟩ := hP2
    exact ⟨hspan, hne, lm, rfl, hroot, hfresh, hstatus⟩

theorem freshParentPayloadSupport_subset {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} :
    FreshParentPayloadSupport cfg ext E store bs b ⊆
      FreshParentSupport cfg ext E store bs b := by
  intro i hi
  obtain ⟨_, hne, lm, hlm, hroot, hfresh, _⟩ := mem_FreshParentPayloadSupport cfg ext hi
  have hi' := hi
  simp only [FreshParentPayloadSupport, Finset.mem_filter] at hi'
  simp only [FreshParentSupport, Finset.mem_filter]
  refine ⟨hi'.1, ?_⟩
  rw [hlm]
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hroot, hfresh⟩, hne⟩

theorem freshParentPayloadStuck_subset_freshParentStuck {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root} :
    FreshParentPayloadStuck cfg ext E store bs b ⊆ FreshParentStuck cfg ext E store bs b :=
  Finset.filter_subset_filter _ (freshParentPayloadSupport_subset cfg ext)

theorem freshParentPayloadStuckByz_subset {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root} :
    FreshParentPayloadStuckByz cfg ext E store bs b ⊆
      FreshParentStuckByz cfg ext E store bs b :=
  Finset.filter_subset_filter _ (freshParentPayloadSupport_subset cfg ext)

/-- The payload-aware discount source splits into its honest and non-honest
parts. Store-generic twin of `fresh_block_support_eq_parent_split_of_prefix`. -/
theorem fresh_payload_support_eq_split_of_prefix {E : Execution Root}
    {v : ValidatorIndex} (n : ℕ)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot) :
    Weak.get_duty_fresh_parent_payload_support_between_slots cfg ext
        (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (get_parent_payload_status (E.store cfg ext v n) ((E.store cfg ext v n).blocks b))
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (FreshParentPayloadStuck cfg ext E (E.store cfg ext v n) bs b)
        + E.weight (FreshParentPayloadStuckByz cfg ext E (E.store cfg ext v n) bs b) := by
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
  have hA : Weak.get_duty_fresh_parent_payload_support_between_slots cfg ext
        (E.store cfg ext v n) bs
        ((E.store cfg ext v n).blocks b).parent_root
        (get_parent_payload_status (E.store cfg ext v n) ((E.store cfg ext v n).blocks b))
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1)
      = E.weight (FreshParentPayloadSupport cfg ext E (E.store cfg ext v n) bs b) := by
    simp only [Weak.get_duty_fresh_parent_payload_support_between_slots,
      FreshParentPayloadSupport, Execution.span_committee, Execution.weight,
      Execution.weight_of, hce]
    exact Finset.sum_congr rfl (fun i _ => by rw [hval])
  rw [hA]
  simp only [FreshParentPayloadStuck, FreshParentPayloadStuckByz, Execution.weight]
  exact (Finset.sum_filter_add_sum_filter_not
    (FreshParentPayloadSupport cfg ext E (E.store cfg ext v n) bs b)
    (fun i => i ∈ E.honest) E.weight_of).symm

private theorem payload_discount_guard {c : Prop} [Decidable c] {Ppre Hp Bp budget : ℕ}
    (hsplit : Ppre = Hp + Bp) (hbe : Bp ≤ budget) :
    (if c then 0 else if Ppre > budget then Ppre - budget else 0) ≤ Hp := by
  split_ifs <;> omega

/-- **The weak payload-aware discount is covered by the matching fresh honest
parent support.** No observer honesty is used. -/
theorem support_discount_le_fresh_parent_payload_stuck_of_prefix {E : Execution Root}
    (hbb : ByzantineWeightPremises cfg E) {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg) :
    Weak.get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (FreshParentPayloadStuck cfg ext E (E.store cfg ext v n) bs b) := by
  have hbyz : E.weight (FreshParentPayloadStuckByz cfg ext E (E.store cfg ext v n) bs b) ≤
      E.weight (FreshParentStuckByz cfg ext E (E.store cfg ext v n) bs b) :=
    E.weight_mono (freshParentPayloadStuckByz_subset cfg ext)
  simp only [Weak.get_support_discount, Weak.compute_empty_slot_support_discount,
    Weak.compute_adversarial_weight]
  exact payload_discount_guard
    (fresh_payload_support_eq_split_of_prefix cfg ext n hcomm hval hbH)
    (hbyz.trans (freshParentStuckByz_le_budget cfg ext hbb hval hstartH hbH htab))

/-! ## 2. Honest opposite supporters -/

/-- An honest endpoint supporter of the opposite resolved status of `a`, whose
endpoint message is old, does not fund the observer's payload-aware discount.
Duty freshness at the observer and the recorded-epoch bound at the honest
endpoint make the two recorded messages equal. That message selects the
opposite status. -/
theorem endpoint_opposite_not_freshParentPayloadStuck {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs w i : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es : Slot}
    {o : PayloadStatus} {bsQ bsW : BeaconState Root}
    {dst : LatestMessage Root}
    (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hprovQ : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hi : i ∈ E.honest) (hiSpan : i ∈ E.span_committee lo es)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hdstSlot : dst.slot ≤ es)
    (hopp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk a o) bsW)
    (ho : o ≠ .pending)
    (hne : o ≠ get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b))
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext obs q).blocks b = (E.store cfg ext w m).blocks b) :
    i ∉ FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  intro hF
  simp only [FreshParentPayloadStuck, Finset.mem_filter] at hF
  obtain ⟨_, _, src, hsrc, hroot, hfresh, hstatus⟩ :=
    mem_FreshParentPayloadSupport cfg ext hF.1
  have hsrcSlot := E.recorded_slot_le_completed_cutoff cfg ext hes hprovQ hsrc
  have hmaxSrc : ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
      ∀ t k (att : Attestation Root), t ≤ es → E.vote i t = some (k, att) →
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm := by
    intro lm hlm t k att ht hvote
    have hlmEq : lm = src := Option.some.inj (hlm.symm.trans hsrc)
    subst hlmEq
    exact epoch_le_of_duty_fresh_cell cfg ext hfresh hes ht (by
      rw [hcomm t (E.slotWithinHorizon_of_le cfg (ht.trans (le_of_lt hesq)) hqH)]
      exact hA.honest_behavior.votes_assigned i hi t
        (by rw [hvote]; exact Option.some_ne_none _))
  have hmsg := E.old_window_latest_messages_agree cfg ext
    hA.honest_behavior hA.externals_coherence hgen hi hsrc hdst
    hsrcSlot hdstSlot hmaxSrc (hmaxW i hi hiSpan)
  subst hmsg
  have hsrcRoot : src.root = a := hroot.trans hparentQ
  have hstatusW : (get_supported_node (E.store cfg ext w m) src).payload_status =
      get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b) ∨
      (get_supported_node (E.store cfg ext w m) src).payload_status = .pending := by
    have h1 : get_supported_node (E.store cfg ext w m) src =
        get_supported_node (E.store cfg ext obs q) src := by
      simp only [get_supported_node]
      rw [hsrcRoot, hagreeA]
    have h2 : get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks b) =
        get_parent_payload_status (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks b) := by
      simp only [get_parent_payload_status]
      rw [← hagreeB, hparentQ, hagreeA]
    rw [h1, h2]
    exact hstatus
  have hs : get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b) ≠ .pending := by
    simp only [get_parent_payload_status]
    split_ifs <;> decide
  obtain ⟨lm, hlm, _, hsupp⟩ := mem_AttSupporters cfg hopp
  have hlmEq : lm = src := Option.some.inj (hlm.symm.trans hdst)
  rw [hlmEq] at hsupp
  rcases hstatusW with hmatch | hpending
  · have hnode : get_supported_node (E.store cfg ext w m) src =
        ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks b)) := by
      rw [← hmatch, ← hsrcRoot]
      rfl
    rw [hnode] at hsupp
    exact not_ancestor_two_resolved_statuses (E.store cfg ext w m) _ a _ o
      hs ho hne ⟨is_ancestor_refl _ _, hsupp⟩
  · have hsuppOwn : is_ancestor (E.store cfg ext w m)
        (get_supported_node (E.store cfg ext w m) src)
        (ForkChoiceNode.mk src.root o) = true := by
      simpa only [hsrcRoot] using hsupp
    have hresolved := (supported_node_own_root_resolved_iff
      (E.store cfg ext w m) src o ho).mp hsuppOwn
    simp only [get_supported_node, hresolved.1, ↓reduceIte] at hpending
    cases hp : src.payload_present <;> simp [hp] at hpending

/-- Honest endpoint supporters of the opposite resolved status of `a` are
sibling-stuck at the endpoint, or they are old ancestor-class voters outside
the observer's payload-aware discount source. -/
theorem endpoint_opposite_honest_classification_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es σ : Slot}
    {o : PayloadStatus} {bsQ bsW : BeaconState Root}
    (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hprovQ : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hesq : es < E.slot_at cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext obs q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hselected : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b) bsW)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m b t)
    (ho : o ≠ .pending)
    (hne : o ≠ get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b)) :
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (ForkChoiceNode.mk a o) bsW,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext w m b lo σ ∨
        i ∈ E.Aclass cfg ext w m b lo es \
          FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpslW : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hprovW := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m hw hmH
  rw [← E.store_current_slot cfg ext w m] at hprovW
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ w m
  have hpM : ((E.store cfg ext w m).blocks b).parent_root ∈
      (E.store cfg ext w m).block_roots := by
    rw [hparentM]
    exact haM
  have hwalkB : ∀ i lm, (E.store cfg ext w m).latest_messages i = some lm →
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b) bsW →
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks
            ((E.store cfg ext w m).blocks b).parent_root).slot lm.root := by
    intro i lm hlm _
    obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovW i lm hlm
    exact hwalkK _ hpM lm.root hk
  have hdisj := childSupporters_disjoint_oppositeParentStatus cfg (bs := bsW) o
    hpslW hbM hpM ho hne hwalkB
  rw [hparentM] at hdisj
  intro i hiOpp hi
  have hiSpan : i ∈ E.span_committee lo σ := by
    have hspan := resolved_supporter_mem_post_root_span (E := E) cfg hpslW
      hprovW ho hiOpp (fun lm hlm => by
        obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovW i lm hlm
        exact hwalkK a haM lm.root hk)
    rwa [← hlo, ← hσ] at hspan
  have hnS : ¬ E.SupportsDesc cfg ext w m b σ i := by
    intro hS
    have hiS : i ∈ E.Sclass cfg ext w m b lo σ := by
      simp only [Execution.Sclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hi⟩, hS⟩
    exact Finset.disjoint_left.mp hdisj
      (List.mem_toFinset.mpr (hselected i hiS)) (List.mem_toFinset.mpr hiOpp)
  by_cases hAnc : E.AncestorOrVoteless cfg ext w m b σ i
  · right
    have hiAσ : i ∈ E.Aclass cfg ext w m b lo σ := by
      simp only [Execution.Aclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hi⟩, hnS, hAnc⟩
    obtain ⟨hiAes, hnoLate⟩ := E.Aclass_es_of_committee_support cfg ext
      hA.honest_behavior hesσ hsupport hiAσ
    have hiSpanEs : i ∈ E.span_committee lo es := by
      have hiAes' := hiAes
      simp only [Execution.Aclass, Finset.mem_filter] at hiAes'
      exact hiAes'.1.1
    obtain ⟨dst, hdst, _, _⟩ := mem_AttSupporters cfg hiOpp
    have hdstSlot : dst.slot ≤ es := by
      obtain ⟨att, u, t, ifb, hsched, hia, hmsg⟩ :=
        E.schedLMProvExact cfg ext hgen w m i dst hdst
      obtain ⟨k, att', hvote, _⟩ :=
        hA.honest_behavior.no_forgery u t att ifb hsched i hi hia
      obtain ⟨_, _, _, _, _, hgate, _, _, _, hslotEq⟩ := hprovW i dst hdst
      have hdstσ : dst.slot ≤ σ := by
        rw [hslotEq, hσ]
        exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hgate)
      by_contra hlate
      have hnone := hnoLate dst.slot (Nat.lt_of_not_le hlate) hdstσ
      have hslot' : dst.slot = att.data.slot := by rw [hmsg]
      rw [hslot', hvote] at hnone
      exact Option.some_ne_none _ hnone
    exact Finset.mem_sdiff.mpr ⟨hiAes,
      endpoint_opposite_not_freshParentPayloadStuck cfg ext hA hqH hcomm hprovQ hi
        hiSpanEs hes hesq hmaxW hdst hdstSlot hiOpp ho hne hparentQ hagreeA hagreeB⟩
  · left
    simp only [Execution.Xclass, Finset.mem_filter]
    exact ⟨⟨hiSpan, hi⟩, hnS, hAnc⟩

/-! ## 3. The lo-anchored strip and margin -/

/-- The weak confirmation strip at the endpoint classes, with the opposite
ancestor debt. The payload-aware discount is charged to matching fresh parent
supporters only; the rest of the endpoint ancestor class stays in the strip. -/
theorem endpoint_status_strip_lo_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {query : FastConfirmationStore Root}
    (hstore : query.store = E.store cfg ext obs q)
    {b : Root}
    (hb : b ∈ (E.store cfg ext obs q).block_roots)
    (hp : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : Weak.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    {lo es : Slot}
    (hlo : lo = ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m) (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (haM : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root =
      ((E.store cfg ext obs q).blocks b).parent_root) :
    E.Xval cfg ext w m b lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b lo es \
            FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q)
              (get_current_balance_source query) b) + 1
      ≤ E.Sval cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconfQ : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true := by
    simpa only [bs, hstore] using hconf
  have hconfStrong : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true :=
    Spec.is_one_confirmed_of_weak cfg ext _ _ _ hconfQ
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hstore]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp b
    rw [← hbsEq]
    exact hconfStrong
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparentne⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
    obs hvalid hgen q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hsched : SchedLMProv E cfg (E.store cfg ext obs q) :=
    E.schedLMProv cfg ext hgen obs q
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparentne⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot := hwf b hb hp
  have hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hb
  have hbH : E.SlotWithinHorizon cfg ((E.store cfg ext obs q).blocks b).slot := by
    have hbcur' := hbcur
    rw [E.store_current_slot cfg ext obs q] at hbcur'
    exact E.slotWithinHorizon_of_le cfg hbcur' hqH
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext obs q)) := by
    rw [E.store_current_slot cfg ext obs q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hloH : E.SlotWithinHorizon cfg lo := by
    refine E.slotWithinHorizon_mono cfg
      (b := ((E.store cfg ext obs q).blocks b).slot) ?_ hbH
    rw [hlo]
    exact hslotlt
  have hesH : E.SlotWithinHorizon cfg es := by
    refine E.slotWithinHorizon_mono cfg
      (b := get_current_slot cfg (E.store cfg ext obs q)) ?_ hcurH
    rw [hes]
    exact Nat.sub_le _ _
  have hlo0 : E.slot_at cfg 0 ≤ lo := by
    have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
      have ht := E.store_current_slot cfg ext obs 0
      rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
        get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
      rw [← ht, hslot]
    have hanchorP : ablk.message.slot ≤ ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hslot hparentne obs q _ hp
    rw [hcur0, hlo]
    exact hanchorP.trans (Nat.le_succ _)
  have hHsup := freshHonestSupport_le_endpoint_Sval cfg ext hA hqH hcomm hval hb hp hprov
    hsched hwalk hlo0 (by rw [hlo]; exact hslotlt) hes hesq hw hmH hslotQM
  have hdisc := support_discount_le_fresh_parent_payload_stuck_of_prefix cfg ext
    hA.byzantine_bound hcomm hval (by rw [← hlo]; exact hloH) hbH htab
  have hAcl := freshParentStuck_subset_endpoint_Aclass cfg ext hA hqH hcomm (bs := bs)
    hval hp hb rfl hprov hsched hlo0 (by rw [hlo]) hes hesq hw hmH hslotQM haM hbM hparentM
  have hFPPS : FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b ⊆
      E.Aclass cfg ext w m b lo es :=
    fun i hi => hAcl (freshParentPayloadStuck_subset_freshParentStuck cfg ext hi)
  have hPA := E.weight_add_sdiff hFPPS
  have hsm := honest_support_majority_at_observer cfg ext hA.byzantine_bound hwf
    hval htab hbH hcurH hprov hconfQ hwalk
  rw [htab] at hsm
  rw [← hlo, ← hes] at hsm
  have hsplit : E.weight (E.span_committee lo es) = E.Jspec lo es + E.Bval lo es := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]
    exact E.weight_split_honest _
  have hMS := hA.byzantine_bound.estimate_sound lo es hloH hesH
  rw [hsplit] at hMS
  have hpart := E.weight_partition cfg ext w m b lo es
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  rw [← hboost]
  exact status_source_arith hsm hHsup hdisc hPA hMS hpart

/-- The endpoint score of the opposite resolved status of `a`, with the
parent-to-endpoint ledger window and the opposite ancestor debt. -/
theorem endpoint_opposite_score_le_lo_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es σ : Slot}
    {blocks : List Root} {bsQ : BeaconState Root}
    (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hprovQ : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hesq : es < E.slot_at cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext obs q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hselected : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m b t) :
    ∀ other ∈ get_node_children (E.store cfg ext w m) blocks
        (ForkChoiceNode.mk a .pending),
      other ≠ ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)) →
      get_attestation_score cfg (E.store cfg ext w m) other
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint) ≤
        E.Xval cfg ext w m b lo σ + E.Bval lo σ +
          E.weight (E.Aclass cfg ext w m b lo es \
            FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b) := by
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
  intro other hm hne
  obtain ⟨oroot, o⟩ := other
  obtain ⟨hroot, hstat⟩ := (mem_get_node_children_pending rfl).mp hm
  have hroot' : oroot = a := hroot
  subst hroot'
  have hstat' : o = .empty ∨ (o = .full ∧
      is_payload_verified (E.store cfg ext w m) oroot = true) := hstat
  have ho : o ≠ .pending := by
    intro hp
    rcases hstat' with h | ⟨h, _⟩ <;> (rw [hp] at h; cases h)
  have hneo : o ≠ get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b) := fun h => hne (by rw [h])
  have hHon := endpoint_opposite_honest_classification_at_observer cfg ext hA
    (bsQ := bsQ) hqH hcomm hprovQ hesq hw hmH hes hσ hesσ hlo haM hbM hparentM hparentQ
    hagreeA hagreeB hmaxW hselected hsupport ho hneo
  have hByz := E.endpoint_opposite_byzantine_window cfg ext hA
    (bsW := (E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) hw hmH hσ hlo haM ho
  rw [attestation_score_eq_weight cfg hvalEnd]
  calc
    _ ≤ E.weight ((E.Xclass cfg ext w m b lo σ ∪ E.Bwin lo σ) ∪
          (E.Aclass cfg ext w m b lo es \
            FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b)) := by
      apply E.weight_mono
      intro i hi
      have hiSupp := List.mem_toFinset.mp hi
      by_cases hh : i ∈ E.honest
      · rcases hHon i hiSupp hh with hX | hO
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hX)
        · exact Finset.mem_union_right _ hO
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (hByz i hiSupp hh))
    _ ≤ E.weight (E.Xclass cfg ext w m b lo σ ∪ E.Bwin lo σ) +
          E.weight (E.Aclass cfg ext w m b lo es \
            FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b) :=
      weight_union_le _ _
    _ ≤ (E.weight (E.Xclass cfg ext w m b lo σ) + E.weight (E.Bwin lo σ)) +
          E.weight (E.Aclass cfg ext w m b lo es \
            FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b) :=
      Nat.add_le_add_right (weight_union_le _ _) _

/-- **Weak G2-004, direct-window and same-epoch arms.** The pending parent
selects the payload status of a child that an arbitrary weak observer
confirms. The strip is read at the honest endpoint; growth from `es` to `σ`
is the committee-support growth of the root ledger. -/
theorem statusMargin_loWindow_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {obs : ValidatorIndex} (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext obs q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a c : Root} {lo es σ : Slot}
    (haQ : a ∈ (E.store cfg ext obs q).block_roots)
    (hcQ : c ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks c).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hconf : Weak.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true)
    (hloQ : lo = ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot + 1)
    (hloW : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (hlo₀ : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hσlt : σ < E.slot_at cfg m)
    (hesσ : es ≤ σ)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m c t)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es))
    (hselected : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)) :
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  have hpQ : ((E.store cfg ext obs q).blocks c).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hpM : ((E.store cfg ext w m).blocks c).parent_root ∈
      (E.store cfg ext w m).block_roots := by
    rw [hparentM]
    exact haM
  have hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext obs q)
      (E.blockProvenance cfg ext w m) haQ haM
  have hagreeC : (E.store cfg ext obs q).blocks c = (E.store cfg ext w m).blocks c :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext obs q)
      (E.blockProvenance cfg ext w m) hcQ hcM
  have hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es :=
    E.WindowRecordedEpochMax_mono_end cfg ext hesσ
      (E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
        hw hmH hlo₀ hσ hσlt)
  have hsource := endpoint_status_strip_lo_at_observer cfg ext hA hqH hvalid hcomm hquery
    hcQ hpQ hconf hloQ hes hesq hw hmH hslotQM (by rw [hparentQ]; exact haM) hcM
    (hparentM.trans hparentQ.symm)
  have hgrowS := E.hgrowS_of_committee_support cfg ext hA.honest_behavior
    w m c lo hesσ hsupport
  have hgrowX := E.hgrowX_of_committee_support cfg ext hA.honest_behavior
    w m c lo hesσ hsupport
  have hstrip := E.opposite_ancestor_strip_window_uniform cfg ext
    (v := w) (n := m) (fun _ _ _ h => h) (fun _ _ _ h => h)
    hsource hgrowS hgrowX hbudget
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hgen hA.domain w hw m hmH
  have hpslW : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hpslQ : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprovQ := E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
    obs hvalid hgen q
  rw [← E.store_current_slot cfg ext obs q] at hprovQ
  have hprovW := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m hw hmH
  rw [← E.store_current_slot cfg ext w m] at hprovW
  have hwalkKQ := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ obs q
  have hwalkKW := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ w m
  have hltW : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks c).slot := by
    have hlt := hpslW c hcM hpM
    rwa [hparentM] at hlt
  have hmem := E.required_parent_status_mem_pending_minimal cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m))
    haM hcM hparentM hltW
  have hconfQ : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q)
      (get_current_balance_source query) c = true := by
    apply Spec.is_one_confirmed_of_weak cfg ext
    rw [← hquery]
    exact hconf
  have hwalkQ : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root c) (get_current_balance_source query), ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks c).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hprovQ i lm hlm
    exact hwalkKQ c hcQ lm.root hk
  have hnotPrev := confirmed_parent_not_previous_at_later_store cfg ext
    hA.wellFormed obs w q m
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
    hcQ hcM (hpslW c hcM hpM) hpslQ hprovQ hwalkQ hslotQM hconfQ
  rw [hparentM] at hnotPrev
  have hwalkB : ∀ i lm, (E.store cfg ext w m).latest_messages i = some lm →
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) →
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks
            ((E.store cfg ext w m).blocks c).parent_root).slot lm.root := by
    intro i lm hlm _
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hprovW i lm hlm
    exact hwalkKW _ hpM lm.root hk
  have hsel := E.selected_parent_score_ge_Sval cfg ext hvalEnd hpslW hcM hpM
    hwalkB hselected
  rw [hparentM] at hsel
  have hopp := endpoint_opposite_score_le_lo_at_observer cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m))
    (bsQ := get_current_balance_source query)
    hqH hcomm hprovQ hesq hw hmH hes hσ hesσ hloW haM hcM hparentM hparentQ
    hagreeA hagreeC hmaxW hselected hsupport
  exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hstrip hopp

/-! ## 4. The crossing arms -/

/-- Weak intra-epoch endpoint inequality with the opposite ancestor debt:
`intraEpochFuture_endpoint_inequality_at_observer` with the payload-aware
discount split and the re-anchored certificate `_opp`. -/
theorem intraEpochFuture_endpoint_inequality_opp_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hwf : ParentSlotLt (E.store cfg ext obs q))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    (hconf : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    (hslotlt : ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot)
    (hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q))
    (hintra : get_block_epoch cfg (E.store cfg ext obs q) b =
      get_block_epoch cfg (E.store cfg ext obs q)
        ((E.store cfg ext obs q).blocks b).parent_root)
    (hesSigma : es ≤ sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hboost : compute_proposer_score cfg bs = get_proposer_score cfg (E.store cfg ext w m))
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hFPPSsub : FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b ∩
        E.span_committee ((E.store cfg ext obs q).blocks b).slot es ⊆
      E.Aclass cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma
        ≤ E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma ≤
      E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es) :
    let lo := ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext obs q).blocks b).slot
    E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
        + E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid sigma
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b ∩
              E.span_committee mid es)) + 1
      ≤ E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext obs q).blocks
    ((E.store cfg ext obs q).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext obs q).blocks b).slot
  let FP := FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b
  have hlo : lo ≤ mid := hslotlt
  have hcurH : E.SlotWithinHorizon cfg (get_current_slot cfg (E.store cfg ext obs q)) := by
    rw [E.store_current_slot cfg ext obs q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext obs q))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hmidH
  have hbaseQ := crossing_hbase_of_confirmed_at_observer cfg ext hA hqH hcomm hval htab
    hbQ hparentQ hprov hsched hwalk hconf hes hesq hw hmH hslotQM hbM
  rw [hboost] at hbaseQ
  rw [← hes] at hbaseQ
  have hMUQ := crossing_hMU_of_canonicalPre cfg ext (obs := obs) (n := q) (bs := bs) (b := b)
    hA.byzantine_bound htab hes hslotlt hbcur hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext obs q b mid es + E.Aval cfg ext obs q b mid es
        + E.Xval cfg ext obs q b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext obs q b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es)
          + E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hdFP : Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b ≤ E.weight FP :=
    support_discount_le_fresh_parent_payload_stuck_of_prefix cfg ext hA.byzantine_bound
      hcomm hval hloH hmidH htab
  have hdSplit : Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b ≤
      E.weight (FP \ E.span_committee mid es) + E.weight (FP ∩ E.span_committee mid es) := by
    refine hdFP.trans ((E.weight_mono ?_).trans (weight_union_le _ _))
    intro i hi
    by_cases hs : i ∈ E.span_committee mid es
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hs⟩)
  have hPreSub : FP \ E.span_committee mid es ⊆
      crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    simp only [crossingParentPre, Finset.mem_sdiff]
    exact ⟨freshParentPayloadStuck_subset_freshParentStuck cfg ext hi.1, hi.2⟩
  have hPreW := E.weight_add_sdiff hPreSub
  have hSubW := E.weight_add_sdiff hFPPSsub
  have hMU' := Execution.mu_shift_opp hMU (le_of_eq hPreW)
  have hguard := adversarial_guard_intra cfg hA.byzantine_bound
    (store := E.store cfg ext obs q) htab hintra hes hmidH hesH
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := freshByzSupporters_le_Bval cfg ext (bs := bs) (b := b) hval hspan
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es) + 0 + 0
        ≤ 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_zero] using hguard.1
  have hbyzfull : E.Bval mid es ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [htab]
    exact hA.byzantine_bound.span_bound mid es hmidH hesH
  have hend := E.reanchored_endpoint_of_fullSpan_certificate_opp
    (v₀ := w) (n₀ := m) (b' := b) (lo := mid) (es := es) (σ := sigma)
    (Bsup := (((FreshAttSupporters cfg ext (E.store cfg ext obs q) (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum)
    (eqSub := 0) (eqExtra := 0) (HAextra := 0) (Bextra := 0)
    (A := Weak.get_adversarial_weight cfg (E.store cfg ext obs q) bs b)
    (d := Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b)
    (MU := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) lo es)
    (qFull := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) mid es / 100)
    (Hpre := E.weight (FP \ E.span_committee mid es))
    (Hsub := E.weight (FP ∩ E.span_committee mid es))
    (xP := E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
      + E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es \
        (FP \ E.span_committee mid es)))
    (Bpre := E.weight (E.crossingByzPre lo mid es))
    (boost := get_proposer_score cfg (E.store cfg ext w m))
    (O := E.weight (E.Aclass cfg ext w m b mid es \ (FP ∩ E.span_committee mid es)))
    cfg ext hA.byzantine_bound hesSigma hmidH hSigmaH hbaseQ hMU' hdSplit (le_of_eq hSubW)
      hguard.2 hdomFull (Nat.zero_le _) (Nat.zero_le _) hbyzsub (by simpa using hbyzfull)
      hAX hxS
  simpa only [Nat.sub_zero] using hend

/-- Weak crossing-edge endpoint inequality with the opposite ancestor debt. -/
theorem crossingEdgeFuture_endpoint_inequality_opp_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hwf : ParentSlotLt (E.store cfg ext obs q))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    (hconf : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    (hslotlt : ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot)
    (hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q))
    (hcross : get_block_epoch cfg (E.store cfg ext obs q) b >
      get_block_epoch cfg (E.store cfg ext obs q)
        ((E.store cfg ext obs q).blocks b).parent_root)
    (hesSigma : es ≤ sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hboost : compute_proposer_score cfg bs = get_proposer_score cfg (E.store cfg ext w m))
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hFPPSsub : FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b ∩
        E.span_committee ((E.store cfg ext obs q).blocks b).slot es ⊆
      E.Aclass cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma
        ≤ E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot sigma ≤
      E.Xval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es) :
    let lo := ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext obs q).blocks b).slot
    E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
        + E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid sigma
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b ∩
              E.span_committee mid es)) + 1
      ≤ E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext obs q).blocks
    ((E.store cfg ext obs q).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext obs q).blocks b).slot
  let sa := compute_start_slot_at_epoch cfg
    (get_block_epoch cfg (E.store cfg ext obs q) b)
  let FP := FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs b
  have hlo : lo ≤ sa := Execution.parent_slot_succ_le_crossing_start (Root := Root) cfg hcross
  have hsa : sa ≤ mid := start_slot_at_block_epoch_le cfg (E.store cfg ext obs q) b
  have hcurH : E.SlotWithinHorizon cfg (get_current_slot cfg (E.store cfg ext obs q)) := by
    rw [E.store_current_slot cfg ext obs q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext obs q))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hsaH : E.SlotWithinHorizon cfg sa :=
    E.slotWithinHorizon_mono cfg hsa hmidH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hsaH
  have hbaseQ := crossing_hbase_of_confirmed_at_observer cfg ext hA hqH hcomm hval htab
    hbQ hparentQ hprov hsched hwalk hconf hes hesq hw hmH hslotQM hbM
  rw [hboost] at hbaseQ
  rw [← hes] at hbaseQ
  have hMUQ := crossing_hMU_of_canonicalPre cfg ext (obs := obs) (n := q) (bs := bs) (b := b)
    hA.byzantine_bound htab hes hslotlt hbcur hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext obs q b mid es + E.Aval cfg ext obs q b mid es
        + E.Xval cfg ext obs q b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext obs q b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es)
          + E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hdFP : Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b ≤ E.weight FP :=
    support_discount_le_fresh_parent_payload_stuck_of_prefix cfg ext hA.byzantine_bound
      hcomm hval hloH hmidH htab
  have hdSplit : Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b ≤
      E.weight (FP \ E.span_committee mid es) + E.weight (FP ∩ E.span_committee mid es) := by
    refine hdFP.trans ((E.weight_mono ?_).trans (weight_union_le _ _))
    intro i hi
    by_cases hs : i ∈ E.span_committee mid es
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hs⟩)
  have hPreSub : FP \ E.span_committee mid es ⊆
      crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    simp only [crossingParentPre, Finset.mem_sdiff]
    exact ⟨freshParentPayloadStuck_subset_freshParentStuck cfg ext hi.1, hi.2⟩
  have hPreW := E.weight_add_sdiff hPreSub
  have hSubW := E.weight_add_sdiff hFPPSsub
  have hMU' := Execution.mu_shift_opp hMU (le_of_eq hPreW)
  have hguard := adversarial_guard_crossing cfg hA.byzantine_bound
    (store := E.store cfg ext obs q) htab hcross hes hsaH hesH
  have hBextra : E.weight (E.crossingByzPre sa mid es) ≤
      E.weight (E.crossingByzPre lo mid es) :=
    E.weight_mono (E.crossingByzPre_mono_lo hlo)
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := freshByzSupporters_le_Bval cfg ext (bs := bs) (b := b) hval hspan
  have hbyzfull : E.Bval mid es + E.weight (E.crossingByzPre sa mid es) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [E.crossing_fullSpan_Bval_split hsa, htab]
    exact hA.byzantine_bound.span_bound sa es hsaH hesH
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + E.weight (E.crossingHonestPre sa mid es)
        + E.weight (E.crossingByzPre sa mid es)
      ≤ 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_assoc] using
      (Eq.trans_le (E.crossing_fullSpan_mass_split hsa) hguard.1)
  have hend := E.reanchored_endpoint_of_fullSpan_certificate_opp
    (v₀ := w) (n₀ := m) (b' := b) (lo := mid) (es := es) (σ := sigma)
    (Bsup := (((FreshAttSupporters cfg ext (E.store cfg ext obs q) (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum)
    (eqSub := 0) (eqExtra := 0)
    (A := Weak.get_adversarial_weight cfg (E.store cfg ext obs q) bs b)
    (d := Weak.get_support_discount cfg ext (E.store cfg ext obs q) bs b)
    (MU := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) lo es)
    (qFull := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) sa es / 100)
    (HAextra := E.weight (E.crossingHonestPre sa mid es))
    (Bextra := E.weight (E.crossingByzPre sa mid es))
    (Hpre := E.weight (FP \ E.span_committee mid es))
    (Hsub := E.weight (FP ∩ E.span_committee mid es))
    (xP := E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
      + E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bs b mid es \
        (FP \ E.span_committee mid es)))
    (Bpre := E.weight (E.crossingByzPre lo mid es))
    (boost := get_proposer_score cfg (E.store cfg ext w m))
    (O := E.weight (E.Aclass cfg ext w m b mid es \ (FP ∩ E.span_committee mid es)))
    cfg ext hA.byzantine_bound hesSigma hmidH hSigmaH hbaseQ hMU' hdSplit (le_of_eq hSubW)
      hguard.2 hdomFull hBextra (Nat.zero_le _) hbyzsub hbyzfull hAX hxS
  simpa only [Nat.sub_zero] using hend

/-- The endpoint score of the opposite resolved status of `a`, re-anchored at
the child slot. Sibling-stuck validators split as in the weak crossing sibling
bound. Old opposite ancestor voters split by the sub-window: the recurring
part is sub-window ancestor debt, and the rest is pre-region parent debt that
the payload-aware discount does not use. -/
theorem endpoint_opposite_score_le_crossing_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo mid es σ : Slot}
    {blocks : List Root} {bsQ : BeaconState Root}
    (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hprovQ : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hesq : es < E.slot_at cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ) (hmidEs : mid ≤ es)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext obs q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext obs q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hparentA : FreshParentStuck cfg ext E (E.store cfg ext obs q) bsQ b ⊆
      E.Aclass cfg ext w m b lo es)
    (hselected : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m b t) :
    ∀ other ∈ get_node_children (E.store cfg ext w m) blocks
        (ForkChoiceNode.mk a .pending),
      other ≠ ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)) →
      get_attestation_score cfg (E.store cfg ext w m) other
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint) ≤
        E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bsQ b lo mid es)
        + E.weight (crossingParentPre cfg ext E (E.store cfg ext obs q) bsQ b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid σ
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid σ
        + E.weight (E.Aclass cfg ext w m b mid es \
            (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b ∩
              E.span_committee mid es)) := by
  classical
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
  have hXback : E.Xclass cfg ext w m b lo σ ⊆ E.Xclass cfg ext w m b lo es :=
    E.Xclass_subset_of_committee_support cfg ext hA.honest_behavior
      w m b lo hesσ hsupport
  have hXsplit : E.Xclass cfg ext w m b lo σ ⊆
      crossingXPre cfg ext E (E.store cfg ext obs q) bsQ b lo mid es ∪
        E.Xclass cfg ext w m b mid σ := by
    intro i hi
    by_cases hiMid : i ∈ E.span_committee mid σ
    · apply Finset.mem_union_right
      have hi' := hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi' ⊢
      exact ⟨⟨hiMid, hi'.1.2⟩, hi'.2⟩
    · apply Finset.mem_union_left
      have hiNotMidEs : i ∉ E.span_committee mid es := by
        intro hiMidEs
        exact hiMid (E.span_committee_mono mid hesσ hiMidEs)
      exact mem_crossingXPre_of_endpoint_Xclass_not_mid (E := E) cfg ext hparentA
        (hXback hi) hiNotMidEs
  have hBsplit : E.Bwin lo σ ⊆ E.crossingByzPre lo mid es ∪ E.Bwin mid σ :=
    Execution.Bwin_subset_crossingByzPre_union (E := E) (lo := lo) hmidEs hesσ
  intro other hm hne
  obtain ⟨oroot, o⟩ := other
  obtain ⟨hroot, hstat⟩ := (mem_get_node_children_pending rfl).mp hm
  have hroot' : oroot = a := hroot
  subst hroot'
  have hstat' : o = .empty ∨ (o = .full ∧
      is_payload_verified (E.store cfg ext w m) oroot = true) := hstat
  have ho : o ≠ .pending := by
    intro hp
    rcases hstat' with h | ⟨h, _⟩ <;> (rw [hp] at h; cases h)
  have hneo : o ≠ get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b) := fun h => hne (by rw [h])
  have hHon := endpoint_opposite_honest_classification_at_observer cfg ext hA
    (bsQ := bsQ) hqH hcomm hprovQ hesq hw hmH hes hσ hesσ hlo haM hbM hparentM hparentQ
    hagreeA hagreeB hmaxW hselected hsupport ho hneo
  have hByz := E.endpoint_opposite_byzantine_window cfg ext hA
    (bsW := (E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) hw hmH hσ hlo haM ho
  rw [attestation_score_eq_weight cfg hvalEnd]
  let XP := crossingXPre cfg ext E (E.store cfg ext obs q) bsQ b lo mid es
  let OP := crossingParentPre cfg ext E (E.store cfg ext obs q) bsQ b mid es \
    (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b \ E.span_committee mid es)
  let Xm := E.Xclass cfg ext w m b mid σ
  let BP := E.crossingByzPre lo mid es
  let Bm := E.Bwin mid σ
  let OA := E.Aclass cfg ext w m b mid es \
    (FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bsQ b ∩ E.span_committee mid es)
  have hsub : (AttSupporters cfg (E.store cfg ext w m) (ForkChoiceNode.mk oroot o)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)).toFinset ⊆
      ((((XP ∪ OP) ∪ Xm) ∪ BP) ∪ Bm) ∪ OA := by
    intro i hi
    have hiSupp := List.mem_toFinset.mp hi
    simp only [Finset.mem_union]
    by_cases hh : i ∈ E.honest
    · rcases hHon i hiSupp hh with hX | hO
      · rcases Finset.mem_union.mp (hXsplit hX) with hXP | hXm
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hXP))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hXm)))
      · obtain ⟨hiA, hiNotPPS⟩ := Finset.mem_sdiff.mp hO
        have hiA' := hiA
        simp only [Execution.Aclass, Finset.mem_filter] at hiA'
        by_cases hs : i ∈ E.span_committee mid es
        · refine Or.inr (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
          · simp only [Execution.Aclass, Finset.mem_filter]
            exact ⟨⟨hs, hiA'.1.2⟩, hiA'.2⟩
          · intro hin
            exact hiNotPPS (Finset.mem_inter.mp hin).1
        · have hiPre : i ∈ E.crossingHonestPre lo mid es := by
            simp only [Execution.crossingHonestPre, Execution.crossingPreRegion,
              Finset.mem_filter, Finset.mem_sdiff]
            exact ⟨⟨hiA'.1.1, hs⟩, hh⟩
          by_cases hpp : i ∈ crossingParentPre cfg ext E (E.store cfg ext obs q) bsQ b mid es
          · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              (Finset.mem_sdiff.mpr ⟨hpp, ?_⟩)))))
            intro hin
            exact hiNotPPS (Finset.mem_sdiff.mp hin).1
          · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))
            change i ∈ crossingXPre cfg ext E (E.store cfg ext obs q) bsQ b lo mid es
            rw [crossingXPre, Finset.mem_sdiff]
            exact ⟨hiPre, hpp⟩
    · rcases Finset.mem_union.mp (hBsplit (hByz i hiSupp hh)) with hBP | hBm
      · exact Or.inl (Or.inl (Or.inr hBP))
      · exact Or.inl (Or.inr hBm)
  calc
    _ ≤ E.weight (((((XP ∪ OP) ∪ Xm) ∪ BP) ∪ Bm) ∪ OA) := E.weight_mono hsub
    _ ≤ E.weight XP + E.weight OP + E.weight Xm + E.weight BP + E.weight Bm +
          E.weight OA := E.weight_union6_le XP OP Xm BP Bm OA

/-- **Weak G2-004, crossing arms.** The pending parent selects the payload
status of a child that an arbitrary weak observer confirms, re-anchored at the
child slot. Both edge regimes use the non-subtractive weak certificate. -/
theorem statusMargin_crossing_at_observer {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {obs : ValidatorIndex} (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext obs q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a c : Root} {lo es σ : Slot}
    (haQ : a ∈ (E.store cfg ext obs q).block_roots)
    (hcQ : c ∈ (E.store cfg ext obs q).block_roots)
    (hparentQ : ((E.store cfg ext obs q).blocks c).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hconf : Weak.is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true)
    (hloQ : lo = ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot + 1)
    (hloW : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (hlo₀ : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hσlt : σ < E.slot_at cfg m)
    (hesσ : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hmidEs : ((E.store cfg ext obs q).blocks c).slot ≤ es)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m c t)
    (hselectedLo : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hselectedMid : ∀ i ∈ E.Sclass cfg ext w m c
        ((E.store cfg ext obs q).blocks c).slot σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)) :
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconfW : Weak.is_one_confirmed cfg ext (E.store cfg ext obs q) bs c = true := by
    simpa only [bs, hquery] using hconf
  have hconf' : Spec.is_one_confirmed cfg ext (E.store cfg ext obs q) bs c = true :=
    Spec.is_one_confirmed_of_weak cfg ext _ _ _ hconfW
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hquery]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp c
    rw [← hbsEq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
    obs hvalid hgen q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hsched : SchedLMProv E cfg (E.store cfg ext obs q) :=
    E.schedLMProv cfg ext hgen obs q
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root c) bs, ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks c).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK c hcQ lm.root hlmKnown
  have hpQ : ((E.store cfg ext obs q).blocks c).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot <
      ((E.store cfg ext obs q).blocks c).slot :=
    hwf c hcQ hpQ
  have hbcur : ((E.store cfg ext obs q).blocks c).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q c hcQ
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m c
    ((E.store cfg ext obs q).blocks c).slot hesσ hsupport
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m c
    ((E.store cfg ext obs q).blocks c).slot hesσ hsupport
  have hagreeA : (E.store cfg ext obs q).blocks a = (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext obs q)
      (E.blockProvenance cfg ext w m) haQ haM
  have hagreeC : (E.store cfg ext obs q).blocks c = (E.store cfg ext w m).blocks c :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext obs q)
      (E.blockProvenance cfg ext w m) hcQ hcM
  have hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es :=
    E.WindowRecordedEpochMax_mono_end cfg ext hesσ
      (E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
        hw hmH hlo₀ hσ hσlt)
  have hparentA : FreshParentStuck cfg ext E (E.store cfg ext obs q) bs c ⊆
      E.Aclass cfg ext w m c lo es :=
    freshParentStuck_subset_endpoint_Aclass cfg ext hA hqH hcomm (a := a) hval haQ hcQ
      hparentQ hprov hsched hlo₀ (by rw [hloQ, hparentQ]) hes hesq hw hmH hslotQM
      haM hcM hparentM
  have hFPPSsub : FreshParentPayloadStuck cfg ext E (E.store cfg ext obs q) bs c ∩
      E.span_committee ((E.store cfg ext obs q).blocks c).slot es ⊆
      E.Aclass cfg ext w m c ((E.store cfg ext obs q).blocks c).slot es := by
    intro i hi
    obtain ⟨hiP, hiS⟩ := Finset.mem_inter.mp hi
    have hia := hparentA (freshParentPayloadStuck_subset_freshParentStuck cfg ext hiP)
    simp only [Execution.Aclass, Finset.mem_filter] at hia ⊢
    exact ⟨⟨hiS, hia.1.2⟩, hia.2⟩
  have hpslW : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hprovW := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m hw hmH
  rw [← E.store_current_slot cfg ext w m] at hprovW
  have hwalkKW := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ w m
  have hpM : ((E.store cfg ext w m).blocks c).parent_root ∈
      (E.store cfg ext w m).block_roots := by
    rw [hparentM]
    exact haM
  have hltW : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks c).slot := by
    have hlt := hpslW c hcM hpM
    rwa [hparentM] at hlt
  have hmem := E.required_parent_status_mem_pending_minimal cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m))
    haM hcM hparentM hltW
  have hnotPrev := confirmed_parent_not_previous_at_later_store cfg ext
    hA.wellFormed obs w q m
    (get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c))
    hcQ hcM (hpslW c hcM hpM) hwf hprov hwalk hslotQM hconf'
  rw [hparentM] at hnotPrev
  have hwalkB : ∀ i lm, (E.store cfg ext w m).latest_messages i = some lm →
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) →
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks
            ((E.store cfg ext w m).blocks c).parent_root).slot lm.root := by
    intro i lm hlm _
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hprovW i lm hlm
    exact hwalkKW _ hpM lm.root hk
  have hsel := E.selected_parent_score_ge_Sval cfg ext hvalEnd hpslW hcM hpM
    hwalkB hselectedMid
  rw [hparentM] at hsel
  have hopp := endpoint_opposite_score_le_crossing_at_observer cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m)) (bsQ := bs)
    (mid := ((E.store cfg ext obs q).blocks c).slot)
    hqH hcomm hprov hesq hw hmH hes hσ hesσ hmidEs hloW haM hcM hparentM hparentQ
    hagreeA hagreeC hmaxW hparentA hselectedLo hsupport
  have hparentLe : get_block_epoch cfg (E.store cfg ext obs q)
      ((E.store cfg ext obs q).blocks c).parent_root ≤
      get_block_epoch cfg (E.store cfg ext obs q) c := by
    simp only [get_block_epoch]
    exact Nat.div_le_div_right (Nat.le_of_lt hslotlt)
  by_cases hcross : get_block_epoch cfg (E.store cfg ext obs q) c >
      get_block_epoch cfg (E.store cfg ext obs q)
        ((E.store cfg ext obs q).blocks c).parent_root
  · have hend := crossingEdgeFuture_endpoint_inequality_opp_at_observer cfg ext hA hqH hcomm
      hwf hval htab hcQ hpQ hprov hsched hconfW hwalk hes hesq hslotlt hbcur hcross
      hesσ hσH hw hmH hslotQM hboost hcM hFPPSsub hAX hxS
    dsimp only at hend
    rw [← hloQ] at hend
    exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hend hopp
  · have hintra : get_block_epoch cfg (E.store cfg ext obs q) c =
        get_block_epoch cfg (E.store cfg ext obs q)
          ((E.store cfg ext obs q).blocks c).parent_root :=
      le_antisymm (not_lt.mp hcross) hparentLe
    have hend := intraEpochFuture_endpoint_inequality_opp_at_observer cfg ext hA hqH hcomm
      hwf hval htab hcQ hpQ hprov hsched hconfW hwalk hes hesq hslotlt hbcur hintra
      hesσ hσH hw hmH hslotQM hboost hcM hFPPSsub hAX hxS
    dsimp only at hend
    rw [← hloQ] at hend
    exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hend hopp

end Weak

end FastConfirmation.Spec

end
