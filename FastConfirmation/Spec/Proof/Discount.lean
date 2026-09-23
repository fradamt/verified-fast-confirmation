module
public import FastConfirmation.Spec.Proof.HonestWeight
public import FastConfirmation.Spec.Proof.PayloadSupport

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

/-- Parent supporters outside the child's required payload branch and PENDING.
These are votes for the opposing resolved status and are not discounted. -/
def ParentOtherSupport (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) : Finset ValidatorIndex :=
  (ParentSupport cfg E store bs b).filter (fun i =>
    ¬ (store.latest_messages i).any (fun lm =>
      decide ((get_supported_node store lm).payload_status =
        get_parent_payload_status store (store.blocks b) ∨
        (get_supported_node store lm).payload_status = .pending)))

omit [Inhabited Root] in
/-- The matching and other parent votes partition root-only parent support.
This is the payload component of the pre-region ledger. -/
theorem parent_payload_partition (E : Execution Root) (store : Store Root)
    (bs : BeaconState Root) (b : Root) :
    E.weight (ParentPayloadSupport cfg E store bs b) +
      E.weight (ParentOtherSupport cfg E store bs b) =
      E.weight (ParentSupport cfg E store bs b) := by
  simp only [ParentPayloadSupport, ParentOtherSupport, Execution.weight]
  exact Finset.sum_filter_add_sum_filter_not
    (ParentSupport cfg E store bs b)
    (fun i => (store.latest_messages i).any (fun lm =>
      decide ((get_supported_node store lm).payload_status =
        get_parent_payload_status store (store.blocks b) ∨
        (get_supported_node store lm).payload_status = .pending))) E.weight_of

/-- A matching parent-root vote cannot support a different resolved payload
status at that root.  The statement uses the complete opposite-status
supporter set, including validators outside the discount's pre-region. -/
theorem parentPayloadStuck_disjoint_oppositeStatus (E : Execution Root)
    (store : Store Root) (bs : BeaconState Root) (b : Root)
    (other : PayloadStatus) (hresolved : other ≠ .pending)
    (hne : other ≠ get_parent_payload_status store (store.blocks b)) :
    Disjoint (ParentPayloadStuck cfg E store bs b)
      (AttSupporters cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root other) bs).toFinset := by
  rw [Finset.disjoint_left]
  intro i hiParent hiOther
  simp only [ParentPayloadStuck, ParentPayloadSupport, ParentSupport,
    Finset.mem_filter] at hiParent
  obtain ⟨⟨⟨_, hroot⟩, hmatch⟩, _⟩ := hiParent
  obtain ⟨lm, hlm, _, hsupp⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp hiOther)
  rw [hlm] at hroot hmatch
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hroot hmatch
  have hstatus := (supported_node_own_root_resolved_iff store lm other hresolved).mp
    (by simpa only [hroot.1] using hsupp)
  have hmatch' : (if lm.payload_present then .full else .empty) =
      get_parent_payload_status store (store.blocks b) := by
    simp only [get_supported_node, hstatus.1, ↓reduceIte] at hmatch
    rcases hmatch with hmatch | hpending
    · exact hmatch
    · cases hp : lm.payload_present <;> simp [hp] at hpending
  exact hne (hstatus.2.trans hmatch')

/-- Matching parent-root votes and votes supporting the child are disjoint
in one recorded store.  The parent is strictly earlier than the child, so a
latest message pinned to the parent stops before it can reach the child's
pending node. -/
theorem parentPayloadStuck_disjoint_childSupporters (E : Execution Root)
    (store : Store Root) (bs : BeaconState Root) (b : Root)
    (hslot : (store.blocks (store.blocks b).parent_root).slot < (store.blocks b).slot) :
    Disjoint (ParentPayloadStuck cfg E store bs b)
      (AttSupporters cfg store (get_node_for_root b) bs).toFinset := by
  rw [Finset.disjoint_left]
  intro i hiParent hiChild
  simp only [ParentPayloadStuck, ParentPayloadSupport, ParentSupport,
    Finset.mem_filter] at hiParent
  obtain ⟨⟨⟨_, hroot⟩, _⟩, _⟩ := hiParent
  obtain ⟨lm, hlm, _, hsupp⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp hiChild)
  rw [hlm] at hroot
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hroot
  have hstop : get_ancestor store (get_supported_node store lm) (store.blocks b).slot
      = get_supported_node store lm :=
    get_ancestor_stop_status (by
      change (store.blocks lm.root).slot ≤ (store.blocks b).slot
      rw [hroot.1]
      exact le_of_lt hslot)
  simp only [get_node_for_root, is_ancestor_pending,
    decide_eq_true_eq] at hsupp
  rw [hstop] at hsupp
  change lm.root = b at hsupp
  have hEq : (store.blocks b).parent_root = b := hroot.1.symm.trans hsupp
  have hbad := hslot
  rw [hEq] at hbad
  exact (lt_irrefl _ hbad).elim

/-- The confirmation-store status budget as a concrete disjoint-set sum.
`O` is the complete opposite resolved supporter set; `S` is the honest child
supporter set; `G` is the matching parent-discount source.  The three
confinement inputs say that these recorded sets lie in one window `C`.
Provenance and the handler's resolved-vote slot rule supply those inputs when
`C` is the confirmation window. -/
theorem recorded_payload_status_budget (E : Execution Root)
    (store : Store Root) (bs : BeaconState Root) (b : Root)
    (other : PayloadStatus) (C : Finset ValidatorIndex)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots)
    (hother : other ≠ .pending)
    (hne : other ≠ get_parent_payload_status store (store.blocks b))
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root b) bs →
        WalkKnown store (store.blocks (store.blocks b).parent_root).slot lm.root)
    (hspanChild : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs,
      i ∈ E.honest → i ∈ C)
    (hspanOpp : ∀ i ∈ AttSupporters cfg store
      (ForkChoiceNode.mk (store.blocks b).parent_root other) bs, i ∈ C)
    (hspanParent : ParentPayloadStuck cfg E store bs b ⊆ C) :
    E.weight (AttSupporters cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root other) bs).toFinset +
      E.weight ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).toFinset +
      E.weight (ParentPayloadStuck cfg E store bs b) ≤ E.weight C := by
  let O := (AttSupporters cfg store
    (ForkChoiceNode.mk (store.blocks b).parent_root other) bs).toFinset
  let S := ((AttSupporters cfg store (get_node_for_root b) bs).filter
    (fun i => i ∈ E.honest)).toFinset
  let G := ParentPayloadStuck cfg E store bs b
  have hchildOpp := childSupporters_disjoint_oppositeParentStatus cfg other
    hwf hb hp hother hne hwalk
  have hparentOpp := parentPayloadStuck_disjoint_oppositeStatus cfg E store bs b
    other hother hne
  have hparentChild := parentPayloadStuck_disjoint_childSupporters cfg E store bs b
    (hwf b hb hp)
  have hOS : Disjoint O S := by
    rw [Finset.disjoint_left]
    intro i hiO hiS
    have hiChild : i ∈ (AttSupporters cfg store (get_node_for_root b) bs).toFinset := by
      exact List.mem_toFinset.mpr (List.mem_of_mem_filter (List.mem_toFinset.mp hiS))
    exact (Finset.disjoint_left.mp hchildOpp) hiChild hiO
  have hOG : Disjoint O G := by
    rw [Finset.disjoint_left]
    intro i hiO hiG
    exact (Finset.disjoint_left.mp hparentOpp) hiG hiO
  have hSG : Disjoint S G := by
    rw [Finset.disjoint_left]
    intro i hiS hiG
    have hiChild : i ∈ (AttSupporters cfg store (get_node_for_root b) bs).toFinset := by
      exact List.mem_toFinset.mpr (List.mem_of_mem_filter (List.mem_toFinset.mp hiS))
    exact (Finset.disjoint_left.mp hparentChild) hiG hiChild
  have hOSG : Disjoint (O ∪ S) G := by
    rw [Finset.disjoint_left]
    intro i hiOS hiG
    rcases Finset.mem_union.mp hiOS with hiO | hiS
    · exact (Finset.disjoint_left.mp hOG) hiO hiG
    · exact (Finset.disjoint_left.mp hSG) hiS hiG
  have hsub : O ∪ S ∪ G ⊆ C := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiOS | hiG
    · rcases Finset.mem_union.mp hiOS with hiO | hiS
      · exact hspanOpp i (List.mem_toFinset.mp hiO)
      · have hi' := List.mem_toFinset.mp hiS
        exact hspanChild i (List.mem_of_mem_filter hi')
          (of_decide_eq_true (List.mem_filter.mp hi').2)
    · exact hspanParent hiG
  change E.weight O + E.weight S + E.weight G ≤ E.weight C
  simp only [Execution.weight]
  rw [← Finset.sum_union hOS, ← Finset.sum_union hOSG]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => Nat.zero_le _)

/-- At an actual confirmed edge, all three disjoint recorded status classes
fit inside the rule's complete parent-to-cutoff committee estimate.  The
resolved-status class starts after the parent slot by exact latest-message
slot provenance. -/
theorem recorded_payload_status_budget_le_estimate {E : Execution Root}
    (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (other : PayloadStatus)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots)
    (hother : other ≠ .pending)
    (hne : other ≠ get_parent_payload_status store (store.blocks b))
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks (store.blocks b).parent_root).slot lm.root ∧
      WalkKnown store (store.blocks b).slot lm.root)
    (hstartH : E.SlotWithinHorizon cfg
      ((store.blocks (store.blocks b).parent_root).slot + 1))
    (hendH : E.SlotWithinHorizon cfg (get_current_slot cfg store - 1))
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hconf : is_one_confirmed cfg ext store bs b = true) :
    E.weight (AttSupporters cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root other) bs).toFinset +
      E.weight ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).toFinset +
      E.weight (ParentPayloadStuck cfg E store bs b) ≤
        estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1) := by
  let lo := (store.blocks (store.blocks b).parent_root).slot + 1
  let es := get_current_slot cfg store - 1
  have hslot := hwf b hb hp
  have hlo : lo ≤ (store.blocks b).slot := Nat.succ_le_of_lt hslot
  have hcutoff : (store.blocks b).slot ≤ es :=
    confirmed_block_slot_le_cutoff cfg ext hwf hprov
      (fun i _hi lm hlm => (hwalk i lm hlm).2) hconf
  have hspanChild : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs,
      i ∈ E.honest → i ∈ E.span_committee lo es := by
    intro i hi _
    have hspan := supporter_mem_span_committee cfg hwf hprov hi
      (fun lm hlm => (hwalk i lm hlm).2) (le_refl _)
    obtain ⟨s, hs, hcomm⟩ := Finset.mem_biUnion.mp hspan
    exact Finset.mem_biUnion.mpr ⟨s,
      Finset.mem_Icc.mpr ⟨hlo.trans (Finset.mem_Icc.mp hs).1,
        (Finset.mem_Icc.mp hs).2⟩, hcomm⟩
  have hspanOpp : ∀ i ∈ AttSupporters cfg store
      (ForkChoiceNode.mk (store.blocks b).parent_root other) bs,
      i ∈ E.span_committee lo es := by
    intro i hi
    exact resolved_supporter_mem_post_root_span cfg hwf hprov hother hi
      (fun lm hlm => (hwalk i lm hlm).1)
  have hspanParent : ParentPayloadStuck cfg E store bs b ⊆
      E.span_committee lo es := by
    intro i hi
    simp only [ParentPayloadStuck, ParentPayloadSupport, ParentSupport,
      Finset.mem_filter] at hi
    obtain ⟨s, hs, hcomm⟩ := Finset.mem_biUnion.mp hi.1.1.1.1
    exact Finset.mem_biUnion.mpr ⟨s,
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
        (Finset.mem_Icc.mp hs).2.trans ((Nat.sub_le _ _).trans hcutoff)⟩,
      hcomm⟩
  have hbudget := recorded_payload_status_budget cfg E store bs b other
    (E.span_committee lo es) hwf hb hp hother hne
    (fun i lm hlm _ => (hwalk i lm hlm).1)
    hspanChild hspanOpp hspanParent
  exact hbudget.trans (by
    simpa only [lo, es, htab] using hbb.estimate_sound lo es hstartH hendH)

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
    (hec : ExternalsCoherence cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest) (n : ℕ)
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
    (hec : ExternalsCoherence cfg ext E) {v : ValidatorIndex} (hv : v ∈ E.honest)
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
CONFIRMATION_BYZANTINE_THRESHOLD` (`ByzantineBound.span_bound`). -/

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
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
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
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
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
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
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
