module
public import FastConfirmationProofs.Discount.SelectedMarginConstruction
public import FastConfirmationProofs.FCRRule.EndpointLedger
public import FastConfirmationProofs.Discount.FutureSiblingScore
public import FastConfirmationProofs.Discount.FutureCrossingMargin
public import FastConfirmationProofs.Execution.Delivery.ObservedAncestryTransport
public import FastConfirmationProofs.Execution.Trajectory.FullParentAvailability
public import FastConfirmationProofs.Execution.Trajectory.CrossEpochDynamics

@[expose] public section

/-!
# Construction of the pending-parent payload status margin

A selected edge `a → c` needs two fork-choice decisions at the endpoint store:
the pending parent `(a, PENDING)` must select the payload status that `c`
requires, and that status node must select `c`. This module constructs the
first decision (`PendingStatusMargin`) for every regime of the selected-edge
construction.

The accounting is the root ledger with one extra debt class. An honest
validator that supports the opposite resolved status of `a` either is a
sibling-stuck validator (`Xclass`) or votes for `a` itself with the opposite
payload bit. The second kind is an ancestor-class validator whose message is
old; its query message is the same message, so it is not a matching
parent-payload supporter at the query. The support discount is charged only to
matching parent-payload supporters. Thus the confirmation slack contains the
weight of the opposite ancestor voters.

* `status_source_arith` and `reanchored_endpoint_fullSpan_opp` are the
  arithmetic cores.
* `endpoint_opposite_honest_classification` classifies honest opposite
  supporters at the endpoint.
* `endpoint_status_strip_lo` is the lo-anchored confirmation strip with the
  opposite debt.
* `statusMargin_loWindow_minimal` supplies the direct-window and same-epoch
  arms. `statusMargin_crossing_minimal` supplies the two crossing arms.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Arithmetic cores -/

/-- The confirmation rule with the matching-parent discount leaves the
opposite ancestor debt `O` inside the confirmation strip. -/
theorem status_source_arith {Hsup d MS P s a x B J pps O : ℕ}
    (hsm : 2 * Hsup + d ≥ MS + P + 1) (hH : Hsup ≤ s) (hd : d ≤ pps)
    (hA : pps + O = a) (hMS : J + B ≤ MS) (hpart : J = s + a + x) :
    x + B + P + O + 1 ≤ s := by
  omega

theorem status_margin_arith {opp P sel S XB O : ℕ}
    (hstrip : XB + P + O + 1 ≤ S) (hopp : opp ≤ XB + O) (hsel : S ≤ sel) :
    opp + P < sel := by
  omega

/-- The full-span re-anchored endpoint with an extra ancestor debt `O`. The
debt is funded by the part of the sub-window ancestor class that the discount
does not use. -/
theorem reanchored_endpoint_fullSpan_opp
    {s0 aS0 xS0 Bsub0 Hpre Hsub xP Bpre Bsup eqSub eqExtra HAextra Bextra
      A d boost MU qFull Bsig Jsig ssig aSsig xSsig C O : ℕ}
    (hbase : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (s0 + aS0 + xS0 + Bsub0) + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub + O ≤ aS0)
    (hAguard : qFull * C ≤ A + eqSub + eqExtra)
    (hdom : (s0 + aS0 + xS0 + Bsub0) + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ Bsub0)
    (hbyzfull : Bsub0 + Bextra ≤ qFull * C)
    (hcap : (100 - C) * Bsig ≤ C * Jsig)
    (hJgrow : s0 + aS0 + xS0 ≤ Jsig)
    (hsigma : ssig + aSsig + xSsig = Jsig)
    (hAX : aSsig + xSsig ≤ aS0 + xS0)
    (hxS : xSsig ≤ xS0)
    (hC : C ≤ 25) :
    xP + xSsig + (Bpre - eqExtra) + Bsig + boost + O + 1 ≤ ssig := by
  interval_cases C <;> omega

/-- A strip with an extra debt `O`, a selected lower bound, and an opposite
upper bound give the pending-parent status margin. -/
theorem pendingStatusMargin_of_strip {store : Store Root} {blocks : List Root}
    {h : Root} {status : PayloadStatus} {XB O S : ℕ}
    (hmem : ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending))
    (hnotPrev : is_previous_slot_payload_decision cfg store
      (ForkChoiceNode.mk h status) = false)
    (hselected : S ≤ get_attestation_score cfg store (ForkChoiceNode.mk h status)
      (store.checkpoint_states store.justified_checkpoint))
    (hstrip : XB + get_proposer_score cfg store + O + 1 ≤ S)
    (hopp : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ ForkChoiceNode.mk h status →
      get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) ≤ XB + O) :
    PendingStatusMargin cfg store blocks h status := by
  refine ⟨hmem, ?_⟩
  intro other hm hne
  left
  constructor
  · change get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) +
        get_proposer_score cfg store <
      get_attestation_score cfg store (ForkChoiceNode.mk h status)
        (store.checkpoint_states store.justified_checkpoint)
    exact status_margin_arith hstrip (hopp other hm hne) hselected
  · exact hnotPrev

namespace Execution

variable (E : Execution Root)

/-! ## Set facts -/

omit [Inhabited Root] in
theorem parentPayloadStuck_subset_parentStuck {store : Store Root}
    {bs : BeaconState Root} {b : Root} :
    ParentPayloadStuck cfg E store bs b ⊆ ParentStuck cfg E store bs b := by
  intro i hi
  simp only [ParentPayloadStuck, ParentPayloadSupport, ParentStuck,
    Finset.mem_filter] at hi ⊢
  exact ⟨hi.1.1, hi.2⟩

/-- A query parent-stuck validator lies in the query parent-to-cutoff window,
and it is an endpoint ancestor-class member of every sub-window that contains
it. Its ground newest vote is exactly for the parent. -/
theorem parentStuck_endpoint_Aclass_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {a b : Root} {es : Slot}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (haQ : a ∈ (E.store cfg ext v q).block_roots)
    (hbQ : b ∈ (E.store cfg ext v q).block_roots)
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hmax : E.WindowRecordedEpochMax cfg ext v q
      (((E.store cfg ext v q).blocks
        ((E.store cfg ext v q).blocks b).parent_root).slot + 1) es) :
    ∀ i ∈ ParentStuck cfg E (E.store cfg ext v q) bs b,
      i ∈ E.span_committee (((E.store cfg ext v q).blocks
        ((E.store cfg ext v q).blocks b).parent_root).slot + 1) es ∧
      ∀ lo' : Slot, i ∈ E.span_committee lo' es →
        i ∈ E.Aclass cfg ext w m b lo' es := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hpslQ : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hpslM : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hprovQ := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprovQ
  have hslotltQ : ((E.store cfg ext v q).blocks a).slot <
      ((E.store cfg ext v q).blocks b).slot := by
    have hlt := hpslQ b hbQ (by rw [hparentQ]; exact haQ)
    rwa [hparentQ] at hlt
  have hslotltM : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks b).slot := by
    have hlt := hpslM b hbM (by rw [hparentM]; exact haM)
    rwa [hparentM] at hlt
  have hbcurQ : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgenEq, hgenSlot⟩ v q b hbQ
  have hbcQ : is_ancestor (E.store cfg ext v q) (get_node_for_root b)
      (get_node_for_root a) = true :=
    is_ancestor_of_parent hpslQ hbQ haQ hparentQ
  have hbcM : is_ancestor (E.store cfg ext w m) (get_node_for_root b)
      (get_node_for_root a) = true :=
    is_ancestor_of_parent hpslM hbM haM hparentM
  have hparentNotDescM : ¬ is_ancestor (E.store cfg ext w m)
      (get_node_for_root a) (get_node_for_root b) = true := by
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
    rw [get_ancestor_stop (le_of_lt hslotltM)]
    intro hcon
    have heq := hcon
    dsimp only at heq
    rw [heq] at hslotltM
    exact lt_irrefl _ hslotltM
  intro i hiParent
  have hiAQuery := E.ParentStuck_subset_Aclass_window cfg ext
    hA.honest_behavior hA.externals_coherence hgen hprovQ rfl hes
    (by simpa only [hparentQ] using hslotltQ) hbcurQ
    (by simpa only [hparentQ] using hbcQ) hmax hiParent
  have hiAQ := hiAQuery
  simp only [Execution.Aclass, Finset.mem_filter] at hiAQ
  obtain ⟨⟨hiSpanFull, hih⟩, _hiNotS, _hiAnc⟩ := hiAQ
  refine ⟨hiSpanFull, ?_⟩
  intro lo' hiSpan'
  have hiParent' := hiParent
  simp only [ParentStuck, Finset.mem_filter] at hiParent'
  obtain ⟨hiPS, _⟩ := hiParent'
  simp only [ParentSupport, Finset.mem_filter] at hiPS
  obtain ⟨_, hiRecorded⟩ := hiPS
  cases hlm : (E.store cfg ext v q).latest_messages i with
  | none => rw [hlm] at hiRecorded; simp at hiRecorded
  | some lm =>
    rw [hlm] at hiRecorded
    simp only [Option.any_some, Bool.and_eq_true,
      decide_eq_true_eq] at hiRecorded
    obtain ⟨hlmParent, _hiNotEquiv⟩ := hiRecorded
    obtain ⟨t, k, att, htle, hvote, hnew, hattRoot⟩ :=
      E.recorded_lm_is_newest_at cfg ext hA.honest_behavior
        hA.externals_coherence hgen hprovQ hes hih hlm
        (hmax i hih hiSpanFull lm hlm)
    have hrootA : att.data.beacon_block_root = a := by
      exact hattRoot.trans (hlmParent.trans hparentQ)
    simp only [Execution.Aclass, Finset.mem_filter]
    refine ⟨⟨hiSpan', hih⟩, ?_, ?_⟩
    · rintro ⟨t₁, k₁, att₁, ht1le, hvote1, hnew1, hdesc⟩
      have htt : t = t₁ := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnew
        (by rw [hvote1]; exact Option.some_ne_none _) hnew1 htle ht1le
      rw [← htt, hvote] at hvote1
      simp only [Option.some.injEq, Prod.mk.injEq] at hvote1
      obtain ⟨_, hattEq⟩ := hvote1
      rw [← hattEq, hrootA] at hdesc
      exact hparentNotDescM hdesc
    · exact Or.inr ⟨t, k, att, htle, hvote, hnew,
        by rw [hrootA]; exact hbcM⟩

/-- An honest validator that does not support `b` at `σ` has no vote and no
committee seat after `es` when every intervening honest committee supports
`b`. -/
theorem no_late_of_not_supportsDesc (hhb : HonestBehavior cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b : Root} {es : Slot} {i : ValidatorIndex}
    (hi : i ∈ E.honest) :
    ∀ σ : Slot, es ≤ σ →
    (∀ t : Slot, es < t → t ≤ σ → E.CommitteeSupportsAt cfg ext w m b t) →
    ¬ E.SupportsDesc cfg ext w m b σ i →
    ∀ t : Slot, es < t → t ≤ σ → E.vote i t = none ∧ i ∉ E.committee t := by
  intro σ hes
  induction σ, hes using Nat.le_induction with
  | base =>
    intro _ _ t h1 h2
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  | succ σ hes ih =>
    intro hsupport hnS t h1 h2
    have hnotComm : i ∉ E.committee (σ + 1) := fun hc =>
      hnS (hsupport (σ + 1) (Nat.lt_succ_of_le hes) (le_refl _) i hi hc)
    have hnone : E.vote i (σ + 1) = none := by
      by_contra hvote
      exact hnotComm (hhb.votes_assigned i hi (σ + 1) hvote)
    have hnS' : ¬ E.SupportsDesc cfg ext w m b σ i := fun hS =>
      hnS (E.SupportsDesc_succ_of_novote cfg ext w m b σ hnone hS)
    rcases Nat.lt_or_ge t (σ + 1) with hlt | hge
    · exact ih (fun t' h1' h2' => hsupport t' h1' (h2'.trans (Nat.le_succ σ)))
        hnS' t h1 (Nat.lt_succ_iff.mp hlt)
    · have ht : t = σ + 1 := le_antisymm h2 hge
      subst ht
      exact ⟨hnone, hnotComm⟩

/-- An endpoint ancestor-class member at `σ` is an ancestor-class member at
`es`, and it has no vote after `es`, when every intervening honest committee
supports `b`. -/
theorem Aclass_es_of_committee_support (hhb : HonestBehavior cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b : Root} {lo' es σ : Slot}
    {i : ValidatorIndex} (hesσ : es ≤ σ)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m b t)
    (hiA : i ∈ E.Aclass cfg ext w m b lo' σ) :
    i ∈ E.Aclass cfg ext w m b lo' es ∧
      ∀ t : Slot, es < t → t ≤ σ → E.vote i t = none := by
  have hiA' := hiA
  simp only [Execution.Aclass, Finset.mem_filter] at hiA'
  obtain ⟨⟨hspan, hi⟩, hnS, _⟩ := hiA'
  have hlate := E.no_late_of_not_supportsDesc cfg ext hhb hi σ hesσ hsupport hnS
  have hspanEs : i ∈ E.span_committee lo' es := by
    simp only [Execution.span_committee, Finset.mem_biUnion,
      Finset.mem_Icc] at hspan ⊢
    obtain ⟨t, ⟨hlo, htσ⟩, hc⟩ := hspan
    refine ⟨t, ⟨hlo, ?_⟩, hc⟩
    by_contra hnot
    exact (hlate t (Nat.lt_of_not_le hnot) htσ).2 hc
  exact ⟨E.Aclass_old_cutoff_of_no_late_vote cfg ext hesσ hspanEs hiA
      (fun t h1 h2 => (hlate t h1 h2).1),
    fun t h1 h2 => (hlate t h1 h2).1⟩

/-- An honest endpoint supporter of the opposite resolved parent status whose
message is old is not a matching parent-payload supporter at the query. The
query and endpoint hold the same message, and the message selects one
resolved status. -/
theorem endpoint_opposite_not_parentPayloadStuck
    (hA : SelectedMarginAssumptions cfg ext E)
    {v w i : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es : Slot}
    {o : PayloadStatus} {bsQ bsW : BeaconState Root}
    {dst : LatestMessage Root}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hi : i ∈ E.honest) (hiSpan : i ∈ E.span_committee lo es)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hdstSlot : dst.slot ≤ es)
    (hopp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk a o) bsW)
    (ho : o ≠ .pending)
    (hne : o ≠ get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b))
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext v q).blocks b = (E.store cfg ext w m).blocks b) :
    i ∉ ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b := by
  obtain ⟨ast, ablk, hgenEq, _, _⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  have hprovQ := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprovQ
  intro hPPS
  simp only [ParentPayloadStuck, ParentPayloadSupport, ParentSupport,
    Finset.mem_filter] at hPPS
  obtain ⟨⟨⟨_, hroot⟩, hstatus⟩, _⟩ := hPPS
  cases hsrc : (E.store cfg ext v q).latest_messages i with
  | none => rw [hsrc] at hroot; simp at hroot
  | some src =>
    rw [hsrc] at hroot hstatus
    simp only [Option.any_some, Bool.and_eq_true,
      decide_eq_true_eq] at hroot hstatus
    have hsrcSlot := E.recorded_slot_le_completed_cutoff cfg ext hes hprovQ hsrc
    have hmsg := E.old_window_latest_messages_agree_window cfg ext
      hA.honest_behavior hA.externals_coherence hgen hi hiSpan hsrc hdst
      hsrcSlot hdstSlot hmaxQ hmaxW
    subst hmsg
    have hsrcRoot : src.root = a := hroot.1.trans hparentQ
    have hstatusW :
        (get_supported_node (E.store cfg ext w m) src).payload_status =
          get_parent_payload_status (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks b) ∨
        (get_supported_node (E.store cfg ext w m) src).payload_status = .pending := by
      have h1 : get_supported_node (E.store cfg ext w m) src =
          get_supported_node (E.store cfg ext v q) src := by
        simp only [get_supported_node]
        rw [hsrcRoot, hagreeA]
      have h2 : get_parent_payload_status (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks b) =
          get_parent_payload_status (E.store cfg ext v q)
            ((E.store cfg ext v q).blocks b) := by
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
sibling-stuck at the endpoint, or they are old ancestor-class voters that the
query discount does not use. -/
theorem endpoint_opposite_honest_classification
    (hA : SelectedMarginAssumptions cfg ext E)
    {v w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es σ : Slot}
    {o : PayloadStatus} {bsQ bsW : BeaconState Root}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext v q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
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
          ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b := by
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
      E.endpoint_opposite_not_parentPayloadStuck cfg ext hA hv hqH hi hiSpanEs
        hes hmaxQ hmaxW hdst hdstSlot hiOpp ho hne hparentQ hagreeA hagreeB⟩
  · left
    simp only [Execution.Xclass, Finset.mem_filter]
    exact ⟨⟨hiSpan, hi⟩, hnS, hAnc⟩

/-- A non-honest endpoint supporter of a resolved status of `a` lies in the
parent-to-endpoint Byzantine window. -/
theorem endpoint_opposite_byzantine_window
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {a : Root} {lo σ : Slot}
    {o : PayloadStatus} {bsW : BeaconState Root}
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (ho : o ≠ .pending) :
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (ForkChoiceNode.mk a o) bsW,
      i ∉ E.honest → i ∈ E.Bwin lo σ := by
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
  intro i hiOpp hi
  have hspan := resolved_supporter_mem_post_root_span (E := E) cfg hpslW
    hprovW ho hiOpp (fun lm hlm => by
      obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovW i lm hlm
      exact hwalkK a haM lm.root hk)
  rw [← hlo, ← hσ] at hspan
  simp only [Execution.Bwin, Finset.mem_filter]
  exact ⟨hspan, hi⟩

/-- The required parent status is a fork-choice child of the pending parent:
EMPTY always is, and FULL is verified for every non-anchor block. -/
theorem required_parent_status_mem_pending_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {a c : Root} {blocks : List Root}
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hlt : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks c).slot) :
    ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) ∈
      get_node_children (E.store cfg ext w m) blocks
        (ForkChoiceNode.mk a .pending) := by
  obtain ⟨ast, ablk, hgenEq, hgenSlot, hgenParent⟩ := hA.genesis
  apply selected_parent_status_mem_pending
  cases hs : get_parent_payload_status (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c) with
  | empty => exact Or.inl rfl
  | full =>
    refine Or.inr ⟨rfl, ?_⟩
    have hcG : c ∉ E.genesis_store.block_roots := by
      rw [hgenEq]
      simp only [get_forkchoice_store, List.mem_singleton]
      intro hc
      subst hc
      have hblk := E.store_anchor_block cfg ext hA.wellFormed hgenEq w m hcM
      have hmin := E.store_anchor_min_slot cfg ext hA.wellFormed
        hA.externals_coherence hgenEq hgenSlot hgenParent w m a haM
      rw [hblk] at hlt
      exact absurd (lt_of_lt_of_le hlt hmin) (lt_irrefl _)
    have hver := E.full_parent_payload_verified cfg ext w m hcM hcG hs
    rwa [hparentM] at hver
  | pending =>
    simp only [get_parent_payload_status] at hs
    split_ifs at hs

/-! ## The lo-anchored strip -/

/-- The confirmation strip at the endpoint classes, with the old opposite
ancestor debt. The discount is charged to matching parent-payload supporters
only; the remaining endpoint ancestor-class weight stays in the strip. -/
theorem endpoint_status_strip_lo
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hstore : query.store = E.store cfg ext v q)
    {b : Root}
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hp : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hdom : E.WindowRecordedEpochMax cfg ext v q lo es)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i)
    (hPPS : ParentPayloadStuck cfg E (E.store cfg ext v q)
        (get_current_balance_source query) b ⊆
      E.Aclass cfg ext w m b lo es) :
    E.Xval cfg ext w m b lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b lo es \
            ParentPayloadStuck cfg E (E.store cfg ext v q)
              (get_current_balance_source query) b) + 1 ≤
      E.Sval cfg ext w m b lo es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hstore] using hconf
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hstore]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      v q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext
      hA.static_validators hA.externals_coherence v q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hb hp
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v q b hb
  have hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v q).blocks b).slot := by
    rw [E.store_current_slot cfg ext v q] at hbcur
    exact E.slotWithinHorizon_of_le cfg hbcur hqH
  have hloH : E.SlotWithinHorizon cfg lo := by
    apply E.slotWithinHorizon_mono cfg (b := (E.store cfg ext v q).blocks b |>.slot)
    · rw [hlo]
      exact hslotlt
    · exact hbH
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v q)) := by
    rw [E.store_current_slot cfg ext v q]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hqH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg
      (b := get_current_slot cfg (E.store cfg ext v q))
    · rw [hes]
      exact Nat.sub_le _ _
    · exact hcurH
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
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
  have hHsup := E.honest_supporters_sum_le_Sval_window cfg ext
    hA.honest_behavior hA.externals_coherence hgen hwf hprov hval hlo hes
    hslotlt hwalk hdom
  have hSQW : E.Sval cfg ext v q b lo es ≤ E.Sval cfg ext w m b lo es := by
    apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  have hne : ∀ i ∈ (E.store cfg ext v q).equivocating_indices,
      i ∉ E.honest :=
    fun i hieq hi =>
      Execution.honest_not_equivocating cfg ext hA.honest_behavior
        hA.externals_coherence hgen hi v q hv hqH hieq
  have hdisc := support_discount_le_matching_parent_stuck cfg ext
    hA.externals_coherence hA.byzantine_bound hv hqH hval
    (hlo ▸ hloH) hbH htab hne
  have hsm := honest_support_majority cfg ext hA.honest_behavior
    hA.externals_coherence hA.byzantine_bound hgen hv hqH hwf hbH hval htab
    hprov hconf' hwalk
  rw [htab, ← hlo, ← hes, hboost] at hsm
  have hsplit : E.weight (E.span_committee lo es) =
      E.Jspec lo es + E.Bval lo es := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]
    exact E.weight_split_honest _
  have hMS := hA.byzantine_bound.estimate_sound lo es hloH hesH
  rw [hsplit] at hMS
  have hpart := E.weight_partition cfg ext w m b lo es
  have hPA := E.weight_add_sdiff hPPS
  exact status_source_arith hsm (hHsup.trans hSQW) hdisc hPA hMS hpart

/-! ## The lo-anchored margin -/

/-- The endpoint score of the opposite resolved status of `a`, with the
parent-to-endpoint ledger window and the opposite ancestor debt. -/
theorem endpoint_opposite_score_le_lo
    (hA : SelectedMarginAssumptions cfg ext E)
    {v w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo es σ : Slot}
    {blocks : List Root} {bsQ : BeaconState Root}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext v q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
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
            ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b) := by
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
  have hHon := E.endpoint_opposite_honest_classification cfg ext hA
    (bsQ := bsQ) hv hqH hw hmH hes hσ hesσ hlo haM hbM hparentM hparentQ
    hagreeA hagreeB hmaxQ hmaxW hselected hsupport ho hneo
  have hByz := E.endpoint_opposite_byzantine_window cfg ext hA
    (bsW := (E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) hw hmH hσ hlo haM ho
  rw [attestation_score_eq_weight cfg hvalEnd]
  calc
    _ ≤ E.weight ((E.Xclass cfg ext w m b lo σ ∪ E.Bwin lo σ) ∪
          (E.Aclass cfg ext w m b lo es \
            ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b)) := by
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
            ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b) :=
      weight_union_le _ _
    _ ≤ (E.weight (E.Xclass cfg ext w m b lo σ) + E.weight (E.Bwin lo σ)) +
          E.weight (E.Aclass cfg ext w m b lo es \
            ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b) :=
      Nat.add_le_add_right (weight_union_le _ _) _

/-- The pending-parent status margin for the direct-window and same-epoch
arms. The source strip is read at the endpoint classes; the growth from `es`
to `σ` is the committee-support growth of the root ledger. -/
theorem statusMargin_loWindow_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a c : Root} {lo es σ : Slot}
    (haQ : a ∈ (E.store cfg ext v q).block_roots)
    (hcQ : c ∈ (E.store cfg ext v q).block_roots)
    (hparentQ : ((E.store cfg ext v q).blocks c).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true)
    (hloQ : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks c).parent_root).slot + 1)
    (hloW : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (hlo₀ : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hσlt : σ < E.slot_at cfg m)
    (hesσ : es ≤ σ)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q c es i → E.SupportsDesc cfg ext w m c es i)
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
  have hpQ : ((E.store cfg ext v q).blocks c).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hpM : ((E.store cfg ext w m).blocks c).parent_root ∈
      (E.store cfg ext w m).block_roots := by
    rw [hparentM]
    exact haM
  have hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m) haQ haM
  have hagreeC : (E.store cfg ext v q).blocks c = (E.store cfg ext w m).blocks c :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m) hcQ hcM
  have hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es :=
    E.WindowRecordedEpochMax_mono_end cfg ext hesσ
      (E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
        hw hmH hlo₀ hσ hσlt)
  have hmaxQ' : E.WindowRecordedEpochMax cfg ext v q
      (((E.store cfg ext v q).blocks
        ((E.store cfg ext v q).blocks c).parent_root).slot + 1) es := by
    rw [← hloQ]
    exact hmaxQ
  have hPS := E.parentStuck_endpoint_Aclass_minimal cfg ext hA
    (bs := get_current_balance_source query) hv hqH hes haQ hcQ hparentQ
    haM hcM hparentM hmaxQ'
  have hPPS : ParentPayloadStuck cfg E (E.store cfg ext v q)
      (get_current_balance_source query) c ⊆
      E.Aclass cfg ext w m c lo es := by
    intro i hi
    obtain ⟨hspan, hAcl⟩ := hPS i (E.parentPayloadStuck_subset_parentStuck cfg hi)
    rw [← hloQ] at hspan
    exact hAcl lo hspan
  have hsource := E.endpoint_status_strip_lo cfg ext hA hv hqH hquery hcQ hpQ
    hconf lo es hloQ hes hmaxQ hw hmH hSt hPPS
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
  have hpslQ : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprovQ := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprovQ
  have hprovW := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen w m hw hmH
  rw [← E.store_current_slot cfg ext w m] at hprovW
  have hwalkKQ := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalkKW := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ w m
  have hltW : ((E.store cfg ext w m).blocks a).slot <
      ((E.store cfg ext w m).blocks c).slot := by
    have hlt := hpslW c hcM hpM
    rwa [hparentM] at hlt
  have hmem := E.required_parent_status_mem_pending_minimal cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m))
    haM hcM hparentM hltW
  have hconfQ : is_one_confirmed cfg ext (E.store cfg ext v q)
      (get_current_balance_source query) c = true := by
    rw [← hquery]
    exact hconf
  have hwalkQ : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root c) (get_current_balance_source query), ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks c).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovQ i lm hlm
    exact hwalkKQ c hcQ lm.root hk
  have hnotPrev := confirmed_parent_not_previous_at_later_store cfg ext
    hA.wellFormed v w q m
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
    obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovW i lm hlm
    exact hwalkKW _ hpM lm.root hk
  have hsel := E.selected_parent_score_ge_Sval cfg ext hvalEnd hpslW hcM hpM
    hwalkB hselected
  rw [hparentM] at hsel
  have hopp := E.endpoint_opposite_score_le_lo cfg ext hA
    (blocks := get_filtered_block_tree cfg (E.store cfg ext w m))
    (bsQ := get_current_balance_source query)
    hv hqH hw hmH hes hσ hesσ hloW haM hcM hparentM hparentQ hagreeA hagreeC
    hmaxQ hmaxW hselected hsupport
  exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hstrip hopp

/-! ## The crossing arms -/

theorem mu_shift_opp {Y P x H xE Bp MU : ℕ}
    (h : Y + (P + x + Bp) ≤ MU) (hp : H + xE ≤ P) :
    Y + (H + (x + xE) + Bp) ≤ MU := by
  omega

theorem fullSpan_base_transport_arith_opp
    {sq se B d MU boost A : Nat}
    (hbase : 2 * sq + 2 * B + d >= MU + boost + 2 * A + 1)
    (hS : sq <= se) :
    2 * se + 2 * B + d >= MU + boost + 2 * A + 1 := by
  omega

omit [LinearOrder Root] [Inhabited Root] in
theorem weight_union6_le (A1 A2 A3 A4 A5 A6 : Finset ValidatorIndex) :
    E.weight (((((A1 ∪ A2) ∪ A3) ∪ A4) ∪ A5) ∪ A6) ≤
      E.weight A1 + E.weight A2 + E.weight A3 + E.weight A4 + E.weight A5 +
        E.weight A6 := by
  refine (weight_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (weight_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (weight_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (weight_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  exact weight_union_le _ _

/-- The full-span crossing certificate with an extra ancestor debt `O`. -/
theorem reanchored_endpoint_of_fullSpan_certificate_opp (hbb : ByzantineBound cfg E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    {Bsup eqSub eqExtra HAextra Bextra A d MU qFull Hpre Hsub xP Bpre boost O : ℕ}
    (hes : es ≤ σ) (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hbase : 2 * E.Sval cfg ext v₀ n₀ b' lo es + 2 * Bsup + d
      ≥ MU + boost + 2 * A + 1)
    (hMU : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub + O ≤ E.Aval cfg ext v₀ n₀ b' lo es)
    (hAguard : qFull * cfg.confirmation_byzantine_threshold
      ≤ A + eqSub + eqExtra)
    (hdom : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ E.Bval lo es)
    (hbyzfull : E.Bval lo es + Bextra
      ≤ qFull * cfg.confirmation_byzantine_threshold)
    (hAX : E.Aval cfg ext v₀ n₀ b' lo σ + E.Xval cfg ext v₀ n₀ b' lo σ
      ≤ E.Aval cfg ext v₀ n₀ b' lo es + E.Xval cfg ext v₀ n₀ b' lo es)
    (hxS : E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es) :
    xP + E.Xval cfg ext v₀ n₀ b' lo σ + (Bpre - eqExtra) + E.Bval lo σ
        + boost + O + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hJgrow : E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
      + E.Xval cfg ext v₀ n₀ b' lo es ≤ E.Jspec lo σ := by
    rw [← E.weight_partition cfg ext v₀ n₀ b' lo es]
    exact E.Jspec_mono lo hes
  have hsigma : E.Sval cfg ext v₀ n₀ b' lo σ + E.Aval cfg ext v₀ n₀ b' lo σ
      + E.Xval cfg ext v₀ n₀ b' lo σ = E.Jspec lo σ :=
    (E.weight_partition cfg ext v₀ n₀ b' lo σ).symm
  exact reanchored_endpoint_fullSpan_opp hbase hMU hd hHsub hAguard hdom hBextra
    heqExtra hbyzsub hbyzfull (E.Rterm_nonneg cfg hbb lo σ hloH hσH) hJgrow hsigma
    hAX hxS cfg.confirmation_byzantine_threshold_le


theorem intraEpochFuture_endpoint_inequality_opp
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈
          (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
        (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hbcur : ((E.store cfg ext v n).blocks b).slot <=
      get_current_slot cfg (E.store cfg ext v n))
    (hdom : E.WindowRecordedEpochMax cfg ext v n
      ((E.store cfg ext v n).blocks b).slot es)
    (hintra : get_block_epoch cfg (E.store cfg ext v n) b =
      get_block_epoch cfg (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).parent_root)
    (hesSigma : es <= sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} {m : ℕ}
    (hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSbase : E.Sval cfg ext v n b ((E.store cfg ext v n).blocks b).slot es <=
      E.Sval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hPPSsub : ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
        E.span_committee ((E.store cfg ext v n).blocks b).slot es ⊆
      E.Aclass cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
        <= E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma <=
      E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid sigma
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
              E.span_committee mid es)) + 1
      <= E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext v n).blocks
    ((E.store cfg ext v n).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext v n).blocks b).slot
  have hlo : lo <= mid := hslotlt
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hnH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext v n))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hmidH
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest :=
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n
      (by assumption) (by assumption)) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost] at hbaseQ
  rw [← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith_opp hbaseQ hSbase
  have hMUQ := E.crossing_hMU_of_canonicalPre cfg ext hbb htab hes hslotlt hbcur
    hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext v n b mid es + E.Aval cfg ext v n b mid es
        + E.Xval cfg ext v n b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext v n b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        <= estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hdPPS : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b) :=
    support_discount_le_matching_parent_stuck cfg ext hec hbb hv hnH hval
      hloH hmidH htab hne
  have hdSplit : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
          E.span_committee mid es) +
        E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
          E.span_committee mid es) := by
    refine hdPPS.trans ((E.weight_mono ?_).trans (weight_union_le _ _))
    intro i hi
    by_cases hs : i ∈ E.span_committee mid es
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hs⟩)
  have hPreSub : ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
      E.span_committee mid es ⊆
        E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    simp only [crossingParentPre, Finset.mem_sdiff]
    exact ⟨E.parentPayloadStuck_subset_parentStuck cfg hi.1, hi.2⟩
  have hPreW := E.weight_add_sdiff hPreSub
  have hSubW := E.weight_add_sdiff hPPSsub
  have hMU' := mu_shift_opp hMU (le_of_eq hPreW)
  have hguard := E.intraEpoch_adversarial_guard cfg ext hbb htab hintra hes hmidH hesH
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := E.hR4b_of_confinement cfg ext hec hv hnH hval hne hesH hspan
  have hbyzfull : E.Bval mid es <=
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [htab]
    exact hbb.span_bound mid es hmidH hesH
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es) + 0 + 0
        <= 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_zero] using hguard.1
  have hAguard : estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
          * cfg.confirmation_byzantine_threshold
      <= get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es + 0 := by
    simpa only [Nat.add_zero] using hguard.2
  have hend := E.reanchored_endpoint_of_fullSpan_certificate_opp
    (v₀ := w) (n₀ := m) (b' := b) (lo := mid) (es := es) (σ := sigma)
    (Bsup := (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum)
    (eqSub := get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es)
    (eqExtra := 0) (HAextra := 0) (Bextra := 0)
    (A := get_adversarial_weight cfg ext (E.store cfg ext v n) bs b)
    (d := get_support_discount cfg ext (E.store cfg ext v n) bs b)
    (MU := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) lo es)
    (qFull := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) mid es / 100)
    (Hpre := E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
      E.span_committee mid es))
    (Hsub := E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
      E.span_committee mid es))
    (xP := E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
      + E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es \
        (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
          E.span_committee mid es)))
    (Bpre := E.weight (E.crossingByzPre lo mid es))
    (boost := get_proposer_score cfg (E.store cfg ext w m))
    (O := E.weight (E.Aclass cfg ext w m b mid es \
      (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
        E.span_committee mid es)))
    cfg ext hbb hesSigma hmidH hSigmaH hbase hMU' hdSplit (le_of_eq hSubW)
      hAguard hdomFull
      (Nat.zero_le _) (Nat.zero_le _) hbyzsub (by simpa using hbyzfull) hAX hxS
  simpa only [Nat.sub_zero] using hend

theorem crossingEdgeFuture_endpoint_inequality_opp
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hwf : ParentSlotLt (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
        (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hbcur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n))
    (hdom : E.WindowRecordedEpochMax cfg ext v n
      ((E.store cfg ext v n).blocks b).slot es)
    (hcross : get_block_epoch cfg (E.store cfg ext v n) b >
      get_block_epoch cfg (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).parent_root)
    (hesSigma : es ≤ sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} {m : ℕ}
    (hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSbase : E.Sval cfg ext v n b ((E.store cfg ext v n).blocks b).slot es ≤
      E.Sval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hPPSsub : ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
        E.span_committee ((E.store cfg ext v n).blocks b).slot es ⊆
      E.Aclass cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
        ≤ E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma ≤
      E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    let sa := compute_start_slot_at_epoch cfg
      (get_block_epoch cfg (E.store cfg ext v n) b)
    E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid sigma
        + (E.weight (E.crossingByzPre lo mid es)
          - E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es))
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
              E.span_committee mid es)) + 1
      ≤ E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext v n).blocks
    ((E.store cfg ext v n).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext v n).blocks b).slot
  let sa := compute_start_slot_at_epoch cfg
    (get_block_epoch cfg (E.store cfg ext v n) b)
  have hlo : lo ≤ sa := parent_slot_succ_le_crossing_start (Root := Root) cfg hcross
  have hsa : sa ≤ mid := start_slot_at_block_epoch_le cfg (E.store cfg ext v n) b
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hnH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext v n))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hsaH : E.SlotWithinHorizon cfg sa :=
    E.slotWithinHorizon_mono cfg hsa hmidH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hsaH
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest :=
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n
      (by assumption) (by assumption)) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost, ← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith_opp hbaseQ hSbase
  have hMUQ := E.crossing_hMU_of_canonicalPre cfg ext hbb htab hes hslotlt hbcur
    hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext v n b mid es + E.Aval cfg ext v n b mid es
        + E.Xval cfg ext v n b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext v n b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hdPPS : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b) :=
    support_discount_le_matching_parent_stuck cfg ext hec hbb hv hnH hval
      hloH hmidH htab hne
  have hdSplit : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
          E.span_committee mid es) +
        E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
          E.span_committee mid es) := by
    refine hdPPS.trans ((E.weight_mono ?_).trans (weight_union_le _ _))
    intro i hi
    by_cases hs : i ∈ E.span_committee mid es
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hs⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hs⟩)
  have hPreSub : ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
      E.span_committee mid es ⊆
        E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    simp only [crossingParentPre, Finset.mem_sdiff]
    exact ⟨E.parentPayloadStuck_subset_parentStuck cfg hi.1, hi.2⟩
  have hPreW := E.weight_add_sdiff hPreSub
  have hSubW := E.weight_add_sdiff hPPSsub
  have hMU' := mu_shift_opp hMU (le_of_eq hPreW)
  have hguard := E.crossing_fullSpan_adversarial_guard cfg ext hbb htab hcross hes
    hsaH hesH
  have hBextra : E.weight (E.crossingByzPre sa mid es) ≤
      E.weight (E.crossingByzPre lo mid es) :=
    E.weight_mono (E.crossingByzPre_mono_lo hlo)
  have heqExtra :
      E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es) ≤
        E.weight (E.crossingByzPre sa mid es) :=
    E.weight_mono (E.crossing_equivPre_subset_byzPre cfg hne)
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := E.hR4b_of_confinement cfg ext hec hv hnH hval hne hesH hspan
  have hbyzfull : E.Bval mid es + E.weight (E.crossingByzPre sa mid es) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [E.crossing_fullSpan_Bval_split hsa, htab]
    exact hbb.span_bound sa es hsaH hesH
  have heqsplit := E.crossing_equivocation_score_split (n := n) (es := es)
    cfg ext hec hv hnH hval hsa hesH
  have hAguard : estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
          * cfg.confirmation_byzantine_threshold
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
        + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es) := by
    calc
      _ ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
          + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es := hguard.2
      _ = get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
          + (get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
            + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es)) := by
              rw [heqsplit]
      _ = _ := (Nat.add_assoc _ _ _).symm
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
  exact E.reanchored_endpoint_of_fullSpan_certificate_opp
    (Hpre := E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
      E.span_committee mid es))
    (Hsub := E.weight (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
      E.span_committee mid es))
    (xP := E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
      + E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es \
        (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b \
          E.span_committee mid es)))
    (O := E.weight (E.Aclass cfg ext w m b mid es \
      (ParentPayloadStuck cfg E (E.store cfg ext v n) bs b ∩
        E.span_committee mid es)))
    cfg ext hbb hesSigma hmidH hSigmaH
    hbase hMU' hdSplit (le_of_eq hSubW) hAguard hdomFull hBextra heqExtra hbyzsub
    hbyzfull hAX hxS


/-- The endpoint score of the opposite resolved status of `a`, re-anchored at
the child slot. Sibling-stuck validators split as in the crossing sibling
bound. Old opposite ancestor voters split by the sub-window: the recurring
part is sub-window ancestor debt, and the rest is pre-region parent debt that
the discount does not use. `EqSet` holds relayed query equivocators. -/
theorem endpoint_opposite_score_le_crossing
    (hA : SelectedMarginAssumptions cfg ext E)
    {v w : ValidatorIndex} {q m : ℕ} {a b : Root} {lo mid es σ : Slot}
    {blocks : List Root} {bsQ : BeaconState Root}
    {EqSet : Finset ValidatorIndex}
    (hv : v ∈ E.honest) (hqH : E.WithinHorizon cfg q)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hesσ : es ≤ σ) (hmidEs : mid ≤ es)
    (hlo : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (hloQ : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
    (haQ : a ∈ (E.store cfg ext v q).block_roots)
    (hbQ : b ∈ (E.store cfg ext v q).block_roots)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root = a)
    (hparentQ : ((E.store cfg ext v q).blocks b).parent_root = a)
    (hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a)
    (hagreeB : (E.store cfg ext v q).blocks b = (E.store cfg ext w m).blocks b)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hselected : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m b t)
    (hEqB : EqSet ⊆ E.crossingByzPre lo mid es)
    (hEqW : EqSet ⊆ (E.store cfg ext w m).equivocating_indices) :
    ∀ other ∈ get_node_children (E.store cfg ext w m) blocks
        (ForkChoiceNode.mk a .pending),
      other ≠ ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)) →
      get_attestation_score cfg (E.store cfg ext w m) other
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint) ≤
        E.weight (E.crossingXPre cfg (E.store cfg ext v q) bsQ b lo mid es)
        + E.weight (E.crossingParentPre cfg (E.store cfg ext v q) bsQ b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b \
              E.span_committee mid es))
        + E.Xval cfg ext w m b mid σ
        + (E.weight (E.crossingByzPre lo mid es) - E.weight EqSet)
        + E.Bval mid σ
        + E.weight (E.Aclass cfg ext w m b mid es \
            (ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b ∩
              E.span_committee mid es)) := by
  classical
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext
    hA.externals_coherence hA.genesis_store hA.domain w hw m hmH
  have hpQ : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hparentA : ParentStuck cfg E (E.store cfg ext v q) bsQ b ⊆
      E.Aclass cfg ext v q b lo es :=
    E.parentStuck_subset_query_Aclass_minimal cfg ext hA hv hqH hbQ hpQ
      hloQ hes hmaxQ
  have hXback : E.Xclass cfg ext w m b lo σ ⊆ E.Xclass cfg ext w m b lo es :=
    E.Xclass_subset_of_committee_support cfg ext hA.honest_behavior
      w m b lo hesσ hsupport
  have hXsplit : E.Xclass cfg ext w m b lo σ ⊆
      E.crossingXPre cfg (E.store cfg ext v q) bsQ b lo mid es ∪
        E.Xclass cfg ext w m b mid σ := by
    intro i hi
    by_cases hiMid : i ∈ E.span_committee mid σ
    · apply Finset.mem_union_right
      have hi' := hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi' ⊢
      exact ⟨⟨hiMid, hi'.1.2⟩, hi'.2⟩
    · apply Finset.mem_union_left
      have hiEndEs := hXback hi
      have hiEndEs' := hiEndEs
      simp only [Execution.Xclass, Finset.mem_filter] at hiEndEs'
      have hiQuery : i ∈ E.Xclass cfg ext v q b lo es := by
        simp only [Execution.Xclass, Finset.mem_filter]
        exact ⟨hiEndEs'.1,
          fun hS => hiEndEs'.2.1 (hSt i hiEndEs'.1.2 hiEndEs'.1.1 hS),
          fun hAnc => hiEndEs'.2.2 (hAt i hiEndEs'.1.2 hiEndEs'.1.1 hAnc)⟩
      have hiNotMidEs : i ∉ E.span_committee mid es := by
        intro hiMidEs
        exact hiMid (E.span_committee_mono mid hesσ hiMidEs)
      exact mem_crossingXPre_of_query_Xclass_not_mid (E := E) cfg ext hparentA
        hiQuery hiNotMidEs
  have hBsplit : E.Bwin lo σ ⊆ E.crossingByzPre lo mid es ∪ E.Bwin mid σ :=
    Bwin_subset_crossingByzPre_union (E := E) (lo := lo) hmidEs hesσ
  have hEqWeight : E.weight EqSet +
      E.weight (E.crossingByzPre lo mid es \ EqSet) =
      E.weight (E.crossingByzPre lo mid es) := E.weight_add_sdiff hEqB
  have hBdiff : E.weight (E.crossingByzPre lo mid es \ EqSet) =
      E.weight (E.crossingByzPre lo mid es) - E.weight EqSet :=
    Nat.eq_sub_of_add_eq' hEqWeight
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
  have hHon := E.endpoint_opposite_honest_classification cfg ext hA
    (bsQ := bsQ) hv hqH hw hmH hes hσ hesσ hlo haM hbM hparentM hparentQ
    hagreeA hagreeB hmaxQ hmaxW hselected hsupport ho hneo
  have hByz := E.endpoint_opposite_byzantine_window cfg ext hA
    (bsW := (E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) hw hmH hσ hlo haM ho
  rw [attestation_score_eq_weight cfg hvalEnd]
  let XP := E.crossingXPre cfg (E.store cfg ext v q) bsQ b lo mid es
  let OP := E.crossingParentPre cfg (E.store cfg ext v q) bsQ b mid es \
    (ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b \ E.span_committee mid es)
  let Xm := E.Xclass cfg ext w m b mid σ
  let BP := E.crossingByzPre lo mid es \ EqSet
  let Bm := E.Bwin mid σ
  let OA := E.Aclass cfg ext w m b mid es \
    (ParentPayloadStuck cfg E (E.store cfg ext v q) bsQ b ∩ E.span_committee mid es)
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
            simp only [crossingHonestPre, crossingPreRegion, Finset.mem_filter,
              Finset.mem_sdiff]
            exact ⟨⟨hiA'.1.1, hs⟩, hh⟩
          by_cases hpp : i ∈ E.crossingParentPre cfg (E.store cfg ext v q) bsQ b mid es
          · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
              (Finset.mem_sdiff.mpr ⟨hpp, ?_⟩)))))
            intro hin
            exact hiNotPPS (Finset.mem_sdiff.mp hin).1
          · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))
            change i ∈ E.crossingXPre cfg (E.store cfg ext v q) bsQ b lo mid es
            rw [crossingXPre, Finset.mem_sdiff]
            exact ⟨hiPre, hpp⟩
    · rcases Finset.mem_union.mp (hBsplit (hByz i hiSupp hh)) with hBP | hBm
      · refine Or.inl (Or.inl (Or.inr (Finset.mem_sdiff.mpr ⟨hBP, ?_⟩)))
        intro hEq
        obtain ⟨_lm, _hlm, hiNotEquiv, _⟩ := mem_AttSupporters cfg hiSupp
        exact hiNotEquiv (hEqW hEq)
      · exact Or.inl (Or.inr hBm)
  calc
    _ ≤ E.weight (((((XP ∪ OP) ∪ Xm) ∪ BP) ∪ Bm) ∪ OA) := E.weight_mono hsub
    _ ≤ E.weight XP + E.weight OP + E.weight Xm + E.weight BP + E.weight Bm +
          E.weight OA := E.weight_union6_le XP OP Xm BP Bm OA
    _ = _ := by
      simp only [BP]
      rw [hBdiff]
      rfl

/-- The pending-parent status margin for the two crossing arms. The endpoint
inequality is the re-anchored full-span certificate with the opposite debt. -/
theorem statusMargin_crossing_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {a c : Root} {lo es σ : Slot}
    (haQ : a ∈ (E.store cfg ext v q).block_roots)
    (hcQ : c ∈ (E.store cfg ext v q).block_roots)
    (hparentQ : ((E.store cfg ext v q).blocks c).parent_root = a)
    (haM : a ∈ (E.store cfg ext w m).block_roots)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks c).parent_root = a)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) c = true)
    (hloQ : lo = ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks c).parent_root).slot + 1)
    (hloW : lo = ((E.store cfg ext w m).blocks a).slot + 1)
    (hlo₀ : E.slot_at cfg 0 ≤ lo)
    (hes : es = get_current_slot cfg (E.store cfg ext v q) - 1)
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hσlt : σ < E.slot_at cfg m)
    (hesσ : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hmidEs : ((E.store cfg ext v q).blocks c).slot ≤ es)
    (hmaxQ : E.WindowRecordedEpochMax cfg ext v q lo es)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q c es i → E.SupportsDesc cfg ext w m c es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q c es i →
        E.AncestorOrVoteless cfg ext w m c es i)
    (hmaxMid : E.WindowRecordedEpochMax cfg ext v q
      ((E.store cfg ext v q).blocks c).slot es)
    (hStMid : ∀ i, i ∈ E.honest →
      i ∈ E.span_committee ((E.store cfg ext v q).blocks c).slot es →
      E.SupportsDesc cfg ext v q c es i → E.SupportsDesc cfg ext w m c es i)
    (hAtMid : ∀ i, i ∈ E.honest →
      i ∈ E.span_committee ((E.store cfg ext v q).blocks c).slot es →
      E.AncestorOrVoteless cfg ext v q c es i →
        E.AncestorOrVoteless cfg ext w m c es i)
    (hsupport : ∀ t : Slot, es < t → t ≤ σ →
      E.CommitteeSupportsAt cfg ext w m c t)
    (hselectedLo : ∀ i ∈ E.Sclass cfg ext w m c lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hselectedMid : ∀ i ∈ E.Sclass cfg ext w m c
        ((E.store cfg ext v q).blocks c).slot σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hregime : get_block_epoch cfg (E.store cfg ext v q) c =
        get_block_epoch cfg (E.store cfg ext v q)
          ((E.store cfg ext v q).blocks c).parent_root ∨
      (get_block_epoch cfg (E.store cfg ext v q) c >
          get_block_epoch cfg (E.store cfg ext v q)
            ((E.store cfg ext v q).blocks c).parent_root ∧
        E.slot_at cfg q + 1 ≤ E.slot_at cfg m)) :
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v q) bs c = true := by
    simpa only [bs, hquery] using hconf
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hquery]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp c
    rw [← hbsEq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      v q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence v q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q hv hqH
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root c) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q) ((E.store cfg ext v q).blocks c).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK c hcQ lm.root hlmKnown
  have hpQ : ((E.store cfg ext v q).blocks c).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    rw [hparentQ]
    exact haQ
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks c).parent_root).slot <
      ((E.store cfg ext v q).blocks c).slot :=
    hwf c hcQ hpQ
  have hbcur : ((E.store cfg ext v q).blocks c).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v q c hcQ
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
  have hSbase := (E.classes_base_transport_honest cfg ext v w q m c
    ((E.store cfg ext v q).blocks c).slot es hStMid hAtMid).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m c
    ((E.store cfg ext v q).blocks c).slot hesσ hsupport
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m c
    ((E.store cfg ext v q).blocks c).slot hesσ hsupport
  have hagreeA : (E.store cfg ext v q).blocks a = (E.store cfg ext w m).blocks a :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m) haQ haM
  have hagreeC : (E.store cfg ext v q).blocks c = (E.store cfg ext w m).blocks c :=
    hA.wellFormed.blocks_agree (E.blockProvenance cfg ext v q)
      (E.blockProvenance cfg ext w m) hcQ hcM
  have hmaxW : E.WindowRecordedEpochMax cfg ext w m lo es :=
    E.WindowRecordedEpochMax_mono_end cfg ext hesσ
      (E.windowRecordedEpochMax_at_query_minimal cfg ext hA hwalkDomain
        hw hmH hlo₀ hσ hσlt)
  have hmaxQ' : E.WindowRecordedEpochMax cfg ext v q
      (((E.store cfg ext v q).blocks
        ((E.store cfg ext v q).blocks c).parent_root).slot + 1) es := by
    rw [← hloQ]
    exact hmaxQ
  have hPS := E.parentStuck_endpoint_Aclass_minimal cfg ext hA
    (bs := bs) hv hqH hes haQ hcQ hparentQ haM hcM hparentM hmaxQ'
  have hPPSsub : ParentPayloadStuck cfg E (E.store cfg ext v q) bs c ∩
      E.span_committee ((E.store cfg ext v q).blocks c).slot es ⊆
      E.Aclass cfg ext w m c ((E.store cfg ext v q).blocks c).slot es := by
    intro i hi
    obtain ⟨hiP, hiS⟩ := Finset.mem_inter.mp hi
    exact (hPS i (E.parentPayloadStuck_subset_parentStuck cfg hiP)).2 _ hiS
  -- Endpoint facts shared by both crossing regimes.
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
    hA.wellFormed v w q m
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
    obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hprovW i lm hlm
    exact hwalkKW _ hpM lm.root hk
  have hsel := E.selected_parent_score_ge_Sval cfg ext hvalEnd hpslW hcM hpM
    hwalkB hselectedMid
  rw [hparentM] at hsel
  rcases hregime with hintra | ⟨hcross, hrelay⟩
  · have hend := E.intraEpochFuture_endpoint_inequality_opp cfg ext
      hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hv hqH
      hwf hval htab hprov hconf' hwalk hes hslotlt hbcur hmaxMid hintra hesσ hσH
      hboost hSbase hPPSsub hAX hxS
    dsimp only at hend
    rw [← hloQ] at hend
    have hend' : E.weight (E.crossingXPre cfg (E.store cfg ext v q) bs c lo
          ((E.store cfg ext v q).blocks c).slot es)
        + E.weight (E.crossingParentPre cfg (E.store cfg ext v q) bs c
            ((E.store cfg ext v q).blocks c).slot es \
          (ParentPayloadStuck cfg E (E.store cfg ext v q) bs c \
            E.span_committee ((E.store cfg ext v q).blocks c).slot es))
        + E.Xval cfg ext w m c ((E.store cfg ext v q).blocks c).slot σ
        + (E.weight (E.crossingByzPre lo ((E.store cfg ext v q).blocks c).slot es)
          - E.weight (∅ : Finset ValidatorIndex))
        + E.Bval ((E.store cfg ext v q).blocks c).slot σ
        + get_proposer_score cfg (E.store cfg ext w m)
        + E.weight (E.Aclass cfg ext w m c ((E.store cfg ext v q).blocks c).slot es \
          (ParentPayloadStuck cfg E (E.store cfg ext v q) bs c ∩
            E.span_committee ((E.store cfg ext v q).blocks c).slot es)) + 1
        ≤ E.Sval cfg ext w m c ((E.store cfg ext v q).blocks c).slot σ := by
      have hzero : E.weight (∅ : Finset ValidatorIndex) = 0 := Finset.sum_empty
      rw [hzero, Nat.sub_zero]
      exact hend
    have hopp := E.endpoint_opposite_score_le_crossing cfg ext hA
      (blocks := get_filtered_block_tree cfg (E.store cfg ext w m)) (bsQ := bs)
      (EqSet := ∅) hv hqH hw hmH hes hσ hesσ hmidEs hloW hloQ haQ hcQ haM hcM
      hparentM hparentQ hagreeA hagreeC hmaxQ hmaxW hSt hAt hselectedLo hsupport
      (Finset.empty_subset _) (Finset.empty_subset _)
    exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hend' hopp
  · have hend := E.crossingEdgeFuture_endpoint_inequality_opp cfg ext
      hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hv hqH
      hwf hval htab hprov hconf' hwalk hes hslotlt hbcur hmaxMid hcross hesσ hσH
      hboost hSbase hPPSsub hAX hxS
    dsimp only at hend
    rw [← hloQ] at hend
    let sa := compute_start_slot_at_epoch cfg
      (get_block_epoch cfg (E.store cfg ext v q) c)
    have hne : ∀ i ∈ (E.store cfg ext v q).equivocating_indices, i ∉ E.honest :=
      fun i hi hih =>
        (Execution.honest_not_equivocating cfg ext hA.honest_behavior
          hA.externals_coherence hgen hih v q hv hqH) hi
    have hloSa : lo ≤ sa := by
      dsimp only [sa]
      rw [hloQ]
      exact parent_slot_succ_le_crossing_start (Root := Root) cfg hcross
    have hEqB : E.crossingEquivPre cfg (E.store cfg ext v q) bs sa
        ((E.store cfg ext v q).blocks c).slot es ⊆
        E.crossingByzPre lo ((E.store cfg ext v q).blocks c).slot es := by
      intro i hi
      exact E.crossingByzPre_mono_lo hloSa
        (E.crossing_equivPre_subset_byzPre cfg hne hi)
    have hEqW : E.crossingEquivPre cfg (E.store cfg ext v q) bs sa
        ((E.store cfg ext v q).blocks c).slot es ⊆
        (E.store cfg ext w m).equivocating_indices := by
      intro i hi
      have hiQ : i ∈ (E.store cfg ext v q).equivocating_indices := by
        simp only [crossingEquivPre, EquivActive, Finset.mem_sdiff,
          Finset.mem_filter, Finset.mem_inter] at hi
        exact hi.1.1.2
      exact E.equiv_subset_of_relay cfg ext hA.synchrony hv hw hqH hmH hrelay hiQ
    have hopp := E.endpoint_opposite_score_le_crossing cfg ext hA
      (blocks := get_filtered_block_tree cfg (E.store cfg ext w m)) (bsQ := bs)
      hv hqH hw hmH hes hσ hesσ hmidEs hloW hloQ haQ hcQ haM hcM
      hparentM hparentQ hagreeA hagreeC hmaxQ hmaxW hSt hAt hselectedLo hsupport
      hEqB hEqW
    exact pendingStatusMargin_of_strip cfg hmem hnotPrev hsel hend hopp

end Execution

end FastConfirmation.Spec

end
