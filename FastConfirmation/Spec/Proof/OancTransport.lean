module
public import FastConfirmation.Spec.Proof.Endpoint
public import FastConfirmation.Spec.Proof.EngineTransport
public import FastConfirmation.Spec.Proof.StepDischarge

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Epoch maximality over a longer window restricts to an earlier cutoff. -/
theorem WindowRecordedEpochMax_mono_end
    {w : ValidatorIndex} {m : ℕ} {lo es σ : Slot}
    (hesσ : es ≤ σ)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo σ) :
    E.WindowRecordedEpochMax cfg ext w m lo es := by
  intro i hi hiSpan lm hlm t k a ht hvote
  exact hmax i hi (E.span_committee_mono lo hesσ hiSpan)
    lm hlm t k a (ht.trans hesσ) hvote

/-- A message recorded at the confirming store has a slot in its completed
vote window. This is the validation gate in latest-message provenance. -/
theorem recorded_slot_le_completed_cutoff
    {v i : ValidatorIndex} {n : ℕ} {es : Slot} {lm : LatestMessage Root}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hlm : (E.store cfg ext v n).latest_messages i = some lm) :
    lm.slot ≤ es := by
  obtain ⟨a, _, _, _, _, hgate, _, _, _, hslot⟩ := hprov i lm hlm
  rw [hslot, hes]
  exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hgate)

/-- Completed-window delivery coverage supplies a source message for an
honest endpoint message from the old window. Exact scheduled provenance
identifies the honest vote that the coverage theorem applies to. -/
theorem old_message_recorded_at_source_of_coverage
    (hhb : HonestBehavior cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w i : ValidatorIndex} {n m : ℕ} {es : Slot} {dst : LatestMessage Root}
    (hi : i ∈ E.honest)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hold : dst.slot ≤ es)
    (hcover : ∀ t k (a : Attestation Root), t ≤ es →
      E.vote i t = some (k, a) →
      ∃ src, (E.store cfg ext v n).latest_messages i = some src ∧
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg src) :
    ∃ src, (E.store cfg ext v n).latest_messages i = some src := by
  obtain ⟨a, u, t, ifb, hsched, hia, hmsg⟩ :=
    E.schedLMProvExact cfg ext hgen w m i dst hdst
  obtain ⟨k, a', hvote, _⟩ := hhb.no_forgery u t a ifb hsched i hi hia
  have ht : a.data.slot ≤ es := by simpa only [hmsg] using hold
  obtain ⟨src, hsrc, _⟩ := hcover a.data.slot k a' ht hvote
  exact ⟨src, hsrc⟩

/-- The confirming store's old-window epoch maximality identifies its
recorded message with the validator's newest genuine vote by `es`. -/
theorem old_source_recorded_is_newest
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v i : ValidatorIndex} {n : ℕ} {lo es : Slot}
    {src : LatestMessage Root}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hmax : E.WindowRecordedEpochMax cfg ext v n lo es)
    (hi : i ∈ E.honest) (hiSpan : i ∈ E.span_committee lo es)
    (hsrc : (E.store cfg ext v n).latest_messages i = some src) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = src.root :=
  E.recorded_lm_is_newest_at cfg ext hhb hec hgen hprov hes hi hsrc
    (hmax i hi hiSpan src hsrc)

/-- An old ancestor-class member remains in the source ancestor class when
the source message is the same old vote seen at the endpoint. The forward
support transport excludes the source supporter class; the ancestor witness
returns by block agreement on the source walk. -/
theorem Aclass_back_of_old_message
    {v w i : ValidatorIndex} {n m : ℕ} {b : Root} {lo es : Slot}
    {src : LatestMessage Root}
    (hA : i ∈ E.Aclass cfg ext w m b lo es)
    (hSt : E.SupportsDesc cfg ext v n b es i →
      E.SupportsDesc cfg ext w m b es i)
    (hnew : ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = src.root)
    (hbr : b ∈ (E.store cfg ext v n).block_roots)
    (hsrcRoot : src.root ∈ (E.store cfg ext v n).block_roots)
    (hwalk : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks src.root).slot b)
    (hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x) :
    i ∈ E.Aclass cfg ext v n b lo es := by
  simp only [Execution.Aclass, Finset.mem_filter] at hA ⊢
  refine ⟨hA.1, ?_, ?_⟩
  · intro hS
    exact hA.2.1 (hSt hS)
  · rcases hA.2.2 with hvoteless | ⟨t, k, a, ht, hvote, hnewEnd, hancEnd⟩
    · exact Or.inl hvoteless
    · obtain ⟨t0, k0, a0, ht0, hvote0, hnew0, hroot0⟩ := hnew
      have htt : t = t0 := newest_vote_unique
        (by rw [hvote]; exact Option.some_ne_none _) hnewEnd
        (by rw [hvote0]; exact Option.some_ne_none _) hnew0 ht ht0
      rw [htt] at hvote
      have ha : a = a0 := congrArg Prod.snd (Option.some.inj (hvote.symm.trans hvote0))
      have hancEnd' : is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root src.root) = true := by
        rw [ha, hroot0] at hancEnd
        exact hancEnd
      refine Or.inr ⟨t0, k0, a0, ht0, hvote0, hnew0, ?_⟩
      have hEq := is_ancestor_congr hagree hbr hsrcRoot hwalk
        (node := get_node_for_root b) (ancestor := get_node_for_root src.root)
      rw [hroot0]
      exact hEq.trans hancEnd'

/-- A same-message opposite supporter at the endpoint is also a source
supporter when the source balance state admits the honest validator. The
complete message equality preserves the payload bit, and block agreement
preserves the resolved ancestry test. -/
theorem opposite_supporter_back_of_old_message
    {v w i : ValidatorIndex} {n m : ℕ} {h : Root}
    {other : PayloadStatus} {bsSrc bsDst : BeaconState Root}
    {src dst : LatestMessage Root}
    (hopp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bsDst)
    (hsrc : (E.store cfg ext v n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hmsg : src = dst)
    (hact : i ∈ get_active_validator_indices bsSrc (get_current_epoch cfg bsSrc))
    (huns : (bsSrc.validators.getD i default).slashed = false)
    (hne : i ∉ (E.store cfg ext v n).equivocating_indices)
    (hsrcRoot : src.root ∈ (E.store cfg ext v n).block_roots)
    (hh : h ∈ (E.store cfg ext v n).block_roots)
    (hwalk : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks h).slot src.root)
    (hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x) :
    i ∈ AttSupporters cfg (E.store cfg ext v n)
      (ForkChoiceNode.mk h other) bsSrc := by
  obtain ⟨lm, hlm, _, hsuppEnd⟩ := mem_AttSupporters cfg hopp
  have hlmEq : lm = dst := Option.some.inj (hlm.symm.trans hdst)
  subst lm
  rw [← hmsg] at hsuppEnd
  have hnodeEq : get_supported_node (E.store cfg ext v n) src =
      get_supported_node (E.store cfg ext w m) src := by
    simp only [get_supported_node]
    rw [hagree src.root hsrcRoot]
  have hAncEq := is_ancestor_congr hagree hsrcRoot hh hwalk
    (node := get_supported_node (E.store cfg ext v n) src)
    (ancestor := ForkChoiceNode.mk h other)
  have hsuppSrc : is_ancestor (E.store cfg ext v n)
      (get_supported_node (E.store cfg ext v n) src)
      (ForkChoiceNode.mk h other) = true := by
    rw [hAncEq, hnodeEq]
    exact hsuppEnd
  exact mem_AttSupporters_of cfg hact huns hsrc hne hsuppSrc

/-- The old-window part of the opposite ancestor class transports back to the
confirming store. Its dynamic inputs are the same forward support transport,
recorded epoch maximality, and source walk facts used by the root ledger. -/
theorem oppositeAncestorClass_old_back
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w i : ValidatorIndex} {n m : ℕ} {b h : Root}
    {lo es : Slot} {other : PayloadStatus}
    {bsSrc bsDst : BeaconState Root} {src dst : LatestMessage Root}
    (hiO : i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext w m)
      bsDst w m b h lo es other)
    (hsrc : (E.store cfg ext v n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hsrcSlot : src.slot ≤ es) (hdstSlot : dst.slot ≤ es)
    (hmaxSrc : E.WindowRecordedEpochMax cfg ext v n lo es)
    (hmaxDst : E.WindowRecordedEpochMax cfg ext w m lo es)
    (hSt : E.SupportsDesc cfg ext v n b es i →
      E.SupportsDesc cfg ext w m b es i)
    (hnew : ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = src.root)
    (hact : i ∈ get_active_validator_indices bsSrc (get_current_epoch cfg bsSrc))
    (huns : (bsSrc.validators.getD i default).slashed = false)
    (hne : i ∉ (E.store cfg ext v n).equivocating_indices)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hh : h ∈ (E.store cfg ext v n).block_roots)
    (hsrcRoot : src.root ∈ (E.store cfg ext v n).block_roots)
    (hwalkA : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks src.root).slot b)
    (hwalkOpp : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks h).slot src.root)
    (hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x) :
    i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext v n)
      bsSrc v n b h lo es other := by
  have hiA := (Finset.mem_inter.mp hiO).1
  have hiOpp := List.mem_toFinset.mp (Finset.mem_inter.mp hiO).2
  have hiHon : i ∈ E.honest := by
    simp only [Execution.Aclass, Finset.mem_filter] at hiA
    exact hiA.1.2
  have hiSpan : i ∈ E.span_committee lo es := by
    simp only [Execution.Aclass, Finset.mem_filter] at hiA
    exact hiA.1.1
  have hmsg := E.old_window_latest_messages_agree_window cfg ext hhb hec hgen
    hiHon hiSpan hsrc hdst hsrcSlot hdstSlot hmaxSrc hmaxDst
  have hiASrc := E.Aclass_back_of_old_message cfg ext hiA hSt hnew
    hb hsrcRoot hwalkA hagree
  have hiOppSrc := E.opposite_supporter_back_of_old_message cfg ext hiOpp
    hsrc hdst hmsg hact huns hne hsrcRoot hh hwalkOpp hagree
  exact Finset.mem_inter.mpr ⟨hiASrc, List.mem_toFinset.mpr hiOppSrc⟩

/-- A later-window honest vote cannot support the opposite resolved parent.
The existing new-voter induction makes the recorded message support `c`; a
child supporter also selects `c`'s required parent status. -/
theorem opposite_supporter_not_newvote
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w i : ValidatorIndex} {m : ℕ} {b h c : Root}
    {s k : Slot} {selected other : PayloadStatus}
    {bs : BeaconState Root} {lm : LatestMessage Root}
    (hi : i ∈ E.honest) (hw : w ∈ E.honest)
    (hmH : E.WithinHorizon cfg m)
    (hslot_m : E.slot_at cfg m = k)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hopp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bs)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hlate : s ≤ lm.slot)
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected)
    (hIH : ∀ j ∈ E.honest, ∀ t'' : Slot, s ≤ t'' → t'' < k →
      ∀ jj (a' : Attestation Root), E.vote j t'' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwa : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c).slot lm.root)
    (hwb : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks c).slot b)
    (hbc : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk c .pending) = true)
    (hchildSubset : (AttSupporters cfg (E.store cfg ext w m)
        (get_node_for_root c) bs).toFinset ⊆
      (AttSupporters cfg (E.store cfg ext w m)
        (ForkChoiceNode.mk h selected) bs).toFinset) :
    False := by
  obtain ⟨a, _, _, _, hepoch, _, hcomm, _, _, hslot⟩ := hprov i lm hlm
  have hcomm' : i ∈ E.committee lm.slot := by rw [hslot]; exact hcomm
  have hepge : compute_epoch_at_slot cfg lm.slot ≤
      get_latest_message_epoch cfg lm := by
    rw [hslot]
    exact le_of_eq hepoch
  have hc := newvoter_recorded_supports_c_of_IH cfg ext hwf hhb hec hgen
    hi hcomm' hlate hlm hepge hslot_m hIH hwf_pl hwa hwb hbc hw hmH
  exact opposite_supporter_excludes_child cfg hselected hother hne
    hopp hlm hc hchildSubset

/-- If a later store's recorded honest message still comes from the old
window, no genuine vote by that validator in the intervening window can be
missing from the message. Epoch maximality rules out a newer epoch; unique
committee assignment rules out a second vote in the same epoch. -/
theorem no_vote_after_old_recorded_message
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    {w i : ValidatorIndex} {m : ℕ} {lo es σ : Slot}
    {lm : LatestMessage Root}
    (hi : i ∈ E.honest) (hiSpan : i ∈ E.span_committee lo σ)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo σ)
    (hold : lm.slot ≤ es) :
    ∀ t : Slot, es < t → t ≤ σ → E.vote i t = none := by
  intro t het htσ
  cases hvote : E.vote i t with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨k, a⟩ := p
    obtain ⟨a0, _, _, _, _, _, hcomm0, _, _, hslot⟩ := hprov i lm hlm
    have hcommOld : i ∈ E.committee lm.slot := by rw [hslot]; exact hcomm0
    have hcommNew : i ∈ E.committee t :=
      hhb.votes_assigned i hi t (by rw [hvote]; exact Option.some_ne_none _)
    have hMax := hmax i hi hiSpan lm hlm t k a htσ hvote
    have hMon : compute_epoch_at_slot cfg lm.slot ≤ compute_epoch_at_slot cfg t := by
      simp only [compute_epoch_at_slot]
      exact Nat.div_le_div_right (hold.trans (Nat.le_of_lt het))
    have hEq : compute_epoch_at_slot cfg lm.slot = compute_epoch_at_slot cfg t := by
      apply Nat.le_antisymm hMon
      simpa only [get_latest_message_epoch] using hMax
    have htEq := hec.committee_assignment_unique i lm.slot t hcommOld hcommNew hEq
    exact (Nat.ne_of_lt (lt_of_le_of_lt hold het)) htEq

/-- An endpoint ancestor-class member whose genuine votes stop by `es`
belongs to the same class at the old cutoff. -/
theorem Aclass_old_cutoff_of_no_late_vote
    {w i : ValidatorIndex} {m : ℕ} {b : Root} {lo es σ : Slot}
    (hesσ : es ≤ σ)
    (hiOldSpan : i ∈ E.span_committee lo es)
    (hAσ : i ∈ E.Aclass cfg ext w m b lo σ)
    (hNoLate : ∀ t : Slot, es < t → t ≤ σ → E.vote i t = none) :
    i ∈ E.Aclass cfg ext w m b lo es := by
  simp only [Execution.Aclass, Finset.mem_filter] at hAσ ⊢
  refine ⟨⟨hiOldSpan, hAσ.1.2⟩, ?_, ?_⟩
  · intro hSes
    apply hAσ.2.1
    obtain ⟨t, k, a, ht, hvote, hnew, hanc⟩ := hSes
    refine ⟨t, k, a, ht.trans hesσ, hvote, ?_, hanc⟩
    intro t' htt htσ
    by_cases hte : t' ≤ es
    · exact hnew t' htt hte
    · exact hNoLate t' (Nat.lt_of_not_le hte) htσ
  · rcases hAσ.2.2 with hvoteless | ⟨t, k, a, htσ, hvote, hnew, hanc⟩
    · exact Or.inl (fun t ht => hvoteless t (ht.trans hesσ))
    · have ht : t ≤ es := by
        by_contra hnot
        have hzero := hNoLate t (Nat.lt_of_not_le hnot) htσ
        rw [hvote] at hzero
        contradiction
      exact Or.inr ⟨t, k, a, ht, hvote,
        (fun t' htt hte => hnew t' htt (hte.trans hesσ)), hanc⟩

/-- An old recorded supporter of a resolved parent belongs to the old
committee window. The resolved status forces its message slot strictly after
the parent's block slot, including when the message names that parent itself. -/
theorem old_resolved_supporter_mem_span
    {store : Store Root} {bs : BeaconState Root} {h : Root}
    {status : PayloadStatus} {i : ValidatorIndex} {lm : LatestMessage Root}
    {lo es : Slot}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hresolved : status ≠ .pending)
    (hopp : i ∈ AttSupporters cfg store (ForkChoiceNode.mk h status) bs)
    (hlm : store.latest_messages i = some lm)
    (hwalk : WalkKnown store (store.blocks h).slot lm.root)
    (hlo : lo ≤ (store.blocks h).slot + 1)
    (hold : lm.slot ≤ es) :
    i ∈ E.span_committee lo es := by
  obtain ⟨lm0, hlm0, _, hsupport0⟩ := mem_AttSupporters cfg hopp
  have heq : lm0 = lm := Option.some.inj (hlm0.symm.trans hlm)
  subst lm0
  obtain ⟨a, _, _, _, _, _, hcomm, _, hblock, hslotEq⟩ := hprov i lm hlm
  have hanc : (get_ancestor store (get_supported_node store lm)
        (store.blocks h).slot).root = h := by
    have hsupport' := hsupport0
    simp only [is_ancestor, Bool.and_eq_true, decide_eq_true_eq] at hsupport'
    exact hsupport'.1
  have hrootLe : (store.blocks h).slot ≤ (store.blocks lm.root).slot := by
    have hbound := get_ancestor_slot_le_status hwf hwalk
      (get_supported_node store lm).payload_status
    change (store.blocks
        (get_ancestor store (get_supported_node store lm)
          (store.blocks h).slot).root).slot ≤ (store.blocks lm.root).slot at hbound
    rw [hanc] at hbound
    exact hbound
  have hlower : (store.blocks h).slot < lm.slot := by
    rcases hrootLe.lt_or_eq with hlt | heq
    · rw [hslotEq]
      exact hlt.trans_le hblock
    · have hstop : get_ancestor store (get_supported_node store lm)
          (store.blocks h).slot = get_supported_node store lm :=
        get_ancestor_stop_status (by
          change (store.blocks lm.root).slot ≤ (store.blocks h).slot
          exact le_of_eq heq.symm)
      rw [hstop] at hanc
      have hsame : lm.root = h := by
        simpa only [get_supported_node] using hanc
      have hown : is_ancestor store (get_supported_node store lm)
          (ForkChoiceNode.mk lm.root status) = true := by
        simpa only [hsame] using hsupport0
      have hafter := (supported_node_own_root_resolved_iff store lm status hresolved).mp hown
      simpa only [hsame] using hafter.1
  refine Finset.mem_biUnion.mpr ⟨lm.slot, Finset.mem_Icc.mpr ⟨?_, hold⟩, ?_⟩
  · exact hlo.trans (Nat.succ_le_of_lt hlower)
  · rw [hslotEq]
    exact hcomm

/-- The old-message part of the endpoint's growing opposite ancestor class
lies in its class at the fixed source cutoff. -/
theorem oppositeAncestorClass_old_cutoff
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    {w i : ValidatorIndex} {m : ℕ} {b h : Root}
    {lo es σ : Slot} {status : PayloadStatus} {bs : BeaconState Root}
    {lm : LatestMessage Root}
    (hesσ : es ≤ σ)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo σ)
    (hresolved : status ≠ .pending)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1)
    (hwalk : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks h).slot lm.root)
    (hiO : i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext w m)
      bs w m b h lo σ status)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hold : lm.slot ≤ es) :
    i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext w m)
      bs w m b h lo es status := by
  have hiAσ := (Finset.mem_inter.mp hiO).1
  have hiOpp := List.mem_toFinset.mp (Finset.mem_inter.mp hiO).2
  have hiHon : i ∈ E.honest := by
    simp only [Execution.Aclass, Finset.mem_filter] at hiAσ
    exact hiAσ.1.2
  have hiSpanσ : i ∈ E.span_committee lo σ := by
    simp only [Execution.Aclass, Finset.mem_filter] at hiAσ
    exact hiAσ.1.1
  have hiOldSpan := E.old_resolved_supporter_mem_span cfg hwf hprov
    hresolved hiOpp hlm hwalk hlo hold
  have hNoVote := E.no_vote_after_old_recorded_message cfg ext hhb hec
    hiHon hiSpanσ hlm hprov hmax hold
  have hiAes := E.Aclass_old_cutoff_of_no_late_vote cfg ext hesσ
    hiOldSpan hiAσ hNoVote
  exact Finset.mem_inter.mpr ⟨hiAes, List.mem_toFinset.mpr hiOpp⟩

/-- Old opposite ancestor voters at a later honest endpoint belong to the
confirming store's fixed debt class. Delivery coverage supplies the source
cell; provenance, epoch maximality, and block agreement identify its message
and resolved ancestry. The remaining premises are existing execution-domain
facts rather than an added assumption field. -/
theorem oppositeAncestorClass_old_back_of_execution
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w i : ValidatorIndex} {n m : ℕ} {b h : Root}
    {lo es σ : Slot} {other : PayloadStatus}
    {bsSrc bsDst : BeaconState Root} {dst : LatestMessage Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hnH : E.WithinHorizon cfg n) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hesH : E.SlotWithinHorizon cfg es) (hesσ : es ≤ σ)
    (hval : bsSrc.validators = E.registry)
    (hbsH : get_current_epoch cfg bsSrc < E.verification_horizon)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hh : h ∈ (E.store cfg ext v n).block_roots)
    (hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext w m).block_roots)
    (hwalkSrc : ∀ t ∈ (E.store cfg ext v n).block_roots,
      ∀ r ∈ (E.store cfg ext v n).block_roots,
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks t).slot r)
    (hwalkDst : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hwfDst : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hprovSrc : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hprovDst : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hmaxSrc : E.WindowRecordedEpochMax cfg ext v n lo es)
    (hmaxDst : E.WindowRecordedEpochMax cfg ext w m lo σ)
    (hcover : ∀ t k (a : Attestation Root), t ≤ es →
      E.vote i t = some (k, a) →
      ∃ src, (E.store cfg ext v n).latest_messages i = some src ∧
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg src)
    (hSt : E.SupportsDesc cfg ext v n b es i →
      E.SupportsDesc cfg ext w m b es i)
    (hother : other ≠ .pending)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1)
    (hiO : i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext w m)
      bsDst w m b h lo σ other)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hold : dst.slot ≤ es) :
    i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext v n)
      bsSrc v n b h lo es other := by
  have hiAσ := (Finset.mem_inter.mp hiO).1
  have hiHon : i ∈ E.honest := by
    simp only [Execution.Aclass, Finset.mem_filter] at hiAσ
    exact hiAσ.1.2
  obtain ⟨src, hsrc⟩ := E.old_message_recorded_at_source_of_coverage
    cfg ext hhb hgen hiHon hdst hold hcover
  have hsrcSlot := E.recorded_slot_le_completed_cutoff cfg ext hes hprovSrc hsrc
  obtain ⟨aSrc, _, _, _, _, _, _, hsrcRoot, _, _⟩ := hprovSrc i src hsrc
  obtain ⟨aDst, _, _, _, _, _, _, hdstRoot, _, _⟩ := hprovDst i dst hdst
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x := by
    intro x hx
    exact hwf.blocks_agree (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext w m) hx (hsub hx)
  have hiOes := E.oppositeAncestorClass_old_cutoff cfg ext hhb hec hesσ
    hwfDst hprovDst hmaxDst hother hlo
    (hwalkDst h (hsub hh) dst.root hdstRoot) hiO hdst hold
  have hiOldSpan : i ∈ E.span_committee lo es := by
    have hiA := (Finset.mem_inter.mp hiOes).1
    simp only [Execution.Aclass, Finset.mem_filter] at hiA
    exact hiA.1.1
  have hnew := E.old_source_recorded_is_newest cfg ext hhb hec hgen
    hes hprovSrc hmaxSrc hiHon hiOldSpan hsrc
  obtain ⟨t, k, a, ht, hvote, hlater, hroot⟩ := hnew
  have htH : E.SlotWithinHorizon cfg t :=
    E.slotWithinHorizon_mono cfg ht hesH
  have hcomm : i ∈ E.committee t :=
    hhb.votes_assigned i hiHon t (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨hact, huns⟩ := honest_active_unslashed cfg ext hhb hec hsv
    hval hbsH hiHon htH hcomm
  have hne := E.honest_not_equivocating cfg ext hhb hec hgen
    hiHon v n hv hnH
  exact E.oppositeAncestorClass_old_back cfg ext hhb hec hgen hiOes
    hsrc hdst hsrcSlot hold hmaxSrc
    (E.WindowRecordedEpochMax_mono_end cfg ext hesσ hmaxDst)
    hSt ⟨t, k, a, ht, hvote, hlater, hroot⟩
    hact huns hne hb hh hsrcRoot
    (hwalkSrc src.root hsrcRoot b hb)
    (hwalkSrc h hh src.root hsrcRoot) hagree

/-- Honest opposite-status supporters split into the current sibling class or
the confirming store's fixed ancestor debt. The old-message premise is
supplied by `oppositeAncestorClass_old_back_of_execution`; the late-message
premise is supplied by `opposite_supporter_not_newvote`. -/
theorem opposite_honest_classification_of_transport
    {v w : ValidatorIndex} {n m : ℕ} {b h c : Root}
    {lo es σ : Slot} {selected other : PayloadStatus}
    {bsSrc bsDst : BeaconState Root}
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected)
    (hSmem : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bsDst)
    (hchildSubset : (AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root c) bsDst).toFinset ⊆
      (AttSupporters cfg (E.store cfg ext w m)
        (ForkChoiceNode.mk h selected) bsDst).toFinset)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bsDst,
      i ∈ E.honest → i ∈ E.span_committee lo σ)
    (hXback : E.Xclass cfg ext w m b lo σ ⊆
      E.Xclass cfg ext v n b lo σ)
    (hOld : ∀ i (lm : LatestMessage Root),
      i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext w m)
        bsDst w m b h lo σ other →
      (E.store cfg ext w m).latest_messages i = some lm →
      lm.slot ≤ es →
      i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext v n)
        bsSrc v n b h lo es other)
    (hLate : ∀ i (lm : LatestMessage Root),
      i ∈ E.honest →
      i ∈ AttSupporters cfg (E.store cfg ext w m)
        (ForkChoiceNode.mk h other) bsDst →
      (E.store cfg ext w m).latest_messages i = some lm →
      es + 1 ≤ lm.slot → False) :
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bsDst,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v n b lo σ ∨
        i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext v n)
          bsSrc v n b h lo es other := by
  intro i hiOpp hiHon
  obtain ⟨lm, hlm, _, _⟩ := mem_AttSupporters cfg hiOpp
  have hold : lm.slot ≤ es := by
    by_contra hn
    exact hLate i lm hiHon hiOpp hlm (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
  have hiSpan := hspan i hiOpp hiHon
  have hnotS : i ∉ E.Sclass cfg ext w m b lo σ := by
    intro hiS
    have hiSelected := List.mem_toFinset.mp
      (hchildSubset (List.mem_toFinset.mpr (hSmem i hiS)))
    obtain ⟨lm', hlm', _, hs⟩ := mem_AttSupporters cfg hiSelected
    obtain ⟨lm'', hlm'', _, ho⟩ := mem_AttSupporters cfg hiOpp
    have heq : lm' = lm'' := Option.some.inj (hlm'.symm.trans hlm'')
    cases heq
    exact not_ancestor_two_resolved_statuses (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm') h selected other
      hselected hother hne ⟨hs, ho⟩
  have hnotDesc : ¬ E.SupportsDesc cfg ext w m b σ i := by
    intro hDesc
    apply hnotS
    simp only [Execution.Sclass, Finset.mem_filter]
    exact ⟨⟨hiSpan, hiHon⟩, hDesc⟩
  by_cases hAnc : E.AncestorOrVoteless cfg ext w m b σ i
  · right
    have hiA : i ∈ E.Aclass cfg ext w m b lo σ := by
      simp only [Execution.Aclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hiHon⟩, hnotDesc, hAnc⟩
    exact hOld i lm (Finset.mem_inter.mpr
      ⟨hiA, List.mem_toFinset.mpr hiOpp⟩) hlm hold
  · left
    apply hXback
    simp only [Execution.Xclass, Finset.mem_filter]
    exact ⟨⟨hiSpan, hiHon⟩, hnotDesc, hAnc⟩

/-- The execution form of honest opposite-score confinement. Every premise is
an existing execution fact or a fork-choice domain fact. In particular,
completed-window delivery is uniform over the honest validators in the score,
and the late branch uses the head-safety induction hypothesis. -/
theorem opposite_honest_classification_of_execution
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w : ValidatorIndex} {n m : ℕ} {b h c : Root}
    {lo es σ k : Slot} {selected other : PayloadStatus}
    {bsSrc bsDst : BeaconState Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hnH : E.WithinHorizon cfg n) (hmH : E.WithinHorizon cfg m)
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hesH : E.SlotWithinHorizon cfg es) (hesσ : es ≤ σ)
    (hslot_m : E.slot_at cfg m = k)
    (hval : bsSrc.validators = E.registry)
    (hbsH : get_current_epoch cfg bsSrc < E.verification_horizon)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hh : h ∈ (E.store cfg ext v n).block_roots)
    (hsub : (E.store cfg ext v n).block_roots ⊆
      (E.store cfg ext w m).block_roots)
    (hcDst : c ∈ (E.store cfg ext w m).block_roots)
    (hwalkSrc : ∀ t ∈ (E.store cfg ext v n).block_roots,
      ∀ r ∈ (E.store cfg ext v n).block_roots,
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks t).slot r)
    (hwalkDst : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r)
    (hwfDst : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hprovSrc : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hprovDst : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hmaxSrc : E.WindowRecordedEpochMax cfg ext v n lo es)
    (hmaxDst : E.WindowRecordedEpochMax cfg ext w m lo σ)
    (hcover : ∀ i ∈ E.honest, ∀ t j (a : Attestation Root), t ≤ es →
      E.vote i t = some (j, a) →
      ∃ src, (E.store cfg ext v n).latest_messages i = some src ∧
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg src)
    (hSt_es : ∀ i, E.SupportsDesc cfg ext v n b es i →
      E.SupportsDesc cfg ext w m b es i)
    (hStσ : ∀ i, E.SupportsDesc cfg ext v n b σ i →
      E.SupportsDesc cfg ext w m b σ i)
    (hAtσ : ∀ i, E.AncestorOrVoteless cfg ext v n b σ i →
      E.AncestorOrVoteless cfg ext w m b σ i)
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1)
    (hSmem : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bsDst)
    (hchildSubset : (AttSupporters cfg (E.store cfg ext w m)
      (get_node_for_root c) bsDst).toFinset ⊆
      (AttSupporters cfg (E.store cfg ext w m)
        (ForkChoiceNode.mk h selected) bsDst).toFinset)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bsDst,
      i ∈ E.honest → i ∈ E.span_committee lo σ)
    (hIH : ∀ j ∈ E.honest, ∀ t'' : Slot, es + 1 ≤ t'' → t'' < k →
      ∀ jj (a' : Attestation Root), E.vote j t'' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hbc : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk c .pending) = true) :
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bsDst,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v n b lo σ ∨
        i ∈ OppositeAncestorClass cfg ext E (E.store cfg ext v n)
          bsSrc v n b h lo es other := by
  apply E.opposite_honest_classification_of_transport cfg ext hselected hother hne
    hSmem hchildSubset hspan
    (by
      intro i hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun hS => hi.2.1 (hStσ i hS),
        fun hA => hi.2.2 (hAtσ i hA)⟩)
  · intro i lm hiO hlm hold
    exact E.oppositeAncestorClass_old_back_of_execution cfg ext hwf hhb hec hsv hgen
      hv hw hnH hmH hes hesH hesσ hval hbsH hb hh hsub hwalkSrc hwalkDst
      hwfDst hprovSrc hprovDst hmaxSrc hmaxDst (hcover i (by
        have hiA := (Finset.mem_inter.mp hiO).1
        simp only [Execution.Aclass, Finset.mem_filter] at hiA
        exact hiA.1.2)) (hSt_es i) hother hlo hiO hlm hold
  · intro i lm hiHon hiOpp hlm hlate
    obtain ⟨_, _, _, _, _, _, _, hroot, _, _⟩ := hprovDst i lm hlm
    exact E.opposite_supporter_not_newvote cfg ext hwf hhb hec hgen
      hiHon hw hmH hslot_m hprovDst hiOpp hlm hlate
      hselected hother hne hIH hwfDst
      (hwalkDst c hcDst lm.root hroot)
      (hwalkDst c hcDst b (hsub hb)) hbc hchildSubset

/-- The current v2 base enemy does not contain a recorded Byzantine message
on the confirmed block's ancestor line. This applies even when that message
supports the opposite resolved payload status. -/
theorem ancestor_recorded_message_not_BbadSet
    {v i : ValidatorIndex} {n : ℕ} {b : Root} {lo es : Slot}
    {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hline : is_ancestor (E.store cfg ext v n)
        (get_node_for_root lm.root) (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root b) (get_node_for_root lm.root) = true) :
    i ∉ E.BbadSet cfg ext v n b lo es := by
  intro hi
  simp only [Execution.BbadSet, Finset.mem_filter] at hi
  rcases hline with h | h
  · exact (hi.2.2 lm hlm).1 h
  · exact (hi.2.2 lm hlm).2 h

/-- An old ancestor-line Byzantine message remains charged by the status
base enemy whenever its validator is in the source window. The root relation
is irrelevant to the Byzantine budget. -/
theorem ancestor_recorded_message_mem_StatusBaseByzSet
    {v i : ValidatorIndex} {n : ℕ} {b : Root} {lo es : Slot}
    {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hline : is_ancestor (E.store cfg ext v n)
        (get_node_for_root lm.root) (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root b) (get_node_for_root lm.root) = true)
    (hspan : i ∈ E.span_committee lo es)
    (hbyz : i ∉ E.honest) :
    i ∉ E.BbadSet cfg ext v n b lo es ∧
      i ∈ E.StatusBaseByzSet lo es := by
  exact ⟨E.ancestor_recorded_message_not_BbadSet cfg ext hlm hline,
    Finset.mem_filter.mpr ⟨hspan, hbyz⟩⟩

/-- A validator with no tail committee assignment also lies outside the
current v2 spent set. Together with the preceding lemma, this records the
precise old ancestor branch that the current enemy does not charge. -/
theorem old_ancestor_message_not_v2_enemy
    {v i : ValidatorIndex} {n : ℕ} {b : Root} {lo es σ : Slot}
    {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hline : is_ancestor (E.store cfg ext v n)
        (get_node_for_root lm.root) (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root b) (get_node_for_root lm.root) = true)
    (hnoTail : ∀ t : Slot, es < t → t ≤ σ → i ∉ E.committee t) :
    i ∉ E.BbadSet cfg ext v n b lo es ∪ E.SpentSet es σ := by
  intro hi
  rcases Finset.mem_union.mp hi with hbase | hspent
  · exact E.ancestor_recorded_message_not_BbadSet cfg ext hlm hline hbase
  · simp only [Execution.SpentSet, Finset.mem_filter,
      Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hspent
    obtain ⟨⟨t, ⟨hlo, hhi⟩, hcomm⟩, _⟩ := hspent
    exact hnoTail t hlo hhi hcomm

/-- The provable Byzantine confinement for an opposite resolved status uses
the entire old Byzantine window. A later setting slot lies in the spent tail;
an older one lies in `Bwin` by the resolved-supporter slot bound. -/
theorem opposite_byz_full_window_or_spent
    {w i : ValidatorIndex} {m : ℕ} {h : Root}
    {lo es σ : Slot} {other : PayloadStatus}
    {bs : BeaconState Root} {lm : LatestMessage Root}
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈
          (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks
          ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext w m)) (E.store cfg ext w m))
    (hresolved : other ≠ .pending)
    (hwalk : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks h).slot lm.root)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hiOpp : i ∈ AttSupporters cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk h other) bs)
    (hiByz : i ∉ E.honest)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm) :
    i ∈ E.Bwin lo es ∨ i ∈ E.SpentSet es σ := by
  by_cases hold : lm.slot ≤ es
  · left
    have hiSpan := E.old_resolved_supporter_mem_span cfg hwf hprov
      hresolved hiOpp hlm hwalk hlo hold
    simp only [Execution.Bwin, Finset.mem_filter]
    exact ⟨hiSpan, hiByz⟩
  · right
    obtain ⟨_, _, _, _, _, hgate, hcomm, _, _, hslot⟩ := hprov i lm hlm
    have hlate : es < lm.slot := Nat.lt_of_not_ge hold
    have hupper : lm.slot ≤ σ := by
      rw [hslot]
      exact (Nat.le_sub_one_of_lt hgate).trans hσcur
    simp only [Execution.SpentSet, Finset.mem_filter,
      Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨⟨lm.slot, ⟨hlate, hupper⟩, ?_⟩, hiByz⟩
    rw [hslot]
    exact hcomm

/-- Both parts of the provable Byzantine confinement fit in the complete
window budget. This is the enemy available to an `INVstar`-based status bound. -/
theorem old_byz_union_spent_le_Bval
    {lo es σ : Slot} (hlo : lo ≤ es + 1) (hesσ : es ≤ σ) :
    E.weight (E.Bwin lo es ∪ E.SpentSet es σ) ≤ E.Bval lo σ := by
  apply E.weight_mono
  intro i hi
  simp only [Execution.Bval, Execution.Bwin, Execution.SpentSet,
    Finset.mem_union, Finset.mem_filter,
    Execution.span_committee, Finset.mem_biUnion,
    Finset.mem_Icc] at hi ⊢
  rcases hi with ⟨⟨t, ⟨htlo, htes⟩, hcomm⟩, hbyz⟩ |
    ⟨⟨t, ⟨htes, htσ⟩, hcomm⟩, hbyz⟩
  · exact ⟨⟨t, ⟨htlo, htes.trans hesσ⟩, hcomm⟩, hbyz⟩
  · exact ⟨⟨t, ⟨hlo.trans htes, htσ⟩, hcomm⟩, hbyz⟩

/-- A complete-window Byzantine bound combines with the honest transport
classification to bound the opposite resolved score by `X + Bval + Oanc`. -/
theorem recorded_opposite_status_le_full_window
    {store source : Store Root} {bs bsSource : BeaconState Root}
    (hval : bs.validators = E.registry)
    {v : ValidatorIndex} {n : ℕ} {b h : Root}
    {lo es σ : Slot} {other : PayloadStatus}
    (hlo : lo ≤ es + 1) (hesσ : es ≤ σ)
    (hHon : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v n b lo σ ∨
          i ∈ OppositeAncestorClass cfg ext E source bsSource
            v n b h lo es other)
    (hByz : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∉ E.honest →
        i ∈ E.Bwin lo es ∨ i ∈ E.SpentSet es σ) :
    get_attestation_score cfg store (ForkChoiceNode.mk h other) bs ≤
      E.Xval cfg ext v n b lo σ + E.Bval lo σ +
        E.weight (OppositeAncestorClass cfg ext E source bsSource
          v n b h lo es other) := by
  have hscore := E.recorded_opposite_status_le_v2 cfg ext hval hHon hByz
  have hB := E.StatusEnemyVal_le_Bval hlo hesσ
  exact le_trans hscore (Nat.add_le_add_right (Nat.add_le_add_left hB _) _)

/-- Endpoint child recording lifts the selected honest class into the
resolved parent status. This is the `hselected` input of the status margin. -/
theorem selected_parent_score_ge_Sval
    {store : Store Root} {bs : BeaconState Root}
    (hval : bs.validators = E.registry)
    {v : ValidatorIndex} {n : ℕ} {b c : Root} {lo σ : Slot}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hc : c ∈ store.block_roots)
    (hp : (store.blocks c).parent_root ∈ store.block_roots)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root c) bs →
        WalkKnown store (store.blocks (store.blocks c).parent_root).slot lm.root)
    (hSmem : ∀ i ∈ E.Sclass cfg ext v n b lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs) :
    E.Sval cfg ext v n b lo σ ≤
      get_attestation_score cfg store
        (ForkChoiceNode.mk (store.blocks c).parent_root
          (get_parent_payload_status store (store.blocks c))) bs := by
  exact le_trans (recorded_bside_ge cfg ext hval hSmem)
    (selected_parent_score_ge_child_score cfg hval hwf hc hp hwalk)

/-- The required status appears in the pending parent's fork-choice children
when it is empty or its full payload has been verified at this store. -/
theorem selected_parent_status_mem_pending
    {store : Store Root} {blocks : List Root} {h : Root}
    {status : PayloadStatus}
    (havailable : status = .empty ∨
      (status = .full ∧ is_payload_verified store h = true)) :
    ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending) := by
  exact (mem_get_node_children_pending rfl).mpr ⟨rfl, havailable⟩

/-- The endpoint strip of `INVstar`, used here without importing the later
ground-step module. -/
private theorem invstar_endpoint_local
    (v : ValidatorIndex) (n : ℕ) (b : Root) (lo es σ : Slot)
    (boost : ℕ) (hinv : E.INVstar cfg ext v n b lo es σ boost) :
    E.Xval cfg ext v n b lo σ + E.Bval lo σ + boost + 1
      ≤ E.Sval cfg ext v n b lo σ := by
  simp only [Execution.INVstar] at hinv
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le
    omega
  refine Nat.le_of_mul_le_mul_left (le_trans (Nat.le_add_right _ _) hinv) hDpos

private theorem invstar_opposite_margin_arith
    {X B P O S Q R : ℕ}
    (hstrip : X + B + (P + O) + 1 ≤ S)
    (hopp : Q ≤ X + B + O) (hselected : S ≤ R) :
    Q + P < R := by omega

/-- The complete-window score bound and a debt-strengthened `INVstar` imply
the payload decision margin at an endpoint. -/
theorem pendingStatusMargin_of_INVstar_opposite
    {store : Store Root} {blocks : List Root}
    {v : ValidatorIndex} {n : ℕ} {b h : Root}
    {lo es σ : Slot} {status : PayloadStatus} {boost O : ℕ}
    (hmem : ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending))
    (hnotPrev : is_previous_slot_payload_decision cfg store
      (ForkChoiceNode.mk h status) = false)
    (hselected : E.Sval cfg ext v n b lo σ ≤
      get_attestation_score cfg store (ForkChoiceNode.mk h status)
        (store.checkpoint_states store.justified_checkpoint))
    (hboost : boost = get_proposer_score cfg store)
    (hinv : E.INVstar cfg ext v n b lo es σ (boost + O))
    (hopp : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ ForkChoiceNode.mk h status →
      get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) ≤
          E.Xval cfg ext v n b lo σ + E.Bval lo σ + O) :
    PendingStatusMargin cfg store blocks h status := by
  refine ⟨hmem, ?_⟩
  intro other hm hne
  left
  constructor
  · have hstrip := E.invstar_endpoint_local cfg ext v n b lo es σ (boost + O) hinv
    rw [hboost] at hstrip
    have hscore := hopp other hm hne
    exact invstar_opposite_margin_arith hstrip hscore hselected
  · exact hnotPrev

private theorem ancestor_strip_survives_growth
    {x0 B0 P s0 xg Bg sg dJ dB : ℕ}
    (hstrip : x0 + B0 + P + 1 ≤ s0) (hs : s0 + dJ ≤ sg)
    (hx : xg ≤ x0) (hB : Bg ≤ B0 + dB) (hbudget : dB ≤ dJ) :
    xg + Bg + P + 1 ≤ sg := by omega

private theorem ancestor_strip_transports
    {x0 x1 B P O s0 s1 : ℕ}
    (hsource : x0 + B + P + O + 1 ≤ s0)
    (hX : x1 ≤ x0) (hS : s0 ≤ s1) :
    x1 + B + (P + O) + 1 ≤ s1 := by omega

private theorem ancestor_le_add_tsub (a b : ℕ) : a ≤ b + (a - b) := by omega

/-- A fixed opposite-ancestor debt survives the complete-window growth
argument. The source strip comes from actual confirmation; the two honest
class movements, honest growth, and window capacity are the existing engine
transport and induction inputs. -/
theorem opposite_ancestor_strip_window_uniform
    {v w : ValidatorIndex} {n m : ℕ} {b : Root}
    {lo es σ : Slot} {P O : ℕ}
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v n b es i → E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v n b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hsource : E.Xval cfg ext v n b lo es + E.Bval lo es + P + O + 1
      ≤ E.Sval cfg ext v n b lo es)
    (hgrowS : E.Sval cfg ext w m b lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b lo σ)
    (hgrowX : E.Xval cfg ext w m b lo σ ≤ E.Xval cfg ext w m b lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es)) :
    E.Xval cfg ext w m b lo σ + E.Bval lo σ + P + O + 1
      ≤ E.Sval cfg ext w m b lo σ := by
  have hSbase : E.Sval cfg ext v n b lo es ≤ E.Sval cfg ext w m b lo es := by
    apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  have hXbase : E.Xval cfg ext w m b lo es ≤ E.Xval cfg ext v n b lo es := by
    apply E.weight_mono
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hs => hi.2.1 (hSt i hi.1.2 hi.1.1 hs),
      fun ha => hi.2.2 (hAt i hi.1.2 hi.1.1 ha)⟩
  have hbase : E.Xval cfg ext w m b lo es + E.Bval lo es +
      (P + O) + 1 ≤ E.Sval cfg ext w m b lo es :=
    ancestor_strip_transports hsource hXbase hSbase
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le
    omega
  have hCD : cfg.confirmation_byzantine_threshold ≤
      100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le
    omega
  have hbud : E.Bval lo σ - E.Bval lo es ≤
      E.Jspec lo σ - E.Jspec lo es :=
    Nat.le_of_mul_le_mul_left
      (le_trans hbudget (Nat.mul_le_mul hCD (le_refl _))) hDpos
  have hB : E.Bval lo σ ≤ E.Bval lo es +
      (E.Bval lo σ - E.Bval lo es) :=
    ancestor_le_add_tsub _ _
  have hfinal := ancestor_strip_survives_growth hbase hgrowS hgrowX hB hbud
  simpa only [add_assoc] using hfinal

/-- The full-window route composes the transported source strip with the
opposite-score bound to produce the exact payload status margin used by a
fork-choice descent step. -/
theorem pendingStatusMargin_of_opposite_window
    {v w : ValidatorIndex} {n m : ℕ} {b h : Root}
    {lo es σ : Slot} {O : ℕ} {status : PayloadStatus}
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v n b es i → E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v n b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hsource : E.Xval cfg ext v n b lo es + E.Bval lo es +
      get_proposer_score cfg (E.store cfg ext w m) + O + 1
      ≤ E.Sval cfg ext v n b lo es)
    (hgrowS : E.Sval cfg ext w m b lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b lo σ)
    (hgrowX : E.Xval cfg ext w m b lo σ ≤ E.Xval cfg ext w m b lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es))
    (hmem : ForkChoiceNode.mk h status ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk h .pending))
    (hnotPrev : is_previous_slot_payload_decision cfg
      (E.store cfg ext w m) (ForkChoiceNode.mk h status) = false)
    (hselected : E.Sval cfg ext w m b lo σ ≤
      get_attestation_score cfg (E.store cfg ext w m)
        (ForkChoiceNode.mk h status)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hopp : ∀ other ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk h .pending),
      other ≠ ForkChoiceNode.mk h status →
      get_attestation_score cfg (E.store cfg ext w m) other
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint) ≤
        E.Xval cfg ext w m b lo σ + E.Bval lo σ + O) :
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h status := by
  have hstrip := E.opposite_ancestor_strip_window_uniform cfg ext
    hSt hAt hsource hgrowS hgrowX hbudget
  exact pendingStatusMargin_of_ancestor_strip cfg ext hmem hnotPrev
    hselected hstrip hopp

end Execution
end FastConfirmation.Spec

end
