module
public import FastConfirmation.Spec.Proof.Endpoint

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

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

end Execution
end FastConfirmation.Spec

end
