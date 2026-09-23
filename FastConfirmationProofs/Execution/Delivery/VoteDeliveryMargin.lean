module
public import FastConfirmationProofs.Discount.WindowStartMargin
public import FastConfirmationProofs.Execution.Delivery.Delivery
public import FastConfirmationProofs.Discount.RecordedSupport
public import FastConfirmationProofs.Handlers.ConfirmationCommitteeWeight

@[expose] public section

/-!
# Spec / Proof / Bridge

Carries delivered honest vote support into the following-slot score margin.

This module contains `old_window_latest_messages_agree`, `PostAnchorHonestVoteTargetWalkDomain`, `PostAnchorRecordedEpochMax` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)




/-- Two honest stores have the same complete latest message for an honest
validator when both recorded votes are within the old window and both stores
have the window's epoch-maximality fact. This includes the payload bit. -/
theorem old_window_latest_messages_agree
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w i : ValidatorIndex} {n m : ℕ} {es : Slot}
    (hi : i ∈ E.honest)
    {src dst : LatestMessage Root}
    (hsrc : (E.store cfg ext v n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hsrcSlot : src.slot ≤ es) (hdstSlot : dst.slot ≤ es)
    (hmaxSrc : ∀ lm, (E.store cfg ext v n).latest_messages i = some lm →
      ∀ t k (a : Attestation Root), t ≤ es → E.vote i t = some (k, a) →
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm)
    (hmaxDst : ∀ lm, (E.store cfg ext w m).latest_messages i = some lm →
      ∀ t k (a : Attestation Root), t ≤ es → E.vote i t = some (k, a) →
        compute_epoch_at_slot cfg t ≤ get_latest_message_epoch cfg lm) :
    src = dst := by
  obtain ⟨aS, uS, tS, ifbS, hschedS, hiS, hsrcEq⟩ :=
    E.schedLMProvExact cfg ext hgen v n i src hsrc
  obtain ⟨aD, uD, tD, ifbD, hschedD, hiD, hdstEq⟩ :=
    E.schedLMProvExact cfg ext hgen w m i dst hdst
  obtain ⟨kS, aS', hvS, _⟩ := hhb.no_forgery uS tS aS ifbS hschedS i hi hiS
  obtain ⟨kD, aD', hvD, _⟩ := hhb.no_forgery uD tD aD ifbD hschedD i hi hiD
  have hsSlot : aS.data.slot ≤ es := by simpa only [hsrcEq] using hsrcSlot
  have hdSlot : aD.data.slot ≤ es := by simpa only [hdstEq] using hdstSlot
  have hleSD : get_latest_message_epoch cfg src ≤
      get_latest_message_epoch cfg dst := by
    have h := hmaxDst dst hdst aS.data.slot kS aS' hsSlot hvS
    simpa only [hsrcEq] using h
  have hleDS : get_latest_message_epoch cfg dst ≤
      get_latest_message_epoch cfg src := by
    have h := hmaxSrc src hsrc aD.data.slot kD aD' hdSlot hvD
    simpa only [hdstEq] using h
  exact E.latest_message_eq_of_same_epoch cfg ext hhb hec hgen hi hsrc hdst
    (Nat.le_antisymm hleSD hleDS)

/-- Model/domain adequacy for honest-attestation delivery. For an actual
post-anchor honest vote, the source head's walk down to its FFG target epoch
boundary stays in the source store's block domain. Source-head knownness is
kept separate and is derived by selected-margin consumers. -/
def PostAnchorHonestVoteTargetWalkDomain : Prop :=
  ∀ (i : ValidatorIndex), i ∈ E.honest →
    ∀ (s : Slot) (n : ℕ) (index : CommitteeIndex),
      E.slot_at cfg 0 ≤ s →
      E.WithinHorizon cfg n →
      E.slot_at cfg n = s →
      E.vote i s = some
        (n, honest_attestation cfg ext (E.store cfg ext i n) s index i) →
      WalkKnown (E.store cfg ext i n)
        (compute_start_slot_at_epoch cfg
          (honest_attestation cfg ext
            (E.store cfg ext i n) s index i).data.target.epoch)
        (get_head cfg (E.store cfg ext i n)).root

/-- Epoch domination restricted to post-anchor votes. Unlike
`RecordedEpochMax`, this predicate never reads the unconstrained pre-anchor
portion of `Execution.vote`. -/
def PostAnchorRecordedEpochMax
    (v : ValidatorIndex) (q : ℕ) (lo es : Slot) : Prop :=
  ∀ i ∈ E.honest, ∀ lm : LatestMessage Root,
    (E.store cfg ext v q).latest_messages i = some lm →
    ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      lo ≤ t → t ≤ es → E.vote i t = some (k, a) →
      compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)

/-- Domination for all votes through `es`, restricted to honest validators
proved to belong to the concrete ledger window `[lo, es]`. A window member's
post-anchor assignment makes the apparently broader vote quantifier sound. -/
def WindowRecordedEpochMax
    (v : ValidatorIndex) (q : ℕ) (lo es : Slot) : Prop :=
  ∀ i ∈ E.honest, i ∈ E.span_committee lo es →
    ∀ lm : LatestMessage Root,
      (E.store cfg ext v q).latest_messages i = some lm →
      ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
        t ≤ es → E.vote i t = some (k, a) →
        compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)


/-- Window-scoped maximality at both stores suffices for exact old-message
agreement. The validator belongs to the fixed source window. -/
theorem old_window_latest_messages_agree_window
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v w i : ValidatorIndex} {n m : ℕ} {lo es : Slot}
    (hi : i ∈ E.honest) (hiSpan : i ∈ E.span_committee lo es)
    {src dst : LatestMessage Root}
    (hsrc : (E.store cfg ext v n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hsrcSlot : src.slot ≤ es) (hdstSlot : dst.slot ≤ es)
    (hmaxSrc : E.WindowRecordedEpochMax cfg ext v n lo es)
    (hmaxDst : E.WindowRecordedEpochMax cfg ext w m lo es) :
    src = dst :=
  E.old_window_latest_messages_agree cfg ext hhb hec hgen hi hsrc hdst
    hsrcSlot hdstSlot (hmaxSrc i hi hiSpan) (hmaxDst i hi hiSpan)

end Execution

/-! ## Newest-vote uniqueness -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Through a fixed window `[·, es]` an honest validator has at most one
"newest" vote: two slots each with no later vote through `es` coincide. -/
theorem newest_vote_unique {E : Execution Root} {i : ValidatorIndex} {es t₀ t₁ : Slot}
    (h0 : E.vote i t₀ ≠ none) (h0n : ∀ t' : Slot, t₀ < t' → t' ≤ es → E.vote i t' = none)
    (h1 : E.vote i t₁ ≠ none) (h1n : ∀ t' : Slot, t₁ < t' → t' ≤ es → E.vote i t' = none)
    (h0le : t₀ ≤ es) (h1le : t₁ ≤ es) : t₀ = t₁ := by
  rcases lt_trichotomy t₀ t₁ with h | h | h
  · exact absurd (h0n t₁ h h1le) h1
  · exact h
  · exact absurd (h1n t₀ h h0le) h0

namespace Execution

variable (E : Execution Root)

/-! ## The core bridge: recorded latest message ⟹ ground newest vote -/

/-- **The reverse-provenance bridge.** At the confirming honest node `(v₀, n₀)`,
an honest validator `i`'s recorded `latest_messages i = some lm` is set by `i`'s
ground **newest-by-`es`** vote (a vote at `t ≤ es`, no later vote through `es`)
whose LMD block is exactly `lm.root`. Existence + block-root from
`SchedLMProv` + `no_forgery`; `t ≤ es` from the provenance slot gate `hprov` +
`committee_assignment_unique`; the newest characterization from the ubiquity
domination `hdom`. -/
theorem recorded_lm_is_newest
    (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} {n₀ : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    {es : Slot} (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {lm : LatestMessage Root}
    (hlm : (E.store cfg ext v₀ n₀).latest_messages i = some lm)
    (hdom : ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) → compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = lm.root := by
  -- existence of a setting vote with block `lm.root`
  obtain ⟨a', u, tsc, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen v₀ n₀ i lm hlm
  obtain ⟨m1, a'', hvote', hdata'⟩ := hhb.no_forgery u tsc a' ifb hsched i hi hvin
  -- `a'.data.slot` is `i`'s vote slot; identify it with the provenance slot `≤ es`
  have hcomm0 : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot (by rw [hvote']; exact Option.some_ne_none _)
  obtain ⟨ap, _, _, _, h4, h5, h6, _, _, _⟩ := hprov i lm hlm
  have hepeq : compute_epoch_at_slot cfg a'.data.slot = compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, h4]
  have hslotdef : a'.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a'.data.slot ap.data.slot hcomm0 h6 hepeq
  have htle : a'.data.slot ≤ es := by
    rw [hslotdef, hes]; exact Nat.le_sub_one_of_lt h5
  -- the block-root of the recovered vote
  have hbbr' : a''.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr
  refine ⟨a'.data.slot, m1, a'', htle, hvote', ?_, hbbr'⟩
  -- newest: any later vote through `es` collides with `a'.data.slot`'s epoch
  intro t' hlt hle
  cases hvt : E.vote i t' with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨k', a3⟩ := p
    have hcomm' : i ∈ E.committee t' :=
      hhb.votes_assigned i hi t' (by rw [hvt]; exact Option.some_ne_none _)
    have heple : compute_epoch_at_slot cfg t' ≤ (get_latest_message_epoch cfg lm) := hdom t' k' a3 hle hvt
    have hepmono : compute_epoch_at_slot cfg a'.data.slot ≤ compute_epoch_at_slot cfg t' :=
      Nat.div_le_div_right (le_of_lt hlt)
    have hle1 : compute_epoch_at_slot cfg t' ≤ compute_epoch_at_slot cfg a'.data.slot := by
      rw [hslotep]; exact heple
    have hepeq' : compute_epoch_at_slot cfg t' = compute_epoch_at_slot cfg a'.data.slot :=
      le_antisymm hle1 hepmono
    have hts : t' = a'.data.slot :=
      hec.committee_assignment_unique i t' a'.data.slot hcomm' hcomm0 hepeq'
    subst hts
    exact lt_irrefl _ hlt

/-! ## `hHsup`: recorded honest supporters are `Sclass` members -/



/-! ## `hdisc`: parent-stuck honest weight is `Aclass` weight -/



/-! ## The assembled weak base — `hHsup` / `hdisc` discharged -/


end Execution

end FastConfirmation.Spec

end
