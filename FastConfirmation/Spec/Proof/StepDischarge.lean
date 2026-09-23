module
public import FastConfirmation.Spec.Proof.LedgerV2

@[expose] public section

/-!
# Spec / Proof / StepDischarge

This module contains `recorded_lm_is_newest_at` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the two `Bridge` generalisations

`Bridge.RecordedEpochMax` is the domination input `recorded_lm_is_newest` needs
(the recorded message dominates, in epoch, every one of the validator's votes
through `es`). It is exactly `Delivery.vote_ubiquity`'s conclusion, ∀-quantified
over the window — the shape `EngineTransport.HS0_in_AttSupporters` already takes
its `hubiq` in. `recorded_lm_is_newest_at` is `Bridge.recorded_lm_is_newest` with
the confirming node `(v₀, n₀)` replaced by an arbitrary honest `(w, m)`. -/


/-- **`recorded_lm_is_newest` at an arbitrary honest `(w, m)`.** Verbatim port of
`Bridge.recorded_lm_is_newest` (its proof uses only per-store facts): at honest
`(w, m)`, an honest validator `i`'s recorded `latest_messages i = some lm` is set
by `i`'s ground newest-by-`es` vote (a vote at `t ≤ es`, no later vote through
`es`) whose LMD block is exactly `lm.root`. Existence + block-root from
`SchedLMProv` + `no_forgery`; `t ≤ es` from the provenance slot gate `hprov` +
`committee_assignment_unique`; the newest characterisation from the ubiquity
domination `hdom`. `Endpoint`'s flag (`Bridge.recorded_lm_is_newest at (w,m)`). -/
theorem recorded_lm_is_newest_at
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    {es : Slot} (hes : es = get_current_slot cfg (E.store cfg ext w m) - 1)
    {i : ValidatorIndex} (hi : i ∈ E.honest) {lm : LatestMessage Root}
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hdom : ∀ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es → E.vote i t = some (k, a) → compute_epoch_at_slot cfg t ≤ (get_latest_message_epoch cfg lm)) :
    ∃ (t : Slot) (k : ℕ) (a : Attestation Root),
      t ≤ es ∧ E.vote i t = some (k, a) ∧
      (∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) ∧
      a.data.beacon_block_root = lm.root := by
  obtain ⟨a', u, tsc, ifb, hsched, hvin, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen w m i lm hlm
  obtain ⟨m1, a'', hvote', hdata'⟩ := hhb.no_forgery u tsc a' ifb hsched i hi hvin
  have hcomm0 : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot (by rw [hvote']; exact Option.some_ne_none _)
  obtain ⟨ap, _, _, _, h4, h5, h6, _, _, _⟩ := hprov i lm hlm
  have hepeq : compute_epoch_at_slot cfg a'.data.slot =
      compute_epoch_at_slot cfg ap.data.slot := by rw [hslotep, h4]
  have hslotdef : a'.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a'.data.slot ap.data.slot hcomm0 h6 hepeq
  have htle : a'.data.slot ≤ es := by
    rw [hslotdef, hes]; exact Nat.le_sub_one_of_lt h5
  have hbbr' : a''.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr
  refine ⟨a'.data.slot, m1, a'', htle, hvote', ?_, hbbr'⟩
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








end Execution

end FastConfirmation.Spec

end
