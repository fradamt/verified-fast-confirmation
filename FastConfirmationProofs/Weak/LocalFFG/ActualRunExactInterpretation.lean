module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunExactLinks

/-! The actual-run interpretation retains all required certificates with exact mixed links. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E E' : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

private theorem span_weight_le_total
    {R : Execution Root} (base : SelectedMarginAssumptions cfg ext R)
    {lo hi : Slot} (hhi : R.SlotWithinHorizon cfg hi) :
    R.weight (R.span_committee lo hi) ≤ R.total_active cfg := by
  let U := (get_active_validator_indices R.anchor_state
    (get_current_epoch cfg R.anchor_state)).toFinset
  have hanchorSlot := R.anchor_state_slot_le cfg base.whole_seconds
    (by obtain ⟨st, b, hg, _⟩ := base.genesis; exact ⟨st, b, hg⟩)
  have hanchorH : get_current_epoch cfg R.anchor_state < R.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hanchorSlot)
      base.static_validators.genesis_within_horizon.2.2
  have hsub : R.span_committee lo hi ⊆ U := by
    intro i hiSpan
    simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiSpan
    obtain ⟨s, hs, hiCommittee⟩ := hiSpan
    have hsH : R.SlotWithinHorizon cfg s :=
      ⟨le_trans hs.2 hhi.1, lt_of_le_of_lt (Nat.div_le_div_right hs.2) hhi.2⟩
    have hact := base.externals_coherence.committee_members_active i s hsH hiCommittee
    rw [base.static_validators.activity_constant i _ _ hsH.2 hanchorH] at hact
    have hir : i < R.registry.length := by
      by_contra hge
      rw [not_lt] at hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hact
      simp only [is_active_validator, decide_eq_true_eq] at hact
      exact Nat.not_lt_zero _ hact.2
    simpa only [U, List.mem_toFinset, get_active_validator_indices,
      List.mem_filter, List.mem_range, Execution.registry] using And.intro hir hact
  have hm : R.weight (R.span_committee lo hi) ≤ R.weight U :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  apply hm.trans
  simp only [U, Execution.weight, Execution.weight_of, Execution.total_active,
    get_total_active_balance, get_total_balance, Execution.registry]
  exact Nat.le_max_right _ _

/-- Any body quorum, including a mixed one, has an actual honest signer. -/
theorem link_honest_signer (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    {I : Root → Attestation Root → Prop} {r source target}
    (L : IncludedSupermajorityLink cfg E I r source target) :
    ∃ i ∈ L.signers, i ∈ E.honest := by
  let R := E.withoutObserver obs
  obtain ⟨i, hi, _, hh⟩ := two_quorums_intersect_honest R (R.total_active_pos cfg)
    L.signers_in_epoch L.signers_in_epoch (span_weight_le_total core.base L.target_span_within.2)
    (core.base.byzantine_bound.span_fraction _ _ L.target_span_within.1 L.target_span_within.2)
    cfg.confirmation_byzantine_threshold_le L.supermajority L.supermajority
  exact ⟨i, hi, (withoutObserver_honest hobs) ▸ hh⟩

/-- The formed relation is unchanged; each of its certificates survives. -/
theorem exact_formed_certificate (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r c} (hf : (state hobs core localInputs B).formed r c) :
    IncludedCertifiedJustified cfg E (exactIncluded hobs core localInputs B)
      E.genesis_store.justified_checkpoint r c := by
  rcases hf with hf | hf
  · obtain ⟨cert⟩ := (core.semantics.state.formed_evidence hf).certified
    have hc := normalize_shared_certificate hobs core localInputs B
      (core.semantics.state.formed_carrier_accepted hf) cert
    simpa only [core.anchor_eq] using hc
  · exact normalize_local_certificate hobs core localInputs B (B.state.formed_domain hf)
      (B.state.formed_certificate hf)

/-- Non-anchor formation still has an individual signed vote and a retained
body attestation with equal data. The quorum supplies the honest signer. -/
theorem exact_formed_evidence (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r c} (hf : (state hobs core localInputs B).formed r c) :
    IncludedVoteCheckpointCertificate cfg ext E (exactIncluded hobs core localInputs B)
      E.genesis_store.justified_checkpoint r c := by
  have hc := exact_formed_certificate hobs core localInputs B hf
  refine ⟨⟨hc⟩, ((state hobs core localInputs B).formed_evidence hf).on_chain, ?_⟩
  by_cases heq : c = E.genesis_store.justified_checkpoint
  · exact Or.inl heq
  right
  obtain ⟨b, hb⟩ := ((state hobs core localInputs B).formed_carrier_accepted hf).exists_blockAt
  cases hc with
  | anchor => exact False.elim (heq rfl)
  | link prev L =>
    obtain ⟨i, hi, hhonest⟩ := link_honest_signer hobs core L
    obtain ⟨a, ⟨carrier, hd, hin⟩, hia, _, ht⟩ := L.signer_attestation i hi
    let ev := (exactRelation hobs core localInputs B).evidence hin
    obtain ⟨w, n, hsched⟩ := ev.received_from_block
    obtain ⟨k, own, _, hv, hdata⟩ := (nonhonest_honestBehavior hobs core localInputs).no_forgery
      w n a true hsched i hhonest hia
    have hslot : a.data.slot < b.slot := ev.slot_before_carrier.trans_le
      (accepted_slot_le hobs core localInputs hb ev.carrier_accepted hd)
    have hownslot : own.data.slot = a.data.slot := (congrArg AttestationData.slot hdata).symm
    exact ⟨b, hb, i, hhonest, a.data.slot, k, own, hslot, ev.slot_within_horizon,
      hv, hownslot, hdata ▸ ht, a, ⟨carrier, hd, hin⟩, hia, hdata⟩

/-- Filtering preserves the exact realized finalization evidence of every accepted root. -/
theorem exact_gf_evidence (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    (r) (hr : E.AcceptedRoot cfg ext r) :
    (state hobs core localInputs B).GF r = E.genesis_store.justified_checkpoint ∨
      Nonempty (IncludedCertifiedFinalized cfg E (exactIncluded hobs core localInputs B)
        E.genesis_store.justified_checkpoint r ((state hobs core localInputs B).GF r)) := by
  by_cases hs : (E.withoutObserver obs).AcceptedRoot cfg ext r
  · rw [(shared_values hobs core localInputs B hs).2.1]
    rcases core.semantics.state.gf_evidence r hs with ha | hF
    · exact Or.inl (ha.trans core.anchor_eq)
    · obtain ⟨F⟩ := hF
      have hF' := normalize_shared_finalized hobs core localInputs B hs F
      exact Or.inr ⟨by simpa only [core.anchor_eq] using hF'⟩
  · have hl := (B.domain_local r).mpr ((accepted_cases hr).resolve_left hs)
    rw [(local_values hobs core localInputs B hl).2.1]
    exact (B.state.gf_evidence r hl).imp_right
      (fun ⟨F⟩ => ⟨normalize_local_finalized hobs core localInputs B hl F⟩)

/-- Filtering also preserves every unrealized finalization certificate. -/
theorem exact_guf_evidence (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    (r) (hr : E.AcceptedRoot cfg ext r) :
    (state hobs core localInputs B).GUF r = E.genesis_store.justified_checkpoint ∨
      Nonempty (IncludedCertifiedFinalized cfg E (exactIncluded hobs core localInputs B)
        E.genesis_store.justified_checkpoint r ((state hobs core localInputs B).GUF r)) := by
  by_cases hs : (E.withoutObserver obs).AcceptedRoot cfg ext r
  · rw [(shared_values hobs core localInputs B hs).2.2.2.1]
    rcases core.semantics.state.guf_evidence r hs with ha | hF
    · exact Or.inl (ha.trans core.anchor_eq)
    · obtain ⟨F⟩ := hF
      have hF' := normalize_shared_finalized hobs core localInputs B hs F
      exact Or.inr ⟨by simpa only [core.anchor_eq] using hF'⟩
  · have hl := (B.domain_local r).mpr ((accepted_cases hr).resolve_left hs)
    rw [(local_values hobs core localInputs B hl).2.2.2.1]
    exact (B.state.guf_evidence r hl).imp_right
      (fun ⟨F⟩ => ⟨normalize_local_finalized hobs core localInputs B hl F⟩)

/-- Only inclusion is restricted. Domain, formed entries, and selectors are unchanged. -/
noncomputable def exactState (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    TrustedCausalCarrierFFGState cfg ext E E.genesis_store.justified_checkpoint
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) :=
  { state hobs core localInputs B with
    includedAttestations := exactRelation hobs core localInputs B
    formed_evidence := exact_formed_evidence hobs core localInputs B
    gf_evidence := exact_gf_evidence hobs core localInputs B
    guf_evidence := exact_guf_evidence hobs core localInputs B }

/-- The filter preserves every formed entry and every AU query exactly. -/
theorem exactState_formed_and_AU (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    (exactState hobs core localInputs B).formed = (state hobs core localInputs B).formed ∧
    (exactState hobs core localInputs B).AU cfg ext = (state hobs core localInputs B).AU cfg ext :=
  ⟨rfl, rfl⟩

/-- Checkpoint projection is closed on the combined accepted domain. -/
def checkpointClosure (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    EpochCheckpointClosure E.genesis_store.justified_checkpoint (E.AcceptedRoot cfg ext)
      (exactState hobs core localInputs B).C where
  checkpoint_root_accepted := by
    intro r e hr he
    change E.AcceptedRoot cfg ext ((state hobs core localInputs B).C r e).root
    rcases accepted_cases hr with hs | hl
    · rw [(shared_values hobs core localInputs B hs).2.2.2.2 e]
      exact shared_acceptedRoot (core.checkpoint_projection.checkpoint_root_accepted hs
        (by simpa only [core.anchor_eq] using he))
    · have hd := (B.domain_local r).mpr hl
      rw [(local_values hobs core localInputs B hd).2.2.2.2 e]
      exact (local_acceptedBlock B
        (B.checkpoint_projection.checkpoint_root_accepted hd he)).acceptedRoot
  checkpoint_comp := by
    intro r se te hr he hle
    change (state hobs core localInputs B).C
      ((state hobs core localInputs B).C r te).root se = (state hobs core localInputs B).C r se
    rcases accepted_cases hr with hs | hl
    · have ht := core.checkpoint_projection.checkpoint_root_accepted hs
        (show core.semantics.anchor.epoch ≤ te by simpa only [core.anchor_eq] using he.trans hle)
      rw [(shared_values hobs core localInputs B hs).2.2.2.2 te,
        (shared_values hobs core localInputs B ht).2.2.2.2 se,
        (shared_values hobs core localInputs B hs).2.2.2.2 se]
      exact core.checkpoint_projection.checkpoint_comp hs
        (by simpa only [core.anchor_eq] using he) hle
    · have hd := (B.domain_local r).mpr hl
      have ht := B.checkpoint_projection.checkpoint_root_accepted hd (he.trans hle)
      rw [(local_values hobs core localInputs B hd).2.2.2.2 te,
        (local_values hobs core localInputs B ht).2.2.2.2 se,
        (local_values hobs core localInputs B hd).2.2.2.2 se]
      exact B.checkpoint_projection.checkpoint_comp hd he hle

/-- Restriction leaves all accepted transition and AU read equations unchanged. -/
def exactCoherence (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext
      (exactState hobs core localInputs B) where
  attestation_validity := rfl
  genesis_gj := (coherence hobs core localInputs B).genesis_gj
  genesis_gf := (coherence hobs core localInputs B).genesis_gf
  genesis_gu := (coherence hobs core localInputs B).genesis_gu
  genesis_guf := (coherence hobs core localInputs B).genesis_guf
  genesis_unrealized_justification :=
    (coherence hobs core localInputs B).genesis_unrealized_justification
  transition_gj := (coherence hobs core localInputs B).transition_gj
  transition_gf := (coherence hobs core localInputs B).transition_gf
  transition_gu := (coherence hobs core localInputs B).transition_gu
  transition_guf := (coherence hobs core localInputs B).transition_guf
  checkpoint_of_known := (coherence hobs core localInputs B).checkpoint_of_known
  au_checkpoint_of_known := (coherence hobs core localInputs B).au_checkpoint_of_known

/-- One interpretation of the complete actual run, with exact mixed-link endpoints. -/
noncomputable def exactInterpretation (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) where
  anchor := E.genesis_store.justified_checkpoint
  state := exactState hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)
  coherence := exactCoherence hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)

/-- All mixed links are exact on the accepted carrier domain used by the interpretation. -/
theorem exactInterpretation_exactLinkValidity (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    (exactInterpretation hobs premises).state.GuardedExactLinkValidity cfg ext
      (E.AcceptedRoot cfg ext) :=
  exactLinkValidity hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)

/-- The final interpretation also preserves checkpoint closure. -/
theorem exactInterpretation_checkpointClosure (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    EpochCheckpointClosure (exactInterpretation hobs premises).anchor
      (E.AcceptedRoot cfg ext) (exactInterpretation hobs premises).state.C :=
  checkpointClosure hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)

/-- The interpretation and exact-link law exist together from the unchanged inputs. -/
theorem actualRun_exactInterpretation (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    ∃ I : TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs),
      I.anchor = E.genesis_store.justified_checkpoint ∧
      I.state.GuardedExactLinkValidity cfg ext (E.AcceptedRoot cfg ext) :=
  ⟨exactInterpretation hobs premises, rfl, exactInterpretation_exactLinkValidity hobs premises⟩

/-- Arbitrary changes to the non-honest observer schedule need only new local inputs. -/
theorem actualRun_exactInterpretation_observer_independent (hobs : obs ∉ E.honest)
    (h : SameOutsideObserver E E' obs)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    (local' : E'.ObserverLocalInputs cfg ext obs) :
    ∃ I : TrustedCausalPrefixFFGInterpretation cfg ext E'
      (E'.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs),
      I.anchor = E'.genesis_store.justified_checkpoint ∧
      I.state.GuardedExactLinkValidity cfg ext (E'.AcceptedRoot cfg ext) :=
  actualRun_exactInterpretation (h.honest ▸ hobs)
    (premises.observer_independent cfg ext h local')

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
