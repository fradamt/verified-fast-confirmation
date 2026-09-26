module
public import FastConfirmationProofs.FFG.SelectedSource.CompletedPredictionProducers
public import FastConfirmationProofs.FCRRule.PredictionSupport

/-!
Checkpoint pinning at an endpoint needs support only at earlier vote slots.

The included certificate supplies an attestation before a known carrier for
each signer. Committee assignment uniqueness identifies that vote's slot
with the slot of the helper's counted signer. Thus the intersecting honest
signer is before the endpoint, even when the target epoch has not ended.
No strict justified-epoch external law is used.
-/

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The current-target threshold implies the no-conflict threshold because
Python's minimum total active balance is positive. -/
theorem currentTargetGate_implies_noConflict {store : Store Root}
    (hgate : will_current_target_be_justified cfg ext store = true) :
    will_no_conflicting_checkpoint_be_justified cfg ext store = true := by
  unfold will_no_conflicting_checkpoint_be_justified
  split_ifs with heq
  · rfl
  · simp only [will_current_target_be_justified, decide_eq_true_eq] at hgate
    simp only [decide_eq_true_eq, one_mul]
    have hpos : 0 < get_total_active_balance cfg (get_pulled_up_head_state cfg ext store) := by
      unfold get_total_active_balance get_total_balance
      exact cfg.effective_balance_increment_pos.trans_le (Nat.le_max_left _ _)
    rw [two_mul] at hgate
    exact (Nat.lt_add_of_pos_right hpos).trans_le hgate

namespace Execution

variable {E : Execution Root}

omit [LinearOrder Root] [Inhabited Root] in
/-- A concrete assigned vote belongs to the committee union of its target
epoch.  Kept local to the accepted pinning proof because the corresponding
legacy helper is intentionally private. -/
private theorem mem_acceptedNoConflict_epoch_span_of_committee
    {i : ValidatorIndex} {s : Slot} {e : Epoch}
    (hcommittee : i ∈ E.committee s)
    (hepoch : compute_epoch_at_slot cfg s = e) :
    i ∈ E.span_committee (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := by
  have hdiv : s / cfg.slots_per_epoch = e := by
    simpa only [compute_epoch_at_slot] using hepoch
  have hlo : e * cfg.slots_per_epoch ≤ s := by
    have h := Nat.div_mul_le_self s cfg.slots_per_epoch
    rwa [hdiv] at h
  have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
    rw [hdiv, Nat.mul_add] at h
    simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
  have hhi : s ≤ e * cfg.slots_per_epoch +
      (cfg.slots_per_epoch - 1) := by
    have hpred := Nat.le_pred_of_lt hlt
    rw [Nat.pred_eq_sub_one,
      Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
    exact hpred
  simp only [Execution.span_committee, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hcommittee⟩

/-- The no-conflict gate pins any property of the counted honest targets to
a same-epoch included certificate. Future support is used only at slots
strictly before the endpoint. -/
theorem completedPrefix_noConflict_includedJustified_property_before
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hfloor : cfg.effective_balance_increment ≤ E.weight (E.anchorActiveValidators cfg))
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true)
    {w : ValidatorIndex} {m : ℕ} {tip : Root}
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (P : Checkpoint Root → Prop)
    (htargetP : P (get_current_target cfg (E.store cfg ext v (n + 1))))
    (hsupport : ∀ i ∈ E.honest, ∀ sl : Slot,
      E.SlotWithinHorizon cfg sl →
      compute_epoch_at_slot cfg sl =
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)) →
      E.slot_at cfg (n + 1) ≤ sl → sl < E.slot_at cfg m →
      ∀ k a, E.vote i sl = some (k, a) →
        a.data.target.epoch =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) ∧ P a.data.target)
    {c : Checkpoint Root}
    (hc : IncludedCertifiedJustified cfg E B.state.includedAttestations.Included
      B.anchor tip c)
    (hcepoch : c.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    P c := by
  classical
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenZero : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgen⟩
  let hA := E.noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    cfg ext B hT hstatic hbyz hanchor hboundary
  let hAccA : FFGAccountabilityAssumptions cfg ext E :=
    { genesis_store := hgenZero
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      externals_coherence := hT.externals_coherence
      static_validator_set := hstatic
      byzantine_bound := hbyz }
  let hacc : CertificateAccountability cfg E B.anchor :=
    CertificateAccountability.of_assumptions cfg ext hAccA
  let store := E.store cfg ext v (n + 1)
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let signers := E.currentTargetA32Signers cfg store state
  change c.epoch = target.epoch at hcepoch
  have hstate : state = get_pulled_up_head_state cfg ext store := rfl
  have hval : state.validators = E.registry := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_validators cfg ext B hT
        hanchor hboundary hv hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_totalActive cfg ext B hT
        hstatic hanchor hboundary hv hHn1
  have hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg store) := by
    simpa only [store] using
      E.currentTargetEpochEnd_within_of_epochEndsFitUint64
        cfg ext hfit (v := v) hHn1
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon :=
    E.completedPrefix_anchor_epoch_within cfg ext hT hstatic
  have hstoreCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v (n + 1)
  obtain ⟨hUJ⟩ :=
    ScheduledFFGInterpretation.unrealizedJustified_certificate
      cfg ext B hgenShort hanchor hstoreCausal
  have hcGlobal := IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) (AcceptedBlockAttestationInclusion.relation cfg ext E
      B.state.includedAttestations) hc
  by_cases heq : target = store.unrealized_justified_checkpoint
  · have hroot := hacc.justified_unique hcGlobal hUJ
      (hcepoch.trans (congrArg Checkpoint.epoch heq))
    have hct : c = target := checkpoint_eq_of_epoch_root_eq hcepoch
      (hroot.trans (congrArg Checkpoint.root heq).symm)
    rwa [hct]
  · have htargetNotAnchor : target ≠ B.anchor := by
      intro htargetAnchor
      have htargetEpoch : target.epoch =
          compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) := by
        simp only [target, store, get_current_target,
          get_checkpoint_for_block, get_current_store_epoch,
          E.store_current_slot cfg ext v (n + 1)]
      have hUJLeTarget : store.unrealized_justified_checkpoint.epoch ≤
          target.epoch := by
        have hbound := (E.store_CkptEpochLe cfg ext
          hT.externals_coherence hT.whole_seconds hgenShort v (n + 1)).2
        change store.unrealized_justified_checkpoint.epoch ≤
          compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) at hbound
        exact hbound.trans_eq htargetEpoch.symm
      have hanchorLeUJ : B.anchor.epoch ≤
          store.unrealized_justified_checkpoint.epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg) hUJ
      have hUJEpoch : store.unrealized_justified_checkpoint.epoch =
          B.anchor.epoch := by
        apply Nat.le_antisymm
        · exact hUJLeTarget.trans_eq
            (congrArg Checkpoint.epoch htargetAnchor)
        · exact hanchorLeUJ
      have hUJRoot : store.unrealized_justified_checkpoint.root =
          B.anchor.root :=
        hacc.justified_unique hUJ CertifiedJustified.anchor hUJEpoch
      have hUJAnchor : store.unrealized_justified_checkpoint = B.anchor := by
        generalize hu : store.unrealized_justified_checkpoint = u
          at hUJEpoch hUJRoot ⊢
        generalize ha : B.anchor = a at hUJEpoch hUJRoot ⊢
        cases u
        cases a
        simp only at hUJEpoch hUJRoot ⊢
        subst_vars
        rfl
      exact heq (htargetAnchor.trans hUJAnchor.symm)
    let p := E.completedScheduledEventPrefix v n
    have hpstore : p.store cfg ext = store := by
      simpa only [p, store] using
        E.completedScheduledEventPrefix_store cfg ext v n
    have hanchorBefore : B.anchor.epoch < target.epoch := by
      have hprefix := p.currentTarget_anchor_epoch_lt_of_ne
        cfg ext B hT hanchor hboundary
        (by
          rw [hpstore]
          simpa only [target, store] using htargetNotAnchor)
      simpa only [hpstore, target, store] using hprefix
    have hvotes : ∀ i ∈ signers,
        ∃ s k a, i ∈ E.honest ∧ i ∈ E.committee s ∧
          compute_epoch_at_slot cfg s = target.epoch ∧
          E.vote i s = some (k, a) ∧
          (s < E.slot_at cfg m → a.data.target.epoch = target.epoch ∧ P a.data.target) := by
      intro i hiSigner
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hiSigner
      rcases hiSigner with hiObserved | hiFuture
      · let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
          cfg ext E B hT hanchor hboundary
        have hboundaryZero : InitialAnchorAtEpochBoundary
            (cfg := cfg) (E := E)
            (anchor := E.genesis_store.justified_checkpoint) := by
          simpa only [← hanchor] using hboundary
        have hvote :=
          E.currentTargetObservedHonestSupporter_vote_of_prefix
            cfg ext B hV hboundaryZero p hv hHn1
              (by simpa only [hpstore, state, store] using hiObserved)
        rw [hpstore] at hvote
        obtain ⟨vote⟩ := hvote
        refine ⟨vote.slot, vote.time, _, vote.honest, vote.assigned,
          vote.slot_epoch, vote.vote, ?_⟩
        intro _hbefore
        rw [vote.target_eq]
        exact ⟨rfl, htargetP⟩
      · simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
          Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiFuture
        obtain ⟨⟨sl, hsl, hiCommittee⟩, hi⟩ := hiFuture
        have hquerySlot : E.slot_at cfg (n + 1) ≤ sl := by
          rw [← E.store_current_slot cfg ext v (n + 1)]
          exact hsl.1
        have hsH : E.SlotWithinHorizon cfg sl :=
          E.slotWithinHorizon_mono cfg hsl.2 hendH
        have hsEpoch : compute_epoch_at_slot cfg sl = target.epoch := by
          have hlo := Nat.div_mul_le_self (get_current_slot cfg store)
            cfg.slots_per_epoch
          have hhi := hsl.2
          change sl ≤ (get_current_slot cfg store / cfg.slots_per_epoch) *
            cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) at hhi
          change sl / cfg.slots_per_epoch =
            get_current_slot cfg store / cfg.slots_per_epoch
          apply Nat.div_eq_of_lt_le (hlo.trans hsl.1)
          rw [Nat.add_mul, one_mul]
          exact hhi.trans_lt (Nat.add_lt_add_left
            (Nat.sub_lt cfg.slots_per_epoch_pos (by decide)) _)
        obtain ⟨k, index, _hkH, _hkSlot, hvote⟩ :=
          hT.honest_behavior.votes_head i hi sl hiCommittee hsH
            ((E.slot_at_mono cfg (Nat.zero_le _)).trans hquerySlot)
        exact ⟨sl, k, _, hi, hiCommittee, hsEpoch, hvote,
          fun hbefore => hsupport i hi sl hsH hsEpoch hquerySlot hbefore k _ hvote⟩
    have hsignersHonest : signers ⊆ E.honest := by
      intro i hi
      obtain ⟨_, _, _, hhonest, _⟩ := hvotes i hi
      exact hhonest
    have hsignersEpoch : signers ⊆
        E.span_committee (target.epoch * cfg.slots_per_epoch)
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
      intro i hi
      obtain ⟨_, _, _, _, hcomm, hepoch, _⟩ := hvotes i hi
      exact mem_acceptedNoConflict_epoch_span_of_committee cfg hcomm hepoch
    have honeThird : E.total_active cfg < 3 * E.weight signers := by
      simpa only [signers, store, state] using
        E.noConflict_arithmeticBranch_oneThird cfg ext hA hv hHn1
          hstate hval htab hendH hanchorH hfloor heq hgate
    have hcurrentH : E.SlotWithinHorizon cfg
        (get_current_slot cfg store) := by
      rw [show get_current_slot cfg store = E.slot_at cfg (n + 1) by
        simpa only [store] using
          E.store_current_slot cfg ext v (n + 1)]
      exact ⟨hHn1.2.1, hHn1.2.2⟩
    let U := E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1))
    have hspanEq : U = E.anchorActiveValidators cfg := by
      simpa only [U, target, store, get_current_target,
        get_checkpoint_for_block, currentTargetEpochStart,
        currentTargetEpochEnd, compute_start_slot_at_epoch] using
        E.current_epoch_span_eq_anchorActive cfg ext
          hT.externals_coherence hstatic hcurrentH hendH
            hanchorH
    have hU : E.weight U ≤ E.total_active cfg := by
      rw [hspanEq, ← E.total_active_eq_anchorActive_weight
        cfg hfloor]
    cases hc with
    | anchor =>
        exfalso
        exact (Nat.ne_of_lt hanchorBefore) hcepoch
    | @link source competing hsource link =>
        have hTU : link.signers ⊆ U := by
          intro i hi
          have hiEpoch := link.signers_in_epoch hi
          simpa only [U, hcepoch] using hiEpoch
        obtain ⟨i, hiSigner, hiLink, hiHonest⟩ :=
          one_third_honest_intersects_two_thirds E
            hsignersEpoch hTU hsignersHonest hU honeThird
              link.supermajority
        obtain ⟨sl, k, aTarget, _, hcomm, hsEpoch, hvoteTarget, hvoteP⟩ :=
          hvotes i hiSigner
        obtain ⟨a, ⟨body, htipBody, hincluded⟩, hiA, _haSource, haTarget⟩ :=
          link.signer_attestation i hiLink
        have evidence := B.state.includedAttestations.evidence hincluded
        have hbodyKnown : body ∈ (E.store cfg ext w m).block_roots :=
          (E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
            hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
            htip ⟨evidence.carrier_message, evidence.carrier_at⟩ htipBody).1
        have hbodyEq : evidence.carrier_message =
            (E.store cfg ext w m).blocks body :=
          evidence.carrier_accepted.unique cfg ext E hT.wellFormed
            (E.acceptedBlockAt_of_causal_known cfg ext
              (E.store_causal cfg ext w m) hbodyKnown)
        have haBefore : a.data.slot < E.slot_at cfg m := by
          calc
            a.data.slot < evidence.carrier_message.slot := evidence.slot_before_carrier
            _ = ((E.store cfg ext w m).blocks body).slot := congrArg BeaconBlock.slot hbodyEq
            _ ≤ get_current_slot cfg (E.store cfg ext w m) :=
              E.store_blocks_slot_le_current cfg ext hT.whole_seconds
                hgenShort w m body hbodyKnown
            _ = E.slot_at cfg m := E.store_current_slot cfg ext w m
        have haEpoch : compute_epoch_at_slot cfg a.data.slot = target.epoch := by
          rw [← evidence.target_epoch, haTarget]
          exact hcepoch
        have haSlot : a.data.slot = sl :=
          hT.externals_coherence.committee_assignment_unique i a.data.slot sl
            (evidence.attesters_in_committee i hiA) hcomm (haEpoch.trans hsEpoch.symm)
        obtain ⟨hepochTarget, hP⟩ := hvoteP (haSlot ▸ haBefore)
        obtain ⟨sender, sent, haSchedule⟩ := evidence.received_from_block
        obtain ⟨kCompeting, aCompeting, _hcausal, hvoteCompeting,
            hdataCompeting⟩ := hT.honest_behavior.no_forgery
              sender sent a true haSchedule i hiHonest hiA
        have haCompetingExact : aCompeting.data.target = c := by
          rw [← hdataCompeting]
          exact haTarget
        have htargets : aTarget.data.target = c := by
          by_contra hneTarget
          have hdataNe : aTarget.data ≠ aCompeting.data := by
            intro hdataEq
            apply hneTarget
            exact (congrArg AttestationData.target hdataEq).trans haCompetingExact
          have hepoch : aTarget.data.target.epoch = aCompeting.data.target.epoch := by
            rw [haCompetingExact]
            exact hepochTarget.trans hcepoch.symm
          have hslash : is_slashable_attestation_data
              aTarget.data aCompeting.data = true := by
            simp [is_slashable_attestation_data, hdataNe, hepoch]
          have hnot := hT.honest_behavior.not_slashable i hiHonest
            sl a.data.slot k kCompeting aTarget aCompeting
            hvoteTarget hvoteCompeting
          rw [hslash] at hnot
          contradiction
        rwa [htargets] at hP



/-- Every endpoint justified checkpoint has an included certificate at a
root known in that endpoint store. This retains the timing data erased by
the global scheduled-certificate projection. -/
theorem ScheduledFFGInterpretation.endpointJustified_includedCertificate
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {w : ValidatorIndex} {m : ℕ} :
    ∃ tip, tip ∈ (E.store cfg ext w m).block_roots ∧
      IncludedCertifiedJustified cfg E B.state.includedAttestations.Included
        B.anchor tip (E.store cfg ext w m).justified_checkpoint := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis_structure
  by_cases heq : (E.store cfg ext w m).justified_checkpoint = B.anchor
  · have hknown : ablk.root ∈ E.genesis_store.block_roots := by
      simp [hgen, get_forkchoice_store]
    refine ⟨ablk.root, (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hknown, ?_⟩
    rw [heq]
    exact .anchor
  · have hevidence := B.globalJustified_anchor_or_AUEvidence
      ⟨ast, ablk, hgen, hslot⟩ hanchor (E.store_causal cfg ext w m)
    obtain ⟨carrier⟩ := hevidence.resolve_left heq
    obtain ⟨body, hbody, _⟩ := carrier.formed_evidence.causal.resolve_left heq
    have hroot : E.ExecutionRoot carrier.carrier := by
      obtain ⟨store, hstore, hr, hmessage⟩ := hbody
      rcases hstore.blockProvenance cfg ext E carrier.carrier hr with
          hgenRoot | ⟨sb, ⟨sender, time, hsched⟩, hsbRoot, hsbMessage⟩
      · exact ⟨store.blocks carrier.carrier, Or.inl hgenRoot⟩
      · exact ⟨store.blocks carrier.carrier,
          Or.inr ⟨sender, time, sb, hsched, hsbRoot, hsbMessage.symm⟩⟩
    have hknown := (E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hT.wellFormed hT.externals_coherence hgen hslot hparent
      carrier.tip_carrier.known hroot carrier.tip_descends_carrier).1
    exact ⟨carrier.carrier, hknown, carrier.formed_evidence.certified.some⟩

/-- Current-target pinning at a real endpoint needs only earlier honest
votes. It does not need a strict bound on the endpoint's justified epoch. -/
theorem completedPrefix_currentTarget_endpoint_root_eq_before
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hfloor : cfg.effective_balance_increment ≤ E.weight (E.anchorActiveValidators cfg))
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hgate : will_current_target_be_justified cfg ext (E.store cfg ext v (n + 1)) = true)
    {w : ValidatorIndex} {m : ℕ}
    (hsupport : E.HonestVotesSupportTargetBefore cfg
      (get_current_target cfg (E.store cfg ext v (n + 1))) (n + 1) (E.slot_at cfg m))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    (E.store cfg ext w m).justified_checkpoint.root =
      (get_current_target cfg (E.store cfg ext v (n + 1))).root := by
  obtain ⟨tip, htip, hcert⟩ := ScheduledFFGInterpretation.endpointJustified_includedCertificate
    cfg ext B hT hanchor
    (w := w) (m := m)
  refine completedPrefix_noConflict_includedJustified_property_before
    cfg ext B hT hstatic hbyz hfloor
    hfit hanchor hboundary hv hH (currentTargetGate_implies_noConflict cfg ext hgate)
    htip (fun c => c.root = (get_current_target cfg (E.store cfg ext v (n + 1))).root)
    rfl ?_ hcert hepoch
  intro i hi sl hsH hsl hqsl hbefore k a hvote
  have ht := hsupport.2 i hi sl hsH hsl hqsl hbefore k a hvote
  exact ⟨congrArg Checkpoint.epoch ht, congrArg Checkpoint.root ht⟩

/-- Previous-result pinning at a real endpoint also needs only earlier
honest votes. Distinct target roots are permitted. -/
theorem completedPrefix_noConflict_endpoint_descends_before
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hfloor : cfg.effective_balance_increment ≤ E.weight (E.anchorActiveValidators cfg))
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg) (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg (n + 1))
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true)
    {w : ValidatorIndex} {m : ℕ} {result : Root}
    (htargetResult : E.RootDescends
      (get_current_target cfg (E.store cfg ext v (n + 1))).root result)
    (hsupport : E.HonestVotesTargetDescendFromBefore cfg result
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) (n + 1) (E.slot_at cfg m))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    E.RootDescends (E.store cfg ext w m).justified_checkpoint.root result := by
  obtain ⟨tip, htip, hcert⟩ := ScheduledFFGInterpretation.endpointJustified_includedCertificate
    cfg ext B hT hanchor
    (w := w) (m := m)
  exact completedPrefix_noConflict_includedJustified_property_before
    cfg ext B hT hstatic hbyz hfloor
    hfit hanchor hboundary hv hH hgate htip (fun c => E.RootDescends c.root result)
    htargetResult hsupport.2 hcert hepoch

end Execution

end FastConfirmation.Spec

end
