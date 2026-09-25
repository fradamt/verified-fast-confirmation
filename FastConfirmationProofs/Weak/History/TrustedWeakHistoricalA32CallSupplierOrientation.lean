module
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32CallSupplier
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32CallSupplier
public import FastConfirmationProofs.FFG.SelectedSource.TrustedEndpointJustifiedOrientationBase
public import FastConfirmationProofs.FFG.SelectedSource.TrustedSelectedJustifiedOrientationRest
public import FastConfirmationProofs.Weak.Certificates.TrustedEndpointQuorumCausality
public import FastConfirmationProofs.Execution.Calls.TrustedScheduledPrefixGeometry
public import FastConfirmationProofs.Execution.Calls.TrustedCurrentTargetPrefixVoteRealization
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetWalkKnownness

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

private theorem mem_observerNoConflict_epoch_span_of_committee
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

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot between the canonical first and last slots of epoch `e` has epoch
exactly `e`.  Cloned rather than reused because the source copy
(`CurrentTargetFutureSupport.lean:65`) is `private`; the statement mentions no
node, no store, and no honesty. -/
private theorem observerNoConflict_epoch_eq_of_epoch_bounds
    {e : Epoch} {s : Slot}
    (hlo : e * cfg.slots_per_epoch ≤ s)
    (hhi : s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) :
    compute_epoch_at_slot cfg s = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le hlo
  calc
    s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := hhi
    _ < e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
      Nat.add_lt_add_left
        (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
    _ = (e + 1) * cfg.slots_per_epoch := by
      simp only [Nat.add_mul, one_mul]

/-- **N3** of `docs/trunkB-two-case-discharge.md` §7: case-β pinning of the
endpoint justification against the query's current target, with **no**
`HonestVotesSupportTarget` proviso.

Case β is the branch in which no honest member of the endpoint
justification's quorum voted at or after the query slot
(`hnoPostQuery`).  The proof is §5.3 of that note, i.e. the existing
arithmetic-branch argument with one seat argument swapped:

* the executable gate still puts more than one third of total active weight in
  the concrete honest signer set `currentTargetA32Signers` (N4, and note that
  the crossing arm supplies the same raw inequality, §5.5);
* `one_third_honest_intersects_two_thirds` still intersects that set with the
  two-thirds quorum, now taken from `Execution.EndpointJustifiedQuorumAt`
  rather than from a bare `SupermajorityLink`;
* an **observed** honest supporter is pinned exactly as before, by
  `no_forgery` plus `HonestBehavior.not_slashable`;
* a **future** seat is now excluded outright: by N1 the quorum attestation is
  assigned to the signer's committee slot and carries the target epoch, so
  `BeaconExternalsPremises.committee_assignment_unique` identifies its slot with the
  future seat's slot, which is at or after the query slot — contradicting
  `hnoPostQuery`.  This is where the proviso used to be consumed
  (`currentTargetFutureHonestSeat_vote`), and the replacement needs no
  statement about future votes at all.

The honesty and epoch-span side conditions on the signer set are re-derived
without the proviso, as §5.2 items 1-2 record. -/
theorem trusted_noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgateRaw :
      get_current_target cfg (E.store cfg ext obs (n + 1)) =
          (E.store cfg ext obs (n + 1)).unrealized_justified_checkpoint ∨
        E.total_active cfg <
          3 * compute_honest_ffg_support_for_current_target cfg ext
            (E.store cfg ext obs (n + 1)))
    {w : ValidatorIndex} {m : Nat}
    (Q : E.EndpointJustifiedQuorumAt cfg ext B.anchor w m)
    (hnoPostQuery : ¬ Q.PostQueryHonestSigner cfg ext (n + 1))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext obs (n + 1))).epoch) :
    (E.store cfg ext w m).justified_checkpoint.root =
      (get_current_target cfg (E.store cfg ext obs (n + 1))).root := by
  classical
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hgenZero : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgen⟩
  let hA := E.trusted_noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    cfg ext B hT hC.static_validators hC.byzantine_bound hanchor hboundary
  let hAccA : FFGAccountabilityAssumptions cfg ext E :=
    { genesis_store := hgenZero
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      externals_coherence := hT.externals_coherence
      static_validator_set := hC.static_validators
      byzantine_bound := hC.byzantine_bound }
  let hacc : CertificateAccountability cfg E B.anchor :=
    CertificateAccountability.of_assumptions cfg ext hAccA
  let store := E.store cfg ext obs (n + 1)
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  change (E.store cfg ext w m).justified_checkpoint.epoch = target.epoch
    at hepoch
  change (E.store cfg ext w m).justified_checkpoint.root = target.root
  obtain ⟨hc⟩ :=
    TrustedCausalPrefixFFGInterpretation.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  have hstate : state = get_pulled_up_head_state cfg ext store := rfl
  have hval : state.validators = E.registry := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_validators_at_observer cfg ext hT
        hcoh hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
        hC.static_validators hcoh hHn1
  have hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg store) := by
    simpa only [store] using
      E.currentTargetEpochEnd_within_of_epochEndsFitUint64
        cfg ext hfit (v := obs) hHn1
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon :=
    E.completedPrefix_anchor_epoch_within cfg ext hT hC.static_validators
  have hstoreCausal : E.CausalStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext obs (n + 1)
  obtain ⟨hUJ⟩ :=
    TrustedCausalPrefixFFGInterpretation.unrealizedJustified_certificate
      cfg ext B hgenShort hanchor hstoreCausal
  by_cases heq : target = store.unrealized_justified_checkpoint
  · have hroot := hacc.justified_unique hc hUJ
      (hepoch.trans (congrArg Checkpoint.epoch heq))
    exact hroot.trans (congrArg Checkpoint.root heq).symm
  · have htargetNotAnchor : target ≠ B.anchor := by
      intro htargetAnchor
      have htargetEpoch : target.epoch =
          compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) := by
        simp only [target, store, get_current_target,
          get_checkpoint_for_block, get_current_store_epoch,
          E.store_current_slot cfg ext obs (n + 1)]
      have hUJLeTarget : store.unrealized_justified_checkpoint.epoch ≤
          target.epoch := by
        have hbound := (E.store_CkptEpochLe cfg ext
          hT.externals_coherence hT.whole_seconds hgenShort obs (n + 1)).2
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
    let p := E.completedScheduledEventPrefix obs n
    have hpstore : p.store cfg ext = store := by
      simpa only [p, store] using
        E.completedScheduledEventPrefix_store cfg ext obs n
    have hanchorBefore : B.anchor.epoch < target.epoch := by
      have hprefix := p.trusted_currentTarget_anchor_epoch_lt_of_ne
        cfg ext B hT hanchor hboundary
        (by
          rw [hpstore]
          simpa only [target, store] using htargetNotAnchor)
      simpa only [hpstore, target, store] using hprefix
    have hobservedVote : ∀ i ∈ E.currentTargetObservedHonestSupporters cfg
        store state,
        Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
          deadline target) := by
      intro i hiObserved
      let hV := CurrentTargetPrefixVoteAssumptions.of_trustedGlobalTrajectory
        cfg ext E B hT hanchor hboundary
      have hboundaryZero : TrustedAnchorBoundaryAligned
          (cfg := cfg) (E := E)
          (anchor := E.genesis_store.justified_checkpoint) := by
        simpa only [← hanchor] using hboundary
      have hvote :=
        E.trusted_currentTargetObservedHonestSupporter_vote_of_prefix_of_provenance
          cfg ext B hV hboundaryZero p
            (p.latestMessageProvenance_of_observer_validity cfg ext hT
              hcoh.validity hHn1) hHn1
            (by simpa only [hpstore, state, store] using hiObserved)
      rw [hpstore] at hvote
      simpa only [store, target, deadline] using hvote
    have hfutureSeat : ∀ i ∈ (E.currentTargetFutureSpan cfg store).filter
        (fun j => j ∈ E.honest),
        i ∈ E.honest ∧ ∃ s : Slot,
          E.slot_at cfg (n + 1) ≤ s ∧ i ∈ E.committee s ∧
            compute_epoch_at_slot cfg s = target.epoch := by
      intro i hiFuture
      simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
        Execution.span_committee, Finset.mem_biUnion,
        Finset.mem_Icc] at hiFuture
      obtain ⟨⟨s, hs, hiCommittee⟩, hi⟩ := hiFuture
      refine ⟨hi, s, ?_, hiCommittee, ?_⟩
      · rw [← E.store_current_slot cfg ext obs (n + 1)]
        exact hs.1
      · have hloCurrent : get_current_store_epoch cfg store *
            cfg.slots_per_epoch ≤ get_current_slot cfg store := by
          have h := Nat.div_mul_le_self (get_current_slot cfg store)
            cfg.slots_per_epoch
          simpa only [get_current_store_epoch, Nat.mul_comm] using h
        have hsEpoch : compute_epoch_at_slot cfg s =
            get_current_store_epoch cfg store := by
          apply observerNoConflict_epoch_eq_of_epoch_bounds cfg
          · exact hloCurrent.trans hs.1
          · simpa only [currentTargetEpochEnd, currentTargetEpochStart,
              compute_start_slot_at_epoch] using hs.2
        exact hsEpoch
    have hsignersHonest : signers ⊆ E.honest := by
      intro i hi
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hi
      rcases hi with hiObserved | hiFuture
      · obtain ⟨vote⟩ := hobservedVote i hiObserved
        exact vote.honest
      · exact (hfutureSeat i hiFuture).1
    have hsignersEpoch : signers ⊆
        E.span_committee (target.epoch * cfg.slots_per_epoch)
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
      intro i hi
      simp only [signers, Execution.currentTargetA32Signers,
        Finset.mem_union] at hi
      rcases hi with hiObserved | hiFuture
      · obtain ⟨vote⟩ := hobservedVote i hiObserved
        exact mem_observerNoConflict_epoch_span_of_committee cfg
          vote.assigned vote.slot_epoch
      · obtain ⟨_hi, s, _hsQuery, hiCommittee, hsEpoch⟩ :=
          hfutureSeat i hiFuture
        exact mem_observerNoConflict_epoch_span_of_committee cfg
          hiCommittee hsEpoch
    have hevidence := E.completedScheduledEventPrefix_accountingEvidence_at_observer
      cfg ext hT hcoh n hHn1
    have hraw : E.total_active cfg <
        3 * compute_honest_ffg_support_for_current_target cfg ext store :=
      hgateRaw.resolve_left heq
    have honeThird : E.total_active cfg < 3 * E.weight signers := by
      simpa only [signers, store, state] using
        E.noConflict_arithmeticBranch_oneThird_of_rawGate cfg ext hA
          hevidence hHn1 hstate hval htab hendH hanchorH hC.balance_floor
          hraw
    have hcurrentH : E.SlotWithinHorizon cfg
        (get_current_slot cfg store) := by
      rw [show get_current_slot cfg store = E.slot_at cfg (n + 1) by
        simpa only [store] using
          E.store_current_slot cfg ext obs (n + 1)]
      exact ⟨hHn1.2.1, hHn1.2.2⟩
    let U := E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1))
    have hspanEq : U = E.currentTargetAnchorActive cfg := by
      simpa only [U, target, store, get_current_target,
        get_checkpoint_for_block, currentTargetEpochStart,
        currentTargetEpochEnd, compute_start_slot_at_epoch] using
        E.current_epoch_span_eq_anchorActive cfg ext
          hT.externals_coherence hC.static_validators hcurrentH hendH
            hanchorH
    have hU : E.weight U ≤ E.total_active cfg := by
      rw [hspanEq, ← E.total_active_eq_anchorActive_weight
        cfg hC.balance_floor]
    have hTU : Q.signers ⊆ U := by
      intro i hi
      have hiEpoch := Q.signers_in_epoch hi
      simpa only [U, hepoch] using hiEpoch
    obtain ⟨i, hiSigner, hiQ, hiHonest⟩ :=
      one_third_honest_intersects_two_thirds E
        hsignersEpoch hTU hsignersHonest hU honeThird Q.supermajority
    obtain ⟨u, n', a, fb, hsched, hia, haTarget, haH, ha0, haEpoch,
      haCommittee, haBound⟩ := Q.signer_attestation i hiQ
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · obtain ⟨vote⟩ := hobservedVote i hiObserved
      obtain ⟨kCompeting, aCompeting, _hcausal, hvoteCompeting, hdataCompeting⟩ := hT.honest_behavior.no_forgery
            u n' a fb hsched i hiHonest hia
      let aTarget := honest_attestation cfg ext
        (E.store cfg ext i vote.time) vote.slot vote.index i
      have hvoteTarget : E.vote i vote.slot =
          some (vote.time, aTarget) := by
        simpa only [aTarget] using vote.vote
      have haTargetExact : aTarget.data.target = target := by
        simpa only [aTarget] using vote.target_eq
      have haCompetingExact : aCompeting.data.target =
          (E.store cfg ext w m).justified_checkpoint := by
        rw [← hdataCompeting]
        exact haTarget
      by_contra hroot
      have hdataNe : aTarget.data ≠ aCompeting.data := by
        intro hdataEq
        have htargets := congrArg
          (fun d : AttestationData Root => d.target) hdataEq
        change aTarget.data.target = aCompeting.data.target at htargets
        rw [haTargetExact, haCompetingExact] at htargets
        exact hroot (congrArg Checkpoint.root htargets).symm
      have htargetEpoch :
          aTarget.data.target.epoch =
            aCompeting.data.target.epoch := by
        rw [haTargetExact, haCompetingExact]
        exact hepoch.symm
      have hslash : is_slashable_attestation_data
          aTarget.data aCompeting.data = true := by
        simp [is_slashable_attestation_data, hdataNe, htargetEpoch]
      have hnot := hT.honest_behavior.not_slashable i hiHonest
        vote.slot a.data.slot vote.time kCompeting aTarget aCompeting
        hvoteTarget hvoteCompeting
      rw [hslash] at hnot
      contradiction
    · exfalso
      obtain ⟨_hi, s, hsQuery, hiCommittee, hsEpoch⟩ :=
        hfutureSeat i hiFuture
      have haSlotEpoch : compute_epoch_at_slot cfg a.data.slot =
          compute_epoch_at_slot cfg s := by
        rw [hsEpoch, haEpoch]
        exact hepoch
      have haSlotEq : a.data.slot = s :=
        hT.externals_coherence.committee_assignment_unique i a.data.slot s
          haCommittee hiCommittee haSlotEpoch
      apply hnoPostQuery
      exact ⟨i, hiQ, hiHonest, u, n', a, fb, hsched, hia, haTarget, haH,
        ha0, haBound, by rw [haSlotEq]; exact hsQuery⟩

set_option maxRecDepth 10000 in
/-- **N6** of `docs/trunkB-two-case-discharge.md` §7 at a possibly-Byzantine
observer: the executable gate alone decides, for every endpoint, between the
trusted anchor, a post-query honest quorum member, and same-epoch pinning
against the query's current target.

The case split is `by_cases` on
`Execution.EndpointJustifiedQuorumAt.PostQueryHonestSigner` applied to the
quorum N1 extracts from a non-anchor endpoint justification; case α is N2 and
case β is N3 above.  Neither the quorum extraction nor the case-β pinning
mentions the observer's honesty, so this is the observer twin of
`Execution.completedPrefix_endpointOriginOrPinnedProducerAt` with the honest
binder replaced by `Execution.ObserverCoherence`. -/
theorem trusted_observerCall_endpointOriginOrPinnedProducerAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor (n + 1)
      (E.weakFcrStep cfg ext obs n) := by
  classical
  intro hgate w m
  simp only [E.weakFcrStep_store] at hgate ⊢
  have htab : get_total_active_balance cfg
      (get_pulled_up_head_state cfg ext (E.store cfg ext obs (n + 1))) =
      E.total_active cfg :=
    E.completedPrefix_pulledUpHead_totalActive_at_observer cfg ext hT
      hC.static_validators hcoh hHn1
  have hpos : 0 < E.total_active cfg := by
    rw [E.total_active_eq_anchorActive_weight cfg hC.balance_floor]
    exact Nat.lt_of_lt_of_le cfg.effective_balance_increment_pos
      hC.balance_floor
  have hgateRaw := E.rawGate_of_executableGate cfg ext htab hpos hgate
  by_cases hne : (E.store cfg ext w m).justified_checkpoint = B.anchor
  · exact Or.inl hne
  · obtain ⟨Q⟩ :=
      TrustedCausalPrefixFFGInterpretation.endpointJustified_quorumAt
        cfg ext B hT hanchor hboundary hne
    by_cases hpost : Q.PostQueryHonestSigner cfg ext (n + 1)
    · exact Or.inr (Or.inl
        (EndpointJustifiedQuorumAt.causalHonestTargetAt_of_postQuerySigner
          cfg ext hT.honest_behavior hpost))
    · refine Or.inr (Or.inr fun hepoch => ?_)
      exact
        E.trusted_noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer
          cfg ext B hT hC hfit hanchor hboundary hcoh hHn1 hgateRaw Q hpost
          hepoch

end Execution
end FastConfirmation.Spec
end
