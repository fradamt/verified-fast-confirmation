module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.Execution.History.CompletedPrefixCalls
public import FastConfirmationProofs.FFG.SourceHistory.CurrentSameSourceHistory
public import FastConfirmationProofs.FFG.Certificates.NoConflictCertificatePinning

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Actual-call accepted selected / justified orientation

This file installs the three abstract producers consumed by
`strictSelected_result_and_child_ancestor_of_endpointJustified_accepted` at
one completed `Execution.fcr` call:

* the accepted live current-target gate;
* the retained historical A3.2 payload; and
* accepted-state no-conflict certificate pinning.

The no-conflict arithmetic branch predicts votes through the last slot of the
current epoch.  `Execution.WithinHorizon` already proves that epoch is inside
the verified epoch range.  For a completely generic `Config`, however, the
last slot of the epoch containing `UINT64_MAX` need not itself be representable.
The preset condition below is the exact missing machine-arithmetic fact.  It
holds for Phase0's power-of-two `SLOTS_PER_EPOCH` presets (in particular the
mainnet value `32`).  The equality branch of the helper does not use it.

No endpoint filter, safety conclusion, legacy `ChainFFGState`, or legacy FFG
pipeline is an input.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-! ## Accepted no-conflict lower contracts -/

/-- The accepted global unrealized-justified field has a concrete Casper
certificate.  This is the accepted-state replacement for the legacy
`ChainFFGState.gu_certified` equality branch. -/
theorem ScheduledFFGInterpretation.unrealizedJustified_certificate
    (B : ScheduledFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store) :
    Nonempty (CertifiedJustified cfg E B.anchor
      store.unrealized_justified_checkpoint) := by
  have horigins :=
    (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
  rcases horigins.unrealized_justified with
      hfieldAnchor | ⟨tip, htip, hfield⟩
  · rw [hfieldAnchor]
    exact ⟨CertifiedJustified.anchor⟩
  · have hAU : B.state.AvailableCheckpoint cfg ext tip
        store.unrealized_justified_checkpoint := by
      rw [hfield]
      exact B.state.gu_AU cfg ext htip.acceptedRoot
    obtain ⟨hincluded⟩ :=
      B.state.includedJustifiedAtTip_of_AU cfg ext hAU
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedBlockAttestationInclusion.relation
        cfg ext E B.state.includedAttestations) hincluded⟩

/-- Accepted global checkpoint geometry supplies the sole store-domain field
of the otherwise protocol-level no-conflict arithmetic bundle. -/
def noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor)) :
    NoConflictPinningAssumptions cfg ext E where
  genesis := hT.genesis_structure
  wellFormed := hT.wellFormed
  whole_seconds := hT.whole_seconds
  honest_behavior := hT.honest_behavior
  externals_coherence := hT.externals_coherence
  static_validators := hstatic
  byzantine_bound := hbyz
  justified_root_known := by
    intro w hw m hmH
    exact E.justifiedRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hw m hmH

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

/-- Accepted-state no-conflict pinning at a completed scheduled boundary.

The equality branch uses the actual accepted global UJ certificate.  The
arithmetic branch reuses the executable helper accounting, but reconstructs
the observed signer votes through the exact accepted prefix rather than the
deprecated scheduled-root FFG state. -/
theorem completedPrefix_noConflict_certifiedJustified_root_eq_currentTarget
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true)
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v (n + 1))) (n + 1))
    {c : Checkpoint Root}
    (hc : CertifiedJustified cfg E B.anchor c)
    (hcepoch : c.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    c.root =
      (get_current_target cfg (E.store cfg ext v (n + 1))).root := by
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
  let hA := E.noConflictPinningAssumptions_of_acceptedGlobalTrajectory
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
  let store := E.store cfg ext v (n + 1)
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  change c.epoch = target.epoch at hcepoch
  change c.root = target.root
  have hstate : state = get_pulled_up_head_state cfg ext store := rfl
  have hval : state.validators = E.registry := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_validators cfg ext B hT
        hanchor hboundary hv hHn1
  have htab : get_total_active_balance cfg state = E.total_active cfg := by
    simpa only [state, store] using
      E.completedPrefix_pulledUpHead_totalActive cfg ext B hT
        hC.static_validators hanchor hboundary hv hHn1
  have hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg store) := by
    simpa only [store] using
      E.currentTargetEpochEnd_within_of_epochEndsFitUint64
        cfg ext hfit (v := v) hHn1
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon :=
    E.completedPrefix_anchor_epoch_within cfg ext hT hC.static_validators
  have hstoreCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v (n + 1)
  obtain ⟨hUJ⟩ :=
    ScheduledFFGInterpretation.unrealizedJustified_certificate
      cfg ext B hgenShort hanchor hstoreCausal
  by_cases heq : target = store.unrealized_justified_checkpoint
  · have hroot := hacc.justified_unique hc hUJ
      (hcepoch.trans (congrArg Checkpoint.epoch heq))
    exact hroot.trans (congrArg Checkpoint.root heq).symm
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
        Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
          deadline target) := by
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
        simpa only [store, target, deadline] using hvote
      · simpa only [store, target, deadline] using
          E.currentTargetFutureHonestSeat_vote cfg ext hT.honest_behavior
            (by simpa only [store] using hendH)
            (by simpa only [store, target] using hsupport) hiFuture
    have hsignersHonest : signers ⊆ E.honest := by
      intro i hi
      obtain ⟨vote⟩ := hvotes i hi
      exact vote.honest
    have hsignersEpoch : signers ⊆
        E.span_committee (target.epoch * cfg.slots_per_epoch)
          (target.epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)) := by
      intro i hi
      obtain ⟨vote⟩ := hvotes i hi
      exact mem_acceptedNoConflict_epoch_span_of_committee cfg
        vote.assigned vote.slot_epoch
    have honeThird : E.total_active cfg < 3 * E.weight signers := by
      simpa only [signers, store, state] using
        E.noConflict_arithmeticBranch_oneThird cfg ext hA hv hHn1
          hstate hval htab hendH hanchorH hC.balance_floor heq hgate
    have hcurrentH : E.SlotWithinHorizon cfg
        (get_current_slot cfg store) := by
      rw [show get_current_slot cfg store = E.slot_at cfg (n + 1) by
        simpa only [store] using
          E.store_current_slot cfg ext v (n + 1)]
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
        obtain ⟨vote⟩ := hvotes i hiSigner
        obtain ⟨w, t, a, fromBlock, haSchedule, hiA,
            _haSource, haTarget⟩ := link.signer_attestation i hiLink
        obtain ⟨kCompeting, aCompeting, _hcausal, hvoteCompeting,
            hdataCompeting⟩ := hT.honest_behavior.no_forgery
              w t a fromBlock haSchedule i hiHonest hiA
        let aTarget := honest_attestation cfg ext
          (E.store cfg ext i vote.time) vote.slot vote.index i
        have hvoteTarget : E.vote i vote.slot =
            some (vote.time, aTarget) := by
          simpa only [aTarget] using vote.vote
        have haTargetExact : aTarget.data.target = target := by
          simpa only [aTarget] using vote.target_eq
        have haCompetingExact : aCompeting.data.target = c := by
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
          exact hcepoch.symm
        have hslash : is_slashable_attestation_data
            aTarget.data aCompeting.data = true := by
          simp [is_slashable_attestation_data, hdataNe, htargetEpoch]
        have hnot := hT.honest_behavior.not_slashable i hiHonest
          vote.slot a.data.slot vote.time kCompeting aTarget aCompeting
          hvoteTarget hvoteCompeting
        rw [hslash] at hnot
        contradiction

/-- Paper Lemma 42: every certified checkpoint in the query epoch descends
from the selected result. The future honest voters can use different targets.
The declaration above keeps the stronger exact-target theorem available. -/
theorem completedPrefix_noConflict_certifiedJustified_descends_result
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true)
    {result : Root}
    (htargetResult : E.RootDescends
      (get_current_target cfg (E.store cfg ext v (n + 1))).root result)
    (hsupport : HonestVotesTargetDescendFrom cfg E result
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) (n + 1))
    {c : Checkpoint Root}
    (hc : CertifiedJustified cfg E B.anchor c)
    (hcepoch : c.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    E.RootDescends c.root result := by
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
  let hA := E.noConflictPinningAssumptions_of_acceptedGlobalTrajectory
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
  let store := E.store cfg ext v (n + 1)
  let target := get_current_target cfg store
  let state := get_pulled_up_head_state cfg ext store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
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
        hC.static_validators hanchor hboundary hv hHn1
  have hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg store) := by
    simpa only [store] using
      E.currentTargetEpochEnd_within_of_epochEndsFitUint64
        cfg ext hfit (v := v) hHn1
  have hanchorH : get_current_epoch cfg E.anchor_state <
      E.verification_horizon :=
    E.completedPrefix_anchor_epoch_within cfg ext hT hC.static_validators
  have hstoreCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v (n + 1)
  obtain ⟨hUJ⟩ :=
    ScheduledFFGInterpretation.unrealizedJustified_certificate
      cfg ext B hgenShort hanchor hstoreCausal
  by_cases heq : target = store.unrealized_justified_checkpoint
  · have hroot := hacc.justified_unique hc hUJ
      (hcepoch.trans (congrArg Checkpoint.epoch heq))
    rw [hroot.trans (congrArg Checkpoint.root heq).symm]
    exact htargetResult
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
          E.vote i s = some (k, a) ∧ a.data.target.epoch = target.epoch ∧
          E.RootDescends a.data.target.root result := by
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
          vote.slot_epoch, vote.vote, ?_, ?_⟩
        · rw [vote.target_eq]
        · rw [vote.target_eq]
          exact htargetResult
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
        obtain ⟨hepoch, hdesc⟩ := hsupport.2 i hi sl hsH hsEpoch hquerySlot k _ hvote
        exact ⟨sl, k, _, hi, hiCommittee, hsEpoch, hvote, hepoch, hdesc⟩
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
          hstate hval htab hendH hanchorH hC.balance_floor heq hgate
    have hcurrentH : E.SlotWithinHorizon cfg
        (get_current_slot cfg store) := by
      rw [show get_current_slot cfg store = E.slot_at cfg (n + 1) by
        simpa only [store] using
          E.store_current_slot cfg ext v (n + 1)]
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
        obtain ⟨sl, k, aTarget, _, _, _, hvoteTarget, hepochTarget, hdesc⟩ :=
          hvotes i hiSigner
        obtain ⟨w, t, a, fromBlock, haSchedule, hiA,
            _haSource, haTarget⟩ := link.signer_attestation i hiLink
        obtain ⟨kCompeting, aCompeting, _hcausal, hvoteCompeting,
            hdataCompeting⟩ := hT.honest_behavior.no_forgery
              w t a fromBlock haSchedule i hiHonest hiA
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
        rwa [htargets] at hdesc


set_option maxRecDepth 10000 in
/-- Producer form used by the exact selector call-site dispatcher. -/
noncomputable def completedPrefix_noConflictCertificatePinningProducerAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.NoConflictCertificatePinningProducerAt cfg ext B.anchor (n + 1)
      (E.fcrStoreAtCall cfg ext v n) := by
  intro result htargetResult hgate hsupport c hc hcepoch
  have hgate' : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v (n + 1)) = true := by
    simpa only [E.fcrStep_store] using hgate
  have hsupport' : HonestVotesTargetDescendFrom cfg E result
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) (n + 1) := by
    simpa only [E.fcrStep_store] using hsupport
  have hcepoch' : c.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch := by
    simpa only [E.fcrStep_store] using hcepoch
  exact E.completedPrefix_noConflict_certifiedJustified_descends_result
    cfg ext B hT hC hfit hanchor hboundary hv hHn1 hgate'
      (by simpa only [E.fcrStep_store] using htargetResult) hsupport' hc hcepoch'

/-! ## Actual-call historical payload -/

private theorem BlockKnownInScheduledPrefix.executionRoot_for_actualOrientation
    {r : Root} {b : BeaconBlock Root}
    (h : E.BlockKnownInScheduledPrefix cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Materialize a retained lineage in an ordinary execution-boundary store.
This is accepted-root reflection plus the trusted-anchor boundary walk; it
does not use an endpoint, no-crossing fact, or safety conclusion. -/
private theorem AcceptedHistoricalA32LineageAt.payloadAtExecutionStore
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {tip : Root} {e : Epoch}
    (hlineage : E.AcceptedHistoricalA32LineageAt cfg ext B tip e)
    (htip : tip ∈ (E.store cfg ext v q).block_roots)
    (htipEpoch : get_block_epoch cfg (E.store cfg ext v q) tip = e) :
    Nonempty (E.AcceptedHistoricalA32GatePayloadAt cfg ext B tip e) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  let store := E.store cfg ext v q
  have hstoreCausal : E.ScheduledPrefixStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v q
  have hstoreParent : ParentSlotLt store := by
    simpa only [store] using E.store_parentSlotLt cfg ext hT.wellFormed
      hT.externals_coherence
      ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
      hT.wellFormed.anchor_parent_unscheduled v q
  have htip' : tip ∈ store.block_roots := by
    simpa only [store] using htip
  have horiginRoot : E.ExecutionRoot hlineage.origin :=
    hlineage.payload.origin_at.executionRoot_for_actualOrientation cfg ext
  have horiginReflection :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
      htip horiginRoot hlineage.descends
  have horigin : hlineage.origin ∈ store.block_roots := by
    simpa only [store] using horiginReflection.1
  have htipOrigin : is_ancestor store (get_node_for_root tip)
      (get_node_for_root hlineage.origin) = true := by
    simpa only [store] using horiginReflection.2
  have horiginAt : E.BlockKnownInScheduledPrefix cfg ext hlineage.origin
      (store.blocks hlineage.origin) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstoreCausal horigin
  have horiginBlock : hlineage.payload.origin_block =
      store.blocks hlineage.origin :=
    hlineage.payload.origin_at.unique cfg ext E hT.wellFormed horiginAt
  have horiginEpoch : get_block_epoch cfg store hlineage.origin = e := by
    simpa only [get_block_epoch, ← horiginBlock] using
      hlineage.payload.origin_epoch
  have htipEpoch' : get_block_epoch cfg store tip = e := by
    simpa only [store] using htipEpoch
  have hanchorLe : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
  have htipWalk : WalkKnown store
      (compute_start_slot_at_epoch cfg e) tip := by
    simpa only [store] using
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v q hanchorLe htip
  exact ⟨hlineage.payloadAtTip cfg ext hphase hstoreCausal hstoreParent
    horigin htip' horiginEpoch htipEpoch' htipOrigin htipWalk⟩

/-- The preceding lineage supplies a no-crossing current result. The call step
uses the no-crossing antecedent to exclude a fresh gate. It retains the
original call instead of requesting global helper support. -/
noncomputable def completedPrefix_acceptedHistoricalA32PayloadProducerAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hC : E.ScheduledFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hinvariant : E.AcceptedHistoricalA32CurrentLineageAt cfg ext B v n)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n)) :
    E.AcceptedHistoricalA32PayloadProducerAt cfg ext B
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  intro hcurrent hnoCrossing
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hqueryStore : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hwrite : E.confirmed cfg ext v (n + 1) = trace.result := by
    exact (E.confirmed_succ_of_advance cfg ext v n hcall).trans
      trace.result_eq.symm
  have hcurrentConfirmed : get_block_epoch cfg
        (E.store cfg ext v (n + 1)) (E.confirmed cfg ext v (n + 1)) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    rw [hwrite]
    simpa only [query, trace, hqueryStore] using hcurrent
  have hprovisos : getLatestSelectorGuard cfg query trace.afterObserved →
      SelectedPredictionVoteSupport cfg ext E v (n + 1) query trace.afterObserved := by
    intro _
    constructor
    · intro a c hedge
      exact False.elim (hnoCrossing ⟨a, c, hedge⟩)
    · intro result hresult _ hnotCurrent _
      have heq : result = trace.result := hresult.symm.trans hselector.result_eq.symm
      exact False.elim (hnotCurrent (by simpa only [heq] using hcurrent))
  obtain ⟨e, ⟨hlineage⟩⟩ := E.getLatestConfirmedTraceAt_currentLineage_step
    cfg ext B hT hC.phase0_source hC.phase0_boundary_source hanchor hboundary hv hHn1
    hinvariant.confirmed_known hcurrent hprovisos
    (E.completedPrefix_acceptedTargetGateProducerAt cfg ext B hT hC hfit
      hanchor hboundary hv hcall hHn1) hinvariant.current_lineage
  have hresultKnown : trace.result ∈ query.store.block_roots :=
    E.getLatestConfirmedTraceAt_result_known cfg ext B hT hanchor hboundary
      hv hHn1 hinvariant.confirmed_known
  have hqueryCausal : E.ScheduledPrefixStore cfg ext query.store := by
    rw [hqueryStore]
    exact E.store_causal cfg ext v (n + 1)
  have hresultAt : E.BlockKnownInScheduledPrefix cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal hresultKnown
  have htipBlock : hlineage.tip_block =
      query.store.blocks trace.result :=
    hlineage.tip_at.unique cfg ext E hT.wellFormed hresultAt
  have hresultEpoch : get_block_epoch cfg query.store trace.result = e := by
    simpa only [get_block_epoch, ← htipBlock] using hlineage.tip_epoch
  have hpayload : Nonempty
      (E.AcceptedHistoricalA32GatePayloadAt cfg ext B trace.result e) := by
    apply hlineage.payloadAtExecutionStore cfg ext B hT hC.phase0_source
      hanchor hboundary
    · simpa only [hqueryStore] using hresultKnown
    · simpa only [hqueryStore] using hresultEpoch
  have hparent : ParentSlotLt query.store := by
    let hdomain := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary
    simpa only [hqueryStore] using (hdomain v hv (n + 1) hHn1).1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    let hdomain := E.storeDomainK_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary
    simpa only [hqueryStore] using (hdomain v hv (n + 1) hHn1).2.1
  have hhead : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    rw [hqueryStore]
    exact E.headRootKnown_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary hv (n + 1) hHn1
  have hstrictFind : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input
      (hselector.result_eq.trans hfixed)
  have hbelow : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root trace.result) = true := by
    rw [hselector.result_eq]
    exact strictSelectedResult_below_head cfg ext hparent hwalk
      hhead (by simpa only [query, trace] using hinput) hstrictFind
  have hboundaryResult : compute_start_slot_at_epoch cfg e ≤
      (query.store.blocks trace.result).slot := by
    rw [← hresultEpoch]
    exact start_slot_at_block_epoch_le cfg query.store trace.result
  have hwalkHead : WalkKnown query.store
      (compute_start_slot_at_epoch cfg e) (get_head cfg query.store).root := by
    have hanchorLe : B.anchor.epoch ≤ e := hlineage.payload.anchor_epoch_le
    have hw :=
      E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
        hanchor hboundary v (n + 1) hanchorLe
          (by simpa only [hqueryStore] using hhead)
    simpa only [hqueryStore] using hw
  have hcheckpoint : get_checkpoint_block cfg query.store
        (get_head cfg query.store).root e =
      get_checkpoint_block cfg query.store trace.result e :=
    get_checkpoint_block_of_ancestor cfg hparent
      (by rw [is_ancestor_node_root] at hbelow; exact hbelow)
      hboundaryResult hwalkHead
  have heCurrent : e = get_current_store_epoch cfg query.store := by
    exact hresultEpoch.symm.trans hcurrent
  refine ⟨e, ?_, hpayload⟩
  calc
    get_current_target cfg query.store =
        get_checkpoint_for_block cfg query.store
          (get_head cfg query.store).root
            (get_current_store_epoch cfg query.store) := rfl
    _ = get_checkpoint_for_block cfg query.store
          (get_head cfg query.store).root e := by rw [heCurrent]
    _ = get_checkpoint_for_block cfg query.store trace.result e := by
      exact congrArg (Checkpoint.mk e) hcheckpoint
    _ = B.state.checkpoint_at_epoch trace.result e :=
      (B.coherence.checkpoint_of_known hqueryCausal trace.result
        hresultKnown e).symm

end Execution

end FastConfirmation.Spec

end
