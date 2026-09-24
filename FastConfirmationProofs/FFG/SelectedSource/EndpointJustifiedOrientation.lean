module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.SelectedSource.SelectedJustifiedOrientation
public import FastConfirmationProofs.Execution.History.CompletedPrefixCalls
public import FastConfirmationProofs.FFG.SourceHistory.CurrentSameSourceHistory
public import FastConfirmationProofs.FFG.Certificates.NoConflictCertificatePinning
public import FastConfirmationProofs.Weak.Certificates.EndpointQuorumCausality
public import FastConfirmationProofs.Weak.History.AcceptedHistoricalA32OriginCall
public import FastConfirmationProofs.ModelFacts

@[expose] public section


/-!
# Actual-call accepted selected / justified orientation

This file installs the two abstract producers consumed by
`strictSelected_result_and_child_ancestor_of_endpointJustified_accepted` at
one completed `Execution.fcr` call:

* the retained historical A3.2 payload; and
* the gate-driven endpoint origin/pinning disjunction
  (`Execution.EndpointOriginOrPinnedProducerAt`), whose case-β half is **N3**
  of `docs/trunkB-two-case-discharge.md` §7.

Since that note's N5/N6 the live current-target gate producer is no longer an
input on this path: both executable gate arms of the call site reduce to the
same raw helper inequality (§5.5), and the disjunction is decided by a
`by_cases` on the endpoint quorum rather than by the target-support proviso.

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
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Accepted no-conflict lower contracts -/

/-- The accepted global unrealized-justified field has a concrete Casper
certificate.  This is the accepted-state replacement for the legacy
`ChainFFGState.gu_certified` equality branch. -/
theorem CausalPrefixFFGInterpretation.unrealizedJustified_certificate
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    Nonempty (CertifiedJustified cfg E B.anchor
      store.unrealized_justified_checkpoint) := by
  have horigins :=
    (B.causalStoreGlobalProjection hgen hanchor hstore).storeGlobal
  rcases horigins.unrealized_justified with
      hfieldAnchor | ⟨tip, htip, hfield⟩
  · rw [hfieldAnchor]
    exact ⟨CertifiedJustified.anchor⟩
  · have hAU : B.state.AU cfg ext tip
        store.unrealized_justified_checkpoint := by
      rw [hfield]
      exact B.state.gu_AU cfg ext htip.acceptedRoot
    obtain ⟨hincluded⟩ :=
      B.state.includedJustifiedAtTip_of_AU cfg ext hAU
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.TrustedCarrierAttestationRelation.relation
        cfg ext E B.state.includedAttestations) hincluded⟩

/-- Accepted global checkpoint geometry supplies the sole store-domain field
of the otherwise protocol-level no-conflict arithmetic bundle. -/
def noConflictPinningAssumptions_of_acceptedGlobalTrajectory
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
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

omit [LinearOrder Root] [Inhabited Root] in
/-- A slot between the canonical first and last slots of epoch `e` has epoch
exactly `e`.  Cloned rather than reused because the source copy
(`CurrentTargetFutureSupport.lean:65`) is `private`; the statement mentions no
node, no store, and no honesty. -/
private theorem acceptedNoConflict_epoch_eq_of_epoch_bounds
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

set_option maxRecDepth 10000 in
/-- **N3** of `docs/trunkB-two-case-discharge.md` §7 in the strong
development: case-β pinning of the endpoint justification against the query's
current target, with **no** `HonestVotesSupportTarget` proviso.

Case β is the branch in which no honest member of the endpoint
justification's quorum voted at or after the query slot (`hnoPostQuery`).  The
proof is §5.3 of that note, i.e. the existing arithmetic-branch argument with
one seat argument swapped:

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
without the proviso, as §5.2 items 1-2 record.  Mirrors
`Execution.noConflict_endpointJustifiedQuorum_root_eq_currentTarget_at_observer`
with the observer coherence binder replaced by the query node's honesty. -/
theorem completedPrefix_noConflict_endpointJustifiedQuorum_root_eq_currentTarget
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hgateRaw :
      get_current_target cfg (E.store cfg ext v (n + 1)) =
          (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint ∨
        E.total_active cfg <
          3 * compute_honest_ffg_support_for_current_target cfg ext
            (E.store cfg ext v (n + 1)))
    {w : ValidatorIndex} {m : Nat}
    (Q : E.EndpointJustifiedQuorumAt cfg ext B.anchor w m)
    (hnoPostQuery : ¬ Q.PostQueryHonestSigner cfg ext (n + 1))
    (hepoch : (E.store cfg ext w m).justified_checkpoint.epoch =
      (get_current_target cfg (E.store cfg ext v (n + 1))).epoch) :
    (E.store cfg ext w m).justified_checkpoint.root =
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
  change (E.store cfg ext w m).justified_checkpoint.epoch = target.epoch
    at hepoch
  change (E.store cfg ext w m).justified_checkpoint.root = target.root
  obtain ⟨hc⟩ :=
    CausalPrefixFFGInterpretation.endpointJustified_certificate
      cfg ext B hgenShort hanchor (E.store_causal cfg ext w m)
  generalize hj : (E.store cfg ext w m).justified_checkpoint = c at hc hepoch ⊢
  have hJepoch : (E.store cfg ext w m).justified_checkpoint.epoch = target.epoch :=
    (congrArg Checkpoint.epoch hj).trans hepoch
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
  have hstoreCausal : E.CausalStore cfg ext store := by
    simpa only [store] using E.store_causal cfg ext v (n + 1)
  obtain ⟨hUJ⟩ :=
    CausalPrefixFFGInterpretation.unrealizedJustified_certificate
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
    have hobservedVote : ∀ i ∈ E.currentTargetObservedHonestSupporters cfg
        store state,
        Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
          deadline target) := by
      intro i hiObserved
      let hV := CurrentTargetPrefixVoteAssumptions.of_acceptedGlobalTrajectory
        cfg ext E B hT hanchor hboundary
      have hboundaryZero : TrustedAnchorBoundaryAligned
          (cfg := cfg) (E := E)
          (anchor := E.genesis_store.justified_checkpoint) := by
        simpa only [← hanchor] using hboundary
      have hvote :=
        E.currentTargetObservedHonestSupporter_vote_of_prefix
          cfg ext B hV hboundaryZero p (by simpa [p, Execution.completedScheduledEventPrefix] using hv) hHn1
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
      · rw [← E.store_current_slot cfg ext v (n + 1)]
        exact hs.1
      · have hloCurrent : get_current_store_epoch cfg store *
            cfg.slots_per_epoch ≤ get_current_slot cfg store := by
          have h := Nat.div_mul_le_self (get_current_slot cfg store)
            cfg.slots_per_epoch
          simpa only [get_current_store_epoch, Nat.mul_comm] using h
        have hsEpoch : compute_epoch_at_slot cfg s =
            get_current_store_epoch cfg store := by
          apply acceptedNoConflict_epoch_eq_of_epoch_bounds cfg
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
        exact mem_acceptedNoConflict_epoch_span_of_committee cfg
          vote.assigned vote.slot_epoch
      · obtain ⟨_hi, s, _hsQuery, hiCommittee, hsEpoch⟩ :=
          hfutureSeat i hiFuture
        exact mem_acceptedNoConflict_epoch_span_of_committee cfg
          hiCommittee hsEpoch
    have hraw : E.total_active cfg <
        3 * compute_honest_ffg_support_for_current_target cfg ext store :=
      hgateRaw.resolve_left heq
    have hgate : will_no_conflicting_checkpoint_be_justified cfg ext store
        = true :=
      E.noConflictGate_of_rawGate cfg ext (by simpa only [hstate] using htab)
        hraw
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
    have hTU : Q.signers ⊆ U := by
      intro i hi
      have hiEpoch := Q.signers_in_epoch hi
      simpa only [U, hJepoch] using hiEpoch
    obtain ⟨i, hiSigner, hiQ, hiHonest⟩ :=
      one_third_honest_intersects_two_thirds E
        hsignersEpoch hTU hsignersHonest hU honeThird Q.supermajority
    obtain ⟨w', t, a, fromBlock, haSchedule, hiA, haTarget,
      haSlotH, haSlot0, haEpoch, haCommittee, haBound⟩ :=
      Q.signer_attestation i hiQ
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · obtain ⟨vote⟩ := hobservedVote i hiObserved
      obtain ⟨kCompeting, aCompeting, _hcausal, hvoteCompeting,
          hdataCompeting⟩ := hT.honest_behavior.no_forgery
            w' t a fromBlock haSchedule i hiHonest hiA
      let aTarget := honest_attestation cfg ext
        (E.store cfg ext i vote.time) vote.slot vote.index i
      have hvoteTarget : E.vote i vote.slot =
          some (vote.time, aTarget) := by
        simpa only [aTarget] using vote.vote
      have haTargetExact : aTarget.data.target = target := by
        simpa only [aTarget] using vote.target_eq
      have haCompetingExact : aCompeting.data.target = c := by
        rw [← hdataCompeting]
        exact haTarget.trans hj
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
    · obtain ⟨_hi, s, hsQuery, hiCommittee, hsEpoch⟩ :=
        hfutureSeat i hiFuture
      have hsEq : s = a.data.slot :=
        hT.externals_coherence.committee_assignment_unique i
          s a.data.slot hiCommittee haCommittee
          (hsEpoch.trans (haEpoch.trans hJepoch).symm)
      have hpost : Q.PostQueryHonestSigner cfg ext (n + 1) := by
        refine ⟨i, hiQ, hiHonest, w', t, a, fromBlock,
          haSchedule, hiA, ?_, haSlotH, haSlot0, haBound, ?_⟩
        · exact haTarget
        · rw [← hsEq]
          exact hsQuery
      exact False.elim (hnoPostQuery hpost)

set_option maxRecDepth 10000 in
/-- **N6** of `docs/trunkB-two-case-discharge.md` §7 in the strong
development: the executable gate alone decides, for every endpoint, between
the trusted anchor, a post-query honest quorum member, and same-epoch pinning
against the query's current target.

The case split is `by_cases` on
`Execution.EndpointJustifiedQuorumAt.PostQueryHonestSigner` applied to the
quorum N1 extracts from a non-anchor endpoint justification; case α is N2 and
case β is N3 above.  Nothing here mentions `HonestVotesSupportTarget`: the
proviso's entire Trunk-B duty is discharged by the endpoint's own
`IncludedCertifiedJustified` evidence (§4) plus the helper arithmetic. -/
theorem completedPrefix_endpointOriginOrPinnedProducerAt
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    E.EndpointOriginOrPinnedProducerAt cfg ext B.anchor (n + 1)
      (E.fcrStoreAtCall cfg ext v n) := by
  classical
  intro hgate w m
  simp only [E.fcrStep_store] at hgate ⊢
  have htab : get_total_active_balance cfg
      (get_pulled_up_head_state cfg ext (E.store cfg ext v (n + 1))) =
      E.total_active cfg :=
    E.completedPrefix_pulledUpHead_totalActive cfg ext B hT
      hC.static_validators hanchor hboundary hv hHn1
  have hpos : 0 < E.total_active cfg := by
    rw [E.total_active_eq_anchorActive_weight cfg hC.balance_floor]
    exact Nat.lt_of_lt_of_le cfg.effective_balance_increment_pos
      hC.balance_floor
  have hgateRaw := E.rawGate_of_executableGate cfg ext htab hpos hgate
  by_cases hne : (E.store cfg ext w m).justified_checkpoint = B.anchor
  · exact Or.inl hne
  · obtain ⟨Q⟩ :=
      CausalPrefixFFGInterpretation.endpointJustified_quorumAt
        cfg ext B hT hanchor hboundary hne
    by_cases hpost : Q.PostQueryHonestSigner cfg ext (n + 1)
    · exact Or.inr (Or.inl
        (EndpointJustifiedQuorumAt.causalHonestTargetAt_of_postQuerySigner
          cfg ext hT.honest_behavior hpost))
    · refine Or.inr (Or.inr fun hepoch => ?_)
      exact
        E.completedPrefix_noConflict_endpointJustifiedQuorum_root_eq_currentTarget
          cfg ext B hT hC hfit hanchor hboundary hv hHn1 hgateRaw Q hpost
          hepoch

/-! ## Actual-call historical payload -/

private theorem AcceptedBlockAt.executionRoot_for_actualOrientation
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) : E.ExecutionRoot r := by
  obtain ⟨store, hstore, hr, _hblock⟩ := h
  rcases hstore.blockProvenance cfg ext E r hr with hgen | hsched
  · exact ⟨store.blocks r, Or.inl ⟨hgen.1, hgen.2⟩⟩
  · obtain ⟨sb, ⟨w, n, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact ⟨store.blocks r,
      Or.inr ⟨w, n, sb, hscheduled, hroot, hmessage.symm⟩⟩

/-- Materialize a retained lineage in an ordinary execution-boundary store.
This is accepted-root reflection plus the trusted-anchor boundary walk; it
does not use an endpoint, no-crossing fact, or safety conclusion. -/
private theorem AcceptedHistoricalA32LineageCoreAt.payloadAtExecutionStore
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {q : Nat} {tip : Root} {e : Epoch}
    {Cert : Checkpoint Root → Prop} {Supp : Root → Epoch → Prop}
    (hlineage : E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      Cert Supp)
    (htip : tip ∈ (E.store cfg ext v q).block_roots)
    (htipEpoch : get_block_epoch cfg (E.store cfg ext v q) tip = e)
    (hsuppT : B.state.C tip e = B.state.C hlineage.origin e →
      B.state.GJ tip = B.state.GJ hlineage.origin →
      Supp hlineage.origin e → Supp tip e) :
    Nonempty (E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B tip e
      Cert Supp) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure

  let store := E.store cfg ext v q
  have hstoreCausal : E.CausalStore cfg ext store := by
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
  have horiginAt : E.AcceptedBlockAt cfg ext hlineage.origin
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
    horigin htip' horiginEpoch htipEpoch' htipOrigin htipWalk hsuppT⟩

/-- The completed-prefix historical induction instantiates the retained
certificate producer on the exact strict selector result.

**This is where the no-crossing antecedent becomes load-bearing.**  Under the
lazy instantiation the lineage carried at write-back second `n + 1` would
require the threaded fold output *at second `n`*, which is what the enclosing
dispatcher is proving.  But `hnoCrossing` says this call created no payload at
all: it transported the input's.  So the transformer is run in its no-crossing
form from the invariant at second `n`, whose certification closure is
discharged by `hprior` — the strictly earlier fold output.  This is D1† of
`docs/crossing-call-support-residue.md` §2.1, now recorded in the types. -/
noncomputable def completedPrefix_acceptedHistoricalCertificateProducerAt
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n)) :
    E.HistoricalCurrentTargetCertificateProducerAt cfg ext B.anchor (n + 1)
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  intro hcurrent hnoCrossing
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hqueryStore : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariantN :=
    E.acceptedHistoricalA32CurrentLineage_invariant_of_completedPrefixes
      cfg ext B hT hC hfit hdomain hanchor hboundary v hv n hHn
  obtain ⟨e, ⟨hlineage⟩⟩ :=
    E.getLatestConfirmedTraceAt_currentLineage_step_noCrossing cfg ext B hT
      hanchor hboundary hv hHn1 hinvariantN.confirmed_known hcurrent
      hnoCrossing (E.lazyCertAt_anchor cfg ext)
      (fun _ _ h => E.lazySupportAt_anchor cfg ext h)
      hinvariantN.current_lineage
  have hresultKnown : trace.result ∈ query.store.block_roots := by
    simpa only [query, trace] using
      E.getLatestConfirmedTraceAt_result_known cfg ext B hT hanchor hboundary
        hv hHn1 hinvariantN.confirmed_known
  have hqueryCausal : E.CausalStore cfg ext query.store := by
    rw [hqueryStore]
    exact E.store_causal cfg ext v (n + 1)
  have hresultAt : E.AcceptedBlockAt cfg ext trace.result
      (query.store.blocks trace.result) :=
    E.acceptedBlockAt_of_causal_known cfg ext hqueryCausal hresultKnown
  have htipBlock : hlineage.tip_block =
      query.store.blocks trace.result :=
    hlineage.tip_at.unique cfg ext E hT.wellFormed hresultAt
  have hresultEpoch : get_block_epoch cfg query.store trace.result = e := by
    simpa only [get_block_epoch, ← htipBlock] using hlineage.tip_epoch
  have hpayload : Nonempty
      (E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B trace.result e
        (E.LazyCertAt cfg ext B n) (E.LazySupportAt cfg ext B v n)) := by
    apply hlineage.payloadAtExecutionStore cfg ext B hT hC.phase0_source
      hanchor hboundary (v := v) (q := n + 1)
    · simpa only [hqueryStore] using hresultKnown
    · simpa only [hqueryStore] using hresultEpoch
    · intro hcheckpoint hsource hsupp
      exact E.lazySupportAt_transport cfg ext hcheckpoint hsource hsupp
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
  have htargetEq : get_current_target cfg query.store =
      B.state.C trace.result e := by
    calc
      get_current_target cfg query.store =
          get_checkpoint_for_block cfg query.store
            (get_head cfg query.store).root
              (get_current_store_epoch cfg query.store) := rfl
      _ = get_checkpoint_for_block cfg query.store
            (get_head cfg query.store).root e := by rw [heCurrent]
      _ = get_checkpoint_for_block cfg query.store trace.result e := by
        exact congrArg (Checkpoint.mk e) hcheckpoint
      _ = B.state.C trace.result e :=
        (B.coherence.checkpoint_of_known hqueryCausal trace.result
          hresultKnown e).symm
  -- the certification closure, discharged by the strictly earlier fold output
  rw [htargetEq]
  exact (Classical.choice hpayload).certified hprior

/-! ## Consumer-ready actual-call orientation -/

/-- Feed all three completed-prefix accepted producers into the endpoint
orientation theorem for one actual strict selector call.

The remaining premises are precisely the outer safety-induction inputs: the
carried input `SafeFrom`, selected-result relay/IH, the concrete child edge at
the endpoint, and noncoverage.  No FFG pipeline, filter conclusion, or
historical-certificate premise remains. -/
theorem actualCall_strictSelected_result_and_child_ancestor_of_endpointJustified
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hC : E.CompletedFCRCallPremises cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hprior : E.PriorStrictCallWriteBackSafe cfg ext n)
    (hinput : (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved ∈
      (E.fcrStoreAtCall cfg ext v n).store.block_roots)
    (hbase : E.SafeFrom cfg ext
      (E.getLatestConfirmedTraceAt cfg ext v n).afterObserved
      (E.slot_start cfg (E.slot_at cfg (n + 1))))
    (hselector : StrictSelectorAdvanceAt cfg ext
      (E.fcrStoreAtCall cfg ext v n)
      (E.getLatestConfirmedTraceAt cfg ext v n))
    {c : Root} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hselectedC : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
      (get_node_for_root c) = true)
    (hselectedKnown : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      (E.getLatestConfirmedTraceAt cfg ext v n).result ∈
        (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (E.getLatestConfirmedTraceAt cfg ext v n).result) = true)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root c)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.getLatestConfirmedTraceAt cfg ext v n).result)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let query := E.fcrStoreAtCall cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hC.synchrony
      externals_coherence := hT.externals_coherence
      static_validators := hC.static_validators
      byzantine_bound := hC.byzantine_bound
      domain := hdomain }
  have hquery : query.store = E.store cfg ext v (n + 1) := by
    simpa only [query] using E.fcrStep_store cfg ext v n
  have hinput' : trace.afterObserved ∈ query.store.block_roots := by
    simpa only [query, trace] using hinput
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have hinputUpper : get_block_epoch cfg query.store trace.afterObserved ≤
      get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right (by
      rw [hquery]
      simpa only [E.store_current_slot] using
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          v (n + 1) trace.afterObserved
            (by simpa only [hquery] using hinput'))
  have hinputEpoch :
      get_block_epoch cfg query.store trace.afterObserved =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store trace.afterObserved + 1 =
          get_current_store_epoch cfg query.store := by
    rcases Nat.eq_or_lt_of_le hinputUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm
        (Nat.succ_le_iff.mpr hlt) hselector.input_recent)
  have hstrict : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact hselector.result_ne_input
      (hselector.result_eq.trans hfixed)
  have hhistorical : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor (n + 1) query trace.afterObserved trace.result := by
    simpa only [query, trace] using
      E.completedPrefix_acceptedHistoricalCertificateProducerAt
        cfg ext B hT hC hfit hdomain hanchor hboundary hv hcall hHn1 hprior hinput
          hselector
  have hhistorical' : E.HistoricalCurrentTargetCertificateProducerAt cfg ext
      B.anchor (n + 1) query trace.afterObserved
        (find_latest_confirmed_descendant cfg ext query
          trace.afterObserved) := by
    rw [← hselector.result_eq]
    exact hhistorical
  have hproducer : E.EndpointOriginOrPinnedProducerAt
      cfg ext B.anchor (n + 1) query := by
    simpa only [query] using
      E.completedPrefix_endpointOriginOrPinnedProducerAt
        cfg ext B hT hC hfit hanchor hboundary hv hHn1
  have hselectedC' : is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query trace.afterObserved))
      (get_node_for_root c) = true := by
    rw [← hselector.result_eq]
    simpa only [trace] using hselectedC
  have hselectedKnown' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.WithinHorizon cfg m' →
      find_latest_confirmed_descendant cfg ext query trace.afterObserved ∈
        (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hstart hm'H
    rw [← hselector.result_eq]
    exact hselectedKnown w' hw' m' hstart hm'H
  have hIH' : ∀ w' ∈ E.honest, ∀ m' : Nat,
      E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root
          (find_latest_confirmed_descendant cfg ext query
            trace.afterObserved)) = true := by
    intro w' hw' m' hstart hm'Lt hm'H
    rw [← hselector.result_eq]
    exact hIH w' hw' m' hstart hm'Lt hm'H
  have hout :=
    E.strictSelected_result_and_child_ancestor_of_endpointJustified_accepted
      cfg ext hA B hT hanchor hboundary hv hHn1 query hquery
      trace.afterObserved hinput' hinputEpoch
      (by simpa only [trace] using hbase) hstrict
      hhistorical' hproducer hw hHm hslotQM hcM hselectedC'
      hselectedKnown' hIH' hnotCovered
  refine ⟨hout.1, ?_⟩
  have hsecond := hout.2
  rw [← hselector.result_eq] at hsecond
  simpa only [trace] using hsecond

end Execution


end FastConfirmation.Spec

end
