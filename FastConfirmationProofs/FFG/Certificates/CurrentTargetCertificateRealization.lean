module
public import FastConfirmationProofs.FFG.Certificates.NoConflictCertificatePinning
public import FastConfirmationProofs.Execution.History.SelectedPreQueryHistoricalSIR
public import FastConfirmationProofs.FFG.State.ScheduledFFGGlobalCheckpointTrajectory

public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Realizing the current-target certificate

The executable current-target helper counts exact-target votes, whereas a
`CertifiedJustified` object needs one source-specific, scheduled
`SupermajorityLink`.  This module reconstructs the source information which
the target-only accounting intentionally forgets and constructs that link.

The construction uses no certificate producer, target certificate, arbitrary
source certificate, or target/source descent premise.  Instead:

* the gate supplies concrete canonical honest votes and their two-thirds
  weight;
* the global FFG trajectory supplies each vote's actual target-boundary walk;
* same-epoch and boundary phase0 laws identify its source with the paper's
  `VSAt` selector, and cross-store block agreement makes that selector common;
* `GJ`/`GU` AU evidence supplies the source certificate and puts source and
  target on one checkpoint chain, from which execution descent is derived; and
* a scheduled-delivery law turns each retained ground vote into the witness
  stored by `SupermajorityLink`.

The last step exposes one genuine finite-horizon seam.  A vote in the last
slot of epoch `e` is first processable at the start of `e+1`.  Therefore the
core constructor accepts the needed local delivery law.  The legacy synchrony
adapter keeps that exact delivery second within the verified horizon, while
the accepted finite-horizon path uses `HorizonVoteDeliveryLookahead`: vote
creation remains inside the public horizon, and receipt may occur at the first
second beyond its exclusive cutoff.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The epoch-boundary source law -/


namespace Execution

variable (E : Execution Root)









/-! ## Gate-to-certificate constructor -/






/-! ## Accepted causal-store current-epoch constructor -/

/-- Actual accepted source evidence for every concrete vote in an intermediate
current-target quorum.  Each vote retains its causal/global source carrier,
and its head is connected to the target root only through accepted
same-epoch transitions.  This is an intermediate proof object, not an input to
the final actual-call producer. -/
def AcceptedConcreteA32QuorumSourceGeometry
    (B : CausalPrefixFFGInterpretation cfg ext E)
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (common : Root) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      AcceptedHonestSourceEvidence B.state
          (E.store cfg ext i vote.time) vote.slot vote.index ∧
        AcceptedProjectedSameEpochSegment cfg ext E B.state common
          (get_head cfg (E.store cfg ext i vote.time)).root

/-- Internal accepted constructor for the current-epoch branch of the
current-target gate.

The target certificate is an output: the theorem obtains the certified source
and target-to-source descent from the target's named accepted `GJ` formed
carrier, turns the concrete quorum's ground votes into one scheduled
supermajority link, and extends the source certificate by that link.  The
old-head/cross-epoch `GU` branch is deliberately absent; it requires
`Phase0BoundarySourceCoherence` and a separate accepted boundary-source
trajectory.

`Q` and `hgeometry` are intentionally intermediate.  Reverse exact-prefix
transition provenance is the remaining prerequisite for constructing them
from `hgate` and `HonestVotesSupportTarget`; they are not advertised as final
actual-call inputs. -/
theorem acceptedCurrentTargetA32GateRealization_of_currentEpochConcreteQuorum_core
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (htargetKnown : (get_current_target cfg store).root ∈ store.block_roots)
    (htargetEpoch : get_block_epoch cfg store
      (get_current_target cfg store).root =
        (get_current_target cfg store).epoch)
    (htargetNotAnchor : get_current_target cfg store ≠ B.anchor)
    (hanchorBefore : B.anchor.epoch < (get_current_target cfg store).epoch)
    (htargetSpan :
      E.SlotWithinHorizon cfg
          ((get_current_target cfg store).epoch * cfg.slots_per_epoch) ∧
        E.SlotWithinHorizon cfg
          ((get_current_target cfg store).epoch * cfg.slots_per_epoch +
            (cfg.slots_per_epoch - 1)))
    (Q : ConcreteA32QuorumBefore cfg ext E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg store).epoch + 1))
      (get_current_target cfg store))
    (hdelivery : ConcreteA32QuorumScheduledDelivery cfg ext E Q)
    (hgeometry : AcceptedConcreteA32QuorumSourceGeometry cfg ext E B Q
      (get_current_target cfg store).root) :
    AcceptedCurrentTargetA32GateRealization cfg ext E B.anchor B.state
      store := by
  classical
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  change get_block_epoch cfg store target.root = target.epoch at htargetEpoch
  change target ≠ B.anchor at htargetNotAnchor
  change B.anchor.epoch < target.epoch at hanchorBefore
  change ConcreteA32QuorumBefore cfg ext E deadline target at Q
  change ConcreteA32QuorumScheduledDelivery cfg ext E Q at hdelivery
  change AcceptedConcreteA32QuorumSourceGeometry cfg ext E B Q target.root
    at hgeometry
  have htargetAt : E.AcceptedBlockAt cfg ext target.root
      (store.blocks target.root) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore htargetKnown
  have htargetCarrier : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) store target.root :=
    Execution.AcceptedCarrierIn.of_causal_known hstore htargetKnown
  obtain ⟨formedCarrier, htargetDescendsCarrier, hformed⟩ :=
    B.state.gj_mem target.root htargetCarrier.acceptedRoot
  let hsourceCarrier : AcceptedSelectorAUCarrier B.state store
      (B.state.GJ target.root) :=
    { tip := target.root
      carrier := formedCarrier
      tip_carrier := htargetCarrier
      au := ⟨formedCarrier, htargetDescendsCarrier, hformed⟩
      tip_descends_carrier := htargetDescendsCarrier
      carrier_accepted := B.state.formed_carrier_accepted hformed
      formed_evidence := B.state.formed_evidence hformed }
  have hsignersNonempty : Q.signers.Nonempty := by
    by_contra hnone
    have hempty : Q.signers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : 2 * E.total_active cfg ≤ 0 := by
      simpa only [hempty, Execution.weight, Finset.sum_empty,
        Nat.mul_zero] using Q.supermajority
    exact (Nat.not_lt_of_ge hzero)
      (Nat.mul_pos (by omega) (E.total_active_pos cfg))
  obtain ⟨i, hi⟩ := hsignersNonempty
  obtain ⟨vote⟩ := Q.votes i hi
  obtain ⟨hsourceEvidence, hsegment⟩ := hgeometry i hi vote
  have hvoteSource :
      (honest_attestation_data cfg ext (E.store cfg ext i vote.time)
        vote.slot vote.index).source = Q.source := by
    simpa only [honest_attestation_data_eq] using
      Q.source_agreement i hi vote
  have hQSource : Q.source = B.state.GJ target.root := by
    exact hvoteSource.symm.trans
      (hsourceEvidence.source_eq.trans
        (hsegment.gj_eq_first hphase
          B.coherence.toFFGSelectorsMatchBeaconStates))
  have hsourceCertifiedGJ : Nonempty
      (CertifiedJustified cfg E B.anchor (B.state.GJ target.root)) := by
    obtain ⟨hincluded⟩ := hsourceCarrier.formed_evidence.certified
    exact ⟨IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg) B.state.includedAttestations.relation hincluded⟩
  have hsourceCertified : Nonempty
      (CertifiedJustified cfg E B.anchor Q.source) := by
    rw [hQSource]
    exact hsourceCertifiedGJ
  have htargetDescendsSource : E.RootDescends target.root Q.source.root := by
    rw [hQSource]
    exact Execution.RootDescends.trans E hsourceCarrier.tip_descends_carrier
      hsourceCarrier.formed_evidence.on_chain
  have htargetBlockEpoch : compute_epoch_at_slot cfg
      (store.blocks target.root).slot = target.epoch := by
    simpa only [get_block_epoch] using htargetEpoch
  have hsourceBeforeGJ :
      (B.state.GJ target.root).epoch < target.epoch := by
    rcases B.state.gj_anchor_or_before htargetAt with hsourceAnchor | hbefore
    · rw [hsourceAnchor]
      exact hanchorBefore
    · exact hbefore.trans_eq htargetBlockEpoch
  have hsourceBefore : Q.source.epoch < target.epoch := by
    rw [hQSource]
    exact hsourceBeforeGJ
  have hsignersEpoch : Q.signers ⊆
      E.span_committee (target.epoch * cfg.slots_per_epoch)
        (target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1)) := by
    intro j hj
    obtain ⟨vj⟩ := Q.votes j hj
    have hdivEpoch : vj.slot / cfg.slots_per_epoch = target.epoch := by
      simpa only [compute_epoch_at_slot] using vj.slot_epoch
    have hlo : target.epoch * cfg.slots_per_epoch ≤ vj.slot := by
      have h := Nat.div_mul_le_self vj.slot cfg.slots_per_epoch
      rwa [hdivEpoch] at h
    have hlt : vj.slot <
        target.epoch * cfg.slots_per_epoch + cfg.slots_per_epoch := by
      have h := Nat.lt_mul_div_succ vj.slot cfg.slots_per_epoch_pos
      rw [hdivEpoch, Nat.mul_add] at h
      simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
    have hhi : vj.slot ≤ target.epoch * cfg.slots_per_epoch +
        (cfg.slots_per_epoch - 1) := by
      have hpred := Nat.le_pred_of_lt hlt
      rw [Nat.pred_eq_sub_one,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
      exact hpred
    simp only [Execution.span_committee, Finset.mem_biUnion]
    exact ⟨vj.slot, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, vj.assigned⟩
  have hlink : SupermajorityLink cfg E Q.source target := {
    signers := Q.signers
    source_before_target := hsourceBefore
    target_descends_source := htargetDescendsSource
    target_epoch_within := Q.target_epoch_within
    target_span_within := by simpa only [target] using htargetSpan
    signers_in_epoch := hsignersEpoch
    signer_attestation := by
      intro j hj
      obtain ⟨vj⟩ := Q.votes j hj
      let a := honest_attestation cfg ext
        (E.store cfg ext j vj.time) vj.slot vj.index j
      refine ⟨j, E.slot_start cfg (vj.slot + 1), a, false, ?_, ?_, ?_, ?_⟩
      · simpa only [a] using hdelivery j hj vj
      · simp only [a, honest_attestation_attesting_indices,
          List.mem_singleton]
      · simpa only [a] using Q.source_agreement j hj vj
      · simpa only [a] using vj.target_eq
    supermajority := Q.supermajority }
  obtain ⟨hsourceCertificate⟩ := hsourceCertified
  have htargetCertificate : Nonempty
      (CertifiedJustified cfg E B.anchor target) :=
    ⟨CertifiedJustified.link hsourceCertificate hlink⟩
  refine ⟨htargetCertificate, Or.inr ⟨htargetNotAnchor, Q, ?_⟩⟩
  change Q.source = B.state.VSAt cfg ext store target.root target.epoch
  simpa only [CausalCarrierFFGState.VSAt, PaperA32StateView.VSAt,
    htargetEpoch, if_pos] using hQSource



/-- Explicitly labeled erasure consumer.  Once the remaining gate-to-Q
obligation supplies an accepted gate producer, the existing crossing pipeline
receives exactly the target certificate and no migration state. -/
theorem acceptedCurrentTargetCertificateProducerAt_of_gateProducer
    (B : CausalPrefixFFGInterpretation cfg ext E)
    {q : ℕ} {query : FastConfirmationStore Root}
    (hproducer : E.AcceptedCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state q query) :
    E.CurrentTargetCertificateProducerAt cfg ext B.anchor q query := by
  intro hgate hsupport
  exact (hproducer hgate hsupport).certified

end Execution

/-! ## Joint non-vacuity of the two phase0 source laws -/

namespace CurrentTargetCertificateRealizationNonvacuity





















end CurrentTargetCertificateRealizationNonvacuity

end FastConfirmation.Spec

end
