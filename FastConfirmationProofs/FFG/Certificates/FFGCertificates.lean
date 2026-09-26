module
public import FastConfirmationProofs.FFG.Certificates.FFGQuorumWeight
public import FastConfirmationStatements.Premises.FFGCertificates

public import FastConfirmationProofs.ModelFacts.FFGState
public import FastConfirmationInternal.FFG.AnchorNormalization
@[expose] public section

/-!
# Spec / Proof / FFGCertificates

Concrete, vote-backed Casper-FFG certificate objects.  Unlike the old
`JustificationInterface` conclusions, a certificate records an actual weighted
signer set and a scheduled attestation naming the target for every signer.
Cryptographic no-forgery turns an honest signer in the set into that validator's
genuine vote; the slashing discipline can then be used in proofs.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
variable (ext : BeaconFunctionInterface Root)

namespace SupermajorityLink

/-- An honest certificate signer has a genuine vote before the scheduled
evidence event and no later than that vote's attestation deadline. This is the
time origin used when relaying the signer's source and target chain. -/
theorem honest_signer_vote_timed
    {E : Execution Root} (hhb : HonestBehavior cfg (ext := ext) E)
    {source target : Checkpoint Root}
    (L : SupermajorityLink cfg E source target)
    {i : ValidatorIndex} (hi : i ∈ L.signers) (hhi : i ∈ E.honest) :
    ∃ (w : ValidatorIndex) (n : ℕ) (a : Attestation Root)
      (fromBlock : Bool) (k : ℕ) (own : Attestation Root),
      Event.attestation a fromBlock ∈ E.schedule w n ∧
      k ≤ n ∧
      E.vote i a.data.slot = some (k, own) ∧
      a.data = own.data ∧
      E.slot_start cfg a.data.slot ≤ k ∧
      k ≤ E.slot_start cfg a.data.slot +
        get_attestation_due_ms cfg / 1000 ∧
      CheckpointReadsAs a.data.source source ∧ a.data.target = target := by
  obtain ⟨w, n, a, fromBlock, hsched, hia, hsource, htarget⟩ :=
    L.signer_attestation i hi
  obtain ⟨k, own, hcausal, hvote, hdata⟩ :=
    hhb.no_forgery w n a fromBlock hsched i hhi hia
  obtain ⟨hstart, hdeadline⟩ := hhb.vote_deadline i hhi a.data.slot k own hvote
  exact ⟨w, n, a, fromBlock, k, own, hsched, hcausal, hvote,
    hdata, hstart, hdeadline, hsource, htarget⟩

/-- Two concrete links sharing an honest signer cannot form a Casper surround
vote. -/
theorem not_surround_of_honest_intersection
    {E : Execution Root} (hhb : HonestBehavior cfg (ext := ext) E)
    {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink cfg E s t)
    (L' : SupermajorityLink cfg E s' t')
    (hinter : ∃ i ∈ L.signers, i ∈ L'.signers ∧ i ∈ E.honest) :
    ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch) := by
  classical
  rintro ⟨hs, ht⟩
  obtain ⟨i, hiL, hiL', hiHonest⟩ := hinter
  obtain ⟨w, n, a, fromBlock, haSchedule, hiA, haSource, haTarget⟩ :=
    L.signer_attestation i hiL
  obtain ⟨w', n', a', fromBlock', haSchedule', hiA', haSource', haTarget'⟩ :=
    L'.signer_attestation i hiL'
  obtain ⟨k, vote, _hcausal, hvote, hdata⟩ :=
    hhb.no_forgery w n a fromBlock haSchedule i hiHonest hiA
  obtain ⟨k', vote', _hcausal', hvote', hdata'⟩ :=
    hhb.no_forgery w' n' a' fromBlock' haSchedule' i hiHonest hiA'
  have hvoteSource : vote.data.source.epoch = s.epoch := by
    rw [← hdata]; exact haSource.epoch_eq
  have hvoteTarget : vote.data.target = t := by rw [← hdata]; exact haTarget
  have hvoteSource' : vote'.data.source.epoch = s'.epoch := by
    rw [← hdata']; exact haSource'.epoch_eq
  have hvoteTarget' : vote'.data.target = t' := by rw [← hdata']; exact haTarget'
  have hslash : is_slashable_attestation_data vote.data vote'.data = true := by
    simp [is_slashable_attestation_data, hvoteSource, hvoteTarget,
      hvoteSource', hvoteTarget', hs, ht]
  have hnot := hhb.not_slashable i hiHonest a.data.slot a'.data.slot k k'
    vote vote' hvote hvote'
  rw [hslash] at hnot
  contradiction

/-- Two target certificates at one epoch have the same root.  The proof is the
actual Casper double-vote argument: weighted quorum intersection supplies an
honest common signer, no-forgery recovers both genuine votes, and distinct
same-epoch targets would make them slashable.

The universe-weight and Byzantine-fraction premises are deliberately explicit;
they are derived for a horizon-bounded epoch from committee activity and
`ByzantineWeightPremises.span_fraction` at the model boundary. -/
theorem root_eq_of_same_epoch
    {E : Execution Root} (hhb : HonestBehavior cfg (ext := ext) E)
    {s c s' c' : Checkpoint Root}
    (C : SupermajorityLink cfg E s c) (C' : SupermajorityLink cfg E s' c')
    (hepoch : c.epoch = c'.epoch)
    (htotal : 0 < E.total_active cfg)
    (hspan_total : E.weight
        (E.span_committee (c.epoch * cfg.slots_per_epoch)
          (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))) ≤
      E.total_active cfg)
    (hfrac : 100 * E.weight
        ((E.span_committee (c.epoch * cfg.slots_per_epoch)
          (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))).filter
            (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold *
        E.weight (E.span_committee (c.epoch * cfg.slots_per_epoch)
          (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)))) :
    c.root = c'.root := by
  classical
  let U := E.span_committee (c.epoch * cfg.slots_per_epoch)
    (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  have hC'U : C'.signers ⊆ U := by
    simpa [U, hepoch] using C'.signers_in_epoch
  obtain ⟨i, hiC, hiC', hiHonest⟩ := two_quorums_intersect_honest E
    htotal C.signers_in_epoch hC'U hspan_total hfrac
    cfg.confirmation_byzantine_threshold_le C.supermajority C'.supermajority
  obtain ⟨w, n, a, fromBlock, haSchedule, hiA, _haSource, haTarget⟩ :=
    C.signer_attestation i hiC
  obtain ⟨w', n', a', fromBlock', haSchedule', hiA', _haSource', haTarget'⟩ :=
    C'.signer_attestation i hiC'
  obtain ⟨k, vote, _hcausal, hvote, hdata⟩ :=
    hhb.no_forgery w n a fromBlock haSchedule i hiHonest hiA
  obtain ⟨k', vote', _hcausal', hvote', hdata'⟩ :=
    hhb.no_forgery w' n' a' fromBlock' haSchedule' i hiHonest hiA'
  have hvoteTarget : vote.data.target = c := by
    rw [← hdata]
    exact haTarget
  have hvoteTarget' : vote'.data.target = c' := by
    rw [← hdata']
    exact haTarget'
  by_contra hroot
  have hdata_ne : vote.data ≠ vote'.data := by
    intro hEq
    have ht : vote.data.target = vote'.data.target :=
      congrArg AttestationData.target hEq
    rw [hvoteTarget, hvoteTarget'] at ht
    exact hroot (congrArg Checkpoint.root ht)
  have htarget_epoch : vote.data.target.epoch = vote'.data.target.epoch := by
    rw [hvoteTarget, hvoteTarget', hepoch]
  have hslash : is_slashable_attestation_data vote.data vote'.data = true := by
    simp [is_slashable_attestation_data, hdata_ne, htarget_epoch]
  have hnot := hhb.not_slashable i hiHonest a.data.slot a'.data.slot k k'
    vote vote' hvote hvote'
  rw [hslash] at hnot
  contradiction

end SupermajorityLink

namespace CertifiedJustified

/-- Certified justification never moves to an epoch before the trusted
anchor. -/
theorem anchor_epoch_le {E : Execution Root} {anchor c : Checkpoint Root}
    (h : CertifiedJustified cfg E anchor c) : anchor.epoch ≤ c.epoch := by
  induction h with
  | anchor => exact Nat.le_refl _
  | link hs cert ih => exact ih.trans (Nat.le_of_lt cert.source_before_target)

/-- A non-anchor justification certificate has advanced through at least one
strict source-to-target link.  This is a certificate-layer fact, so keep it
beside `anchor_epoch_le` rather than in a downstream cache realization. -/
theorem anchor_epoch_lt_of_ne
    {E : Execution Root} {anchor c : Checkpoint Root}
    (h : CertifiedJustified cfg E anchor c) (hne : c ≠ anchor) :
    anchor.epoch < c.epoch := by
  induction h with
  | anchor => exact (hne rfl).elim
  | link hsource link _ih =>
      exact lt_of_le_of_lt
        (CertifiedJustified.anchor_epoch_le (cfg := cfg) hsource)
        link.source_before_target


end CertifiedJustified

namespace CertifiedFinalized

/-- The Casper finalized-prefix argument, separated from quorum arithmetic.
Once same-epoch uniqueness and the no-surround property have been derived from
the concrete certificates, every certified checkpoint at least as new as a
finalized checkpoint descends from it in the execution parent graph. -/
theorem prefix_of_accountable
    {E : Execution Root} {anchor finalized justified : Checkpoint Root}
    (hunique : ∀ {x y : Checkpoint Root},
      CertifiedJustified cfg E anchor x →
      CertifiedJustified cfg E anchor y →
      x.epoch = y.epoch → x.root = y.root)
    (hnosurround : ∀ {s t s' t' : Checkpoint Root},
      (L : SupermajorityLink cfg E s t) →
      (L' : SupermajorityLink cfg E s' t') →
      ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch))
    (hfinalized : CertifiedFinalized cfg E anchor finalized)
    (hjustified : CertifiedJustified cfg E anchor justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    E.RootDescends justified.root finalized.root := by
  induction hjustified with
  | anchor =>
      have hanchor_le := CertifiedJustified.anchor_epoch_le
        (cfg := cfg) hfinalized.justified
      have heq : finalized.epoch = anchor.epoch := Nat.le_antisymm hepoch hanchor_le
      have hroot := hunique hfinalized.justified (.anchor) heq
      rw [hroot]
      exact .refl _
  | @link source target hsource link ih =>
      by_cases hsource_epoch : finalized.epoch ≤ source.epoch
      · exact Execution.RootDescends.trans E link.target_descends_source
          (ih hsource_epoch)
      · have hsource_lt : source.epoch < finalized.epoch :=
          Nat.lt_of_not_ge hsource_epoch
        by_cases htarget_eq : target.epoch = finalized.epoch
        · have hroot := hunique (.link hsource link) hfinalized.justified htarget_eq
          rw [hroot]
          exact .refl _
        · have hfinalized_lt : finalized.epoch < target.epoch :=
            lt_of_le_of_ne hepoch (Ne.symm htarget_eq)
          have hchildJustified : CertifiedJustified cfg E anchor hfinalized.child :=
            .link hfinalized.justified hfinalized.finalizing_link
          by_cases htarget_child : target.epoch = hfinalized.child.epoch
          · have hroot := hunique (.link hsource link) hchildJustified htarget_child
            rw [hroot]
            exact hfinalized.finalizing_link.target_descends_source
          · by_cases hmiddle : hfinalized.child.epoch = finalized.epoch + 2 ∧
                target.epoch = finalized.epoch + 1
            · -- The skipped epoch of a 2-epoch finalizing link is justified
              -- on the finalized chain, so the target is that checkpoint.
              obtain ⟨middle, hmiddleEpoch, hmiddleDesc, hmiddleJustified⟩ :=
                hfinalized.middle_justified hmiddle.1
              have hroot := hunique (.link hsource link) hmiddleJustified
                (hmiddle.2.trans hmiddleEpoch.symm)
              rw [hroot]
              exact hmiddleDesc
            · have hchild_lt : hfinalized.child.epoch < target.epoch := by
                have key : ∀ f t d : ℕ, f < t → ¬ t = d → ¬ (d = f + 2 ∧ t = f + 1) →
                    (d = f + 1 ∨ d = f + 2) → d < t := by omega
                exact key _ _ _ hfinalized_lt htarget_child hmiddle hfinalized.child_epoch
              exact False.elim
                ((hnosurround link hfinalized.finalizing_link) ⟨hsource_lt, hchild_lt⟩)

end CertifiedFinalized

end FastConfirmation.Spec

end
