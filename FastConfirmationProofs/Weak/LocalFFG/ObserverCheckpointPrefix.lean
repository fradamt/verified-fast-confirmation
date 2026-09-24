module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFinalizedSafety
public import FastConfirmationProofs.Checkpoints.HonestVotePathAdmissibility

/-! Local finalization and shared justification have an exact checkpoint prefix.
Each certificate retains its own inclusion relation and carrier domain.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}
namespace ObserverLocalFFG

set_option maxRecDepth 4096 in
/-- Compare a local finalized certificate with a shared included certificate.
The two inclusion relations are not merged. -/
theorem finalized_prefix_shared
    (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {q n : ℕ} {w : ValidatorIndex} (hw : w ≠ obs)
    {fcarrier jcarrier : Root} {finalized justified : Checkpoint Root}
    (hfknown : fcarrier ∈ (E.store cfg ext obs q).block_roots)
    (hjknown : jcarrier ∈ ((E.withoutObserver obs).store cfg ext w n).block_roots)
    (hf : IncludedCertifiedFinalized cfg E B.state.included
      E.genesis_store.justified_checkpoint fcarrier finalized)
    (hj : IncludedCertifiedJustified cfg (E.withoutObserver obs)
      core.semantics.state.includedAttestations.Included core.semantics.anchor
      jcarrier justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    ExactCheckpointPrefix core.semantics.state.C finalized justified := by
  let R := E.withoutObserver obs
  let S := core.semantics
  let I := S.state.includedAttestations.relation
  let P := core.checkpoint_projection
  let V := core.exact_link_validity
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  let hTR := ScheduledPrefixPremises.of_selectedMarginAssumptions
    cfg ext R core.base core.genesis
  have hanchorEq : S.anchor = E.genesis_store.justified_checkpoint := core.anchor_eq
  have hanchorExact := acceptedAnchorExact_of_trajectory cfg ext R S hTR
    core.anchor_eq core.anchor_boundary
  have hacc := CheckpointCertificateAccountability.of_assumptions cfg
    (anchor := E.genesis_store.justified_checkpoint)
    (nonhonest_accountability hobs core localInputs)
  have toGlobalJ {tip c} (h : IncludedCertifiedJustified cfg R I.Included S.anchor tip c) :
      CertifiedJustified cfg E E.genesis_store.justified_checkpoint c := by
    have hc := withoutObserver_justified
      (IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg) I h)
    rw [hanchorEq] at hc
    exact hc
  let toGlobalL := fun {tip source target}
      (L : IncludedSupermajorityLink cfg R I.Included tip source target) =>
    withoutObserver_link (IncludedSupermajorityLink.toSupermajorityLink (cfg := cfg) I L)
  let fGlobal := IncludedCertifiedFinalized.toCertifiedFinalized (cfg := cfg)
    (B.includedRelation hobs core localInputs) hf
  have hFglobal : CertifiedJustified cfg E E.genesis_store.justified_checkpoint finalized :=
    fGlobal.justified
  have hanchorF : E.genesis_store.justified_checkpoint.epoch ≤ finalized.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hFglobal
  have hanchorFShared : S.anchor.epoch ≤ finalized.epoch := hanchorEq.symm ▸ hanchorF
  have hFChildLocal : finalized = B.state.C hf.child.root finalized.epoch := by
    have hd := B.known_domain (store_observerCausal q) hfknown
    obtain ⟨hs, ht⟩ := B.exact_link_endpoints hd hf.finalizing_link hf.justified
    have hc := B.checkpoint_projection.checkpoint_comp hd hanchorF
      hf.finalizing_link.source_before_target.le
    rw [← ht] at hc
    exact hs.trans hc.symm
  have hChildKnownLocal : hf.child.root ∈ (E.store cfg ext obs q).block_roots := by
    have hd := B.known_domain (store_observerCausal q) hfknown
    have ht := (B.exact_link_endpoints hd hf.finalizing_link hf.justified).2
    rw [B.checkpoint_of_known (store_observerCausal q) fcarrier hfknown hf.child.epoch] at ht
    have hwalk := E.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hT
      hanchorEq core.anchor_boundary obs q
      (hanchorFShared.trans hf.finalizing_link.source_before_target.le) hfknown
    have hp := E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hT.wellFormed.anchor_parent_unscheduled obs q
    rw [congrArg Checkpoint.root ht]
    exact (get_ancestor_spec hp hwalk).1
  induction hj with
  | anchor =>
    have he : finalized.epoch = E.genesis_store.justified_checkpoint.epoch := by
      rw [hanchorEq] at hepoch
      exact Nat.le_antisymm hepoch hanchorF
    have hr := hacc.justified_unique hFglobal CertifiedJustified.anchor he
    have hfAnchor : finalized = S.anchor :=
      (checkpoint_eq_of_epoch_root_eq he hr).trans hanchorEq.symm
    change finalized = S.state.C S.anchor.root finalized.epoch
    rw [hfAnchor]
    exact hanchorExact
  | @link source target hsource link ih =>
    have hsourceGlobal := toGlobalJ hsource
    have htargetGlobal := CertifiedJustified.link hsourceGlobal (toGlobalL link)
    have hanchorSource : S.anchor.epoch ≤ source.epoch :=
      IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hsource
    by_cases hsourceEpoch : finalized.epoch ≤ source.epoch
    · exact P.prefix_trans (V.target_accepted (cfg := cfg) P link hsource hanchorSource)
        hanchorFShared hsourceEpoch (ih hsourceEpoch)
        (V.source_prefix_target (cfg := cfg) P link hsource hanchorSource)
    · have hsourceLt : source.epoch < finalized.epoch := Nat.lt_of_not_ge hsourceEpoch
      by_cases htargetEq : target.epoch = finalized.epoch
      · have hr := hacc.justified_unique htargetGlobal hFglobal htargetEq
        have he := checkpoint_eq_of_epoch_root_eq htargetEq hr
        have hself := V.target_self (cfg := cfg) P link hsource
          (hanchorSource.trans link.source_before_target.le)
        change finalized = S.state.C target.root finalized.epoch
        rw [← he]
        exact hself
      · have hfinalizedLt : finalized.epoch < target.epoch :=
          lt_of_le_of_ne hepoch (Ne.symm htargetEq)
        have hchildGlobal := CertifiedJustified.link hFglobal fGlobal.finalizing_link
        by_cases htargetChild : target.epoch = hf.child.epoch
        · have hr := hacc.justified_unique htargetGlobal hchildGlobal htargetChild
          have he : target = hf.child := checkpoint_eq_of_epoch_root_eq htargetChild hr
          have htargetKnown : target.root ∈ (R.store cfg ext w n).block_roots := by
            have ht := (V.endpoints_on_carrier link hsource).2
            rw [S.coherence.checkpoint_of_known (R.store_causal cfg ext w n)
              jcarrier hjknown target.epoch] at ht
            have hwalk := R.trustedAnchor_boundaryWalkAtEpoch_of_trajectory cfg ext hTR
              core.anchor_eq core.anchor_boundary w n
              (hanchorSource.trans link.source_before_target.le) hjknown
            have hp := R.store_parentSlotLt cfg ext core.base.wellFormed
              core.base.externals_coherence core.base.genesis
              core.base.wellFormed.anchor_parent_unscheduled w n
            rw [congrArg Checkpoint.root ht]
            exact (get_ancestor_spec hp hwalk).1
          have hChildKnown : hf.child.root ∈ (E.store cfg ext w n).block_roots := by
            rw [he] at htargetKnown
            simpa only [R, withoutObserver_store cfg ext E obs w hw n] using htargetKnown
          change finalized = S.state.C target.root finalized.epoch
          rw [he]
          exact hFChildLocal.trans
            (B.shared_checkpoint_agree core localInputs q n hw hChildKnownLocal hChildKnown hanchorF)
        · have hchildLt : hf.child.epoch < target.epoch := by
            have hsuccLe : finalized.epoch + 1 ≤ target.epoch :=
              Nat.succ_le_iff.mpr hfinalizedLt
            have hne : target.epoch ≠ finalized.epoch + 1 := by
              intro he
              apply htargetChild
              rw [hf.child_epoch]
              exact he
            have hlt := lt_of_le_of_ne hsuccLe hne.symm
            simpa only [hf.child_epoch] using hlt
          exact False.elim ((hacc.links_not_surround (toGlobalL link)
            fGlobal.finalizing_link) ⟨hsourceLt, hchildLt⟩)

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
