module
public import FastConfirmationProofs.Checkpoints.ExactCheckpointLinks

/-! Exact checkpoint prefixes use link laws only at their accepted carriers. -/

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
variable {E : Execution Root} {anchor : Checkpoint Root}

/-- An unguarded exact-link law restricts to any carrier domain. -/
def ExactIncludedLinkValidity.onDomain
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root} {Accepted Domain : Root → Prop}
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted) :
    ExactIncludedLinkValidity cfg E included anchor C Accepted Domain where
  carrier_accepted := fun L hc _ => V.carrier_accepted L hc trivial
  endpoints_on_carrier := fun L hc _ => V.endpoints_on_carrier L hc trivial

namespace ExactIncludedLinkValidity

omit [LinearOrder Root] [Inhabited Root] in
/-- A valid contributing link's target root remains in the accepted domain. -/
theorem guarded_target_accepted
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted Domain)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcarrier : Domain carrier)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorSource : anchor.epoch ≤ source.epoch) :
    Accepted target.root := by
  have haccepted := V.carrier_accepted L hcontributing hcarrier
  have htargetEpoch : anchor.epoch ≤ target.epoch :=
    hanchorSource.trans (Nat.le_of_lt L.source_before_target)
  have hprojected := P.checkpoint_root_accepted haccepted htargetEpoch
  have htarget := (V.endpoints_on_carrier L hcontributing hcarrier).2
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  rw [htargetRoot]
  exact hprojected

omit [LinearOrder Root] [Inhabited Root] in
/-- Same-carrier endpoint realization derives exact source/target checkpoint
prefix; the prefix is not assumed as a free link law. -/
theorem guarded_source_prefix_target
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted Domain)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcarrier : Domain carrier)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorSource : anchor.epoch ≤ source.epoch) :
    ExactCheckpointPrefix C source target := by
  obtain ⟨hsource, htarget⟩ :=
    V.endpoints_on_carrier L hcontributing hcarrier
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  have hcomp := P.checkpoint_comp (V.carrier_accepted L hcontributing hcarrier)
    hanchorSource (Nat.le_of_lt L.source_before_target)
  unfold ExactCheckpointPrefix
  calc
    source = C carrier source.epoch := hsource
    _ = C (C carrier target.epoch).root source.epoch := hcomp.symm
    _ = C target.root source.epoch := by rw [htargetRoot]

omit [LinearOrder Root] [Inhabited Root] in
/-- A valid contributing link target is itself an exact checkpoint value. -/
theorem guarded_target_self
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted Domain)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcarrier : Domain carrier)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorTarget : anchor.epoch ≤ target.epoch) :
    target = C target.root target.epoch := by
  have htarget := (V.endpoints_on_carrier L hcontributing hcarrier).2
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  have hcomp := P.checkpoint_comp (V.carrier_accepted L hcontributing hcarrier)
    hanchorTarget (Nat.le_refl target.epoch)
  calc
    target = C carrier target.epoch := htarget
    _ = C (C carrier target.epoch).root target.epoch := hcomp.symm
    _ = C target.root target.epoch := by rw [htargetRoot]

end ExactIncludedLinkValidity

namespace IncludedCertifiedJustified

omit [LinearOrder Root] [Inhabited Root] in
/-- Every checkpoint produced by an exact included certificate is itself an
epoch checkpoint.  The trusted anchor is the explicit base case. -/
theorem guarded_exact_self
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted Domain)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    {carrier c}
    (hcarrier : Domain carrier)
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    c = C c.root c.epoch := by
  cases h with
  | anchor => exact hanchorExact
  | @link source target hsource link =>
      have hanchorTarget :=
        (IncludedCertifiedJustified.anchor_epoch_le
          (cfg := cfg) hsource).trans
          (Nat.le_of_lt link.source_before_target)
      exact V.guarded_target_self (cfg := cfg) P link hcarrier hsource hanchorTarget

omit [LinearOrder Root] [Inhabited Root] in
/-- The trusted anchor is an exact prefix of every checkpoint in an exact
included certificate. -/
theorem guarded_anchor_prefix
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted Domain)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    {carrier c}
    (hcarrier : Domain carrier)
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    ExactCheckpointPrefix C anchor c := by
  induction h with
  | anchor =>
      unfold ExactCheckpointPrefix
      exact hanchorExact
  | @link source target hsource link ih =>
      have hanchorSource : anchor.epoch ≤ source.epoch :=
        IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hsource
      have hsourceTarget := V.guarded_source_prefix_target (cfg := cfg) P
        link hcarrier hsource hanchorSource
      have htargetAccepted := V.guarded_target_accepted (cfg := cfg) P
        link hcarrier hsource hanchorSource
      exact P.prefix_trans htargetAccepted (Nat.le_refl anchor.epoch)
        hanchorSource ih hsourceTarget

end IncludedCertifiedJustified


namespace IncludedCertifiedFinalized

/-- Casper accountable finalized-prefix strengthened from root ancestry to
the exact epoch-indexed checkpoint relation. -/
theorem guarded_exact_prefix_of_accountable
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : Execution.IncludedAttestationRelation cfg E validity)
    {C : Root → Epoch → Checkpoint Root}
    {Accepted Domain : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E I.Included anchor C Accepted Domain)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {finalizedCarrier justifiedCarrier : Root}
    {finalized justified : Checkpoint Root}
    (hfcarrier : Domain finalizedCarrier) (hjcarrier : Domain justifiedCarrier)
    (hfinalized : IncludedCertifiedFinalized cfg E
      I.Included anchor finalizedCarrier finalized)
    (hjustified : IncludedCertifiedJustified cfg E
      I.Included anchor justifiedCarrier justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    ExactCheckpointPrefix C finalized justified := by
  let toGlobalJ := fun {carrier : Root} {c : Checkpoint Root}
      (h : IncludedCertifiedJustified cfg E
        I.Included anchor carrier c) =>
    IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg) I h
  let toGlobalL := fun {carrier : Root} {source target : Checkpoint Root}
      (L : IncludedSupermajorityLink cfg E
        I.Included carrier source target) =>
    IncludedSupermajorityLink.toSupermajorityLink
      (cfg := cfg) I L
  have hfinalizedGlobal : CertifiedJustified cfg E anchor finalized :=
    toGlobalJ hfinalized.justified
  induction hjustified with
  | anchor =>
      have hanchorLe := CertifiedJustified.anchor_epoch_le
        (cfg := cfg) hfinalizedGlobal
      have heqEpoch : finalized.epoch = anchor.epoch :=
        Nat.le_antisymm hepoch hanchorLe
      have heqRoot := hacc.justified_unique hfinalizedGlobal
        (CertifiedJustified.anchor) heqEpoch
      have heq : finalized = anchor :=
        checkpoint_eq_of_epoch_root_eq heqEpoch heqRoot
      unfold ExactCheckpointPrefix
      rw [heq]
      exact hanchorExact
  | @link source target hsource link ih =>
      have hsourceGlobal : CertifiedJustified cfg E anchor source :=
        toGlobalJ hsource
      have htargetGlobal : CertifiedJustified cfg E anchor target :=
        CertifiedJustified.link hsourceGlobal (toGlobalL link)
      have hanchorSource : anchor.epoch ≤ source.epoch :=
        CertifiedJustified.anchor_epoch_le (cfg := cfg) hsourceGlobal
      by_cases hsourceEpoch : finalized.epoch ≤ source.epoch
      · have hfinalizedAnchor : anchor.epoch ≤ finalized.epoch :=
          CertifiedJustified.anchor_epoch_le (cfg := cfg) hfinalizedGlobal
        have hsourceTarget := V.guarded_source_prefix_target (cfg := cfg) P
          link hjcarrier hsource hanchorSource
        have htargetAccepted := V.guarded_target_accepted (cfg := cfg) P
          link hjcarrier hsource hanchorSource
        exact P.prefix_trans htargetAccepted hfinalizedAnchor hsourceEpoch
          (ih hsourceEpoch) hsourceTarget
      · have hsourceLt : source.epoch < finalized.epoch :=
          Nat.lt_of_not_ge hsourceEpoch
        by_cases htargetEq : target.epoch = finalized.epoch
        · have hroot := hacc.justified_unique htargetGlobal
            hfinalizedGlobal htargetEq
          have htargetFinalized : target = finalized :=
            checkpoint_eq_of_epoch_root_eq htargetEq hroot
          have hanchorTarget : anchor.epoch ≤ target.epoch :=
            hanchorSource.trans (Nat.le_of_lt link.source_before_target)
          have hself := V.guarded_target_self (cfg := cfg) P
            link hjcarrier hsource hanchorTarget
          unfold ExactCheckpointPrefix
          rw [← htargetFinalized]
          exact hself
        · have hfinalizedLt : finalized.epoch < target.epoch :=
            lt_of_le_of_ne hepoch (Ne.symm htargetEq)
          have hchildIncluded : IncludedCertifiedJustified cfg E
              I.Included anchor finalizedCarrier
              hfinalized.child :=
            IncludedCertifiedJustified.link hfinalized.justified
              hfinalized.finalizing_link
          have hchildGlobal : CertifiedJustified cfg E anchor hfinalized.child :=
            toGlobalJ hchildIncluded
          by_cases htargetChild : target.epoch = hfinalized.child.epoch
          · have hroot := hacc.justified_unique htargetGlobal hchildGlobal
              htargetChild
            have heq : target = hfinalized.child :=
              checkpoint_eq_of_epoch_root_eq htargetChild hroot
            have hanchorFinalized : anchor.epoch ≤ finalized.epoch :=
              CertifiedJustified.anchor_epoch_le (cfg := cfg)
                hfinalizedGlobal
            have hprefix := V.guarded_source_prefix_target (cfg := cfg) P
              hfinalized.finalizing_link hfcarrier hfinalized.justified
              hanchorFinalized
            simpa only [heq] using hprefix
          · have hchildLt : hfinalized.child.epoch < target.epoch := by
              have hsuccLe : finalized.epoch + 1 ≤ target.epoch :=
                Nat.succ_le_iff.mpr hfinalizedLt
              have htargetNeSucc : target.epoch ≠ finalized.epoch + 1 := by
                intro heq
                apply htargetChild
                rw [hfinalized.child_epoch]
                exact heq
              have hsuccLt : finalized.epoch + 1 < target.epoch :=
                lt_of_le_of_ne hsuccLe htargetNeSucc.symm
              simpa only [hfinalized.child_epoch] using hsuccLt
            exact False.elim
              ((hacc.links_not_surround (toGlobalL link)
                (toGlobalL hfinalized.finalizing_link))
                ⟨hsourceLt, hchildLt⟩)

end IncludedCertifiedFinalized

end FastConfirmation.Spec
end
