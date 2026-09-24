module
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots
public import FastConfirmationProofs.Checkpoints.CheckpointGeometry
public import FastConfirmationProofs.FFG.Certificates.FFGAccountability

@[expose] public section

/-!
# Spec / Proof / ExactCheckpointLinks

Production theorems for certificate-scoped exact checkpoint links.  The
semantic law lives in `Model/ExactCheckpointLinks`; this module derives exact
source/target prefix, exact certificate prefix, and executable checkpoint
reflection without widening that law to arbitrary included attestations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Mechanical checkpoint composition -/

omit [Inhabited Root] in
/-- Walking first to a later epoch boundary and then to an earlier boundary
is the same as walking directly to the earlier boundary. -/
theorem get_checkpoint_for_block_comp
    {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot <
          (store.blocks r).slot)
    {carrier : Root} {sourceEpoch targetEpoch : Epoch}
    (hepoch : sourceEpoch ≤ targetEpoch)
    (hwalk : WalkKnown store
      (compute_start_slot_at_epoch cfg sourceEpoch) carrier) :
    get_checkpoint_for_block cfg store
        (get_checkpoint_for_block cfg store carrier targetEpoch).root
        sourceEpoch =
      get_checkpoint_for_block cfg store carrier sourceEpoch := by
  refine checkpoint_eq_of_epoch_root_eq (a :=
      get_checkpoint_for_block cfg store
        (get_checkpoint_for_block cfg store carrier targetEpoch).root
        sourceEpoch)
      (b := get_checkpoint_for_block cfg store carrier sourceEpoch) rfl ?_
  have hboundary : compute_start_slot_at_epoch cfg sourceEpoch ≤
      compute_start_slot_at_epoch cfg targetEpoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hepoch
  have hcomp := get_ancestor_comp_root hwf hboundary hwalk
  simpa only [get_checkpoint_for_block, get_checkpoint_block] using hcomp

namespace EpochCheckpointClosure

omit [LinearOrder Root] [Inhabited Root] in
/-- Exact checkpoint prefix is transitive on the accepted post-anchor
domain. -/
theorem prefix_trans
    {anchor : Checkpoint Root} {Accepted : Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    (P : EpochCheckpointClosure anchor Accepted C)
    {a b c : Checkpoint Root}
    (hc : Accepted c.root)
    (hanchor : anchor.epoch ≤ a.epoch)
    (habEpoch : a.epoch ≤ b.epoch)
    (hab : ExactCheckpointPrefix C a b)
    (hbc : ExactCheckpointPrefix C b c) :
    ExactCheckpointPrefix C a c := by
  have hbroot : b.root = (C c.root b.epoch).root :=
    congrArg Checkpoint.root hbc
  calc
    a = C b.root a.epoch := hab
    _ = C (C c.root b.epoch).root a.epoch := by rw [hbroot]
    _ = C c.root a.epoch :=
      P.checkpoint_comp hc hanchor habEpoch

end EpochCheckpointClosure

variable {E : Execution Root} {anchor : Checkpoint Root}

/-! ## Certificate-level constructors -/





namespace ExactIncludedLinkValidity

omit [LinearOrder Root] [Inhabited Root] in
/-- A valid contributing link's target root remains in the accepted domain. -/
theorem target_accepted
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorSource : anchor.epoch ≤ source.epoch) :
    Accepted target.root := by
  have hcarrier := V.carrier_accepted L hcontributing trivial
  have htargetEpoch : anchor.epoch ≤ target.epoch :=
    hanchorSource.trans (Nat.le_of_lt L.source_before_target)
  have hprojected := P.checkpoint_root_accepted hcarrier htargetEpoch
  have htarget := (V.endpoints_on_carrier L hcontributing trivial).2
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  rw [htargetRoot]
  exact hprojected

omit [LinearOrder Root] [Inhabited Root] in
/-- Same-carrier endpoint realization derives exact source/target checkpoint
prefix; the prefix is not assumed as a free link law. -/
theorem source_prefix_target
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorSource : anchor.epoch ≤ source.epoch) :
    ExactCheckpointPrefix C source target := by
  obtain ⟨hsource, htarget⟩ :=
    V.endpoints_on_carrier L hcontributing trivial
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  have hcomp := P.checkpoint_comp (V.carrier_accepted L hcontributing trivial)
    hanchorSource (Nat.le_of_lt L.source_before_target)
  unfold ExactCheckpointPrefix
  calc
    source = C carrier source.epoch := hsource
    _ = C (C carrier target.epoch).root source.epoch := hcomp.symm
    _ = C target.root source.epoch := by rw [htargetRoot]

omit [LinearOrder Root] [Inhabited Root] in
/-- A valid contributing link target is itself an exact checkpoint value. -/
theorem target_self
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E included carrier source target)
    (hcontributing : IncludedSupermajorityLink.Contributing cfg anchor L)
    (hanchorTarget : anchor.epoch ≤ target.epoch) :
    target = C target.root target.epoch := by
  have htarget := (V.endpoints_on_carrier L hcontributing trivial).2
  have htargetRoot : target.root = (C carrier target.epoch).root :=
    congrArg Checkpoint.root htarget
  have hcomp := P.checkpoint_comp (V.carrier_accepted L hcontributing trivial)
    hanchorTarget (Nat.le_refl target.epoch)
  calc
    target = C carrier target.epoch := htarget
    _ = C (C carrier target.epoch).root target.epoch := hcomp.symm
    _ = C target.root target.epoch := by rw [htargetRoot]

end ExactIncludedLinkValidity

namespace IncludedCertifiedJustified

omit [LinearOrder Root] [Inhabited Root] in
/-- Carrier-local included justification never moves before its trusted
anchor.  This structural fact does not need to forget inclusion. -/
theorem anchor_epoch_le
    {included : Root → Attestation Root → Prop}
    {carrier : Root} {c : Checkpoint Root}
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    anchor.epoch ≤ c.epoch := by
  induction h with
  | anchor => exact Nat.le_refl _
  | link _ link ih =>
      exact ih.trans (Nat.le_of_lt link.source_before_target)

omit [LinearOrder Root] [Inhabited Root] in
/-- Every checkpoint produced by an exact included certificate is itself an
epoch checkpoint.  The trusted anchor is the explicit base case. -/
theorem exact_self
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    {carrier c}
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    c = C c.root c.epoch := by
  cases h with
  | anchor => exact hanchorExact
  | @link source target hsource link =>
      have hanchorTarget :=
        (IncludedCertifiedJustified.anchor_epoch_le
          (cfg := cfg) hsource).trans
          (Nat.le_of_lt link.source_before_target)
      exact V.target_self (cfg := cfg) P link hsource hanchorTarget

omit [LinearOrder Root] [Inhabited Root] in
/-- The trusted anchor is an exact prefix of every checkpoint in an exact
included certificate. -/
theorem anchor_prefix
    {included : Root → Attestation Root → Prop}
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E included anchor C Accepted)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    {carrier c}
    (h : IncludedCertifiedJustified cfg E included anchor carrier c) :
    ExactCheckpointPrefix C anchor c := by
  induction h with
  | anchor =>
      unfold ExactCheckpointPrefix
      exact hanchorExact
  | @link source target hsource link ih =>
      have hanchorSource : anchor.epoch ≤ source.epoch :=
        IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hsource
      have hsourceTarget := V.source_prefix_target (cfg := cfg) P
        link hsource hanchorSource
      have htargetAccepted := V.target_accepted (cfg := cfg) P
        link hsource hanchorSource
      exact P.prefix_trans htargetAccepted (Nat.le_refl anchor.epoch)
        hanchorSource ih hsourceTarget

end IncludedCertifiedJustified

/-! ## Exact accountable finalized prefix -/

/-- The two certificate-accountability laws needed by the exact prefix proof.
This record is deliberately independent of endpoint stores and filter state. -/
structure CheckpointCertificateAccountability
    (E : Execution Root) (anchor : Checkpoint Root) : Prop where
  justified_unique : ∀ {x y : Checkpoint Root},
    CertifiedJustified cfg E anchor x →
    CertifiedJustified cfg E anchor y →
    x.epoch = y.epoch → x.root = y.root
  links_not_surround : ∀ {s t s' t' : Checkpoint Root},
    (L : SupermajorityLink cfg E s t) →
    (L' : SupermajorityLink cfg E s' t') →
    ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch)

/-- Concrete economic/no-slashing accountability realizes the narrow laws
used by exact checkpoint-prefix. -/
theorem CheckpointCertificateAccountability.of_assumptions
    {ext : Externals Root}
    {E : Execution Root} {anchor : Checkpoint Root}
    (hA : FFGAccountabilityAssumptions cfg ext E) :
    CheckpointCertificateAccountability cfg E anchor where
  justified_unique := fun hx hy he =>
    E.certified_justified_unique cfg ext hA hx hy he
  links_not_surround := fun L L' =>
    E.certified_links_not_surround cfg ext hA L L'

namespace IncludedCertifiedFinalized

/-- Casper accountable finalized-prefix strengthened from root ancestry to
the exact epoch-indexed checkpoint relation. -/
theorem exact_prefix_of_accountable
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : Execution.IncludedAttestationRelation cfg E validity)
    {C : Root → Epoch → Checkpoint Root}
    {Accepted : Root → Prop}
    (P : EpochCheckpointClosure anchor Accepted C)
    (V : ExactIncludedLinkValidity cfg E I.Included anchor C Accepted)
    (hanchorExact : anchor = C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {finalizedCarrier justifiedCarrier : Root}
    {finalized justified : Checkpoint Root}
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
        have hsourceTarget := V.source_prefix_target (cfg := cfg) P
          link hsource hanchorSource
        have htargetAccepted := V.target_accepted (cfg := cfg) P
          link hsource hanchorSource
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
          have hself := V.target_self (cfg := cfg) P
            link hsource hanchorTarget
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
            have hprefix := V.source_prefix_target (cfg := cfg) P
              hfinalized.finalizing_link hfinalized.justified
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

namespace CausalCarrierFFGState

/-- Production accepted-state adapter for exact accountable finalized prefix.
The only forgotten data is the extra proof that each positive inclusion
carrier is accepted; the inclusion predicate and every certificate witness
remain definitionally identical. -/
theorem exactFinalizedPrefix_of_accountable
    {ext : Externals Root}
    {S : CausalCarrierFFGState cfg ext E anchor}
    (P : EpochCheckpointClosure anchor
      (E.AcceptedRoot cfg ext) S.C)
    (V : S.ExactLinkValidity)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : CheckpointCertificateAccountability cfg E anchor)
    {finalizedCarrier justifiedCarrier : Root}
    {finalized justified : Checkpoint Root}
    (hfinalized : IncludedCertifiedFinalized cfg E
      S.includedAttestations.Included anchor finalizedCarrier finalized)
    (hjustified : IncludedCertifiedJustified cfg E
      S.includedAttestations.Included anchor justifiedCarrier justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    ExactCheckpointPrefix S.C finalized justified := by
  let I := Execution.TrustedCarrierAttestationRelation.relation
    (cfg := cfg) (ext := ext) (E := E) S.includedAttestations
  exact IncludedCertifiedFinalized.exact_prefix_of_accountable
    (cfg := cfg) I P V hanchorExact hacc hfinalized hjustified hepoch

end CausalCarrierFFGState


namespace CausalCarrierFFGState


end CausalCarrierFFGState

end FastConfirmation.Spec

end
