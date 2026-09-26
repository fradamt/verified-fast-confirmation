module
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-!
# Premises/CheckpointLinks

The reduced beacon-state projection does not retain enough block-history data
to turn arbitrary root descent into epoch-indexed checkpoint descent.  This
module records the narrow, certificate-scoped semantic interface.

The core declarations do not depend on `AcceptedBlockFFGState`: callers supply
the positive inclusion relation, formed predicate, checkpoint projection, and
accepted carrier domain.  `AcceptedBlockFFGState.LinkCheckpointAgreement` is the
accepted-state instance.

Only an included supermajority link whose source already has a carrier-local
included justification certificate is constrained.  Links with uncertified
sources remain unconstrained.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## Accepted checkpoint projection -/

/-- A checkpoint projection on an accepted execution domain.  Composition is
only required from the trusted anchor epoch onward; values below a
checkpoint-sync anchor remain outside the law. -/
structure EpochCheckpointProjectionLaws
    (anchor : Checkpoint Root)
    (Accepted : Root → Prop)
    (C : Root → Epoch → Checkpoint Root) : Prop where
  checkpoint_root_accepted : ∀ {r e}, Accepted r →
    anchor.epoch ≤ e → Accepted (C r e).root
  checkpoint_comp : ∀ {r sourceEpoch targetEpoch}, Accepted r →
    anchor.epoch ≤ sourceEpoch → sourceEpoch ≤ targetEpoch →
    C (C r targetEpoch).root sourceEpoch = C r sourceEpoch

variable {anchor : Checkpoint Root}

/-! ## Generic certificate-scoped exact-link validity -/

namespace IncludedSupermajorityLink

/-- A carrier-local included link contributes to a justification certificate
exactly when its source is already certified on that same carrier.  Applying
the link constructor then certifies its target. -/
def Contributing
    (anchor : Checkpoint Root)
    {E : Execution Root}
    {included : Root → Attestation Root → Prop}
    {carrier source target}
    (_L : IncludedSupermajorityLink cfg E included
      carrier source target) : Prop :=
  IncludedCertifiedJustified cfg E included anchor carrier source

end IncludedSupermajorityLink

/-- Exact carrier law for the included links which actually extend a
carrier-local justification certificate.

This does not constrain arbitrary included attestations or links with an
uncertified source. -/
structure IncludedLinkCheckpointAgreement
    (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root)
    (C : Root → Epoch → Checkpoint Root)
    (Accepted : Root → Prop) : Prop where
  carrier_accepted : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    Accepted carrier
  endpoints_on_carrier : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    source = C carrier source.epoch ∧
      target = C carrier target.epoch

/-! ## State-specific abbreviations -/

variable {E : Execution Root}

namespace AcceptedBlockFFGState

/-- Production accepted-state instance of the generic exact-link law. -/
abbrev LinkCheckpointAgreement
    {ext : BeaconFunctionInterface Root}
    (S : AcceptedBlockFFGState cfg ext E anchor) : Prop :=
  IncludedLinkCheckpointAgreement cfg E S.includedAttestations.Included anchor
    S.checkpoint_at_epoch (E.RootKnownInScheduledPrefix cfg ext)

end AcceptedBlockFFGState

end FastConfirmation.Spec

end
