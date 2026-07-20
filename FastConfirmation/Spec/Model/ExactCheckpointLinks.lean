import FastConfirmation.Spec.Model.FFGStateSemantics

/-!
# Spec / Model / ExactCheckpointLinks

The reduced beacon-state projection does not retain enough block-history data
to turn arbitrary root descent into epoch-indexed checkpoint descent.  This
module records the narrow, certificate-scoped semantic interface.

The core declarations are independent of either the production
`AcceptedChainFFGState` or the migration-only `ChainFFGState`: callers supply
the positive inclusion relation, formed predicate, checkpoint projection, and
accepted carrier domain.  This lets the same certificate proof consume the
accepted-prefix state without projecting through the broader scheduled-root state.

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
structure AcceptedEpochCheckpointProjection
    (anchor : Checkpoint Root)
    (Accepted : Root → Prop)
    (C : Root → Epoch → Checkpoint Root) : Prop where
  checkpoint_root_accepted : ∀ {r e}, Accepted r →
    anchor.epoch ≤ e → Accepted (C r e).root
  checkpoint_comp : ∀ {r sourceEpoch targetEpoch}, Accepted r →
    anchor.epoch ≤ sourceEpoch → sourceEpoch ≤ targetEpoch →
    C (C r targetEpoch).root sourceEpoch = C r sourceEpoch

/-- The exact epoch-indexed checkpoint-prefix relation represented by `C`. -/
def ExactCheckpointPrefix
    (C : Root → Epoch → Checkpoint Root)
    (source target : Checkpoint Root) : Prop :=
  source = C target.root source.epoch

variable {anchor : Checkpoint Root}

/-! ## Generic certificate-scoped exact-link validity -/

/-- Carrier-local exactness for an abstract formed-checkpoint predicate and
checkpoint projection. -/
def FormedCheckpointExact
    (formed : Root → Checkpoint Root → Prop)
    (C : Root → Epoch → Checkpoint Root)
    (Accepted : Root → Prop) : Prop :=
  ∀ {carrier c}, Accepted carrier → formed carrier c →
    c = C carrier c.epoch

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

/-- Accepted-carrier closure for links which extend an included certificate.
The bare anchor constructor on an arbitrary carrier is intentionally outside
this closure. -/
def IncludedCertificateCarrierAccepted
    (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root)
    (Accepted : Root → Prop) : Prop :=
  ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
      Accepted carrier

/-- Certificate-to-formed closure at one contributing link.  Both the already
certified source and the target produced by applying the link are formed on
that carrier.  The bare anchor constructor remains unconstrained. -/
def IncludedCertificateFormedClosure
    (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root)
    (formed : Root → Checkpoint Root → Prop) : Prop :=
  ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
      formed carrier source ∧ formed carrier target

/-- Both endpoints of a contributing link are formed on its accepted
certificate carrier. -/
structure IncludedLinkEndpointsFormed
    (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root)
    (formed : Root → Checkpoint Root → Prop)
    (Accepted : Root → Prop) : Prop where
  carrier_accepted : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    Accepted carrier
  endpoints_formed : ∀ {carrier source target},
    (L : IncludedSupermajorityLink cfg E included
      carrier source target) →
    IncludedSupermajorityLink.Contributing cfg anchor L →
    formed carrier source ∧ formed carrier target

/-- Exact carrier law for the included links which actually extend a
carrier-local justification certificate.

This does not constrain arbitrary included attestations or links with an
uncertified source. -/
structure ExactIncludedLinkValidity
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

namespace AcceptedChainFFGState

/-- Production accepted-state instance of the generic exact-link law. -/
abbrev ExactLinkValidity
    {ext : Externals Root}
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop :=
  ExactIncludedLinkValidity cfg E S.includedAttestations.Included anchor
    S.C (E.AcceptedRoot cfg ext)

/-- Production accepted-state instance of formed checkpoint exactness. -/
abbrev FormedExact
    {ext : Externals Root}
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop :=
  FormedCheckpointExact S.formed S.C (E.AcceptedRoot cfg ext)

/-- Production accepted-state certificate-to-formed closure. -/
abbrev CertificateFormedClosure
    {ext : Externals Root}
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop :=
  IncludedCertificateFormedClosure cfg E S.includedAttestations.Included
    anchor S.formed

end AcceptedChainFFGState

namespace ChainFFGState

/-- Exact-link validity specialized to the scheduled-root state. -/
abbrev ExactLinkValidity
    (S : ChainFFGState cfg E anchor) (Accepted : Root → Prop) : Prop :=
  ExactIncludedLinkValidity cfg E S.includedAttestations.Included anchor
    S.C Accepted

end ChainFFGState

end FastConfirmation.Spec
