module
public import FastConfirmationStatements.Premises.FFGCertificates

@[expose] public section

/-! Concrete scheduled FFG link certificates used by proofs. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
namespace Execution
variable (E : Execution Root)
end Execution
/-- A two-thirds source-to-target link backed by concrete scheduled
attestations.  The signers are confined to the target epoch's committee union,
and a link always advances the checkpoint epoch. -/
structure SupermajorityLink (E : Execution Root)
    (source target : Checkpoint Root) : Type where
  signers : Finset ValidatorIndex
  source_before_target : source.epoch < target.epoch
  target_descends_source : E.RootDescends target.root source.root
  target_epoch_within : target.epoch < E.verification_horizon
  target_span_within :
    E.SlotWithinHorizon cfg (target.epoch * cfg.slots_per_epoch) ∧
    E.SlotWithinHorizon cfg
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  signers_in_epoch : signers ⊆
    E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  signer_attestation : ∀ i ∈ signers,
    ∃ (w : ValidatorIndex) (n : ℕ) (a : Attestation Root) (fromBlock : Bool),
      Event.attestation a fromBlock ∈ E.schedule w n ∧
      i ∈ a.attesting_indices ∧
      a.data.source = source ∧ a.data.target = target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers

/-- Checkpoint justification generated from the trusted anchor by concrete
supermajority links. -/
inductive CertifiedJustified (E : Execution Root) (anchor : Checkpoint Root) :
    Checkpoint Root → Prop
  | anchor : CertifiedJustified E anchor anchor
  | link {source target : Checkpoint Root} :
      CertifiedJustified E anchor source →
      SupermajorityLink cfg E source target →
      CertifiedJustified E anchor target

/-- Casper finalization certificate: a justified checkpoint with a concrete
supermajority link to a descendant checkpoint in the immediately following
epoch. -/
structure CertifiedFinalized (E : Execution Root) (anchor c : Checkpoint Root) where
  justified : CertifiedJustified cfg E anchor c
  child : Checkpoint Root
  child_epoch : child.epoch = c.epoch + 1
  finalizing_link : SupermajorityLink cfg E c child

end FastConfirmation.Spec

end
