module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Traces
public import FastConfirmationStatements.Premises.Live
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.Execution
public import FastConfirmationStatements.Premises.Trajectory

@[expose] public section

/-! Defines the public next-slot safety and live monotonicity propositions over accepted executions. -/

section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
namespace NextSlotSafetyPremises
end NextSlotSafetyPremises
end Execution
/-- Accepted whole-output safety with the same endpoint quantifiers and timing
as `Spec_Safety_next_slot`, under the accepted executable-semantics bundle.

The global `NextSlotSynchronyPremises` inside `completed_calls` makes this the
current model's GST-0 specialization. Its four fields are honest-attestation
delivery, block relay, payload-envelope relay, and equivocation-evidence relay;
it does not require the additional `latest_message_relay` premise of the full
`Synchrony` bundle. -/
def ConfirmedRootSafeFromNextSlot : Prop :=
  ∀ E : Execution Root,
    E.NextSlotSafetyPremises cfg ext →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
          E.WithinHorizon cfg m →
            is_ancestor (E.store cfg ext w m)
              (get_head cfg (E.store cfg ext w m))
              (get_node_for_root (E.confirmed cfg ext v n)) = true

/-- Accepted-bundle specialization of the upstream strict-monotonicity
statement. The fifth live field now bounds FFG checkpoint visibility at
epoch boundaries. The one-confirmation, reconfirmation, and fork-choice
bridges are developed in the live-monotonicity proof modules. -/
def LiveConfirmedRootMonotonicity : Prop :=
  ConfirmedRootMonotonicity cfg ext
    (fun E => Nonempty (E.NextSlotSafetyPremises cfg ext))

end FastConfirmation.Spec
end

end
