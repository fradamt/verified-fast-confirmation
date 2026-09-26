module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.NextSlotSafety
public import FastConfirmationStatements.Premises.FCRCallPremises

@[expose] public section

/-! Defines the public next-slot safety proposition over accepted executions. -/

section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- Accepted whole-output safety: every stored FCR output of an honest node is
in the observer's block store and is an ancestor of its head from the next
slot on, within the verification horizon, under the accepted executable-semantics bundle.

The global `NextSlotSynchronyPremises` inside `completed_calls` makes this the
current model's GST-0 specialization. Its delivery contracts cover honest votes,
cutoff block paths, ordered payload envelopes, data availability, and cutoff
equivocation evidence under a positive delay and strict deadline fit. -/
def ConfirmedRootSafeFromNextSlot : Prop :=
  ∀ E : Execution Root,
    E.NextSlotSafetyPremises cfg ext →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at cfg n + 1 ≤ E.slot_at cfg m →
          E.WithinHorizon cfg m →
            E.confirmed cfg ext v n ∈ (E.store cfg ext w m).block_roots ∧
              is_ancestor (E.store cfg ext w m)
                (get_head cfg (E.store cfg ext w m))
                (get_node_for_root (E.confirmed cfg ext v n)) = true

end FastConfirmation.Spec
end

end
