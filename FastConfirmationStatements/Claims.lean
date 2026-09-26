module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Premises.LiveMonotonicity
public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationStatements.Premises.NextSlotSafety
public import FastConfirmationStatements.Premises.FCRCallPremises

@[expose] public section

/-! Defines the public next-slot safety and live monotonicity propositions over accepted executions. -/

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

/-- Conditional live result, separate from the safety review claim.
`LiveMonotonicityPremises.ffg_timely_justification` supplies the store outcomes
that close `previous_epoch_greatest_unrealized_checkpoint`,
`is_head_unrealized_justified_ok`, and the previous-slot-head voting-source
recency guard of `find_latest_confirmed_descendant`.
`LiveMonotonicityPremises.honest_block_each_slot` supplies production and
descendant voting from execution start, with no reorg of those honest blocks.
These are store outcomes, not network or behavior assumptions. -/
def LiveConfirmedRootMonotonicity : Prop :=
  ConfirmedRootMonotonicity cfg ext
    (fun E => Nonempty (E.NextSlotSafetyPremises cfg ext))

end FastConfirmation.Spec
end

end
