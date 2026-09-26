module
public import FastConfirmationProofs.Checkpoints.DeadlineBlockAdmissibility

@[expose] public section

/-! Checkpoint-compatible roots reach honest receivers after their source cutoff. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable {E : Execution Root}

/-- Exact checkpoint compatibility discharges the permanent exclusion branch
of deadline block delivery. All times remain inside the supplied horizon. -/
theorem deadline_root_known_of_checkpointCompatible
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hrelay : DeadlineBlockRelay cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : InitialAnchorAtEpochBoundary (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v w : ValidatorIndex} {n m : ℕ} {r : Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (hr : r ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m)
    (hFknown : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hanchorLe : B.anchor.epoch ≤
      (E.store cfg ext w m).finalized_checkpoint.epoch)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext v n) r
        (E.store cfg ext w m).finalized_checkpoint.epoch) :
    r ∈ (E.store cfg ext w m).block_roots := by
  rcases hrelay v hv n r hHn hr hdue
      w hw m hHm hnext hlt with hknown | hexcluded
  · exact hknown
  · by_cases hm : r ∈ (E.store cfg ext w m).block_roots
    · exact hm
    have hexcluded := E.permanentBlockExclusion_mono_of_not_mem cfg ext
      ((Nat.sub_le _ 1).trans hnext) hm hexcluded
    exact False.elim (E.checkpointCompatible_not_permanentlyExcluded
      cfg ext B hT hanchor hboundary hHm hr hFknown hanchorLe
      hcheckpoint hexcluded)

end Execution
end FastConfirmation.Spec

end
