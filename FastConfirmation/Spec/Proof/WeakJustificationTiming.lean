import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedResetAdoption

/-!
# Spec / Proof / WeakJustificationTiming

The justified-side mirror of
`Execution.includedCertifiedFinalized_epoch_lt_current_of_acceptedCarrier`
(`AcceptedResetCheckpointClassification.lean`).

That theorem says a non-anchor *finalized* checkpoint carried by a reachable
store is strictly older than the store's current epoch.  The observed-reset
arm of the weak phase dispatcher needs the same timing fact one level down, on
the *unrealized-justified* side and in slot rather than epoch form: a
non-anchor accepted `AU` checkpoint of a block known to a store cannot have its
own epoch boundary at or after that store's current slot.

The proof is the finalized one with the finalizing link replaced by the
justifying link supplied by `AcceptedFormedCheckpointEvidence.certified`:

1. `B.state.AU` unfolds to a carrier with
   `AcceptedFormedCheckpointEvidence … carrier c`;
2. its `certified` component is an `IncludedCertifiedJustified` derivation —
   the `anchor` constructor is excluded by `c ≠ B.anchor`, so a
   supermajority `link` into `c` exists;
3. the minimum-total-balance rule makes that link's signer set nonempty, and
   one signer's attestation is included on the carrier's chain, hence (by
   `E.RootDescends` transitivity through `tip`) on the *tip's* chain;
4. `Execution.includedAttestationSlot_lt_acceptedCarrierBlock` at `tip` and
   `Execution.store_blocks_slot_le_current` place that attestation strictly
   before the store's current slot;
5. `IncludedAttestationEvidence.target_epoch` identifies `c.epoch` with the
   attestation's own epoch, so `c`'s start slot is at most the attestation
   slot.

No honesty hypothesis is used: every step is a store-domain or accepted-FFG
fact, so the observer may be Byzantine.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- **The trusted anchor's root is a genesis-store block.**

`hanchor` makes the anchor the genesis store's justified checkpoint, and
`get_forkchoice_store` seeds that checkpoint at the anchor block, whose root is
the single entry of `block_roots`.  Factored out of
`Weak.StrictSelectorAdvanceAt.previousFinalizedReset_anchorLineage`, which
derived it inline, so that the observed-reset arm can reuse it. -/
theorem anchorRoot_mem_genesis
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    B.anchor.root ∈ E.genesis_store.block_roots := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
  have hroot : B.anchor.root = ablk.root := by
    rw [hanchor, hgen]
    rfl
  rw [hgen, hroot]
  simp only [get_forkchoice_store, List.mem_singleton]

/-- **A non-anchor accepted `AU` checkpoint's epoch boundary is strictly
before its tip's store clock.**

Justified-side mirror of
`Execution.includedCertifiedFinalized_epoch_lt_current_of_acceptedCarrier`,
stated in slot form because the observed-reset arm compares the checkpoint's
boundary against the call's own slot rather than against an epoch index.

`tip` only has to be known at `(obs, n)`; the carrier supplying the evidence
need not be, since the included attestation is transported onto the tip's own
chain by `Execution.RootDescends.trans` before the slot bound is read. -/
theorem auCheckpoint_startSlot_lt_currentSlot
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex} {n : ℕ} {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU cfg ext tip c) (hne : c ≠ B.anchor) :
    compute_start_slot_at_epoch cfg c.epoch <
      get_current_slot cfg (E.store cfg ext obs n) := by
  obtain ⟨ast, ablk, hgenEq, hslotEq, hparentNe⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslotEq⟩
  obtain ⟨carrier, hdesc, hformed⟩ := hAU
  obtain ⟨hcertified⟩ := (B.state.formed_evidence hformed).certified
  cases hcertified with
  | anchor => exact absurd rfl hne
  | link _hsource L =>
      have hsigners : L.signers.Nonempty := by
        by_contra hnone
        have hempty : L.signers = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnone
        have hzero : 2 * E.total_active cfg ≤ 0 := by
          simpa only [hempty, Execution.weight, Finset.sum_empty,
            Nat.mul_zero] using L.supermajority
        exact (Nat.not_lt_of_ge hzero)
          (Nat.mul_pos (by omega) (E.total_active_pos cfg))
      obtain ⟨i, hi⟩ := hsigners
      obtain ⟨a, ⟨containing, hcarrierContaining, hincluded⟩,
        _hiAttests, _haSource, haTarget⟩ := L.signer_attestation i hi
      have hchainTip : AttestationIncludedOnChain E
          B.state.includedAttestations.Included tip a :=
        ⟨containing, Execution.RootDescends.trans E hdesc hcarrierContaining,
          hincluded⟩
      have hslotLt : a.data.slot <
          ((E.store cfg ext obs n).blocks tip).slot :=
        E.includedAttestationSlot_lt_acceptedCarrierBlock cfg ext B hT htip
          hchainTip
      have htipLe : ((E.store cfg ext obs n).blocks tip).slot ≤
          get_current_slot cfg (E.store cfg ext obs n) :=
        E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
          obs n tip htip
      have hevidence := B.state.includedAttestations.evidence hincluded
      have hcEpoch : c.epoch = compute_epoch_at_slot cfg a.data.slot := by
        calc
          c.epoch = a.data.target.epoch :=
            (congrArg Checkpoint.epoch haTarget).symm
          _ = compute_epoch_at_slot cfg a.data.slot := hevidence.target_epoch
      have hstartLe : compute_start_slot_at_epoch cfg c.epoch ≤ a.data.slot := by
        have hmulDiv := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
        have hdiv : a.data.slot / cfg.slots_per_epoch = c.epoch := by
          simpa only [compute_epoch_at_slot] using hcEpoch.symm
        rw [hdiv] at hmulDiv
        simpa only [compute_start_slot_at_epoch] using hmulDiv
      exact Nat.lt_of_le_of_lt hstartLe (Nat.lt_of_lt_of_le hslotLt htipLe)

end Weak

end FastConfirmation.Spec
