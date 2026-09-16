import FastConfirmation.Spec.Proof.AcceptedActualFCRCommon
import FastConfirmation.Spec.Proof.WeakObservedRestartAdoption

/-!
# Spec / Proof / WeakObservedRestartDynamicSafety

The arm-by-arm discharge of `Weak.ObservedResetSeedSafety`
(`WeakTrajectorySafety.lean`), the single open obligation of the weak
full-rule fold.  Weak twin of
`Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`
(`AcceptedObservedRestartDynamicSafety.lean`), with the querying node's
honesty binder dropped.

The strong proof splits the endpoint's realized justified epoch `J.epoch`
against the banked checkpoint's epoch `c.epoch` two ways — `c.epoch = J.epoch`
by accountable uniqueness, `c.epoch < J.epoch` by an honest formation-target
vote plus the `safeFrom_of_headStep_at` strong induction — after first using
the querying node's honesty twice, to relay the banked root and the GU carrier
tip.  Rule delta 5's head-indexed banking replaces both relays
(`Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`,
`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`), and stage 2
(`WeakObservedRestartAdoption.lean`) replaces the epoch bound that feeds the
split.

This file adds the arms that the split itself needs, in the order of
`docs/weak-full-rule.md`'s staged plan:

* **stage 3, the anchor arm** — `Weak.genesisRoot_safeFrom_of_acceptedGlobalTrajectory`
  and its call-scoped form.  The weak invariant
  `Weak.CertifiedBankedJustification` degenerates to "the banked root is a
  genesis block root", which has no supplier and no certificate at all; the
  genesis store's `block_roots` is the anchor singleton, so this arm never
  reaches the epoch split — it closes outright by
  `Execution.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`, whose honesty
  is quantified over the *receiving* endpoint only.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Stage 3 — the anchor arm -/

/-- **Every genesis block root is safe from every second.** The genesis store
built by `get_forkchoice_store` knows exactly one block, the anchor block, so a
root in `E.genesis_store.block_roots` *is* `B.anchor.root`, and the trusted
anchor is below every in-horizon honest endpoint's head from second `0`
(`Execution.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory`).

This is the whole content of the anchor arm of
`Weak.CertifiedBankedJustification`: that arm records only genesis membership
of the banked root — it carries no supplier, no certificate, and hence no epoch
bound — so it cannot be routed through the adoption law of stage 2, and does
not need to be. -/
theorem genesisRoot_safeFrom_of_acceptedGlobalTrajectory
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {r : Root} (hr : r ∈ E.genesis_store.block_roots) (q : ℕ) :
    E.SafeFrom cfg ext r q := by
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hT.genesis
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hroot := congrArg Checkpoint.root hanchor
    rw [hgeq] at hroot
    simpa only [get_forkchoice_store] using hroot
  have hrEq : r = B.anchor.root := by
    rw [hgeq] at hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    rw [hr, hanchorRoot]
  rw [hrEq]
  exact (E.trustedAnchor_safeFrom_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary).mono cfg ext E (Nat.zero_le q)

/-- **The observed-reset seed is safe whenever its banking certificate
degenerates.** Call-scoped form of the anchor arm: at a weak FCR call whose
candidate came from the epoch-start restart branch, if the banked checkpoint's
root is a genesis block root then the restarted-from root is `SafeFrom` at the
call second.

No honesty binder at `obs`, no certificate, and no epoch premise — the arm is
closed before the epoch split of the strong proof is reached. -/
theorem ObservedResetCandidateInputAt.safeFrom_of_anchorArm
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex} {n : ℕ}
    {trace : Weak.GetLatestConfirmedTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hgenesis : ((E.weakFcrStep cfg ext obs n).current_epoch_observed_justified_checkpoint).root ∈
      E.genesis_store.block_roots) :
    E.SafeFrom cfg ext trace.afterObserved (n + 1) := by
  rw [hinput.input_eq]
  exact Weak.genesisRoot_safeFrom_of_acceptedGlobalTrajectory cfg ext B hT
    hanchor hboundary hgenesis (n + 1)

end Weak

end FastConfirmation.Spec
