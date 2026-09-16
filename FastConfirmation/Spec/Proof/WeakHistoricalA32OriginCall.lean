import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall
import FastConfirmation.Spec.Proof.WeakFCRCallContracts

/-!
# Spec / Proof / WeakHistoricalA32OriginCall

Observer-side twin of the strong lazy-crossing plumbing in
`AcceptedHistoricalA32OriginCall.lean`, `docs/weak-final-wave.md` §3.2.

This module sits *below* the whole weak A3.2 stack, because the predicate it
defines is what the weak strict-edge dispatcher and the weak write-back
induction both consume.  It therefore imports only `weakConfirmed`'s defining
module and the strong origin-call file it mirrors.

## Why the weak predicate is simpler than the strong one

`Execution.PriorStrictCallWriteBackSafe` carries two things the weak twin does
not need:

* a quantifier `∀ i ∈ E.honest` — the weak trajectory is about **one** fixed
  observer, so the weak predicate is single-node by construction, and the
  strong proof's "pick the origin node out of the honest quantifier" step
  (`AcceptedHistoricalA32OriginCallAt.safeFrom_of_prior`) disappears; and
* the strictness conjunct
  `E.confirmed v (k + 1) ≠ (E.getLatestConfirmedTraceAt v k).afterObserved`.

The strictness conjunct is a *strong-side artefact*
(`docs/weak-final-wave.md` §3.2, correcting
`docs/crossing-call-support-residue.md` §9.1's Correction to A4).  On the
strong side the `finalizedResetUnchanged` arm recovers safety only through
`finalizedReset_safeFrom_of_nextSlotSynchrony`, which genuinely needs
`slot_at (n + 1) + 1 ≤ slot_at q` and so fails at `q = n + 1`.  The weak fold
has no such arm: `Execution.weak_safeFrom_observerCall_closed` closes **all
four** branches of `Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`
unconditionally, because the weak fold hands it `hbase` at
`slot_start (slot_at (n + 1)) = n + 1`.  So the weak call step already proves
the unweakened `SafeFrom trace.result (n + 1)` on every branch and merely
throws it away; `Weak.ObserverFoldSafetyAt` keeps it, with no side condition.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable (E : Execution Root)

/-- **The threaded weak fold output the lazy A3.2 transport consumes.**

Every weak FCR call of the observer at a second *strictly below* `n` writes
back a root that is safe from its own write-back second — the **unweakened**
`slot_start`-indexed deadline, not the `followingSlotStart`-mono'd one.

This is exactly the `callSecond` component of `Weak.ObserverFoldSafetyAt`
(`WeakTrajectorySafety.lean`) at the seconds `k + 1 ≤ n`, i.e. precisely what
the weak fold's strengthened induction hypothesis hands out at its `succ n`
step.  Well-foundedness is the strict `k < n`. -/
def ObserverPriorCallWriteBackSafe (obs : ValidatorIndex) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → E.WithinHorizon cfg (k + 1) →
    E.IsFCRCallAt cfg ext obs k →
      E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs (k + 1)) (k + 1)

/-- Monotonicity in the horizon: a wider prior window restricts. -/
theorem ObserverPriorCallWriteBackSafe.mono {E : Execution Root}
    {obs : ValidatorIndex} {n m : ℕ} (hnm : n ≤ m)
    (h : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs m) :
    Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hnm)

end Weak

end FastConfirmation.Spec
