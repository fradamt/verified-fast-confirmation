module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-!
# Premises/LiveMonotonicity

Vote support and live monotonicity premises. States vote support and timely FFG conditions for live monotonicity.
-/

section

/-! ## Live premise support -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
/-- The spec's proviso on both `will_*` predictions ("This function assumes
that all honest validators will be voting in support of the current epoch
target"): from second `n` on, every honest vote of a slot in the target's
epoch carries target `T`.

This is *not* an extra behavioral assumption on top of `HonestBehavior` —
honest validators always vote the target derived from their own head
(validator.md over fork-choice.md). But that per-validator fact yields
support for *`v`'s* target `T` only under **cross-validator head/boundary
agreement** (every honest head's epoch-boundary block is `T.root`), which is
exactly what the FCR's preceding checks are mid-way through establishing
when the gates are consulted. The property is an explicit, call-scoped
hypothesis. The
accepted theorem requires it through `completed_calls.helper_provisos` at each
actual guarded FCR call whose next second is in the verification horizon.
Without the gating the fields would be inconsistent:
the `will_*` booleans are arithmetically true early in every epoch (the
elapsed-committee estimate is still small) even while honest heads — and
hence honest targets — are split across an adversarial boundary proposal. -/
def HonestVotesSupportTarget (E : Execution Root) (T : Checkpoint Root) (n : ℕ) :
    Prop :=
  E.WithinHorizon cfg n ∧
    ∀ v ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = T.epoch → E.slot_at cfg n ≤ s →
      ∀ k a, E.vote v s = some (k, a) → a.data.target = T

/-- Execution-level liveness used by the proved strict monotonicity claim. The initial
head is used as the common voting branch; no field names a confirmed root or
an FCR branch condition. Committee coverage and honest vote production are
already fields of the accepted trajectory assumptions. -/
structure LiveMonotonicityPremises (E : Execution Root)
    (v : ValidatorIndex) (n m : ℕ) : Prop where
  /-- An honestly proposed block for every slot from the execution start
  through the interval is in every honest store by the next slot's first
  second. Honest votes in that slot and later slots support that block's
  descendants; the block is known to each such voter when it votes. Prefix
  production and support are needed before `n`: interval-only liveness admits
  a stale cached root already at the interval's first call. -/
  honest_block_each_slot : ∀ s : Slot,
    E.slot_at cfg 0 ≤ s → s < E.slot_at cfg m →
    ∃ r b, E.BlockAt r b ∧ b.slot = s ∧
      b.proposer_index ∈ E.honest ∧
      (∀ w ∈ E.honest,
        r ∈ (E.store cfg ext w (E.slot_start cfg (s + 1))).block_roots) ∧
      ∀ i ∈ E.honest, ∀ t k a,
        s ≤ t → t < E.slot_at cfg m →
        E.vote i t = some (k, a) →
          r ∈ (E.store cfg ext i k).block_roots ∧
          is_ancestor (E.store cfg ext i k)
            (get_node_for_root a.data.beacon_block_root)
            (get_node_for_root r) = true
  /-- Paper Assumption 6 counterpart: conditional eventual FFG closure is
  visible at the last-slot call of each completed epoch. The checkpoint is
  an epoch block on every honest head chain. At the
  next epoch start the head agrees with that observation and the previous
  head has a recent voting source. Paper Assumption 3.2 alone permits a
  two-epoch lag, which closes the executable gates in
  `MonotonicityLiveGates.lean`. This field also requires production: the
  checkpoint root is the block at the first slot of epoch `e`, and enough
  blocks in `e` carry its votes to justify it by the last slot. See
  `docs/REVIEW_GUIDE.md`, "Scope of the live premises". -/
  ffg_timely_justification : ∀ e : Epoch,
    compute_epoch_at_slot cfg (E.slot_at cfg 0) ≤ e →
    compute_start_slot_at_epoch cfg (e + 1) ≤ E.slot_at cfg m →
    ∃ c : Checkpoint Root,
      c.epoch = e ∧
      (∃ r b, E.BlockAt r b ∧
        compute_epoch_at_slot cfg b.slot = e ∧ c.root = r) ∧
      ∀ w ∈ E.honest,
        let last := E.store cfg ext w
          (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1) - 1))
        let next := E.store cfg ext w
          (E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1)))
        last.unrealized_justified_checkpoint = c ∧
        get_checkpoint_for_block cfg next (get_head cfg next).root e = c ∧
        next.unrealized_justifications (get_head cfg next).root = c ∧
        (get_voting_source cfg next (get_head cfg last).root).epoch + 2 ≥ e + 1

/-- Executable-spec counterpart of the monotonicity half of paper Theorem 1
(arXiv:2405.00549): under accepted execution assumptions, honest block
production and descendant voting, and timely FFG closure, an earlier stored
confirmed root remains an ancestor of the later stored root. The `accepted`
argument is instantiated with `NextSlotSafetyPremises` downstream: that record
is not available in this upstream statement module. -/
def ConfirmedRootMonotonicity
    (accepted : Execution Root → Prop) : Prop :=
  ∀ E : Execution Root, accepted E →
    ∀ v ∈ E.honest, ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      LiveMonotonicityPremises cfg ext E v n m →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.confirmed cfg ext v m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true

end FastConfirmation.Spec

end

end
