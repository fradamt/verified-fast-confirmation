module
public import FastConfirmation.Spec.Model

@[expose] public section

/-!
# Premises/Live

Vote support and live monotonicity premises. Reads the Spec Model. Read Claims next.
-/

section

/-! ## From TheoremStatements -/

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
hypothesis. The older `SpecAssumptions` record does not contain it. The
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

namespace Execution
/-- Actual non-honest active stake in the execution's initial epoch. The
accepted static-validator-set law keeps the active set fixed in the horizon. -/
def activeNonHonestWeight (E : Execution Root) : Gwei :=
  E.weight ((Finset.range E.registry.length).filter fun i =>
    i ∉ E.honest ∧
      is_active_validator (E.registry.getD i default)
        (compute_epoch_at_slot cfg (E.slot_at cfg 0)) = true)

end Execution
/-- Execution-level liveness proposed for strict monotonicity. The initial
head is used as the common voting branch; no field names a confirmed root or
an FCR branch condition. Committee coverage and honest vote production are
already fields of the accepted trajectory assumptions. -/
structure MonotonicityLiveAssumptions (E : Execution Root)
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
  /-- Every honest committee vote in the interval supports a descendant of
  the observer's initial head, in the voter's store when it votes. -/
  honest_votes_extend_initial_head : ∀ i ∈ E.honest, ∀ s k a,
    E.slot_at cfg n ≤ s → s < E.slot_at cfg m →
    E.vote i s = some (k, a) →
      is_ancestor (E.store cfg ext i k)
        (get_node_for_root a.data.beacon_block_root)
        (get_node_for_root (get_head cfg (E.store cfg ext v n)).root) = true
  /-- Integer form of paper Assumption 4 using actual non-honest stake and
  the proposer boost computed from the common anchor balance source. -/
  paper_byzantine_boost_bound :
    4 * E.activeNonHonestWeight cfg +
      compute_proposer_score cfg E.anchor_state < E.total_active cfg
  /-- The executable threshold budgets the configured Byzantine cap, which
  can exceed actual Byzantine stake. This additional arithmetic margin
  covers that conservative budget for a full-epoch committee window. -/
  configured_threshold_margin :
    2 * E.activeNonHonestWeight cfg +
      2 * (E.total_active cfg / 100 * cfg.confirmation_byzantine_threshold) +
      compute_proposer_score cfg E.anchor_state < E.total_active cfg
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

/-- Proposed executable-spec counterpart of the monotonicity half of paper
Theorem 1 (arXiv:2405.00549): under the accepted execution assumptions and
continued production, honest descendant voting, and Assumption 4, an earlier
stored confirmed root remains an ancestor of the later stored root. The
executable threshold also needs a margin against its configured Byzantine
allowance; this is a separate field of the proposed liveness bundle. The
`accepted` argument is instantiated with
`AcceptedActualFCRNextSlotSafetyAssumptions` downstream: that record is not
available in this upstream statement module. -/
def Spec_Monotonicity_live
    (accepted : Execution Root → Prop) : Prop :=
  ∀ E : Execution Root, accepted E →
    ∀ v ∈ E.honest, ∀ n m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      MonotonicityLiveAssumptions cfg ext E v n m →
      is_ancestor (E.store cfg ext v m)
        (get_node_for_root (E.confirmed cfg ext v m))
        (get_node_for_root (E.confirmed cfg ext v n)) = true

end FastConfirmation.Spec

end

end
