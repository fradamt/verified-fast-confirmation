# Removed live monotonicity theorem

The last commit that contains the theorem is `c9402973623708c2b5993836c7ac7aa0dee48fab`. The theorem was deleted after this commit.

## Exact former Lean statement

The code below copies the premise, its two fields and docstrings, the statement wrapper, and the theorem with its docstring from that commit. The namespace is `FastConfirmation.Spec`. `Root`, `cfg`, and `ext` are the section variables in the former source files.

```lean
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
  the live-monotonicity proof modules. This field also requires production: the
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
```

```lean
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
```

```lean
/-- Conditional live monotonicity for the stored executable FCR output.
The `LiveMonotonicityPremises` witness supplies store outcomes in addition to
the safety premise. Its `ffg_timely_justification` field closes
`previous_epoch_greatest_unrealized_checkpoint`,
`is_head_unrealized_justified_ok`, and the previous-slot-head voting-source
recency guard of `find_latest_confirmed_descendant`. Its
`honest_block_each_slot` field supplies honest blocks from execution start
without reorg of those blocks. These fields are store outcomes, not network
or behavior assumptions. -/
theorem live_confirmed_root_monotonicity :
    LiveConfirmedRootMonotonicity cfg ext := by
  intro E haccepted v hv n m hnm hHm live
  obtain ⟨h⟩ := haccepted
  exact h.live_confirmed_ancestor_interval cfg ext E live hv hHm
    m (Nat.le_refl m) n hnm
```

## Reason for deletion

The FCR can reset a stored confirmed root to an ancestor. `get_latest_confirmed` can fall back to the finalized or justified checkpoint when a guard fails. The relevant cases are a mismatch in `previous_epoch_greatest_unrealized_checkpoint`, failure of `is_head_unrealized_justified_ok`, a stale previous-slot-head voting source, and a confirmed block that is off the head chain. Monotonicity can hold only on an interval with no such reset.

A proof that excludes resets needs liveness assumptions about synchrony, an honest majority, honest block production, and timely justification, in the style of paper Assumption 6. The deleted `ffg_timely_justification` field instead required the FFG store outcomes that made those guards pass. The `honest_block_each_slot` field required blocks and descendant votes from execution start with no reorg of those honest blocks. These requirements were close to the desired result and did not establish it from network and behavior assumptions.

The former premise also cannot hold from real genesis past epoch 2. The Python `process_justification_and_finalization` function returns early in epochs 0 and 1. It therefore cannot produce the epoch-1 unrealized justification that `ffg_timely_justification` requires at the epoch-2 boundary. The former finite witness covered only a short interval whose FFG timing used the genesis anchor.

The safety theorem does not depend on this result. A reset to a justified or finalized ancestor preserves the safety claim. A future monotonicity theorem needs a clear interval condition that excludes resets or a derived no-reset result from satisfiable liveness premises. It must cover the real genesis behavior and justify the FFG timing from the executable transitions.
