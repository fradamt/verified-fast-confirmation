module
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability

@[expose] public section

/-!
# Spec / Proof / AheadFacade: the ahead-regime observed-anchor geometry

At an honest store `(w, m)` the fork-choice head is computed on `get_filtered_block_tree`,
which is **rooted at the store's realized justified checkpoint** `jc := jc(w, m)`: every
filtered root descends from `jc.root`, and `head ⪰ jc.root` always
(`E5Filter.filtered_through_justified_K` / `get_head_root_mem_or`). The observed anchor
`obs := (fcrStoreAtCall v n).current_epoch_observed_justified_checkpoint` is `JustifiedIn (store w m)`
everywhere (`ObservedDom.fcrStep_observed_justifiedIn`). The question `head ⪰ obs.root` splits
on `obs.epoch` vs `jc.epoch`:

* **`obs.epoch ≤ jc.epoch`** — closed (`E5Filter.head_ge_of_justifiedIn_le`): `justified_ancestry`
  puts `obs` on `jc`'s chain (`jc ⪰ obs`), and `E5Filter.head_ge_of_justified_ge_K` lifts
  `head ⪰ obs` through the filter alone — no weight margin.
* **`jc.epoch < obs.epoch`** — the *ahead* regime. This module keeps the two structural facts
  about it that survive; the proposition that generalized over it does not (see below).

## Results

1. `obs_descends_justified` — in the ahead regime `obs.root` **descends from** `jc.root`
   (`justified_ancestry` with the roles swapped: the higher-epoch justified checkpoint is
   below on the chain). So `obs.root` sits strictly between `jc.root` and any filtered leaf
   on `obs`'s branch.

2. `justifiedIn_root_known_of_realized` — the realized-checkpoint cases of observed-anchor
   root knownness: when the observed anchor coincides with the store's *realized* justified or
   finalized checkpoint its root is known (`checkpoint_known`); the
   unrealized/`unrealized_justifications` disjuncts of `JustifiedIn` carry no such export.

## Why the ahead regime never needed an explicit premise, and why the premise is gone

The ahead regime is **not** closable from filter mechanics + `JustifiedIn`. The filter is
rooted at `jc.root`, and a branch that forks off *below* `obs.root` (a sibling of `obs`'s
chain) survives `filter_block_tree` whenever its leaf's `get_voting_source` is recent enough
— `correct_justified` asks only `voting_source.epoch + 2 ≥ current_epoch` (or `= jc.epoch`),
which a pre-fork justified source at epoch `obs.epoch − 1` satisfies. So a heavier sibling
branch can carry the `get_head` argmax away from `obs.root`; nothing in the filter forbids
it. The head could be forced above `obs` only by **weight**. `obs` being justified means ≥ 2/3
of its epoch's committee attested to it (`JustificationInterface.justified_requires_targets`),
and converting that 2/3 into an `is_ancestor (head) obs` fact would be the head-safety weight
engine (`Descent` / `QuorumAccounting` / `Endpoint.ghost_step_dominates`) re-run for a
*justified* checkpoint. **That conversion does not go through here.** The adversary may sit
entirely inside the quorum, so the honest quorum share is `2/3 − β`, not `2/3`, and the
per-fork ledger needs `1/3 + β + pb < 2/3 − β`, i.e. `β < 1/6 − pb/2 ≈ 0.1604`. At this
development's design point `β = 1/4` it reads `5/12` against `7/12` — the sibling wins, and
the same threshold is the hypothesis of the paper's own Lemma 4
(`Paper/LMDGhost/Proof/Quorum.lean:88-92`). An earlier draft of this header claimed the
opposite ("2/3 exceeds the confirmation bar"); that claim was false at
`CONFIRMATION_BYZANTINE_THRESHOLD = 25`. The live weight-engine name is
`MajorityPersists.fork_majority`.

The right conclusion is not to assume the ahead regime away but to **avoid it**. That is what
the audited route does. On the accepted/actual route
`AcceptedObservedRestartDynamicSafety.safeFrom_of_acceptedDynamics` proves
`obs.epoch ≤ jc(w, n+1).epoch` at **every** honest `w`, from
`ActualFCRGuardedObservedAdoption` (boundary adoption of the observed checkpoint) plus
`store_justified_epoch_mono`. Under that inequality the ahead regime **never arises**: the
observed anchor's `SafeFrom` is discharged by `E5Filter.head_ge_of_justified_ge_K` alone, on
the at-or-below branch. No head-tracking proposition of any kind is projected there.

So the ahead-regime proposition that used to live here — the LMD-GHOST "justification
friendliness" claim that an honest head descends every `JustifiedIn` checkpoint above the
store's realized justified epoch — is **deleted**, together with the whole legacy
`SpecAssumptions` observed-anchor cone that carried it (38 declarations across 16 files; 14 of
them unconsumed roots, none reached by any of the 21 `scripts/Audit.lean` witnesses). It was
the `JustificationInterface.justified_descends` field until `fe724fd`, then an explicitly
threaded premise; it is now nothing. See `docs/p6-justified-descends-derivation.md` §8 and
`docs/plumbing-spec-citations.md` P-6.

**Note on the runtime re-check.** Earlier prose in this repository said the accepted route
discharges head-tracking via `get_latest_confirmed`'s runtime equation
`current_epoch_observed_justified_checkpoint = store.unrealized_justifications head`. That is
**wrong** for the accepted route: there the guard is projected and then deliberately ignored
(`AcceptedObservedRestartAdoption`'s `ActualFCRGuardedObservedAdoption` takes
`ObservedRestartCompatible` as an argument its proof states is "intentionally unused", because
the branch-indexed `ObservedResetCandidateInputAt` premise is stronger). The re-check *is*
load-bearing on the **weak** route, where `Weak.ObservedResetCandidateInputAt`'s
`observed_eq_head_unrealized` conjunct is what
`Weak.ObservedResetCandidateInputAt.bankedAU` / `.certifiedJustified` read the banked value's
accepted certificate off.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the ahead regime places `obs` above `jc` on the chain -/

/-- **The observed anchor descends from the realized justified root (ahead regime).** When
`jc.epoch < obs.epoch`, `justified_ancestry` (with `c := jc`, `c' := obs`, the ordered pair
`jc.epoch ≤ obs.epoch`) gives `is_ancestor (store w m) obs.root jc.root` — `obs.root`
descends from `jc.root`. Both are `JustifiedIn (store w m)` (`jc` by `Or.inl rfl`, `obs` by
`fcrStep_observed_justifiedIn`); `jc.root` is known (`checkpoint_known`), `obs.root` by the
`observed_known` hypothesis. This is the structural placement the weight argument then rides:
`obs.root` lies strictly between `jc.root` (the filter base) and any leaf on its branch. -/
theorem obs_descends_justified (hji : JustificationInterface cfg ext E)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint))
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m)
    (hknown : (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hahead : (E.store cfg ext w m).justified_checkpoint.epoch <
      (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true :=
  hji.justified_ancestry w hw m (E.store cfg ext w m).justified_checkpoint
    ((E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint)
    hH (Or.inl rfl)
    (E.fcrStep_observed_justifiedIn cfg ext hji hprev v hv n w hw m hm hH)
    (le_of_lt hahead) (hji.checkpoint_known w hw m hH).1 hknown

/-! ## Section 2 — deleted: the ahead-regime head-tracking premise and its two reductions

The ahead-regime LMD head-tracking proposition, together with
`observed_head_ahead_of_headTracks` and `observedFilterResiduals_of_headTracks`, stood here.

They are deleted with the rest of the legacy `SpecAssumptions` observed-anchor cone. Nothing
produced it: it was `JustificationInterface.justified_descends` until that
field was removed as not-an-FFG-export and not-derivable-at-`β = 1/4` (P-6, `fe724fd`), and
thereafter an explicit premise threaded through 35 further conditional declarations, every one
of which was an unconsumed root or fed one. No audited public witness reached any of it.

The audited route does not need it. `AcceptedObservedRestartDynamicSafety` proves
`obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, so the observed anchor is never in the
ahead regime and `E5Filter.head_ge_of_justified_ge_K` closes its `SafeFrom` on the
at-or-below branch alone (module header). See `docs/p6-justified-descends-derivation.md` §8. -/

/-! ## Section 3 — realized-checkpoint knownness -/

/-- **`observed_known` for the realized-checkpoint disjuncts.** A `JustifiedIn (store w m)`
checkpoint whose value is the store's own *realized* justified or finalized checkpoint has a
known root (`checkpoint_known`). The remaining `JustifiedIn` disjuncts — the
`unrealized_justified_checkpoint` / `unrealized_finalized_checkpoint` fields and the
`∃ r ∈ block_roots, unrealized_justifications r = c` case — carry no root-knownness export;
those cases require the general `observed_known` premise (the observed anchor is typically an
*unrealized* checkpoint precisely in the ahead regime). A sufficient interface is a knownness export
for the observed/unrealized checkpoint family — the observed-checkpoint analog of
`checkpoint_known` — or the block-relay-of-attested-target bridge
(`justified_requires_targets`' targets are honestly-seen blocks that relay everywhere). -/
theorem justifiedIn_root_known_of_realized (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (c : Checkpoint Root)
    (hH : E.WithinHorizon cfg m)
    (hrealized : c = (E.store cfg ext w m).justified_checkpoint ∨
      c = (E.store cfg ext w m).finalized_checkpoint) :
    c.root ∈ (E.store cfg ext w m).block_roots := by
  rcases hrealized with h | h <;> rw [h]
  · exact (hji.checkpoint_known w hw m hH).1
  · exact (hji.checkpoint_known w hw m hH).2

end Execution

end FastConfirmation.Spec

end
