import FastConfirmation.Spec.Proof.E5Filter

/-!
# Spec / Proof / AheadFacade: the ahead-regime observed-anchor interface

This module analyzes the ahead-regime head-domination premise
`ObservedFilterResiduals.observed_head_ahead`. It reduces
`ObservedFilterResiduals` to the named `HeadTracksJustified` premise together with the
knownness and boundary-source premises used by the public interface.

## The regime

At an honest store `(w, m)` the fork-choice head is computed on `get_filtered_block_tree`,
which is **rooted at the store's realized justified checkpoint** `jc := jc(w, m)`: every
filtered root descends from `jc.root`, and `head ⪰ jc.root` always
(`E5Filter.filtered_through_justified_K` / `get_head_root_mem_or`). The observed anchor
`obs := (fcrStep v n).current_epoch_observed_justified_checkpoint` is `JustifiedIn (store w m)`
everywhere (`ObservedDom.fcrStep_observed_justifiedIn`). The residual splits on `obs.epoch`
vs `jc.epoch`:

* **`obs.epoch ≤ jc.epoch`** — closed (`E5Filter.head_ge_of_justifiedIn_le`): `justified_ancestry`
  puts `obs` on `jc`'s chain (`jc ⪰ obs`), and `head_ge_of_justified_ge` lifts `head ⪰ obs`
  through the filter alone — no weight margin.
* **`jc.epoch < obs.epoch`** (the *ahead* regime, `observed_head_ahead`) — the subject here.

## Results

1. `obs_descends_justified` — in the ahead regime `obs.root` **descends from** `jc.root`
   (`justified_ancestry` with the roles swapped: the higher-epoch justified checkpoint is
   below on the chain). So `obs.root` sits strictly between `jc.root` and any filtered leaf
   on `obs`'s branch.

2. `HeadTracksJustified` — the head-tracking interface: at an honest store
   the fork-choice head descends from every `JustifiedIn` checkpoint whose root is known and
   whose epoch exceeds the store's realized justified epoch. This is LMD-GHOST *justification
   friendliness* — an honest head tracks the highest justified checkpoint.

3. `observed_head_ahead_of_headTracks` / `observedFilterResiduals_of_headTracks` — the head
   residual, and the whole `ObservedFilterResiduals`, reduced to `HeadTracksJustified` +
   `prev_greatest_justifiedIn` (boundary-source justification) +
   `observed_known` (knownness).

4. `justifiedIn_root_known_of_realized` — the realized-checkpoint cases of
   `observed_known`: when the
   observed anchor coincides with the store's *realized* justified or finalized checkpoint
   its root is known (`checkpoint_known`); the unrealized/`unrealized_justifications`
   disjuncts of `JustifiedIn` require the general knownness premise.

## Why the ahead regime needs an explicit interface

`observed_head_ahead` is **not** derivable from filter mechanics + `JustifiedIn`. The filter
is rooted at `jc.root`, and a branch that forks off *below* `obs.root` (a sibling of `obs`'s
chain) survives `filter_block_tree` whenever its leaf's `get_voting_source` is recent enough
— `correct_justified` asks only `voting_source.epoch + 2 ≥ current_epoch` (or `= jc.epoch`),
which a pre-fork justified source at epoch `obs.epoch − 1` satisfies. So a heavier sibling
branch can carry the `get_head` argmax away from `obs.root`; nothing in the filter forbids
it. The head is forced above `obs` only by **weight**: `obs` being justified means ≥ 2/3 of
its epoch's committee attested to it (`JustificationInterface.justified_requires_targets`),
so `obs`'s subtree dominates every sibling and the argmax descends through it. Converting
that 2/3 into an `is_ancestor (head) obs` fact is exactly the head-safety weight engine
(`Descent` / `QuorumAccounting` / `get_head_descends`) re-run for a *justified* checkpoint —
which is not available in this package and is not filter-mechanical.

The public interface exports `HeadTracksJustified` as a
`JustificationInterface`-family field — "the honest fork-choice head descends from every
known-root `JustifiedIn` checkpoint above the store's realized justified epoch". It is the
FFG-friendliness of LMD-GHOST (the fork-choice counterpart of `justified_requires_targets`,
whose 2/3-target content it consumes); same high-probability family as `observed_justified`.
It can alternatively be derived by applying the head-safety weight argument to justified
checkpoints: the 2/3 bound feeds the same `fork_majority_of_windows` descent used by the
confirmation engine, with no boost/discount arms because 2/3 exceeds the confirmation bar.

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
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint))
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m)
    (hknown : (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hahead : (E.store cfg ext w m).justified_checkpoint.epoch <
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true :=
  hji.justified_ancestry w hw m (E.store cfg ext w m).justified_checkpoint
    ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
    hH (Or.inl rfl)
    (E.fcrStep_observed_justifiedIn cfg ext hji hprev v hv n w hw m hm hH)
    (le_of_lt hahead) (hji.checkpoint_known w hw m).1 hknown

/-! ## Section 2 — the head-tracking interface and residual reduction -/

/-- **LMD-GHOST justification friendliness.** At an honest store,
the fork-choice head descends from every `JustifiedIn` checkpoint `c` whose root is known and
whose epoch is above the store's *realized* justified epoch. This is precisely the ahead
regime `observed_head_ahead` generalizes over `obs`; it is **not** filter-mechanical (see the
module header) — its honest content is the 2/3-attestation weight of a justified checkpoint
(`justified_requires_targets`) dominating every sibling in `get_head`'s argmax descent. The
`obs.epoch ≤ jc.epoch` complement is already closed (`E5Filter.head_ge_of_justifiedIn_le`);
this predicate states the ahead-regime premise. -/
def HeadTracksJustified (E : Execution Root) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, ∀ c : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c →
    c.root ∈ (E.store cfg ext w m).block_roots →
    (E.store cfg ext w m).justified_checkpoint.epoch < c.epoch →
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true

/-- **`observed_head_ahead` from `HeadTracksJustified`.** Instantiates the friendliness fact
at `c := obs`: `obs` is `JustifiedIn (store w m)`
(`fcrStep_observed_justifiedIn`, consuming `hprev`), its root is known
(`hknown` = `observed_known`), and `jc.epoch < obs.epoch`
is the ahead hypothesis. This is the exact `ObservedFilterResiduals.observed_head_ahead`
field statement. -/
theorem observed_head_ahead_of_headTracks (hji : JustificationInterface cfg ext E)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint))
    (hknown : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots)
    (htracks : E.HeadTracksJustified cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m)
    (hahead : (E.store cfg ext w m).justified_checkpoint.epoch <
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true :=
  htracks w hw m ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
    hH (E.fcrStep_observed_justifiedIn cfg ext hji hprev v hv n w hw m hm hH)
    (hknown v hv n w hw m hm hH) hahead

/-- **The whole `ObservedFilterResiduals` from `HeadTracksJustified` + the two carries.**
The observed-anchor filter bundle reduces exactly to: `HeadTracksJustified` (the ahead-regime
weight fact, the interface candidate), `prev_greatest_justifiedIn` (the boundary
greatest-unrealized propagation), and `observed_known` (the observed-anchor root knownness).
The ahead field is `observed_head_ahead_of_headTracks`; the other two pass through. -/
theorem observedFilterResiduals_of_headTracks (hji : JustificationInterface cfg ext E)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint))
    (hknown : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots)
    (htracks : E.HeadTracksJustified cfg ext) :
    E.ObservedFilterResiduals cfg ext where
  prev_greatest_justifiedIn := hprev
  observed_known := hknown
  observed_head_ahead := fun v hv n w hw m hm hH hahead =>
    E.observed_head_ahead_of_headTracks cfg ext hji hprev hknown htracks
      v hv n w hw m hm hH hahead

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
  · exact (hji.checkpoint_known w hw m).1
  · exact (hji.checkpoint_known w hw m).2

end Execution

end FastConfirmation.Spec
