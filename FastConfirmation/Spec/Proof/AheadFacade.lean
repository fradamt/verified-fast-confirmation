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
it. The head could be forced above `obs` only by **weight**. `obs` being justified means ≥ 2/3
of its epoch's committee attested to it (`JustificationInterface.justified_requires_targets`),
and converting that 2/3 into an `is_ancestor (head) obs` fact would be the head-safety weight
engine (`Descent` / `QuorumAccounting` / `Endpoint.ghost_step_dominates`) re-run for a
*justified* checkpoint. **That conversion does not go through here.** The adversary may sit
entirely inside the quorum, so the honest quorum share is `2/3 − β`, not `2/3`, and the
per-fork ledger needs `1/3 + β + pb < 2/3 − β`, i.e. `β < 1/6 − pb/2 ≈ 0.1604`. At this
development's design point `β = 1/4` it reads `5/12` against `7/12` — the sibling wins. An
earlier draft of this header claimed the opposite ("2/3 exceeds the confirmation bar"); that
claim was false at `CONFIRMATION_BYZANTINE_THRESHOLD = 25`.

`HeadTracksJustified` is therefore carried as an **explicit premise** by the routes that
consume it, not as a `JustificationInterface` field. It used to be the field
`JustificationInterface.justified_descends`, presented as an FFG export; that presentation was
wrong on two counts, and the field was deleted (P-6; see the `HeadTracksJustified` docstring
below and `docs/p6-justified-descends-derivation.md`):

* it is an LMD-GHOST *weight* fact, not a Casper-FFG export; and
* it does **not** follow from the 2/3-target export at this development's Byzantine design
  point. Running the 2/3 quorum through the spec's own per-fork ledger
  (`Endpoint.ghost_step_dominates`) needs `β < 1/6 − pb/2 ≈ 0.1604`, while
  `Config.confirmation_byzantine_threshold` is `≤ 25` structurally and `= 25` on mainnet. The
  live weight-engine name is `MajorityPersists.fork_majority` (an earlier draft of this header
  cited `fork_majority_of_windows`, which no longer exists) and it carries exactly that
  threshold, as does the paper's own Lemma 4 (`Paper/LMDGhost/Proof/Quorum.lean:88-92`).

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
    (le_of_lt hahead) (hji.checkpoint_known w hw m hH).1 hknown

/-! ## Section 2 — the head-tracking interface and residual reduction -/

/-- **LMD-GHOST justification friendliness — an explicitly-carried, unproven LMD premise.**
At an honest store, the fork-choice head descends from every `JustifiedIn` checkpoint `c`
whose root is known and whose epoch is above the store's *realized* justified epoch. This is
precisely the ahead regime `observed_head_ahead` generalizes over `obs`; it is **not**
filter-mechanical (see the module header) — its honest content is the 2/3-attestation weight
of a justified checkpoint (`justified_requires_targets`) dominating every sibling in
`get_head`'s argmax descent. The `obs.epoch ≤ jc.epoch` complement is already closed
(`E5Filter.head_ge_of_justifiedIn_le`); this predicate states the ahead-regime premise.

**Provenance and why it is a premise, not a theorem (P-6).** This statement was the
`JustificationInterface.justified_descends` field until that field was deleted
(14 → 13 fields). Two things were wrong with carrying it there.

*It is not an FFG export.* It is an LMD-GHOST weight claim; `JustificationInterface` is the
Casper-FFG export surface. The deleted field's docstring asserted "2/3 of an epoch's
attesters named it as target; honest ones' newest messages keep descending from it", which is
the conclusion, not a derivation.

*It is not derivable from the 2/3 quorum at this development's Byzantine floor.* Feed an FFG
quorum into the spec's own per-fork ledger `Endpoint.ghost_step_dominates` (`Endpoint.lean`),
charging the proposer boost adversarially as `MajorityPersists.fork_weight_lt` does. With
`Sval ≥ (2/3 − β)·W` honest quorum weight, `Xval ≤ 1/3·W` honest-but-sibling-stuck,
`Bval ≤ β·W`, and `pb = proposer_score_boost/100/32 = 40/100/32 = 0.0125`, the required
`Xval + Bval + proposer_score + 1 ≤ Sval` reads

    1/3 + β + pb < 2/3 − β    ⟺    β < 1/6 − pb/2 ≈ 0.1604.

But `Config.confirmation_byzantine_threshold` is `≤ 25` structurally (`Config.lean:35-39`)
and `= 25` on mainnet (`:66`). At `β = 1/4` the honest quorum share is `5/12` against `7/12`
— the sibling wins the argmax. Instantaneous LMD dominance from a 2/3 quorum therefore needs
`β < 1/6 − pb/2`, which is exactly the hypothesis of the paper's own Lemma 4
(`Paper/LMDGhost/Proof/Quorum.lean:88-92`, `Q > 1/2·(1 + Wp/W) + β`), so transplanting the
paper imports the bound rather than removing it. `Spec/Proof/Fraction.lean:31-41` records
that this development already hit, and retreated from, the same β mismatch once.

**Where it survives.** It does *not* survive on the accepted/actual route, which never needed
it: `get_latest_confirmed` re-checks `current_epoch_observed_justified_checkpoint =
store.unrealized_justifications head` at runtime (`Model/Confirmation.lean`), making the
ancestry chain-intrinsic, and `AcceptedObservedRestartDynamicSafety` proves the observed
anchor's `SafeFrom` from that guard with no head-tracking premise. It does not survive in
`AnchorClose` either: the covering fold that consumed it there was redundant, since the
observed anchor's own threaded `SafeFrom` witness already gives `head ⪰ r₀`.

What remains is the **legacy `SpecAssumptions` observed-anchor bundle**, where the fact has no
runtime guard to lean on because the strong rule rotates in a *store-global* running maximum
(`Model/Confirmation.lean`'s `update_fast_confirmation_variables`), not a read off the head's
own `unrealized_justifications`. The chain-intrinsic banking property that makes the weak
rule's version provable (`Weak.headUnrealizedJustification_known_and_below`) is a consequence
of the *weak* rule delta, and the corresponding claim for the strong rule's store-global value
is recorded in-tree as **false in general** — the branch-switch hole, `Model/WeakSynchrony.lean`
and `Proof/WeakBankedJustification.lean`'s headers. So on that one route the fact is **carried
explicitly** rather than asserted, in the style of `Nucleus.CurrentEpochCoveringBridge`.

No audited public witness reaches it: the forward proof-term closure of the 21
`scripts/Audit.lean` witnesses (19251 constants, 5353 of them from project modules) contained
neither the old field nor either of its two consumers. Full analysis:
`docs/p6-justified-descends-derivation.md` §7; audit row
`docs/plumbing-spec-citations.md` P-6. -/
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
  · exact (hji.checkpoint_known w hw m hH).1
  · exact (hji.checkpoint_known w hw m hH).2

end Execution

end FastConfirmation.Spec
