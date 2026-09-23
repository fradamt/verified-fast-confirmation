module
public import FastConfirmationProofs.ForkChoice.Filter.AnchorFilterViability

@[expose] public section

/-!
# Spec / Proof / AheadFacade

This module contains `obs_descends_justified`, `justifiedIn_root_known_of_realized` and related declarations.
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

end
