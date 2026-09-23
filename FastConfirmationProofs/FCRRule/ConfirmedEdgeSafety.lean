module
public import FastConfirmationProofs.FFG.SourceHistory.MarginInvariant
public import FastConfirmationProofs.Checkpoints.EdgeWeightAlgebra
public import FastConfirmationProofs.Execution.Delivery.VoteDeliveryMargin
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.ForkChoice.Head.AheadHeadDominance
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.Execution.StoreInvariants.CheckpointDomain
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Discount.SupportDiscount

@[expose] public section

/-!
# Spec / Proof / Closing

Proves safety of each newly selected FCR descendant edge.

This module contains `EngineAdvanceCore` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the four localized irreducible cores -/

/-- **The localized engine cores** — the transparent residual bundle obtained by opening the
`hbk` and `hdisj` advance supplies. Four per-confirmed-block fields:

* `hbconf` — the confirmed block `b` is known at its own confirming store `(v, n+1)` (the `hck`
  store-knownness family);
* `hb_sameslot` — `b` is known at a foreign endpoint `(w, m)` inside the confirming slot,
  before `block_relay`'s next-slot gate applies;
* `hcov` — a per-endpoint covering justified checkpoint `jcb` (`b ⪰ jcb`) plus the strict-epoch
  advance sub-case `hadv_hi` (the disjunction's engine content; the `≤`-epoch side is closed inside
  `disjunction_of_covering` from `justified_ancestry`);
* `heng` — the chain-branch head-safety engine (`b ⪰ jc → head ⪰ b`, the `INVstar` core).

`advance_safe_of_core` rebuilds the advance leg from this: `hbk` via `hbk_of_confirming`
(`hbconf` + `hb_sameslot`, later slot by `block_relay`), `hdisj` via `hdisj_of_covering` (`hcov`),
`heng` verbatim. -/
structure EngineAdvanceCore (E : Execution Root) : Prop where
  /-- The confirmed block is known at its own confirming store `(v, n+1)` (the `hck` family). -/
  hbconf : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    E.WithinHorizon cfg (n + 1) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    b ∈ (E.store cfg ext v (n + 1)).block_roots
  /-- The confirmed block is known at a foreign endpoint `(w, m)` inside the confirming slot
      (the same-slot availability corner for `b`). -/
  hb_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
      b ∈ (E.store cfg ext w m).block_roots
  /-- A per-endpoint covering justified checkpoint `jcb` with `b ⪰ jcb`, plus the strict-epoch
      advance sub-case `hadv_hi` — the disjunction's localized engine content. -/
  hcov : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      ∃ jcb : Checkpoint Root,
        b ∈ (E.store cfg ext w m).block_roots ∧
        JustifiedIn (E.store cfg ext w m) jcb ∧
        jcb.root ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root jcb.root) = true ∧
        (jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
          is_ancestor (E.store cfg ext w m)
            (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
            (get_node_for_root b) = true)
  /-- The chain-branch head-safety engine (`b ⪰ jc → head ⪰ b`) — the `INVstar` core. -/
  heng : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true


/-! ## Section 2 — the advance leg from the localized cores -/



end Execution

/-! ## Section 3 — the safety headline -/



end FastConfirmation.Spec

end
