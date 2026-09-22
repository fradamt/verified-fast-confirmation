module
public import FastConfirmation.Spec.Proof.AheadFacade
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.HeadStack

@[expose] public section

/-!
# Spec / Proof / ExportWiring: justification-interface wiring

This module uses `observed_checkpoint_known` and `justified_block_boundary` from
`JustificationInterface` to discharge the observed-anchor constituents of the internal safety
inputs.

## What is delivered

1. `boundarySource_known` — the root of the epoch-boundary rotation source `src` is a known
   block at every honest store from `n + 1` on, from `observed_checkpoint_known`'s first two
   conjuncts. What that does *not* give is the *justification* of `src` in `w`'s view — a
   cross-store semantic fact of the unrealized / greatest-unrealized checkpoint family, NOT
   delivered by the knownness-only `observed_checkpoint_known`.

   `observedKnown_of_interface` and `observedFilterResiduals_of_interface` stood beside it:
   the first closed the observed anchor's own root knownness across the three `fcrStep`-observed
   cases, the second bundled that with the ahead-regime head-tracking premise into an
   `E5Filter`'s observed-anchor residual bundle. All of it is deleted with the legacy
   `SpecAssumptions`
   observed-anchor cone (P-6) — see the Section 1 and Section 3 notes below.

2. `hbound_of_justified_block_boundary` + `vote_lands_export_closed` /
   `vote_ubiquity_export_closed` — `HeadStack`'s vote-landing bundle had one residual, the
   checkpoint-boundary bound `hbound`. `justified_block_boundary` **is** that bound, given the
   honest voter witness (built from `hvote`, `a.data.target = t` by `rfl`) and the epoch ordering
   `jc.epoch ≤ target.epoch`. So the vote-landing residual shrinks from the slot bound `hbound`
   to the epoch-ordering `hjc_le`.

The module retains as inputs the migration Finset algebra `hSmono`/`hXmono`/`hsat`
(`Sclass` set algebra over the vote-landing bundle) and the L4 `hcase`
cross-store descent (which needs transport of the confirming-store
`find_latest_confirmed_descendant_mem` to the arbitrary `DynamicsChainStruct` endpoint).

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — deleted: the ahead-regime head-tracking wiring

Two declarations stood here in turn. `headTracksJustified_of_interface` projected the
`JustificationInterface.justified_descends` field; the field was deleted in `fe724fd` (P-6) as
an LMD-GHOST weight claim wrongly presented as an FFG export, and the projection with it. The
fact then lived on as the explicit premise `AheadFacade`'s ahead-regime head-tracking premise, threaded through
`observedFilterResiduals_of_interface` (deleted in Section 3's place below) into the legacy
`SpecAssumptions` observed-anchor cone.

That whole cone is now retired. Nothing ever produced the premise, and the audited route does
not need it: `AcceptedObservedRestartDynamicSafety` proves `obs.epoch ≤ jc(w, n+1).epoch` at
every honest `w`, so the observed anchor is never in the ahead regime and
`E5Filter.head_ge_of_justified_ge_K` suffices. See
`docs/p6-justified-descends-derivation.md` §8 and `docs/plumbing-spec-citations.md` P-6. -/

/-! ## Section 2 — `observed_known` from `observed_checkpoint_known` -/

/-! ### Deleted: `observedKnown_of_interface`

The `observed_known` field of the observed-anchor filter bundle, closed from
`observed_checkpoint_known`. Its only consumer was `observedFilterResiduals_of_interface`
(deleted with the cone). `boundarySource_known` below still delivers the same two knownness
conjuncts for the boundary rotation source.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-! ## Section 3 — deleted: `observedFilterResiduals_of_interface`

This bundled `observedKnown_of_interface` with the carried `htracks` premise and the
boundary-source `prev_greatest_justifiedIn` into `E5Filter`'s observed-anchor residual
bundle. It is
deleted with the rest of the legacy `SpecAssumptions` observed-anchor cone (Section 1's note):
the ahead-regime premise it threaded had no producer, and the accepted route closes the
observed anchor without ever entering the ahead regime. -/

/-! ## Section 4 — boundary-source knownness and justification

`MicroSteps.prev_greatest_justifiedIn_of_boundarySource` reduces the boundary-source
`prev_greatest_justifiedIn` residual to `JustifiedIn (store w m) src`, where `src` is the
epoch-boundary rotation source

    src = if is_start_slot_at_epoch (cur+1) then (store v (n+1)).unrealized_justified_checkpoint
          else (fcr v n).previous_epoch_greatest_unrealized_checkpoint.

`boundarySource_known` delivers the *knownness* half of that input (`src.root ∈ block_roots`)
from `observed_checkpoint_known`. Root knownness alone
does not establish the *justification* of `src` in `w`'s view: `JustifiedIn` needs
`src` to be one of `(store w m)`'s own checkpoint fields or an `unrealized_justifications` entry
of a known block, whereas `observed_checkpoint_known` exports only root-knownness. The
remaining premise is semantic: the unrealized / greatest-unrealized checkpoint is
justified everywhere later. This is the unrealized analogue of
`observed_justified`, which applies to the realized current-epoch observed checkpoint. -/

/-- **Knownness of the boundary rotation source.** The root of `src` (the
`fcrStep_observed_boundary` if-then-else) is a known block at every honest store from `n + 1`
on — the first two `observed_checkpoint_known` conjuncts. This supplies the knownness
half of the reduced premise; the justification half is stated separately above. -/
theorem boundarySource_known (hji : JustificationInterface cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hH : E.WithinHorizon cfg m) :
    (if is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else (E.fcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint).root ∈
      (E.store cfg ext w m).block_roots := by
  split_ifs with hnext
  · exact (hji.observed_checkpoint_known v hv (n + 1) w hw m
      (E.withinHorizon_mono cfg hm hH) hH (E.slot_at_mono cfg hm)).1
  · exact (hji.observed_checkpoint_known v hv n w hw m
      (E.withinHorizon_mono cfg (Nat.le_trans (Nat.le_succ n) hm) hH) hH
      (E.slot_at_mono cfg (Nat.le_trans (Nat.le_succ n) hm))).2.1

/-! ## Section 5 — `hbound` from `justified_block_boundary`: the vote-landing bundle,
    reduced to the epoch-ordering fact

`HeadStack.vote_lands_closed` / `vote_ubiquity_closed` leave the checkpoint-boundary bound
`hbound` (the justified block slot ≤ the honest target epoch's start slot) as their sole
residual. `JustificationInterface.justified_block_boundary` **is** that bound, given a voter
witness for the target and the epoch ordering `jc.epoch ≤ target.epoch`. An honest vote at
`(v, n)` is its own witness (`hvote`, with `a.data.target = target` by `rfl`), so the residual
reduces to the epoch-ordering `hjc_le` — "an honest target never trails the store's justified
epoch" (the current-epoch ≥ justified-epoch invariant the honest target derives from its own
head state; strictly smaller than the raw slot bound). -/

/-- **The boundary bound `hbound` from `justified_block_boundary`.** At `(v, n)` with the honest
target `t := (honest_attestation …).data.target`, the export applied at `w := v`, `m := n`,
`t` — with the voter witness built from `hvote` (`a.data.target = t` is `rfl`) and the epoch
ordering `hjc_le` — yields exactly the `hbound` shape
`(blocks jc.root).slot ≤ compute_start_slot_at_epoch t.epoch`. -/
theorem hbound_of_justified_block_boundary (hji : JustificationInterface cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot} {n : ℕ} {index : CommitteeIndex}
    (hHn : E.WithinHorizon cfg n) (hHs : E.SlotWithinHorizon cfg s)
    (hvote : E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hjc_le : (E.store cfg ext v n).justified_checkpoint.epoch ≤
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch) :
    ((E.store cfg ext v n).blocks (E.store cfg ext v n).justified_checkpoint.root).slot ≤
      compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch :=
  hji.justified_block_boundary v hv n
    (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target
    hHn ⟨v, hv, s, n, honest_attestation cfg ext (E.store cfg ext v n) s index v,
      hHs, hHn, hvote, rfl⟩
    hjc_le

/-- **`vote_lands`, export-closed** (`ExportWiring`). `HeadStack.vote_lands_closed` with its last
residual `hbound` discharged by `hbound_of_justified_block_boundary`: the honest vote of `v` at
slot `s` (`hn : slot_at n = s`) is recorded at every honest node by second `slot_start (s+1)`,
with the checkpoint-boundary bound now sourced from the `justified_block_boundary` export. The
only carried hypothesis is the epoch ordering `hjc_le`. -/
theorem vote_lands_export_closed
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : Synchrony cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHdeliver : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hjc_le : (E.store cfg ext v n).justified_checkpoint.epoch ≤
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch) :
    ∃ msg, (E.store cfg ext w (E.slot_start cfg (s + 1))).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        msg.epoch :=
  vote_lands_closed cfg ext hwf hhb hsyn hec hji hdiv hgen hv hw hn hHn hHdeliver hvote
    (E.hbound_of_justified_block_boundary cfg ext hji hv hHn
      (E.slotWithinHorizon_of_le cfg (by rw [hn]) hHn) hvote hjc_le)

/-- **`vote_ubiquity`, export-closed** (`ExportWiring`). As `vote_lands_export_closed`, for the
persistence form (`HeadStack.vote_ubiquity_closed`): the recorded message is present at every
honest node from `slot_start (s+1)` on. This is the exact call site the migration cruxes
`hSmono` / `hXmono` / `hsat` route their late voters through; `hbound` is now interface-sourced,
leaving only the epoch ordering `hjc_le`. -/
theorem vote_ubiquity_export_closed
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : Synchrony cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hjc_le : (E.store cfg ext v n).justified_checkpoint.epoch ≤
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
    {m : ℕ} (hm : E.slot_start cfg (s + 1) ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        msg.epoch :=
  vote_ubiquity_closed cfg ext hwf hhb hsyn hec hji hdiv hgen hv hw hn hHn hvote
    (E.hbound_of_justified_block_boundary cfg ext hji hv hHn
      (E.slotWithinHorizon_of_le cfg (by rw [hn]) hHn) hvote hjc_le) hm hHm

end Execution

end FastConfirmation.Spec

end
