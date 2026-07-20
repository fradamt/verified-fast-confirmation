import FastConfirmation.Spec.Proof.AheadFacade
import FastConfirmation.Spec.Proof.MicroSteps
import FastConfirmation.Spec.Proof.HeadStack

/-!
# Spec / Proof / ExportWiring: justification-interface wiring

This module uses `observed_checkpoint_known`, `justified_descends`, and
`justified_block_boundary` from `JustificationInterface` to discharge the
observed-anchor constituents of the internal safety inputs.

## What is delivered

1. `headTracksJustified_of_interface` — the `head_tracks_justified` field
   (`AheadFacade.HeadTracksJustified`) **is** the `justified_descends` export verbatim (the
   two statements are binder-identical). So the one "missing fork-choice fact" of the ahead
   regime is exactly the interface export; no weight engine port is needed at this layer.

2. `observedKnown_of_interface` — the `observed_known` field is closed from
   `observed_checkpoint_known` across all three `fcrStep`-observed cases (off-boundary via
   `fcrStep_observed_else`; on-boundary via `fcrStep_observed_boundary`, whose two rotation
   sources are the interface's first two knownness conjuncts). The synchrony hypothesis
   `slot_at n ≤ slot_at m` comes from `n + 1 ≤ m` by `slot_at_mono`.

3. `observedFilterResiduals_of_interface` — bundles 1 + 2 into
   `E5Filter.ObservedFilterResiduals` with only the boundary-source
   `prev_greatest_justifiedIn` premise carried
   as a hypothesis (item 4 below reduces it further).

4. `boundarySource_known`: `MicroSteps.prev_greatest_justifiedIn_of_boundarySource`
   reduces the boundary-source premise to `JustifiedIn (store w m) src` for the
   boundary rotation source `src`. Its root
   is known (`observed_checkpoint_known`, the same two conjuncts as item 2 — delivered here), so
   what remains is the *justification* of `src` in `w`'s view — a cross-store semantic fact of the
   unrealized / greatest-unrealized checkpoint family, NOT delivered by the knownness-only
   `observed_checkpoint_known`.

5. `hbound_of_justified_block_boundary` + `vote_lands_export_closed` /
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

/-! ## Section 1 — `head_tracks_justified` is the `justified_descends` export -/

/-- **`HeadTracksJustified` from `justified_descends`.** The ahead-regime "one missing
fork-choice fact" (`AheadFacade.HeadTracksJustified`: the honest head descends from every
known-root `JustifiedIn` checkpoint above the store's realized justified epoch) is *exactly*
the justification-interface export `JustificationInterface.justified_descends` — the two `Prop`s are
binder-identical (honest `w`, second `m`, checkpoint `c`; same `JustifiedIn`, knownness, and
strict-epoch premises; same `is_ancestor (get_head …) c.root` conclusion). So the residual
closes by projection, with no head-safety weight-engine port. -/
theorem headTracksJustified_of_interface (hji : JustificationInterface cfg ext E) :
    E.HeadTracksJustified cfg ext :=
  hji.justified_descends

/-! ## Section 2 — `observed_known` from `observed_checkpoint_known` -/

/-- **`observed_known` from `observed_checkpoint_known`.** The `fcrStep`-observed checkpoint's
root is a known block at every honest store from `n + 1` on. Case split on the epoch boundary
of `store v (n+1)`:

* **off boundary** — `fcrStep_observed_else`: the value is `(fcr v n)`'s observed checkpoint;
  its root is the third `observed_checkpoint_known` conjunct at `(v, n)`.
* **on boundary** — `fcrStep_observed_boundary`: the value is the rotation source, either the
  store's `unrealized_justified_checkpoint` (first conjunct at `(v, n+1)`) or the carried
  `previous_epoch_greatest_unrealized_checkpoint` (second conjunct at `(v, n)`).

The synchrony premise `slot_at _ ≤ slot_at m` follows from `n + 1 ≤ m` by `slot_at_mono`. -/
theorem observedKnown_of_interface (hji : JustificationInterface cfg ext E) :
    ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := by
  intro v hv n w hw m hm hH
  have hHn1 : E.WithinHorizon cfg (n + 1) := E.withinHorizon_mono cfg hm hH
  have hnm : n ≤ m := Nat.le_trans (Nat.le_succ n) hm
  have hHn : E.WithinHorizon cfg n := E.withinHorizon_mono cfg hnm hH
  by_cases hstart :
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true
  · rw [E.fcrStep_observed_boundary cfg ext v n hstart]
    split_ifs with hnext
    · exact (hji.observed_checkpoint_known v hv (n + 1) w hw m
        hHn1 hH (E.slot_at_mono cfg hm)).1
    · exact (hji.observed_checkpoint_known v hv n w hw m
        hHn hH (E.slot_at_mono cfg hnm)).2.1
  · rw [Bool.not_eq_true] at hstart
    rw [E.fcrStep_observed_else cfg ext v n hstart]
    exact (hji.observed_checkpoint_known v hv n w hw m
      hHn hH (E.slot_at_mono cfg hnm)).2.2

/-! ## Section 3 — the observed-anchor filter bundle, two of three fields interface-closed -/

/-- **`ObservedFilterResiduals` with only boundary-source justification carried.** Feeding `observedKnown_of_interface`
(the `observed_known` field) and `headTracksJustified_of_interface` (the `observed_head_ahead`
field, via `AheadFacade.observed_head_ahead_of_headTracks`) into
`AheadFacade.observedFilterResiduals_of_headTracks` leaves the sole boundary-source hypothesis
`prev_greatest_justifiedIn` (the on-boundary/no-advance corner) as the only input. Two of the
three observed-anchor fields are thus discharged directly from `JustificationInterface`. -/
theorem observedFilterResiduals_of_interface (hji : JustificationInterface cfg ext E)
    (hprev : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
      ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)) →
      JustifiedIn (E.store cfg ext w m)
        ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)) :
    E.ObservedFilterResiduals cfg ext :=
  E.observedFilterResiduals_of_headTracks cfg ext hji hprev
    (E.observedKnown_of_interface cfg ext hji)
    (E.headTracksJustified_of_interface cfg ext hji)

/-! ## Section 4 — boundary-source knownness and justification

`MicroSteps.prev_greatest_justifiedIn_of_boundarySource` reduces the boundary-source
`prev_greatest_justifiedIn` residual to `JustifiedIn (store w m) src`, where `src` is the
epoch-boundary rotation source

    src = if is_start_slot_at_epoch (cur+1) then (store v (n+1)).unrealized_justified_checkpoint
          else (fcr v n).previous_epoch_greatest_unrealized_checkpoint.

`boundarySource_known` delivers the *knownness* half of that input (`src.root ∈ block_roots`)
from `observed_checkpoint_known` — the same two conjuncts item 2 uses. Root knownness alone
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
