import FastConfirmation.Spec.Proof.Anchoring
import FastConfirmation.Spec.Proof.Dominance
import FastConfirmation.Spec.Proof.Closing
import FastConfirmation.Spec.Proof.EngineCore

/-!
# Spec / Proof / AnchorThread: `ConfirmedWithAnchor` and the covering composition

This module carries the
`Anchoring.ConfirmedWithAnchor` package into the advance-leg quantification and uses it to reduce
the `CoveringFFG` covering residual, then composes the per-edge dominance
(`Dominance.descendStep_of_confirmMargin`) into the transparent engine bundle.

## Anchoring the advance leg

The `L4Fold.L4Residual.advance_safe` leg is consumed **only** at the `get_latest_confirmed` output
(`safeFrom_get_latest_confirmed`): the `b` that reaches the engine is `E.confirmed v (n+1) =
get_latest_confirmed (fcrStep v n)` in the advance regime. That block is exactly the subject of
`Anchoring.get_latest_confirmed_ge`: it **descends from one of the three reset anchors**
`r₀ ∈ {confirmed_root, finalized.root, observed.root}` at its confirming store `(v, n+1)`. So the
advance leg can carry the confirming-store `ConfirmedWithAnchor` package for free — `b ⪰ r₀` is not
a free hypothesis, it is `get_latest_confirmed_ge`'s output. `confirmedWithAnchor_of_advance`
produces it from `SpecAssumptions` (the fork-choice domain via `AnchorFacade.store_domainK`) plus
the three reset-anchor knownness facts and the confirmed-block knownness (the `hbconf`/`hck`
family) as the precise residual hypotheses.

## The covering composition

`Anchoring.coveringFFG_of_anchor` assembles `Execution.CoveringFFG cfg ext b w m` at a foreign
endpoint `(w, m)` from `ConfirmedWithAnchor` (its `b ⪰ jcb.root` conjunct is the **transported
anchoring**, no longer a free covering hypothesis) plus the transport inputs (`hsub` block-root
containment, `hw` reverse walk) and the FFG/geometry exports (`jcb`'s `JustifiedIn`/knownness, the
head witness). `coveringFFG_of_advance` chains `confirmedWithAnchor_of_advance` into it, so the
covering input reduces to the **anchor-scoped** bundle: the three reset-anchor
knownness facts, the transport inputs, the per-`r₀`-kind `jcb`
exports, and the strict-branch head-witness geometry (the dominance / `hadv_hi` route).

## Explicit engine inputs

The head-witness geometry (`head ⪰ b`, `get_checkpoint_block head jc.epoch = jc.root`) and the
economic core are supplied per edge by `descendStep_of_confirmMargin` as a
`DescendStep`. This module reduces the covering input to the anchor-scoped form and exposes the
dominance composition point.

**P-6 note.** The glc-scoped fold this module used to carry — `safeFrom_get_latest_confirmed_glc`,
`L4ResidualGlc`, `confirmed_safeFrom_of_residualGlc`, `spec_safety_of_residualGlc` — and the four
closing theorems above it (`Spec_Safety_of_anchored` / `_of_selectedCore` and their
`Spec_Monotonicity_*` companions) are **deleted**. The fold's `observed_safe` field was an
observed-anchor `SafeFrom` that only the retired ahead-regime route produced; the closings
carried the never-produced ahead-regime head-tracking premise. Sections 1-2 —
`confirmedWithAnchor_of_advance`, `coveringFFG_of_advance`, `hdisj_of_coveringFFG` — are
unaffected. See the section notes below and `docs/p6-justified-descends-derivation.md` §8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the `ConfirmedWithAnchor` re-thread (item 1) -/

/-- **`ConfirmedWithAnchor` for the advance-regime confirmed block.** The block
`get_latest_confirmed (fcrStep v n)` — the confirmed root at a slot update `(v, n+1)` in the advance
regime — descends, at its confirming store, from one of the three reset anchors
`r₀ ∈ {confirmed_root, finalized.root, observed.root}` (both known). This is `Anchoring.
get_latest_confirmed_ge` at the confirming store `(fcrStep v n).store = store v (n+1)`
(`fcrStep_store`), with the fork-choice domain conditions discharged from `SpecAssumptions`
(`store_domainK` + `get_head_root_mem_or`) and the three reset-anchor knownness facts
(`h0`/`h1`/`h2`) plus the confirmed-block knownness (`hbk`, the `hbconf`/`hck` family) carried as
the precise residual hypotheses. The reset-anchor kind `r₀` is returned in the disjunction so the
caller can dispatch the per-`r₀`-kind `JustifiedIn` export in `coveringFFG_of_anchor`. -/
theorem confirmedWithAnchor_of_advance (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hH : E.WithinHorizon cfg (n + 1))
    (hbk : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (h0 : (E.fcrStep cfg ext v n).confirmed_root ∈ (E.store cfg ext v (n + 1)).block_roots)
    (h1 : (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (h2 : (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots) :
    ∃ r₀ : Root,
      (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
        r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
        r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) ∧
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hs : (E.fcrStep cfg ext v n).store = E.store cfg ext v (n + 1) :=
    E.fcrStep_store cfg ext v n
  obtain ⟨hwf, hwalk, hjust⟩ :=
    E.store_domainK cfg ext hwfE hec hgen hji v hv (n + 1) hH
  have hhead : (get_head cfg (E.store cfg ext v (n + 1))).root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (n + 1)) with h | h
    · exact h
    · rw [h]; exact hjust
  obtain ⟨r₀, hdisj, hr0mem, hanc⟩ :=
    get_latest_confirmed_ge cfg ext (E.fcrStep cfg ext v n)
      (by rw [hs]; exact hwf) (by rw [hs]; exact hwalk) (by rw [hs]; exact hhead)
      (by rw [hs]; exact h0) (by rw [hs]; exact h1) (by rw [hs]; exact h2)
  rw [hs] at hdisj hr0mem hanc
  exact ⟨r₀, hdisj, ⟨hbk, hr0mem, hanc⟩⟩

/-! ## Section 2 — the covering composition (item 2) -/

/-- **`CoveringFFG` for the advance-regime confirmed block, from the anchor.**
Chains `confirmedWithAnchor_of_advance` into `Anchoring.coveringFFG_of_anchor`: the confirming-store
`ConfirmedWithAnchor` package is produced from `SpecAssumptions` + the anchor-knownness residuals
(`hbk`/`h0`/`h1`/`h2`), and the **anchor-scoped covering supply** `hcov` — parameterized over the
returned reset anchor `r₀` and the `ConfirmedWithAnchor` package — provides the block-root
containment transport `hsub`, the reverse walk `hw`, the per-`r₀`-kind covering checkpoint `jcb`
(`JustifiedIn`/knownness, `jcb.root = r₀`), and the head-witness geometry. The `b ⪰ jcb.root`
conjunct of `Execution.CoveringFFG` is derived by transported
anchoring
(`coveringFFG_of_anchor`'s `is_ancestor_transport_rev` from `hsub`/`hw`). Thus the covering
input reduces to this anchor-scoped `hcov`: the
reset-anchor knownness, the transport inputs, the per-`r₀`-kind `JustifiedIn` exports, and the
strict-branch
head-witness geometry (the dominance / `hadv_hi` route). -/
theorem coveringFFG_of_advance (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hH : E.WithinHorizon cfg (n + 1))
    (hbk : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (h0 : (E.fcrStep cfg ext v n).confirmed_root ∈ (E.store cfg ext v (n + 1)).block_roots)
    (h1 : (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (h2 : (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (w : ValidatorIndex) (m : ℕ)
    (hcov : ∀ r₀ : Root,
      (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
        r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
        r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) →
      ((E.store cfg ext v (n + 1)).block_roots ⊆ (E.store cfg ext w m).block_roots) ∧
      WalkKnown (E.store cfg ext v (n + 1))
          ((E.store cfg ext v (n + 1)).blocks r₀).slot
          (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) ∧
      ∃ (jcb : Checkpoint Root) (head : Root),
        jcb.root = r₀ ∧
        JustifiedIn (E.store cfg ext w m) jcb ∧
        jcb.root ∈ (E.store cfg ext w m).block_roots ∧
        head ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m) (get_node_for_root head)
            (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true ∧
        get_checkpoint_block cfg (E.store cfg ext w m) head
            (E.store cfg ext w m).justified_checkpoint.epoch =
          (E.store cfg ext w m).justified_checkpoint.root ∧
        ((E.store cfg ext w m).blocks
            (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))).slot ≤
          compute_start_slot_at_epoch cfg (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.CoveringFFG cfg ext (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) w m := by
  obtain ⟨r₀, hkind, hanc⟩ :=
    E.confirmedWithAnchor_of_advance cfg ext hSA v hv n hH hbk h0 h1 h2
  obtain ⟨hsub, hw, jcb, head, hjcb_root, hjust, hjcb_known, hHk, hHb, hckpt, hbslot⟩ :=
    hcov r₀ hkind hanc
  exact E.coveringFFG_of_anchor cfg ext hSA.2.1 hanc hsub hw jcb hjcb_root hjust hjcb_known
    head hHk hHb hckpt hbslot

/-- **The `jc ⪰ b ∨ b ⪰ jc` disjunction from `CoveringFFG`.** At an
endpoint `(w, m)` with `b` known, an `Execution.CoveringFFG` bundle discharges the disjunction the
glc-scoped advance leg (`hdisj_glc`) needs: `Structural.disjunction_of_covering` closes the
`≤`-epoch side from `justified_ancestry`, and the strict side is the covering head witness routed
through `EngineCore.hadv_hi_of_head` (`head ⪰ b` with `get_checkpoint_block head jc.epoch = jc.root`
⟹ `jc ⪰ b`). Composed with `coveringFFG_of_advance`, this reduces `hdisj_glc` at the
`get_latest_confirmed` block to the **anchor-scoped covering supply** `hcov` — the `b ⪰ jcb.root`
conjunct being the transported anchoring; the remaining input is the head-witness
geometry inside `hcov` (the strict-branch `hadv_hi` route). -/
theorem hdisj_of_coveringFFG (hSA : SpecAssumptions cfg ext E)
    {b : Root} (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hbk : b ∈ (E.store cfg ext w m).block_roots)
    (hcffg : E.CoveringFFG cfg ext b w m) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root b) = true ∨
      is_ancestor (E.store cfg ext w m) (get_node_for_root b)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true := by
  obtain ⟨jcb, head, hjust, hjcb_known, hbge, hHk, hHb, hckpt, hbslot⟩ := hcffg
  exact E.disjunction_of_covering cfg ext hSA w hw m hH hbk hjust hjcb_known hbge
    (fun _ => E.hadv_hi_of_head cfg ext hSA w hw m hH hbk hHk hHb hckpt hbslot)

/-! ## Section 3 — the glc-scoped fold (item 3, the re-thread)

`L4Fold.L4Residual.advance_safe` quantifies over **every** `is_one_confirmed` block `b` at the
update store, but the trajectory fold consumes it **only** at the `get_latest_confirmed` output.
The anchoring (`get_latest_confirmed_ge`, hence `ConfirmedWithAnchor`) holds **only** for that
output — an arbitrary `is_one_confirmed` block need not descend from a reset anchor. So to benefit
from the anchoring, the advance leg must be re-scoped to the `get_latest_confirmed` block. This
section re-states the fold with the advance leg **`get_latest_confirmed`-scoped**
(`L4ResidualGlc.advance_safe_glc`), so its consumers carry the `ConfirmedWithAnchor` package. The
three E5 reset legs are unchanged. -/

/-! ### Deleted: the glc-scoped `L4Residual` fold

`safeFrom_get_latest_confirmed_glc`, `L4ResidualGlc`, `confirmed_safeFrom_of_residualGlc` and
`spec_safety_of_residualGlc` stood here. The fold's `observed_safe` field was an
observed-anchor `SafeFrom`, which only `AnchorFacade.safeFrom_observed_of_filter_K` produced,
and its only consumer was `Spec_Safety_of_anchored`.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

end Execution

/-! ## Sections 4 and 5 — deleted: the anchoring-scoped and selected-core closings

`Spec_Safety_of_anchored` / `Spec_Monotonicity_of_anchored` (the glc-scoped closing) and
`Spec_Safety_of_selectedCore` / `Spec_Monotonicity_of_selectedCore` (its selected-result bridge)
stood here. All four carried the unproduced ahead-regime head-tracking premise `htracks`. `Spec_Safety_of_anchored` built its
`observed_safe` leg
by running `AnchorFacade.safeFrom_observed_of_filter_K` on
`ExportWiring.observedFilterResiduals_of_interface`, and the other three inherited it.

They are deleted with the rest of the legacy `SpecAssumptions` observed-anchor cone (P-6).
Nothing ever produced that premise, and the audited route does not need it:
`AcceptedObservedRestartDynamicSafety` proves `obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`,
so the observed anchor never enters the ahead regime and `E5Filter.head_ge_of_justified_ge_K`
closes its `SafeFrom` alone. Sections 1-3 (`confirmedWithAnchor_of_advance`,
`coveringFFG_of_advance`, `hdisj_of_coveringFFG`, the `L4ResidualGlc` fold) are unaffected. See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
