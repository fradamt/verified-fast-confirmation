import FastConfirmation.Spec.Proof.ShellInstantiation
import FastConfirmation.Spec.Proof.InterfaceRewire
import FastConfirmation.Spec.Proof.Engine
import FastConfirmation.Spec.Proof.EdgeDynamics
import FastConfirmation.Spec.Proof.EngineTransport
import FastConfirmation.Spec.Proof.DynamicsClosure

/-!
# Spec / Proof / IHMechanize: constructing IH-dependent inputs

`ShellInstantiation.ShellResiduals` contains two inputs per confirmed block: the
**structural** confirmed chain `dynamics_struct`
(`DynamicsChainStruct`) and the **per-edge** store-dynamics supply `fork_edges`
(`ForkAssembly.ForkEdgeSupply`, packaged from `EdgeDynamics.EdgeInputResidual`). The three
IH-dependent fields of `EdgeInputResidual` — the pre-`T1` class-migration deltas
`hdeltas`, the post-`T1` saturated majority `hmaj`, and the per-`Sclass`-member recorded
`c`-support `hrec` — are explicit engine premises that use the head-safety IH.
This module constructs these fields from smaller store-dynamics inputs.

## Constructions

* **Section 1 — `dynamics_struct`.** `dynamicsChainStruct_of_endpoint` constructs
  `ShellResiduals.dynamics_struct` from two flat per-endpoint
  facts under the shell IH — `hb` (the confirmed block is relay-known at the endpoint) and
  `hcase` (the L4 loop-inversion descent: `b` is on the justified chain or `= jc`) —
  deriving `ParentSlotLt` from `WFTrajectory`, the
  filtered-tree containment from `Engine.filter_block_tree_aux_output_mem`, justified
  knownness from `JustificationInterface`, and the `b`-walk domain from
  `AnchorFacade.store_walkKnownK`) from `SpecAssumptions`.

* **Section 2 — `hmaj` (post-`T1` saturation).** `hmaj_of_saturation_support` reduces the
  saturated honest-majority field to the clean "full saturation" store-dynamics crux —
  `Sclass = honest window` and `Xclass = ∅` at the endpoint (every honest span member has
  re-voted `desc(b')` by `T1`, `committee_coverage` + `votes_head` + IH) — plus the pure-ℕ
  boost-dilution arithmetic `C·J/(100−C) + boost + 1 ≤ J`. `Sval_eq_Jspec_of_saturation` /
  `Xval_eq_zero_of_saturation` carry the class-collapse; `boost_dilution` isolates the
  arithmetic as an explicit hypothesis on the endpoint span.

* **Section 3 — `hrec` (recorded support).** `hrec_of_domain` packages
  `EngineTransport.recorded_supports_c_of_IH` per `Sclass` member at the endpoint anchor
  `(w, m)` (`v₀ := w`, `n₀ := m`, so the cross-store transport is reflexive): the member's
  vote witness comes from its own `SupportsDesc`, the recorded `lm` and its epoch floor from
  `Delivery.vote_ubiquity`, and the `WalkKnown` domain from `AnchorFacade.store_walkKnownK`.
  The ubiquity landing and endpoint slot bound are explicit hypotheses.

* **Section 4 — `hdeltas` (class migration).** `hdeltas_of_monotone` constructs
  the pre-`T1` per-slot `∃ξα` step from same-epoch monotonicity premises.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — `dynamics_struct` from `hb` + `hcase`

`ResidualMechanicalII.dynamicsChainStruct_body` builds the `DynamicsChainStruct` existential
(`Nodup`/`IsChain`/`getLast` over `get_ancestor_roots store b jc`) from the parent-slot
order `hwf`, the filtered containment `hfilt`, `b`/`jc` knownness, the `b`-walk domain
`hwalk`, and the descent case split `hcase`. The other inputs are derived from
`SpecAssumptions`. -/

omit [Inhabited Root] in
/-- **The filtered block tree is contained in `block_roots`.** `get_filtered_block_tree`
wraps `filter_block_tree_aux` at base `justified_checkpoint.root`; every emitted root is a
known block or that base (`Engine.filter_block_tree_aux_output_mem`), and the base is known
(`hjc`). -/
theorem filtered_subset_block_roots (store : Store Root)
    (hjc : store.justified_checkpoint.root ∈ store.block_roots) :
    ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots := by
  intro r hr
  simp only [get_filtered_block_tree] at hr
  rcases filter_block_tree_aux_output_mem cfg (store.block_roots.length + 1)
    store.justified_checkpoint.root r hr with h | rfl
  · exact h
  · exact hjc

namespace Execution

variable (E : Execution Root)

/-- **`DynamicsChainStruct` from two per-endpoint inputs.** Under
`SpecAssumptions`, the structural confirmed-chain obligation follows from
`hb` (the confirmed `b` is relay-known at each honest endpoint under the shell IH) and
`hcase` (the L4 loop-inversion descent: `get_ancestor_roots store b jc ≠ []` or `b = jc`).
The other fields — `ParentSlotLt` (`store_parentSlotLt`), filtered containment
(`filtered_subset_block_roots`), justified knownness (`justified_known_of_interface`), and
the `b`-walk domain (`store_walkKnownK`, with `jc`/`b` both known) — follow from
`SpecAssumptions`. -/
theorem dynamicsChainStruct_of_endpoint (hSA : SpecAssumptions cfg ext E) {b : Root} {n₀ : ℕ}
    (hb : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true) →
      b ∈ (E.store cfg ext w m).block_roots)
    (hcase : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true) →
      get_ancestor_roots (E.store cfg ext w m) b
          (E.store cfg ext w m).justified_checkpoint.root ≠ [] ∨
        b = (E.store cfg ext w m).justified_checkpoint.root) :
    E.DynamicsChainStruct cfg ext b n₀ := by
  obtain ⟨hgen, hwf, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  intro w hw m hm hH hIH
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled w m
  have hjcw : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justified_known_of_interface cfg ext hji w hw m hH
  have hbmem := hb w hw m hm hH hIH
  have hwalk : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks (E.store cfg ext w m).justified_checkpoint.root).slot b :=
    E.store_walkKnownK cfg ext hwf hec hgen w m
      (E.store cfg ext w m).justified_checkpoint.root hjcw b hbmem
  exact dynamicsChainStruct_body cfg b hpsl
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjcw)
    hbmem hjcw hwalk (hcase w hw m hm hH hIH)

/-! ## Section 2 — `hmaj`: post-`T1` saturation and boost dilution

The saturated honest-majority field of `EdgeDynamics.EdgeInputResidual` is
`x(σ') + ⌊C·J(σ')/(100−C)⌋ + boost + 1 ≤ s(σ')` for `σ'` at least two epochs past `es`.
Past `T1` every honest span member has re-voted `desc(b')` (`committee_coverage` +
`votes_head` + IH), represented by `hsat`: `SupportsDesc` holds for every
honest window member. It collapses the honest partition to `Sclass = window`
(`Sval = Jspec`) and `Xclass = ∅` (`Xval = 0`), so `hmaj` reduces to the pure-ℕ
boost-dilution inequality `⌊C·J/(100−C)⌋ + boost + 1 ≤ J`, represented by `hdil`.
The class collapse is proved here. -/

/-- **Support saturation collapses `Sclass` to the honest window.** If every honest window
member supports `desc(b')` at `σ`, then `Sclass σ` is the whole honest window (`filter` by a
predicate true on all members). -/
theorem Sclass_eq_window_of_saturation (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot)
    (hsat : ∀ i ∈ (E.span_committee lo σ).filter (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' σ i) :
    E.Sclass cfg ext v₀ n₀ b' lo σ =
      (E.span_committee lo σ).filter (fun i => i ∈ E.honest) := by
  classical
  simp only [Execution.Sclass]
  exact Finset.filter_true_of_mem hsat

/-- **`s(σ) = J(σ)` under support saturation.** `Sclass = window` (`Sclass_eq_window_of_
saturation`) and both are weighted by `E.weight`, so `Sval = Jspec`. -/
theorem Sval_eq_Jspec_of_saturation (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot)
    (hsat : ∀ i ∈ (E.span_committee lo σ).filter (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' σ i) :
    E.Sval cfg ext v₀ n₀ b' lo σ = E.Jspec lo σ := by
  simp only [Execution.Sval, Execution.Jspec]
  rw [E.Sclass_eq_window_of_saturation cfg ext v₀ n₀ b' lo σ hsat]

/-- **`x(σ) = 0` under support saturation.** Every honest window member supports `desc(b')`,
so the `¬SupportsDesc ∧ ¬AncestorOrVoteless` filter defining `Xclass` is empty. -/
theorem Xval_eq_zero_of_saturation (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot)
    (hsat : ∀ i ∈ (E.span_committee lo σ).filter (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' σ i) :
    E.Xval cfg ext v₀ n₀ b' lo σ = 0 := by
  classical
  have hempty : E.Xclass cfg ext v₀ n₀ b' lo σ = ∅ := by
    simp only [Execution.Xclass]
    rw [Finset.filter_eq_empty_iff]
    exact fun i hi hbad => hbad.1 (hsat i hi)
  simp only [Execution.Xval, hempty, Execution.weight, Finset.sum_empty]

/-- **`hmaj` from support saturation + boost dilution.** In the saturated regime
`hsat` gives `x(σ') = 0` and `s(σ') = J(σ')`, so the saturated-majority
field is exactly the pure-ℕ boost-dilution inequality `hdil`
(`⌊C·J/(100−C)⌋ + boost + 1 ≤ J`). This yields `EdgeInputResidual.hmaj`. -/
theorem hmaj_of_saturation (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (boost : ℕ)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
        E.SupportsDesc cfg ext v₀ n₀ b' σ' i)
    (hdil : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
          / (100 - cfg.confirmation_byzantine_threshold) + boost + 1 ≤ E.Jspec lo σ') :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext v₀ n₀ b' lo σ'
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
              / (100 - cfg.confirmation_byzantine_threshold)
          + boost + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ' := by
  intro σ' h1 h2 hσH
  rw [E.Xval_eq_zero_of_saturation cfg ext v₀ n₀ b' lo σ' (hsat σ' h1 h2 hσH),
      E.Sval_eq_Jspec_of_saturation cfg ext v₀ n₀ b' lo σ' (hsat σ' h1 h2 hσH)]
  simpa using hdil σ' h1 h2 hσH

/-! ## Section 3 — `hrec`: every `Sclass` member records a `c`-supporting message

`EdgeDynamics.EdgeInputResidual.hrec` asks that every `Sclass w m b lo σ` member records, at
the endpoint `(w, m)`, a latest message supporting the fork child `c` on `b`'s chain. Each
`Sclass` member carries its own `SupportsDesc` vote witness `(t, kk, a)` (newest by `σ`, its
block `⪰ b`); `EngineTransport.recorded_supports_c_of_IH` — instantiated at the endpoint
anchor `(v₀, n₀) := (w, m)` so the cross-store transport is **reflexive** — turns that into
the recorded `c`-support, handling both the equality case (the recorded root *is* the vote
block, `latest_message_root`) and the displacement case (a later `[σ+1, k)` vote installed
`lm`; the engine IH `hIH` covers it). The `WalkKnown` domains come from
`AnchorFacade.store_walkKnownK`; the recorded message and its epoch floor from
`Delivery.vote_ubiquity` (packaged as `hubiq`); endpoint knownness, the
recorded-root walk, and the fork edge are explicit hypotheses. -/

/-- **`hrec` from the per-endpoint domain package.** Every `Sclass w m b lo σ` member
records a `c`-supporting latest message at `(w, m)`. Mechanizes the iteration over the class
+ the reflexive-anchor instantiation of `recorded_supports_c_of_IH` (equality + displacement
cases) + the `store_walkKnownK`/`store_parentSlotLt` derivation of its walk-domain premises.
Its inputs are the engine IH `hIH` (vote block `⪰ b`), the ubiquity
landing `hubiq`, the vote-block knownness `hbbr_known`, the recorded-root walk `hwalk_wm`, and
the endpoint knownness/edge facts (`hb_wm`, `hc_wm`, `hbc_wm`). -/
theorem hrec_of_domain (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b c : Root} {lo σ : Slot} (_hw : w ∈ E.honest)
    (hb_wm : b ∈ (E.store cfg ext w m).block_roots)
    (hc_wm : c ∈ (E.store cfg ext w m).block_roots)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hIH : ∀ j ∈ E.honest, ∀ t' : Slot, σ + 1 ≤ t' → t' < E.slot_at cfg m →
      ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hubiq : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) →
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        compute_epoch_at_slot cfg t ≤ lm.epoch)
    (hbbr_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) → a.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots)
    (hwalk_wm : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ lm,
      (E.store cfg ext w m).latest_messages i = some lm →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root) :
    ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true := by
  obtain ⟨hgen, hwf, _hdiv, hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, heq, _, _⟩ := hgen; exact ⟨ast, ablk, heq⟩
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled w m
  intro i hi
  have hi' := hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi'
  obtain ⟨⟨_hspan, hhon⟩, hsupp⟩ := hi'
  obtain ⟨t, kk, a, htle, hvote, hmidle, hgvn⟩ := hsupp
  obtain ⟨lm, hlm, hepge⟩ := hubiq i hi t kk a hvote
  have hbbr_vn := hbbr_known i hi t kk a hvote
  have hwa_vn : WalkKnown (E.store cfg ext w m)
      ((E.store cfg ext w m).blocks b).slot a.data.beacon_block_root :=
    E.store_walkKnownK cfg ext hwf hec hgen w m b hb_wm _ hbbr_vn
  have hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b :=
    E.store_walkKnownK cfg ext hwf hec hgen w m c hc_wm b hb_wm
  have hsupp : is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true :=
    recorded_supports_c_of_IH cfg ext hwf hhb hec hgen' hhon (Nat.lt_succ_of_le htle)
      hvote (fun t' h1 h2 => hmidle t' h1 (Nat.lt_succ_iff.mp h2)) hgvn hlm hepge rfl hIH
      (List.Subset.refl _) hbbr_vn hb_wm hwa_vn hpsl (hwalk_wm i hi lm hlm) hwb_wm hbc_wm
  exact ⟨lm, hlm, hsupp⟩

/-! ## Section 4 — `hdeltas`: the pre-`T1` per-slot step, reduced to same-epoch monotonicity

`EdgeDynamics.EdgeInputResidual.hdeltas` is the per-slot `∃ξα` class-migration step for a
pre-`T1` slot (`σ' + 1` still inside `epoch(es) + 2`). In the **same-epoch** regime the
`ρ = 0` bookkeeping (each member is assigned at
most once per epoch, `committee_assignment_unique`) forces the `X → S` migrant weight to be
**zero** — no window member re-votes within the epoch, so the only class movement is the
fresh honest committee of slot `σ' + 1` entering `Sclass` (`votes_head` + IH: it votes
`desc(b')`). Hence the `∃ξα` witness is `ξ = α = 0`, and `hdeltas` collapses to the three
per-slot facts `hSmono` / `hXmono` / `hρ0` below. This section mechanizes that `ξ = α = 0`
assembly; the three monotonicity facts are explicit inputs. -/

/-- **`hdeltas` from same-epoch monotonicity.** The pre-`T1` per-slot step with the
same-epoch `ρ = 0` witness `ξ = α = 0`: given per slot the honest-support growth `hSmono`
(`s(σ')` grows by at least the fresh honest committee), the sibling-stuck antitonicity
`hXmono` (`x` never grows), and the fresh-committee/`Unrec`-drop partition `hρ0`, the `∃ξα`
migration field holds with witnesses `ξ = α = 0`. -/
theorem hdeltas_of_monotone (w : ValidatorIndex) (m : ℕ) (b : Root) (lo es : Slot)
    (hSmono : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.Sval cfg ext w m b lo σ' +
          E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
            (fun i => i ∈ E.honest))
        ≤ E.Sval cfg ext w m b lo (σ' + 1))
    (hXmono : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.Xval cfg ext w m b lo (σ' + 1) ≤ E.Xval cfg ext w m b lo σ')
    (hρ0 : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.weight ((E.span_committee (σ' + 1) (σ' + 1)).filter (fun i => i ∈ E.honest)) ≤
        E.weight (E.Unrec cfg ext w m b lo es σ' \ E.Unrec cfg ext w m b lo es (σ' + 1))
          + E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
            (fun i => i ∈ E.honest))) :
    ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      ∃ ξ α : ℕ,
        (E.Sval cfg ext w m b lo σ' + ξ + α +
            E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
              (fun i => i ∈ E.honest))
          ≤ E.Sval cfg ext w m b lo (σ' + 1)) ∧
        (E.Xval cfg ext w m b lo (σ' + 1) + ξ ≤ E.Xval cfg ext w m b lo σ') ∧
        (E.weight ((E.span_committee (σ' + 1) (σ' + 1)).filter (fun i => i ∈ E.honest)) ≤
          E.weight (E.Unrec cfg ext w m b lo es σ' \ E.Unrec cfg ext w m b lo es (σ' + 1))
            + ξ + α +
            E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
              (fun i => i ∈ E.honest))) := by
  intro σ' h1 hσH hσ1H h2
  exact ⟨0, 0, by simpa using hSmono σ' h1 hσH hσ1H h2,
    by simpa using hXmono σ' h1 hσH hσ1H h2,
    by simpa using hρ0 σ' h1 hσH hσ1H h2⟩

end Execution

end FastConfirmation.Spec
