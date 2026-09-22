module
public import FastConfirmation.Spec.Proof.ResidualDischarge
public import FastConfirmation.Spec.Proof.ForkAssembly

@[expose] public section

/-!
# Spec / Proof / E5Filter: the E5 filter route for the observed anchor

The `observed_dom` premise (`InterfaceRewire.FinalResiduals`,
`ForkAssembly.FinalResidualsER`, `ResidualDischarge.L4ResidualHyps`) asks for

> `is_ancestor (store w m) (jc(w,m)) (obs(v,n)) = true`, i.e. `obs(v,n) ⪯ jc(w,m)`

(the realized justified checkpoint dominates the observed anchor). This relation is not
valid in general: within an epoch an honest node's *realized*
`justified_checkpoint` can lag the *observed* (unrealized) one, so `obs ⪯ jc` is
transiently false and therefore cannot serve as a Casper interface fact. The E5
filter route proves that the fork-choice head dominates the
observed anchor directly from the FILTER layer, replacing the justified-dominance
route with the sound goal `SafeFrom(observed-root)`.

## Contents

* **Section 1 — the filter-route head lemma.** `head_ge_of_justifiedIn`: at an
  honest store `(w, m)` with the fork-choice domain conditions, any checkpoint `c`
  that is `JustifiedIn (store w m)` with `c.root` known is dominated by the head.
  Two regimes:
  * `c.epoch ≤ jc.epoch` (`head_ge_of_justifiedIn_le`): `justified_ancestry`
    puts `c` on the justified chain (`jc ⪰ c`), then `EngineStore.head_ge_of_justified_ge`
    (`filtered_through_justified`) puts the head above `c` — no LMD margin, filter only.
  * `jc.epoch < c.epoch` (the explicit input `hahead`): the observed anchor is *ahead*
    of the store's realized justified checkpoint; the head follows it via the filter's
    unrealized-justification admission (`get_voting_source` / conflicting-justification
    exclusion). This premise is represented by
    `ObservedFilterResiduals.observed_head_ahead`.

* **Section 2 — `SafeFrom(observed-root)` and the L4 discharge.**
  `safeFrom_observed_of_filter` assembles `L4Residual.observed_safe` from the filter
  head lemma + `ObservedDom.fcrStep_observed_justifiedIn` (obs is `JustifiedIn`
  everywhere — using the `prev_greatest` boundary-source justification) +
  the observed-anchor knownness. `L4ResidualHypsFilter` is `L4ResidualHyps` with
  the invalid-in-general `observed_dom` field replaced by the filter inputs;
  `l4Residual_of_hypsFilter` reuses `ResidualDischarge`'s finalized/advance discharges
  and routes the observed anchor through the filter. `spec_safety_of_hypsFilter` is the
  corresponding safety theorem.

* **Section 3 — the walk-closure anchor reshape.** `walkClosure_of_anchorSlot`
  reshapes the `WalkClosure` consumer to target slots `≥` the anchor block's slot,
  eliminating the `anchor_guard` residual's `∀ sl` over-strength (false for
  checkpoint-sync anchors) without any anchor-at-genesis assumption. The consumer
  analysis is documented per call site.

These inputs are recorded explicitly by the structures named above.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the filter-route head lemma

The head of an honest store dominates every `JustifiedIn` checkpoint whose root is
known. The store's own realized justified checkpoint `jc` is `JustifiedIn`
(`Or.inl rfl`), and every filtered root — hence the head — descends from `jc`
(`EngineStore.filtered_through_justified`). For a `JustifiedIn` `c` at-or-below `jc`'s
epoch, `justified_ancestry` puts `c` on `jc`'s chain, so the head descends past `c`. -/

/-- **Filter-route head domination, `c` at-or-below `jc`'s epoch (closed).** At an
honest store `(w, m)` with the fork-choice domain conditions, a `JustifiedIn`
checkpoint `c` with `c.root` known and `c.epoch ≤ jc.epoch` is dominated by the head.
`justified_ancestry` (Casper cross-epoch coherence, the justification-interface export) gives
`jc ⪰ c` (`is_ancestor jc.root c.root`), which `EngineStore.head_ge_of_justified_ge`
lifts to `head ⪰ c` through the filter alone — no LMD weight margin. This is the sound
core of the observed-anchor dominance: `obs ⪯ jc` used only where it *holds*. -/
theorem head_ge_of_justifiedIn_le (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
          < ((E.store cfg ext w m).blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ (E.store cfg ext w m).block_roots →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (c : Checkpoint Root) (hc_just : JustifiedIn (E.store cfg ext w m) c)
    (hc_known : c.root ∈ (E.store cfg ext w m).block_roots)
    (hle : c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true :=
  head_ge_of_justified_ge cfg hwf hwalk hjust
    (hji.justified_ancestry w hw m c (E.store cfg ext w m).justified_checkpoint
      hH hc_just (Or.inl rfl) hle hc_known hjust)

/-- **Filter-route head domination (full, with the ahead residual).** The head
dominates a `JustifiedIn` `c` with known root, splitting on `c.epoch` vs `jc.epoch`:
at-or-below is `head_ge_of_justifiedIn_le` (closed); strictly above is the named
residual `hahead` — the observed anchor is *ahead* of the store's realized justified
checkpoint (where `obs ⪯ jc` is false), and the head follows it through the
filter's unrealized-justification admission. `hahead` states this premise explicitly. -/
theorem head_ge_of_justifiedIn (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
          < ((E.store cfg ext w m).blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ (E.store cfg ext w m).block_roots →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (c : Checkpoint Root) (hc_just : JustifiedIn (E.store cfg ext w m) c)
    (hc_known : c.root ∈ (E.store cfg ext w m).block_roots)
    (hahead : (E.store cfg ext w m).justified_checkpoint.epoch < c.epoch →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root c.root) = true) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true := by
  by_cases hle : c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch
  · exact E.head_ge_of_justifiedIn_le cfg ext hji w hw m hH
      hwf hwalk hjust c hc_just hc_known hle
  · exact hahead (not_le.mp hle)

/-! ## Section 2 — `SafeFrom(observed-root)` and the L4 discharge

The observed anchor `obs(v,n) := (fcrStep v n).current_epoch_observed_justified_checkpoint`
is `JustifiedIn` in every honest view (`ObservedDom.fcrStep_observed_justifiedIn`, which
uses the on-boundary `prev_greatest` premise `hprev`). The
filter head lemma then dominates it. `safeFrom_observed_of_filter` assembles
`L4Residual.observed_safe` this way; the residual bundle `ObservedFilterResiduals` carries
the three genuine store facts (the boundary `JustifiedIn`, the observed-anchor knownness,
and the ahead-regime head domination). `L4ResidualHypsFilter` replaces
`L4ResidualHyps`'s invalid-in-general `observed_dom` field with this bundle. -/

/-- **`SafeFrom(observed-root)` from the filter route.** For honest `(v, n)`, the observed
anchor is safe from second `n+1`: at every honest `(w, m)` past `n+1` it is `JustifiedIn`
(`fcrStep_observed_justifiedIn`, consuming the boundary-source premise `hprev`) with known root,
so `head_ge_of_justifiedIn` dominates it — the ≤-epoch case through the filter, the
ahead case through `hahead`. This is `L4Residual.observed_safe`'s conclusion via the sound
E5 route, replacing `ResidualDischarge`'s `safeFrom_of_domain_dom` (which needs the
rejected `obs ⪯ jc`). -/
theorem safeFrom_observed_of_filter (hji : JustificationInterface cfg ext E)
    (hdomain : E.StoreDomain cfg ext)
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
    (hahead : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.epoch <
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root
          (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1) := by
  intro w hw m hm hH
  obtain ⟨hwf, hwalk, hjust⟩ := hdomain w hw m hH
  exact E.head_ge_of_justifiedIn cfg ext hji w hw m hH hwf hwalk hjust
    ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
    (E.fcrStep_observed_justifiedIn cfg ext hji hprev v hv n w hw m hm hH)
    (hknown v hv n w hw m hm hH) (hahead v hv n w hw m hm hH)

/-- **The observed-anchor filter residuals** (`E5Filter`). The three genuine store facts the
filter route consumes, replacing the unsound `is_ancestor jc obs` residual:

* `prev_greatest_justifiedIn` — on an epoch boundary with no slot advance the
  re-rotated `fcrStep`-observed checkpoint is `JustifiedIn` everywhere later (the
  greatest-unrealized propagation, `ObservedDom`/`MicroSteps` shape). This is the sole
  corner `observed_justified` does not cover directly; folded here so the whole
  observed-anchor `JustifiedIn` fact is available (`fcrStep_observed_justifiedIn`).
* `observed_known` — the observed anchor's root is a known block at every honest store
  from `n+1` on (the explicit observed-anchor root-knownness premise; the
  totalized ancestry walk is meaningless otherwise).
* `observed_head_ahead` — the ahead regime `jc.epoch < obs.epoch` (where `obs ⪯ jc` is
  false): the head follows the observed anchor through the filter's unrealized-
  justification admission. This is represented by the explicit field below. -/
structure ObservedFilterResiduals (E : Execution Root) : Prop where
  /-- The on-boundary/no-advance observed checkpoint is justified everywhere later. -/
  prev_greatest_justifiedIn : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_start_slot_at_epoch cfg (get_current_slot cfg (E.store cfg ext v (n + 1))) = true →
    ¬ (get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)) →
    JustifiedIn (E.store cfg ext w m)
      ((E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint)
  /-- the observed anchor's root is a known block at every honest store from `n+1` on. -/
  observed_known : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots
  /-- ahead regime: when the observed anchor's epoch exceeds the store's realized
      justified epoch, the head descends from it (the filter's unrealized-justification
      admission — the genuine E5 residual). -/
  observed_head_ahead : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.epoch <
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch →
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true

/-- **`L4Residual.observed_safe` from the filter residuals.** Threads
`ObservedFilterResiduals`' three fields through `safeFrom_observed_of_filter` at every
`(v, n)`. This is the sound replacement for `ResidualDischarge`'s observed-anchor
discharge. -/
theorem observed_safe_of_filterResiduals (hji : JustificationInterface cfg ext E)
    (hdomain : E.StoreDomain cfg ext) (hobs : E.ObservedFilterResiduals cfg ext) :
    ∀ v ∈ E.honest, ∀ n : ℕ,
      E.SafeFrom cfg ext
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1) :=
  fun v hv n => E.safeFrom_observed_of_filter cfg ext hji hdomain
    hobs.prev_greatest_justifiedIn hobs.observed_known hobs.observed_head_ahead v hv n

/-- **The L4 residual bundle, observed-anchor rerouted through the filter** (`E5Filter`).
`ResidualDischarge.L4ResidualHyps` with the unsound `observed_dom` field
(`is_ancestor jc obs`, which is not valid in general) replaced by `observed_filter`
(`ObservedFilterResiduals`, the sound E5 route). The finalized/genesis/advance
residuals are carried verbatim. -/
structure L4ResidualHypsFilter (E : Execution Root) : Prop where
  /-- the FFG interface (a `SpecAssumptions` field). -/
  interface : JustificationInterface cfg ext E
  /-- the shared fork-choice domain conditions at every honest store. -/
  store_domain : E.StoreDomain cfg ext
  /-- E5: every honest store's finalized block descends from the genesis anchor's
      finalized root. -/
  genesis_fin_track : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true
  /-- E5: every honest store's finalized block descends from the finalized reset anchor. -/
  finalized_track : ∀ v ∈ E.honest, ∀ n : ℕ,
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true
  /-- **E5 (filter route)**: the observed-anchor filter residuals, replacing the
      invalid-in-general `observed_dom`. -/
  observed_filter : E.ObservedFilterResiduals cfg ext
  /-- engine: every `is_one_confirmed` block at an update store carries a
      `LedgerChainInputCert`. -/
  advance_cert : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    LedgerChainInputCert cfg ext E b (n + 1)

/-- **`L4Residual` from the filter-rerouted bundle.** The finalized and advance anchors
are discharged exactly as `ResidualDischarge.l4Residual_of_hyps` does (through
`safeFrom_of_finalized_track` / `safeFrom_of_certificates`); the observed anchor is
discharged through the **sound filter route** (`observed_safe_of_filterResiduals`),
never through `safeFrom_of_domain_dom`. -/
theorem l4Residual_of_hypsFilter (h : E.L4ResidualHypsFilter cfg ext) :
    E.L4Residual cfg ext where
  genesis_safe := fun v hv =>
    E.safeFrom_of_finalized_track cfg ext h.interface h.store_domain
      (fun w hw m _ hH => h.genesis_fin_track v hv w hw m hH)
  finalized_safe := fun v hv n => by
    rw [E.fcrStep_store]
    exact E.safeFrom_of_finalized_track cfg ext h.interface h.store_domain
      (h.finalized_track v hv n)
  observed_safe :=
    E.observed_safe_of_filterResiduals cfg ext h.interface h.store_domain h.observed_filter
  advance_safe := fun v hv n b hconf =>
    E.safeFrom_of_certificates cfg ext (h.advance_cert v hv n b hconf)

end Execution

/-! ## Section 3 — the walk-closure anchor reshape

The committed `WalkClosure`/`WalkKnown` consumers (`ResidualDischarge.StoreDomain`'s
`hwalk`, `EngineStore.head_ge_of_justified_ge` / `filtered_through_justified`) demand a
**blanket** walk domain `∀ t r, r ∈ block_roots → WalkKnown store (blocks t).slot r` — a
walk to `(blocks t).slot` for *arbitrary* `t`. For an unknown `t` the totalized
`(blocks t).slot` is `0`, and `WalkKnown store 0 r` is **false** for any descendant of a
checkpoint-sync anchor (the walk to slot `0` steps off the anchor block at `anchorSlot > 0`
into the dangling parent). So the blanket form — and the `∀ sl` `anchor_guard` residual it
induces — is stronger than the call sites require.

The reshape: every *genuine* call site instantiates the target `t` at a **known** block, so
the target slot is `≥ anchorSlot`:

* `StoreDomain.hwalk` / `head_ge_of_justified_ge` use `t ∈ {b, justified-root}` — known.
* `filtered_through_justified` / `filter_block_tree_aux_output_descends` use `t = base`, a
  known root threaded down the recursion (children of known roots are known).

`walkClosure_of_anchorSlot` builds `WalkClosure store sl` for `sl ≥ anchorSlot` from the
**sound fixed-slot** anchor-min fact `∀ r, parent = P → slot ≤ anchorSlot` (the anchor
block is the minimal-slot block — a genuine Layer-0 invariant), replacing the false
`∀ sl` guard. The `_K` descent lemmas re-prove the `EngineStore` chain with the
target-known walk domain `hwalkK` (`∀ t ∈ block_roots, ∀ r ∈ block_roots, WalkKnown store
(blocks t).slot r`), so the head lemma needs only walks to known-block slots — dischargeable
from `anchorSlot ≤ (blocks t).slot` (anchor minimal) with no `anchor_guard`. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **`WalkClosure` at target `sl ≥ anchorSlot` from the sound anchor-min fact.** The
reshaped producer: instead of the `∀ sl` guard `parent = P → slot ≤ sl` (false at
`sl < anchorSlot`), it needs only the fixed-slot anchor-min fact `parent = P → slot ≤
anchorSlot` (sound — the only `P`-parented block is the anchor, at `anchorSlot`) together
with `anchorSlot ≤ sl`. `walkClosure_of_min` then closes `WalkClosure store sl`. -/
theorem walkClosure_of_anchorSlot {store : Store Root} {P : Root} {anchorSlot sl : Slot}
    (hQ : ParentInRootsOr P store)
    (hanc : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ anchorSlot)
    (hsl : anchorSlot ≤ sl) :
    WalkClosure store sl :=
  walkClosure_of_min hQ (fun r hr hP => le_trans (hanc r hr hP) hsl)

omit [LinearOrder Root] [Inhabited Root] in
/-- **`WalkKnown` at every target `sl ≥ anchorSlot`.** Composes `walkClosure_of_anchorSlot`
with `walkKnown_of_closure` (the `ParentSlotLt` + closure → `WalkKnown` builder): for
`sl ≥ anchorSlot`, every known root's walk down to `sl` stays known, with no `anchor_guard`
— only the sound fixed-slot anchor-min fact. -/
theorem walkKnown_of_anchorSlot {store : Store Root} {P : Root} {anchorSlot sl : Slot}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hQ : ParentInRootsOr P store)
    (hanc : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root = P → (store.blocks r).slot ≤ anchorSlot)
    (hsl : anchorSlot ≤ sl) :
    ∀ r ∈ store.block_roots, WalkKnown store sl r :=
  walkKnown_of_closure sl hwf (walkClosure_of_anchorSlot hQ hanc hsl)

/-! ### The descent chain with a target-known walk domain (`_K`)

Re-proofs of `EngineStore`'s filter-output descent lemmas with the walk domain
`hwalkK : ∀ t ∈ block_roots, ∀ r ∈ block_roots, WalkKnown store (blocks t).slot r`
(targets restricted to known blocks) in place of the committed blanket `hwalk`. The
proofs are the committed bodies verbatim, threading the extra `t ∈ block_roots` witness at
each `hwalk` call (always available — `base`/`b`/`justified-root` are known). This makes the
FFG-takeover head lemma consume only walks to known-block slots. -/

omit [Inhabited Root] in
/-- Inductive step of `filter_block_tree_aux_output_descends_K` — `EngineStore`'s
`output_descends_step` with the target-known walk `hwalkK` (base is known: `hbase`). -/
private theorem output_descends_step_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {base : Root} (hbase : base ∈ store.block_roots) {fuel : ℕ}
    (ih : ∀ b' : Root, b' ∈ store.block_roots → ∀ r,
      r ∈ (filter_block_tree_aux cfg store fuel b').2 →
        is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk b') = true)
    {child r : Root}
    (hchild : child ∈ store.block_roots.filter
      (fun root => (store.blocks root).parent_root = base))
    (hrl : r ∈ (filter_block_tree_aux cfg store fuel child).2) :
    is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk base) = true := by
  have hchild_mem : child ∈ store.block_roots := (List.mem_filter.mp hchild).1
  have hp : (store.blocks child).parent_root = base := by
    have h := (List.mem_filter.mp hchild).2
    simpa using h
  have hac := ih child hchild_mem r hrl
  have hcb := is_ancestor_of_parent hwf hchild_mem hbase hp
  have hr_mem : r ∈ store.block_roots := by
    rcases filter_block_tree_aux_output_mem cfg _ _ _ hrl with h | h
    · exact h
    · rw [h]; exact hchild_mem
  exact is_ancestor_trans hwf (hwalkK base hbase r hr_mem) (hwalkK base hbase child hchild_mem)
    hac hcb

omit [Inhabited Root] in
/-- **Filter-output descent with a target-known walk** — `EngineStore`'s
`filter_block_tree_aux_output_descends` re-proved with `hwalkK`. Every root the worker
emits from `base` (known) descends from `base`. -/
theorem filter_block_tree_aux_output_descends_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ (fuel : ℕ) (base : Root), base ∈ store.block_roots →
      ∀ r, r ∈ (filter_block_tree_aux cfg store fuel base).2 →
        is_ancestor store (ForkChoiceNode.mk r) (ForkChoiceNode.mk base) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro base _ r hr
    simp only [filter_block_tree_aux] at hr
    exact absurd hr List.not_mem_nil
  | succ fuel ih =>
    intro base hbase r hr
    by_cases hne :
      store.block_roots.filter (fun x => (store.blocks x).parent_root = base) ≠ []
    · rw [filter_block_tree_aux_internal cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · rcases List.mem_append.mp hr with hr' | hr'
        · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr'
          obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
          exact output_descends_step_K cfg hwf hwalkK hbase ih hchild hrl
        · rw [List.mem_singleton] at hr'
          subst hr'
          exact is_ancestor_refl store _
      · obtain ⟨l, hl, hrl⟩ := List.mem_flatten.mp hr
        obtain ⟨res, hres, rfl⟩ := List.mem_map.mp hl
        obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hres
        exact output_descends_step_K cfg hwf hwalkK hbase ih hchild hrl
    · rw [not_not] at hne
      rw [filter_block_tree_aux_leaf cfg store fuel base hne] at hr
      dsimp only at hr
      split_ifs at hr
      · rw [List.mem_singleton] at hr
        subst hr
        exact is_ancestor_refl store _
      · exact absurd hr List.not_mem_nil

omit [Inhabited Root] in
/-- **Every filtered root descends from the justified root, target-known walk.**
`EngineStore.filtered_through_justified` re-proved with `hwalkK`. -/
theorem filtered_through_justified_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r : Root} (hr : r ∈ get_filtered_block_tree cfg store) :
    is_ancestor store (get_node_for_root r)
      (get_node_for_root store.justified_checkpoint.root) = true := by
  simp only [get_node_for_root]
  have hr' : r ∈ (filter_block_tree_aux cfg store (store.block_roots.length + 1)
      store.justified_checkpoint.root).2 := hr
  exact filter_block_tree_aux_output_descends_K cfg hwf hwalkK _ _ hjust r hr'

/-- **FFG-takeover head lemma with a target-known walk** — `EngineStore.head_ge_of_justified_ge`
re-proved with `hwalkK`. Adds `hb : b ∈ block_roots` (the target block is known — always
so at the genuine call sites), which lets the final `is_ancestor_trans` use walks to the
known slot `(blocks b).slot`. No `anchor_guard`: `hwalkK` is dischargeable from
`walkKnown_of_anchorSlot` at every needed (known-block) target. -/
theorem head_ge_of_justified_ge_K {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {b : Root} (hb : b ∈ store.block_roots)
    (hjb : is_ancestor store (get_node_for_root store.justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  simp only [get_node_for_root] at hjb ⊢
  have hmem : (get_head cfg store).root ∈ get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg ((get_filtered_block_tree cfg store).length + 1)
      (ForkChoiceNode.mk store.justified_checkpoint.root)
  rcases hmem with hin | heq
  · have hgt := filtered_through_justified_K cfg hwf hwalkK hjust hin
    simp only [get_node_for_root] at hgt
    have hqr_mem : (get_head cfg store).root ∈ store.block_roots := by
      have hin' : (get_head cfg store).root ∈
          (filter_block_tree_aux cfg store (store.block_roots.length + 1)
            store.justified_checkpoint.root).2 := hin
      rcases filter_block_tree_aux_output_mem cfg _ _ _ hin' with h | h
      · exact h
      · rw [h]; exact hjust
    exact is_ancestor_trans hwf (hwalkK b hb _ hqr_mem) (hwalkK b hb _ hjust) hgt hjb
  · change is_ancestor store (ForkChoiceNode.mk (get_head cfg store).root)
      (ForkChoiceNode.mk b) = true
    rw [heq]
    exact hjb

namespace Execution

variable (E : Execution Root)

/-- **The sound observed-anchor head core, anchor-reshaped.** `head_ge_of_justifiedIn_le`
re-proved on the target-known walk domain `hwalkK` (Section 3) instead of the blanket
`hwalk`: for a `JustifiedIn` `c` with known root at-or-below `jc`'s epoch, the head
dominates `c` — with the walk domain dischargeable from `walkKnown_of_anchorSlot` (the
sound fixed-slot anchor-min fact, **no `anchor_guard`**). This is the anchor-reshaped
sound core of the observed-anchor dominance; `b := c.root`'s knownness is `hc_known`. -/
theorem head_ge_of_justifiedIn_le_K (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
          < ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots, ∀ r ∈ (E.store cfg ext w m).block_roots,
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (c : Checkpoint Root) (hc_just : JustifiedIn (E.store cfg ext w m) c)
    (hc_known : c.root ∈ (E.store cfg ext w m).block_roots)
    (hle : c.epoch ≤ (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root c.root) = true :=
  head_ge_of_justified_ge_K cfg hwf hwalkK hjust hc_known
    (hji.justified_ancestry w hw m c (E.store cfg ext w m).justified_checkpoint
      hH hc_just (Or.inl rfl) hle hc_known hjust)

end Execution

/-! ## Section 2 — `Spec_Safety` via the observed-anchor filter route -/

/-- **`Spec_Safety` from the filter-rerouted residuals** (`E5Filter`). Composes
`l4Residual_of_hypsFilter` with `L4Fold.spec_safety_of_residual`: FCR safety follows
from a proof that every execution's `SpecAssumptions` supplies `L4ResidualHypsFilter` —
the residual bundle with the observed anchor discharged through the **sound** E5 filter
route (`ObservedFilterResiduals`) rather than the invalid-in-general `obs ⪯ jc` dominance. The
downstream facades (`InterfaceRewire.spec_safety_of_final`,
`ForkAssembly.spec_safety_final_residuals`) use the corresponding
`ObservedFilterResiduals` bundle. -/
theorem spec_safety_of_hypsFilter
    (hres : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.L4ResidualHypsFilter cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_residual cfg ext
    (fun E hSA => E.l4Residual_of_hypsFilter cfg ext (hres E hSA))

end FastConfirmation.Spec

end
