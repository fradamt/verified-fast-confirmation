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
transiently false and therefore cannot serve as a Casper interface fact.

This module supplies the FILTER-layer head lemmas that replace it. What it does **not** supply
any more is the ahead-regime half: the route that quantified over the transient lag was the
legacy `SpecAssumptions` observed-anchor route, retired in full (P-6). The route that is
actually audited establishes the epoch inequality directly and therefore stays inside the
at-or-below regime; see `docs/p6-justified-descends-derivation.md` §8.

## Contents

* **Section 1 — the filter-route head lemma, at-or-below regime.**
  `head_ge_of_justifiedIn_le`: at an honest store `(w, m)` with the fork-choice domain
  conditions, a checkpoint `c` that is `JustifiedIn (store w m)` with `c.root` known and
  `c.epoch ≤ jc.epoch` is dominated by the head. `justified_ancestry` puts `c` on the justified
  chain (`jc ⪰ c`), then `EngineStore.head_ge_of_justified_ge` (`filtered_through_justified`)
  puts the head above `c` — no LMD margin, filter only.

  The complementary **ahead** regime `jc.epoch < c.epoch` was never closable here: the filter is
  rooted at `jc.root` and admits siblings that fork off below `c`, so only weight could force
  the head above `c`, and the per-fork ledger needs `β < 1/6 − pb/2 ≈ 0.1604` against this
  development's `β = 1/4` (`AheadFacade`'s header carries the arithmetic). It was represented by
  an explicit input, and the two-regime lemma `head_ge_of_justifiedIn`, the residual bundle that
  carried that input, and the whole discharge chain above them are **deleted** (P-6) — see the
  Section 2 note below.

* **Section 2 — deleted: the ahead-regime proposition and the filter route above it.** The
  audited route does not need it: `AcceptedObservedRestartDynamicSafety` proves
  `obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, so the observed anchor is always in the
  at-or-below regime — which that route closes with `head_ge_of_justified_ge_K` (Section 3),
  the target-known-walk core, having derived `jc ⪰ obs` itself from `justified_ancestry`. With
  the ahead-regime route gone, Section 1's `head_ge_of_justifiedIn_le` — the same argument
  packaged on the blanket walk domain — has no consumer left; it is kept as the statement of
  the closed regime.

* **Section 3 — the walk-closure anchor reshape.** `walkClosure_of_anchorSlot`
  reshapes the `WalkClosure` consumer to target slots `≥` the anchor block's slot,
  eliminating the `anchor_guard` residual's `∀ sl` over-strength (false for
  checkpoint-sync anchors) without any anchor-at-genesis assumption. The consumer
  analysis is documented per call site. `head_ge_of_justified_ge_K` — the at-or-below
  head core on the target-known walk domain — is the lemma the accepted and weak routes
  actually use; its anchor-reshaped ahead-capable companion `head_ge_of_justifiedIn_le_K`
  is deleted with the ahead-regime route (P-6, see the section note there).

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

/-! ## Section 2 — deleted: the ahead-regime proposition and the filter route above it

Seven declarations stood here and in the closing section at the end of this file:

* `head_ge_of_justifiedIn` — the two-regime filter head lemma, whose ahead branch
  (`jc.epoch < c.epoch`) was supplied as an explicit input;
* `safeFrom_observed_of_filter` — `L4Residual.observed_safe` assembled from it;
* the three-field observed-anchor residual bundle, whose `observed_head_ahead`
  field *was* the ahead-regime proposition, instantiated at the observed anchor;
* `observed_safe_of_filterResiduals`, `L4ResidualHypsFilter`, `l4Residual_of_hypsFilter`,
  `spec_safety_of_hypsFilter` — the discharge chain above it.

Nothing produced `observed_head_ahead`. It came from
`AheadFacade.observedFilterResiduals_of_headTracks`, which took the ahead-regime head-tracking
premise as a hypothesis; that premise was `JustificationInterface.justified_descends` until
`fe724fd` deleted the field as an LMD-GHOST weight claim wrongly presented as an FFG export and
not derivable at `β = 1/4`, and it has now been deleted outright together with the legacy
`SpecAssumptions` observed-anchor cone (P-6).

**The audited route never enters the ahead regime.** `AcceptedObservedRestartDynamicSafety`
proves `obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, from
`ActualFCRGuardedObservedAdoption`'s boundary adoption plus `store_justified_epoch_mono` — i.e.
the observed anchor is always in the **at-or-below** regime. That route closes it with
`head_ge_of_justified_ge_K` (Section 3) on the ancestry it derives itself from
`justified_ancestry`, with no weight margin and no premise. Section 1's
`head_ge_of_justifiedIn_le` packages the same argument on the blanket walk domain; it now has
no consumer and is kept only as the statement of the closed regime. See
`docs/p6-justified-descends-derivation.md` §8. -/

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
        is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk b' .pending) = true)
    {child r : Root}
    (hchild : child ∈ store.block_roots.filter
      (fun root => (store.blocks root).parent_root = base))
    (hrl : r ∈ (filter_block_tree_aux cfg store fuel child).2) :
    is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk base .pending) = true := by
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
        is_ancestor store (ForkChoiceNode.mk r .pending) (ForkChoiceNode.mk base .pending) = true := by
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
  rw [is_ancestor_node_root]
  simp only [get_node_for_root] at hjb ⊢
  have hmem : (get_head cfg store).root ∈ get_filtered_block_tree cfg store ∨
      (get_head cfg store).root = store.justified_checkpoint.root := by
    simp only [get_head]
    exact get_head_aux_root_mem_or cfg (2 * (get_filtered_block_tree cfg store).length + 2)
      (ForkChoiceNode.mk store.justified_checkpoint.root .pending)
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
  · change is_ancestor store (ForkChoiceNode.mk (get_head cfg store).root .pending)
      (ForkChoiceNode.mk b .pending) = true
    rw [heq]
    exact hjb

namespace Execution

variable (E : Execution Root)

/-! ### Deleted: `head_ge_of_justifiedIn_le_K`

The anchor-reshaped at-or-below head core. Its only consumer was
`AnchorFacade.head_ge_of_justifiedIn_K`, the ahead-regime split. The unreshaped
`head_ge_of_justifiedIn_le` and the general `head_ge_of_justified_ge_K` — the lemma the
accepted and weak routes actually use — are unaffected.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

end Execution

end FastConfirmation.Spec

end
