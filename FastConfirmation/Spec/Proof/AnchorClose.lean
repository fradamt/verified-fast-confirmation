module
public import FastConfirmation.Spec.Proof.Anchoring
public import FastConfirmation.Spec.Proof.Dominance
public import FastConfirmation.Spec.Proof.Closing
public import FastConfirmation.Spec.Proof.INVstarTrack
public import FastConfirmation.Spec.Proof.AncestryRoots
public import FastConfirmation.Spec.Proof.Bridge
public import FastConfirmation.Spec.Proof.Engine
public import FastConfirmation.Spec.Proof.Registry
public import FastConfirmation.Spec.Proof.EdgeDynamics
public import FastConfirmation.Spec.Proof.Endpoint
public import FastConfirmation.Spec.Proof.Reanchor
public import FastConfirmation.Spec.Proof.EngineStore
public import FastConfirmation.Spec.Proof.HeadReroot
public import FastConfirmation.Spec.Proof.CheckpointDomain
public import FastConfirmation.Spec.Proof.HonestWeight
public import FastConfirmation.Spec.Proof.Discount
public import FastConfirmation.Spec.Proof.AnchorFacade
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.Delivery
public import FastConfirmation.Spec.Proof.EngineTransport

@[expose] public section

/-!
# Spec / Proof / AnchorClose: the closing composition

This module holds the anchor-scoped `SafeFrom` machinery for the `get_latest_confirmed` output:
the mid-walk fold helpers, the per-edge `DescendStep` supply `DescendStepChainSupply`, the
strong-induction shell `safeFrom_of_headStep`, the confirm-margin collapse
`descendStepChainSupply_of_confirmMargin`, and the anchor-kind covering helpers.

Everything above those — the anchor-scoped covering supply `AnchorCovSupply`, the two glc folds
`safeFromGlc_of_covSupply` / `safeFromGlc_of_chainSupply`, and the eight closing theorems
`Spec_Safety_of_chainSupply` / `_of_close` / `_of_confirmMargin` / `_of_chainConfirmMargin`
with their `Spec_Monotonicity_*` companions — is **deleted** (P-6). Each closing refined
`AnchorThread.Spec_Safety_of_anchored` and so carried the never-produced ahead-regime
head-tracking premise; the covering supply and the folds were consumed only by them. See the
section notes below and `docs/p6-justified-descends-derivation.md` §8.

The header sections that follow describe the *former* full composition; they are kept for the
machinery that survives and for the record of what the flags were.

## Anchor-scoped supplies and the four-case fold

The supplies `DescendStepChainSupply`/`ForkEdgeConfirmMarginSupply` now carry the **anchor-root
parameter `r₀`** and a per-edge **`c ⪰ r₀` scoping premise**, so the confirm-margin producer (whose
certificates live only on the `[r₀, glc]` segment) is faced only with `[r₀, glc]`-segment edges.
`advance_safe_of_descendStepChain` / `heng_of_descendStepChain` / `hdisj_glc_of_anchorCov` are
replaced by the strong-induction shell `safeFrom_of_headStep`. All three anchor kinds use their
threaded `SafeFrom` witnesses and `head_ge_of_safe_scoped_terminal` on `[r₀, glc]`; the observed
kind used to run a 4-case covering fold `head_ge_glc_endpoint` instead, which was redundant and
is deleted (see the note where it stood).
`safeFromGlc_of_covSupply` extracts a single `r₀` from the L4 anchoring
(`confirmedWithAnchor_of_advance`) and threads it through both `hcov` and the supply.

## The three glc supplies

* **`heng_glc`** — the chain-branch head-safety engine (`b ⪰ jc(w,m) → head(w,m) ⪰ b`), discharged
  by the **disjunctive strong-induction engine** on a per-edge `DescendStep` supply
  (`advance_safe_of_descendStepChain`, consuming a `DescendStep` **directly** rather than lifting an
  `INVstarTrack.ForkEdgeGroundInputs`). The per-edge `DescendStep` is produced by the
  confirm-margin collapse
  (`Dominance.descendStep_of_confirmMargin` / `Assembly.descendStep_of_assemblyResidual`) — the
  plain confirm-margin strip (`Base.weak_base_of_rule`, no arms disjunction, no min-reserve
  `INVstar`, no `hBb`) plus the three aggregate window-growth facts.
  `descendStepChainSupply_of_assembly` wires that producer, so the engine flag is the
  **transparent** per-`b`-chain-edge `DescendStep` supply `DescendStepChainSupply`, and the
  confirm-margin residual bundle discharges it.
* **`hbk_glc`** — the endpoint knownness (`get_latest_confirmed ∈ (store w m).block_roots`),
  discharged internally by `SameSlotProvenance`: executable canonical membership and known-parent
  provenance force an honest strictly-past supporter and relay the selected block in the same slot.
* **`hdisj_glc`** — the `jc ⪰ b ∨ b ⪰ jc` disjunction is retained only in the observed-anchor
  route. Confirmed/finalized anchors instead receive `head ⪰ r₀` directly from their threaded
  `SafeFrom` invariants. In every route `b ⪰ r₀` is the transported `ConfirmedWithAnchor` fact.

## Explicit hypotheses

The conditional `Spec_Safety` result follows from `SpecAssumptions` + `hanchor0` (genesis-start) + exactly:

* `hcov` — the anchor-scoped covering supply: direct `SafeFrom` covering for confirmed/finalized,
  and the observed kind's `JustifiedIn` + quorum-comparability payload.
* `heng_supply` — `DescendStepChainSupply` per confirmed block: the per-`b`-chain-edge
  `DescendStep`, produced by the confirm-margin collapse; its own inputs are the
  economic core
  (`hstrip0` = `weak_base_of_rule`'s confirm-margin strip, the three aggregate growth facts, the
  recorded-support transport `hSmem`, and the sibling confinements `hHon`/`hByz`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! The selected closing uses the ancestor-roots case split directly.  Keep its
small walk argument here instead of importing the arbitrary-root engine
module merely for this helper. -/

/-! ## Section 0 — r₀-scoped mid-walk fold helpers

The chain fold, re-rooted at an arbitrary anchor `x` on `b`'s chain and consuming the **r₀-scoped**
edge supply (each demanded edge child `c` descends from `r₀`). `parentChain_at` builds the
parent-link chain from `x` to `b` (`AncestryRoots.get_ancestor_roots`, terminal `x` instead of the
justified root); `head_ge_of_scoped_terminal` lifts each edge to a `DescendStep` — supplying the
`c ⪰ r₀` scoping premise from `Anchoring.get_ancestor_roots_descends` (`c ⪰ x`) composed with
`x ⪰ r₀` — and folds through `HeadRerootChain.head_ge_of_intermediate_ledger`. Cases (ii) and (iii)
of the covering fold are the two instantiations (`x = jc.root` resp. `x = r₀`). -/

omit [Inhabited Root] in
/-- **The parent-link chain from an arbitrary terminal `x` to `b`.** The `get_ancestor_roots`
segment `x :: get_ancestor_roots store b x`, parent-linked, all-known, ending at `b`. The
`dynamicsChainStruct_body` body re-rooted at `x` (any known ancestor of `b`) rather than the
store's justified root. -/
theorem parentChain_at {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {x b : Root} (hx : x ∈ store.block_roots) (hb : b ∈ store.block_roots)
    (hcase : get_ancestor_roots store b x ≠ [] ∨ b = x) :
    (∀ r ∈ x :: get_ancestor_roots store b x, r ∈ store.block_roots) ∧
    List.IsChain (fun a c => (store.blocks c).parent_root = a)
      (x :: get_ancestor_roots store b x) ∧
    (x :: get_ancestor_roots store b x).getLast (List.cons_ne_nil _ _) = b := by
  have hwalk : WalkKnown store (store.blocks x).slot b := hwalkK x hx b hb
  rcases hcase with hne | heq
  · obtain ⟨d0, dr, hds⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hx
      · exact get_ancestor_roots_mem hwf hwalk hr
    · rw [hds, List.isChain_cons_cons]
      refine ⟨?_, ?_⟩
      · have hhd : (get_ancestor_roots store b x).head? = some d0 := by rw [hds]; rfl
        exact get_ancestor_roots_head? hwf hwalk hhd
      · have := get_ancestor_roots_isChain hwf hwalk
        rwa [hds] at this
    · rw [List.getLast_cons hne]
      have hgl : (get_ancestor_roots store b x).getLast? = some b :=
        get_ancestor_roots_getLast? hwf hwalk hne
      have heq := List.getLast?_eq_some_getLast hne
      rw [hgl] at heq
      exact (Option.some.inj heq).symm
  · subst heq
    have hnil : get_ancestor_roots store b b = [] := get_ancestor_roots_stop (le_refl _)
    rw [hnil]
    refine ⟨?_, List.IsChain.singleton _, rfl⟩
    intro r hr
    rw [List.mem_singleton] at hr; subst hr; exact hb

omit [Inhabited Root] in
/-- Every child of an actual edge in a parent-linked chain beginning at `x`
lies strictly above `x`.  This is the exact strictness needed to exclude the
terminal/root edge from certificate supplies. -/
theorem parentChain_edge_child_slot_gt_head {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a c : Root} {l : List Root}
    (hmem : ∀ r ∈ x :: l, r ∈ store.block_roots)
    (hchain : List.IsChain (fun a c => (store.blocks c).parent_root = a) (x :: l))
    (ha : a ∈ x :: l) (hc : c ∈ x :: l)
    (hlink : (store.blocks c).parent_root = a) :
    (store.blocks x).slot < (store.blocks c).slot := by
  have hslotChain : List.IsChain
      (fun a c : Root => (store.blocks a).slot < (store.blocks c).slot) (x :: l) := by
    refine isChain_imp_of_mem hchain ?_
    intro a' ha' c' hc' hlink'
    have hp : (store.blocks c').parent_root ∈ store.block_roots :=
      hlink' ▸ hmem a' ha'
    have hlt := hwf c' (hmem c' hc') hp
    rwa [hlink'] at hlt
  have _htrans : Trans
      (fun a c : Root => (store.blocks a).slot < (store.blocks c).slot)
      (fun a c : Root => (store.blocks a).slot < (store.blocks c).slot)
      (fun a c : Root => (store.blocks a).slot < (store.blocks c).slot) :=
    ⟨fun h₁ h₂ => lt_trans h₁ h₂⟩
  have hpair := (List.isChain_iff_pairwise
    (R := fun a c : Root => (store.blocks a).slot < (store.blocks c).slot)).mp hslotChain
  rcases List.mem_cons.mp hc with hcEq | hcTail
  · subst c
    have haLt : (store.blocks a).slot < (store.blocks x).slot := by
      have hp : (store.blocks x).parent_root ∈ store.block_roots :=
        hlink ▸ hmem a ha
      have ht := hwf x (hmem x (List.mem_cons_self)) hp
      rwa [hlink] at ht
    rcases List.mem_cons.mp ha with haEq | haTail
    · have hxx : (store.blocks x).slot < (store.blocks x).slot := by
        simpa only [haEq] using haLt
      exact False.elim ((lt_irrefl _) hxx)
    · have hxLtA := (List.pairwise_cons.mp hpair).1 a haTail
      exact False.elim ((Nat.not_lt_of_ge hxLtA.le) haLt)
  · exact (List.pairwise_cons.mp hpair).1 c hcTail



namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the per-edge `DescendStep` supply and the disjunctive engine

The ground per-edge route folds `INVstarTrack.ForkEdgeGroundSupply` into head
descent, lifting each edge's
`ForkEdgeGroundInputs` (the `INVstar`/arms base) to a `DescendStep` by
`descendStep_of_forkEdgeGroundInputs`. The confirm-margin reduction produces the per-fork `DescendStep`
**directly** (`Dominance.descendStep_of_confirmMargin`), with no `INVstar`. This section re-states
the fold consuming a per-edge `DescendStep` supply directly, so the confirm-margin producer plugs in
without the `INVstar` intermediate. -/


/-- **`SafeFrom` from a per-endpoint head-descent producer.** The strong-induction
skeleton, with the per-endpoint work
abstracted into `hstep`: strong induction on the cutoff slot supplies the head-safety IH (`head ⪰ b`
at strictly earlier slots), and `hstep` closes `head ⪰ b` at the maximal-slot endpoint given that
IH. The 4-case covering fold (`safeFromGlc_of_covSupply`) is the `hstep` this shell folds. -/
theorem safeFrom_of_headStep {b : Root} {n : ℕ}
    (hstep : ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
        E.WithinHorizon cfg m' →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true) →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true) :
    E.SafeFrom cfg ext b (n + 1) := by
  refine E.safeFrom_of_engineInv cfg ext ?_
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro w hw m hm hmk hH
    by_cases hlt : E.slot_at cfg m < k
    · exact IH (E.slot_at cfg m) hlt w hw m hm (le_refl _) hH
    · have hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
        E.WithinHorizon cfg m' →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true :=
      fun w' hw' m' hm' hlt' hH' =>
        IH (E.slot_at cfg m') (lt_of_lt_of_le hlt' hmk) w' hw' m' hm' (le_refl _) hH'
      exact hstep w hw m hm hH hIH

/-! ## Section 1b — the confirm-margin collapse produces the `DescendStep` supply

The per-edge `DescendStep` of `DescendStepChainSupply` is produced by the confirm-margin reduction:
`Assembly.descendStep_of_assemblyResidual` (which composes `Dominance.descendStep_of_confirmMargin`)
turns the **plain confirm-margin strip** at the confirming anchor (`Base.weak_base_of_rule`, no arms
disjunction, no min-reserve `INVstar`, no `hBb`) plus the three aggregate window-growth facts into a
`DescendStep`. `ForkEdgeConfirmMarginSupply` packages exactly its per-edge residual bundle, and
`descendStepChainSupply_of_confirmMargin` lifts it — so the confirm-margin residual bundle is an
alternative, fully-unfolded engine flag for the closing. -/



/-! ## Section 2 — the anchor-scoped covering supply and `hdisj_glc`

`hdisj_glc` is discharged through the **anchoring covering route**: at the confirming store the
`get_latest_confirmed` block descends from one of the three reset anchors
(`Anchoring.get_latest_confirmed_ge`, hence `AnchorThread.confirmedWithAnchor_of_advance`), so the
`b ⪰ jcb.root` conjunct of `Execution.CoveringFFG` is the transported anchoring, not a free
hypothesis. The three reset-anchor knownness facts and the confirmed-block knownness are discharged
internally; the covering flag shrinks to the **anchor-scoped** supply `AnchorCovSupply`. -/

/-! ### Deleted: `AnchorCovSupply`, `safeFromGlc_of_covSupply`, `safeFromGlc_of_chainSupply`

The anchor-scoped covering supply and the two `get_latest_confirmed`-scoped folds that
produced `AnchorThread.L4ResidualGlc.advance_safe_glc` stood here. `AnchorCovSupply` was never
produced in-tree; the two folds were consumed only by the eight closing theorems deleted
below.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/






/-! ### Deleted: `head_ge_glc_endpoint`, the 4-case covering fold


The observed-anchor route of `safeFromGlc_of_covSupply` used to run a per-endpoint 4-case
covering fold here. Its case (iii) (`b ⪰ jc.root`, `r₀ ⪰ jc.root`, `jc.epoch < jcb.epoch`) was
the sole consumer of `JustificationInterface.justified_descends` on this path, obtaining
`head ⪰ r₀` from the covering checkpoint `jcb`.

The fold was **redundant**. The route tag already says `r₀` is the FCR's
`current_epoch_observed_justified_checkpoint.root`, and `safeFromGlc_of_covSupply` already
threads that root's own `SafeFrom` witness `hobs` — which *is* `head ⪰ r₀` at every honest
endpoint from `n + 1` on. The pre-deadline branch of the same proof had always used exactly
that (`simpa only [hobserved] using hobs w hw m hm hH`); the post-deadline branch now does
too, finishing through `finishDirect` like the confirmed and finalized kinds. So the fold, and
with it this path's dependence on the head-tracking claim, is gone — no weight arithmetic and
no new hypothesis. See `docs/p6-justified-descends-derivation.md` (W0) and
`docs/plumbing-spec-citations.md` P-6.

`AnchorCovSupply`'s observed disjunct keeps its `jcb` covering payload and covering
disjunction: the flag is never produced in-tree, and `Nucleus.covering_comparability` /
`Nucleus.CurrentEpochCoveringBridge` are still stated in that field shape. -/



end Execution

/-! ## Sections 3 and 4 — deleted: the eight closing theorems

`Spec_Safety_of_chainSupply` / `_of_close` / `_of_confirmMargin` / `_of_chainConfirmMargin` and
their four `Spec_Monotonicity_*` companions stood here. Every one of them refined
`AnchorThread.Spec_Safety_of_anchored` and therefore carried the unproduced ahead-regime head-tracking premise `htracks`, which entered through that theorem's `observed_safe`
leg (`AnchorFacade.safeFrom_observed_of_filter_K` on
`ExportWiring.observedFilterResiduals_of_interface`).

They are deleted with the rest of the legacy `SpecAssumptions` observed-anchor cone (P-6): 38
declarations across 16 files, 14 of them unconsumed roots, none reached by any of the 21
`scripts/Audit.lean` witnesses. Nothing in the development ever produced
that premise, and the audited route does not need it —
`AcceptedObservedRestartDynamicSafety` proves `obs.epoch ≤ jc(w, n+1).epoch` at every honest
`w`, so the observed anchor never enters the ahead regime and
`E5Filter.head_ge_of_justified_ge_K` closes its `SafeFrom` on the at-or-below branch alone. See
`docs/p6-justified-descends-derivation.md` §8 and `docs/plumbing-spec-citations.md` P-6. -/

end FastConfirmation.Spec

end
