module
public import FastConfirmation.Spec.Proof.ResidualMechanical

@[expose] public section

/-!
# Spec / Proof / ResidualMechanicalII: refining `MechanicalResiduals`

`ResidualMechanical.spec_safety_of_mechanical` reduces `Spec_Safety` to the
seven-field bundle `MechanicalResiduals`. This module derives or restructures
four of those fields from the trajectory invariants and `SpecAssumptions`, and
records the resulting inputs in `MechanicalResidualsII`:

* **`anchor_unscheduled`** — this is supplied by
  `WellFormedExecution.anchor_parent_unscheduled` from `SpecAssumptions` and is
  therefore not repeated in `MechanicalResidualsII`.

* **`walk_domain`** — the `WalkKnown` ancestor-closure per honest store. The
  generic pure-store lemma `walkKnown_of_closure` builds every `WalkKnown` from the
  Layer-0 parent-slot order (`ParentSlotLt`, delivered by
  `WFTrajectory.store_parentSlotLt`) plus a **flat first-order closure**
  `WalkClosure` (a known block above the target slot has a known parent). So
  `walk_domain` reduces to `WalkClosure` at every honest store — the `WalkKnown`
  inductive obligation follows. `WalkClosure`'s "parent is known **or** the
  anchor's dangling pointer `P`" half is itself Layer-0 derivable
  (`Execution.store_parentInRootsOr`, re-exposed here from `WFTrajectory.WFPlus`);
  the remaining input is only the anchor/minimal-slot guard.

* **`justified_known` / `finalized_known`** — checkpoint-knownness. Both
  are `WellFormedStore` fields set from **abstract** state-transition checkpoint
  outputs, so they are not handler-local (`Preservation`) and not interface-exported; they
  stay named, unchanged.

* **`finalized_descent`** — cross-store Casper finalization consistency. It is a
  separate input from the current `JustificationInterface` exports:
  the interface exports `observed_justified` propagation but no *finalized*
  propagation, and `justified_unique` only covers the equal-epoch case.

* **`dynamics_chain`** — the per-confirmed-block `DynamicsChainSupply`. Split
  into a **structural** chain residual `DynamicsChainStruct` (the ascending
  parent-linked `get_ancestor_roots` chain from the justified root to `b`, all
  known, `Nodup`) and a **per-edge** residual `DynamicsEdgeSupply` (each real
  parent edge carries a `DynamicsResidual`). `dynamicsChainSupply_of_split` lifts
  the structural chain to the `DynamicsResidual` chain edge-wise
  (`isChain_imp_of_mem`). The structural chain is additionally **built** from the
  cleaner `b`-descends-justified fact by `dynamicsChainStruct_of_descends`
  (`AncestryRoots.get_ancestor_roots` characterization + the slot-monotone `Nodup`).

-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Section 0 — two reusable helpers

A member-restricted `List.IsChain` lift (mathlib's `IsChain.imp` is blanket), and
the generic `WalkKnown`-from-closure construction that discharges `walk_domain`'s
inductive obligation. -/

/-- **Member-restricted `IsChain` lift.** `List.IsChain.imp` requires the edge
implication for *all* pairs; this variant only needs it on pairs of list members —
enough to keep the per-edge residual scoped to the chain. -/
theorem isChain_imp_of_mem {α : Type*} {R S : α → α → Prop} :
    ∀ {l : List α}, List.IsChain R l →
      (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) → List.IsChain S l := by
  intro l p
  induction p with
  | nil => intro _; exact .nil
  | singleton a => intro _; exact .singleton a
  | @cons_cons a b rest hr _ ih =>
    intro h
    refine .cons_cons (h a (by simp) b (by simp) hr) (ih ?_)
    intro x hx y hy hxy
    exact h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy

/-- **A flat ancestor-closure store predicate.** Every known block strictly above
the target slot `sl` has a known parent — the first-order fact that makes the
`WalkKnown` walk toward `sl` stay inside the store. -/
def WalkClosure (store : Store Root) (sl : Slot) : Prop :=
  ∀ r ∈ store.block_roots, sl < (store.blocks r).slot →
    (store.blocks r).parent_root ∈ store.block_roots

/-- **`WalkKnown` from the parent-slot order + the flat closure.** Strong
induction on the block's slot: at or below `sl` the walk stops; above `sl` the
closure hands a known parent whose slot strictly drops (`ParentSlotLt`), so the
induction hypothesis walks it the rest of the way. Thus `ParentSlotLt` and
`WalkClosure` imply the required `WalkKnown` property. -/
theorem walkKnown_of_closure {store : Store Root} (sl : Slot)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hclosure : WalkClosure store sl) :
    ∀ r ∈ store.block_roots, WalkKnown store sl r := by
  have key : ∀ N r, (store.blocks r).slot = N → r ∈ store.block_roots →
      WalkKnown store sl r := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro r hs hr
      by_cases hle : (store.blocks r).slot ≤ sl
      · exact WalkKnown.stop hr hle
      · have hlt : sl < (store.blocks r).slot := not_le.mp hle
        have hpar_in : (store.blocks r).parent_root ∈ store.block_roots :=
          hclosure r hr hlt
        have hpar_lt := hwf r hr hpar_in
        exact WalkKnown.step hr hlt (ih _ (hs ▸ hpar_lt) _ rfl hpar_in)
  intro r hr
  exact key _ r rfl hr

/-- **A parent-linked chain of known roots is `Nodup`.** Along a parent-link chain
`(blocks c).parent_root = a`, the parent-slot order makes slots strictly increase
(oldest→newest), so all elements are distinct. Discharges the `Nodup` obligation of
the structural confirmed chain. -/
theorem parentLinkChain_nodup {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {l : List Root} (hmem : ∀ x ∈ l, x ∈ store.block_roots)
    (hchain : List.IsChain (fun a b => (store.blocks b).parent_root = a) l) :
    l.Nodup := by
  have hslt : List.IsChain
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot) l := by
    refine isChain_imp_of_mem hchain ?_
    intro a ha b hb hlink
    have hpin : (store.blocks b).parent_root ∈ store.block_roots := hlink ▸ hmem a ha
    have hlt := hwf b (hmem b hb) hpin
    rwa [hlink] at hlt
  have _htrans : Trans
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)
      (fun a b : Root => (store.blocks a).slot < (store.blocks b).slot) :=
    ⟨fun h1 h2 => lt_trans h1 h2⟩
  have hpair := (List.isChain_iff_pairwise
    (R := fun a b : Root => (store.blocks a).slot < (store.blocks b).slot)).mp hslt
  exact hpair.imp (fun {a b} h (heq : a = b) => absurd (heq ▸ h) (lt_irrefl _))

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ### The structural chain, built from `get_ancestor_roots`

`dynamicsChainStruct_body` discharges the `∃ ds`-existential of
`DynamicsChainStruct` at one store directly from the `AncestryRoots`
characterization of `get_ancestor_roots store b jc` (the ascending parent-linked
segment from the justified root `jc` to `b`): `Nodup` from `parentLinkChain_nodup`,
the chain / `getLast` / membership from the `get_ancestor_roots_*` wrapper lemmas.
The only non-mechanical input left is `hcase` — that `b` genuinely descends from the
justified root (`get_ancestor_roots … ≠ []`) or equals it — the L4 loop-inversion
output. -/

omit [Inhabited Root] in
/-- **The structural confirmed-chain body from `get_ancestor_roots`.** At a store
with parent-slot order `hwf`, filtered containment `hfilt`, known `b`/`jc`, the walk
domain `hwalk` (`b` down to the justified slot), and the descent case split `hcase`,
the `DynamicsChainStruct` existential holds with `ds := get_ancestor_roots store b jc`.
This reduces the structural residual to `hcase` (`b`-on-`jc`'s-chain) + the flat
knownness/filter facts — the `Nodup`/`IsChain`/`getLast` list obligations are
discharged mechanically. -/
theorem dynamicsChainStruct_body {store : Store Root} (b : Root)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hfilt : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hb : b ∈ store.block_roots)
    (hjc : store.justified_checkpoint.root ∈ store.block_roots)
    (hwalk : WalkKnown store
      (store.blocks store.justified_checkpoint.root).slot b)
    (hcase : get_ancestor_roots store b store.justified_checkpoint.root ≠ [] ∨
      b = store.justified_checkpoint.root) :
    ∃ ds : List Root,
      (∀ r ∈ store.block_roots,
        (store.blocks r).parent_root ∈ store.block_roots →
          (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot) ∧
      (∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots) ∧
      b ∈ store.block_roots ∧
      ds.Nodup ∧
      (∀ r ∈ store.justified_checkpoint.root :: ds, r ∈ store.block_roots) ∧
      List.IsChain (fun a c => (store.blocks c).parent_root = a)
        (store.justified_checkpoint.root :: ds) ∧
      (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b := by
  set jc := store.justified_checkpoint.root with hjcdef
  rcases hcase with hne | rfl
  · -- `b` descends strictly: `ds = get_ancestor_roots store b jc ≠ []`
    obtain ⟨d0, dr, hds⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨get_ancestor_roots store b jc, hwf, hfilt, hb, ?_, ?_, ?_, ?_⟩
    · exact parentLinkChain_nodup hwf
        (fun x hx => get_ancestor_roots_mem hwf hwalk hx)
        (get_ancestor_roots_isChain hwf hwalk)
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hjc
      · exact get_ancestor_roots_mem hwf hwalk hr
    · rw [hds, List.isChain_cons_cons]
      refine ⟨?_, ?_⟩
      · have hhd : (get_ancestor_roots store b jc).head? = some d0 := by rw [hds]; rfl
        exact get_ancestor_roots_head? hwf hwalk hhd
      · have := get_ancestor_roots_isChain hwf hwalk
        rwa [hds] at this
    · rw [List.getLast_cons hne]
      have hgl : (get_ancestor_roots store b jc).getLast? = some b :=
        get_ancestor_roots_getLast? hwf hwalk hne
      have heq := List.getLast?_eq_some_getLast hne
      rw [hgl] at heq
      exact (Option.some.inj heq).symm
  · -- `b = jc`: the segment is empty, the chain is the singleton `[jc]`
    have hnil : get_ancestor_roots store jc jc = [] :=
      get_ancestor_roots_stop (le_refl _)
    refine ⟨get_ancestor_roots store jc jc, hwf, hfilt, hb, ?_, ?_, ?_, ?_⟩
    · rw [hnil]; exact List.nodup_nil
    · intro r hr
      rw [hnil] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hjc
      · exact absurd hr (by simp)
    · rw [hnil]; exact List.IsChain.singleton _
    · rw [hnil]; rfl

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `walk_domain` from the flat closure `WalkClosure`

`MechanicalResiduals.walk_domain` asks for a `WalkKnown` walk domain over every
known root and every target slot. `walkKnown_of_closure` builds each `WalkKnown`
from the Layer-0 parent-slot order (`ParentSlotLt`, delivered at the trajectory
level by `WFTrajectory.store_parentSlotLt`) and the flat closure `WalkClosure` at
the target slot. So `walk_domain` reduces to `WalkClosure` at every honest store —
the `WalkKnown` inductive obligation is discharged; only the first-order closure
remains. -/

/-- **`walk_domain` from `ParentSlotLt` (Layer 0) + `WalkClosure`.** For each honest
`(w, m)`, each target `t` and known root `r`, `walkKnown_of_closure` walks `r` down
to `(blocks t).slot` using the closure at that slot. The parent-slot order is the
Layer-0 `store_parentSlotLt`; the closure is the named residual. -/
theorem walkDomain_of_walkClosure
    (hpsl : ∀ w ∈ E.honest, ∀ m : ℕ, ParentSlotLt (E.store cfg ext w m))
    (hclosure : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
      WalkClosure (E.store cfg ext w m) sl) :
    ∀ w ∈ E.honest, ∀ m : ℕ, ∀ t r : Root,
      r ∈ (E.store cfg ext w m).block_roots →
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r :=
  fun w hw m t r hr =>
    walkKnown_of_closure ((E.store cfg ext w m).blocks t).slot
      (hpsl w hw m) (hclosure w hw m _) r hr

/-! ## Section 2 — `dynamics_chain` split into structure + per-edge

`MechanicalResiduals.dynamics_chain` is the per-confirmed-block `DynamicsChainSupply`
— an ascending `List.IsChain DynamicsResidual` from the justified root to `b`. Its
per-edge `DynamicsResidual` is the whole engine at one fork; its list structure is
the `get_ancestor_roots` chain (`AncestryRoots`). The two are separated: the
**structural** chain residual `DynamicsChainStruct` (parent-linked, all-known,
`Nodup`, ending at `b`) and the **per-edge** residual `DynamicsEdgeSupply` (each
real parent edge carries a `DynamicsResidual`). `dynamicsChainSupply_of_split` lifts
the structural chain to the `DynamicsResidual` chain edge-wise
(`isChain_imp_of_mem` — member-scoped so the edge residual only ever fires on chain
elements). -/

/-- **The structural confirmed-chain residual.** `DynamicsChainSupply`'s shape with
the `DynamicsResidual` edges replaced by the purely structural parent-link
`(blocks c).parent_root = a`, and carrying membership of every chain element in
`block_roots` (so the per-edge lift is member-scoped). This is the
`AncestryRoots.get_ancestor_roots` chain from the justified root to `b`; it
contains no `DynamicsResidual` assumptions. -/
def DynamicsChainStruct (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∃ ds : List Root,
      (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
        r ∈ (E.store cfg ext w m).block_roots) ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      ds.Nodup ∧
      (∀ r ∈ (E.store cfg ext w m).justified_checkpoint.root :: ds,
        r ∈ (E.store cfg ext w m).block_roots) ∧
      List.IsChain
        (fun a c => ((E.store cfg ext w m).blocks c).parent_root = a)
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **The per-edge dynamics residual supply.** At every honest endpoint `(w, m)`
past `n₀` (given the strong-induction head-safety hypothesis), every real parent
edge `a ← c` of known blocks carries a `DynamicsResidual w m a c` — the engine's
per-fork content (`ResidualDischarge.DynamicsResidual`). The chain structure is
separated out so this predicate is required only on confirmed-chain edges. -/
def DynamicsEdgeSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
        E.DynamicsResidual cfg ext w m a c

/-- **`DynamicsChainSupply` from the structure + per-edge split.** The
structural parent-link chain lifts edge-wise to the `DynamicsResidual` chain: each
chain element is known (`hmem`), so the member-scoped `DynamicsEdgeSupply` supplies
the per-edge `DynamicsResidual` for every adjacent pair (`isChain_imp_of_mem`). The
domain facts and `getLast` pass through unchanged. This is the strongest
chain-supply reduction: `dynamics_chain` reduces to exactly `DynamicsChainStruct`
(fork-choice-mechanical) + `DynamicsEdgeSupply` (per-fork engine). -/
theorem dynamicsChainSupply_of_split {b : Root} {n₀ : ℕ}
    (hstruct : E.DynamicsChainStruct cfg ext b n₀)
    (hedge : E.DynamicsEdgeSupply cfg ext b n₀) :
    E.DynamicsChainSupply cfg ext b n₀ := by
  intro w hw m hm hH hIH
  obtain ⟨ds, hpsl, hfilt, hb, hnd, hmem, hchain, hlast⟩ := hstruct w hw m hm hH hIH
  refine ⟨ds, hpsl, hfilt, hb, hnd, ?_, hlast⟩
  refine isChain_imp_of_mem hchain ?_
  intro a ha c hc hlink
  exact hedge w hw m hm hH hIH a c (hmem a ha) (hmem c hc) hlink

/-- **`DynamicsChainStruct` from flat per-endpoint facts.** Constructs the
structural existential from the Layer-0
parent-slot order `hwf`, the filtered-tree containment `hfilt`, the flat closure
`hclos` (as `WalkClosure`, reused to build the `b`-walk),
justified-knownness `hjc`, endpoint `b`-knownness `hb`, and the loop-inversion
descent `hcase` (`b` on the justified chain, or `= jc`). `dynamicsChainStruct_body`
does the mechanical list assembly. So `dynamics_struct` reduces to exactly
`hfilt` (filter containment) + `hb` (endpoint `b`-known) + `hcase` (`b`-descends-
justified) — three flat per-endpoint facts, no list construction. -/
theorem dynamicsChainStruct_of_facts {b : Root} {n₀ : ℕ}
    (hwf : ∀ w ∈ E.honest, ∀ m : ℕ, ParentSlotLt (E.store cfg ext w m))
    (hfilt : ∀ w ∈ E.honest, ∀ m : ℕ,
      ∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
        r ∈ (E.store cfg ext w m).block_roots)
    (hclos : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
      WalkClosure (E.store cfg ext w m) sl)
    (hjc : ∀ w ∈ E.honest, ∀ m : ℕ,
      (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
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
  intro w hw m hm hH hIH
  have hbmem := hb w hw m hm hH hIH
  have hwalk := walkKnown_of_closure
    ((E.store cfg ext w m).blocks (E.store cfg ext w m).justified_checkpoint.root).slot
    (hwf w hw m) (hclos w hw m _) b hbmem
  exact dynamicsChainStruct_body cfg b (hwf w hw m) (hfilt w hw m) hbmem
    (hjc w hw m) hwalk (hcase w hw m hm hH hIH)

/-! ## Section 3 — the smaller residual bundle and the `MechanicalResiduals` assembly

`MechanicalResidualsII` is `MechanicalResiduals` after `ResidualMechanicalII`'s reductions:
`anchor_unscheduled` comes from `WellFormedExecution`, `walk_domain` is derived
from the flat `walk_closure`, and `dynamics_chain` is split into
`dynamics_struct` plus `dynamics_edges`. `justified_known`,
`finalized_known`, `finalized_descent`, `observed_dom` pass through unchanged as
explicit store/FFG inputs. `mechanicalResiduals_of_II` rebuilds
the full `MechanicalResiduals` from `SpecAssumptions` + this bundle. -/

/-- **The reduced residual bundle** (`ResidualMechanicalII`). Relative to
`MechanicalResiduals`, `anchor_unscheduled` comes from `WellFormedExecution`,
`walk_domain` is represented by `walk_closure`, and `dynamics_chain` is split
into structural and per-edge inputs. -/
structure MechanicalResidualsII (E : Execution Root) : Prop where
  /-- The flat ancestor-closure at every honest store and every target slot;
      together with `ParentSlotLt`, it implies `walk_domain`'s `WalkKnown`
      property. -/
  walk_closure : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
    WalkClosure (E.store cfg ext w m) sl
  /-- Justified-knownness per honest store. -/
  justified_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- Finalized-knownness per honest store. -/
  finalized_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- Cross-store finalized descent (Casper finalization consistency). -/
  finalized_descent : ∀ v ∈ E.honest, ∀ k : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, k ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v k).finalized_checkpoint.root) = true
  /-- The observed-justified anchor lies on every later honest justified chain. -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- The structural confirmed-chain per `is_one_confirmed` block (the
      `get_ancestor_roots` parent-link chain — fork-choice-mechanical). -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- The per-edge `DynamicsResidual` supply. -/
  dynamics_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsEdgeSupply cfg ext b (n + 1)

/-- **`MechanicalResiduals` from `SpecAssumptions` + `MechanicalResidualsII`.** All
seven `MechanicalResiduals` fields: `anchor_unscheduled` from
`WellFormedExecution.anchor_parent_unscheduled`; `walk_domain` from
`walkDomain_of_walkClosure` fed by the Layer-0 `store_parentSlotLt` and
`walk_closure`; `dynamics_chain` from `dynamicsChainSupply_of_split` over
`dynamics_struct`/`dynamics_edges`; and the other fields directly from
`MechanicalResidualsII`. -/
theorem mechanicalResiduals_of_II (hSA : SpecAssumptions cfg ext E)
    (hII : E.MechanicalResidualsII cfg ext) : E.MechanicalResiduals cfg ext := by
  obtain ⟨hgen, hwf, _hdiv, _hbeh, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  exact
    { anchor_unscheduled := hwf.anchor_parent_unscheduled
      walk_domain := E.walkDomain_of_walkClosure cfg ext
        (fun w hw m => E.store_parentSlotLt cfg ext hwf hec hgen
          hwf.anchor_parent_unscheduled w m)
        hII.walk_closure
      justified_known := hII.justified_known
      finalized_known := hII.finalized_known
      finalized_descent := hII.finalized_descent
      observed_dom := hII.observed_dom
      dynamics_chain := fun v hv n b hconf =>
        E.dynamicsChainSupply_of_split cfg ext
          (hII.dynamics_struct v hv n b hconf) (hII.dynamics_edges v hv n b hconf) }

end Execution

/-! ## Section 4 — the headline: `Spec_Safety` from `MechanicalResidualsII`

Composing `mechanicalResiduals_of_II` with
`ResidualMechanical.spec_safety_of_mechanical`: the FCR safety guarantee follows
from a proof that every execution's `SpecAssumptions` supplies the reduced bundle
`MechanicalResidualsII`. -/

/-- **`Spec_Safety` from the reduced mechanical residuals.** The input bundle is
`MechanicalResidualsII`, with a flat walk closure and separate structural and
per-edge dynamics-chain fields. -/
theorem spec_safety_of_mechanicalII
    (hmech : ∀ E : Execution Root,
      SpecAssumptions cfg ext E → E.MechanicalResidualsII cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_mechanical cfg ext
    (fun E hSA => E.mechanicalResiduals_of_II cfg ext hSA (hmech E hSA))

end FastConfirmation.Spec

end
