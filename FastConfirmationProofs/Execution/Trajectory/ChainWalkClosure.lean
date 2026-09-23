module
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant
public import FastConfirmationProofs.Discount.ByzantineBudgetLedger
public import FastConfirmationProofs.Execution.Trajectory.WFTrajectory

@[expose] public section

/-!
# Execution / Trajectory / ChainWalkClosure

Proves chain-walk closure and store dynamics from scheduled handler steps.

This module contains `DynamicsChainSupply`, `MechanicalResiduals` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)




/-! ## Section 2 — finalized tracking from one cross-store residual

`genesis_fin_track` and `finalized_track` are the same statement at two anchors:
each honest store's finalized block is known and descends from an earlier honest
finalized root. Both collapse onto one cross-store finalized-descent residual
`hfin_descent` (`finalized(w, m) ⪰ finalized(v, k)` whenever `k ≤ m`) plus
finalized-knownness `hfin_known`. The genesis anchor `(E.store v 0)` is
`E.genesis_store` by definition — `hfin_descent … 0 …` (with `0 ≤ m`) supplies it,
`hfin_descent … (n+1) …` (with `n+1 ≤ m`) supplies the update anchor. This is the
Casper cross-store finalization-consistency fact represented by
`finalized_descent`. -/











end Execution




end FastConfirmation.Spec

/-!
# Spec / Proof / ResidualMechanicalII

This module contains `isChain_imp_of_mem`, `WalkClosure`, `walkKnown_of_closure` and related declarations.
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












end Execution




end FastConfirmation.Spec

end
