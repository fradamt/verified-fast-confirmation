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
# Spec / Proof / AnchorClose

This module contains `parentChain_at`, `parentChain_edge_child_slot_gt_head`, `safeFrom_of_headStep` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! The selected closing uses the ancestor-roots case split directly.  Keep its
small walk argument here instead of importing the arbitrary-root engine
module merely for this helper. -/





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















end Execution

/-! ## Section 3 — selected chain-only closing -/













end FastConfirmation.Spec

end
