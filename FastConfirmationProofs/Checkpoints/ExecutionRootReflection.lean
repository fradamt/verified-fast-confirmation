module
public import FastConfirmationProofs.Checkpoints.AnchorParentKnownness
public import FastConfirmationProofs.Safety.BlockAgreement
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-!
# Reflection between semantic execution descent and reachable-store ancestry

The block-local FFG model uses `Execution.RootDescends`, while fork choice uses
the executable `is_ancestor` relation of a concrete reachable store.  This
module contains the provenance argument relating the two representations in
the difficult semantic-to-store direction.

The proof follows unique execution parent pointers. `NonAnchorParentKnown`
supplies every intermediate parent. The only exceptional edge is the trusted
anchor's dangling parent, which cannot be a concrete execution root.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Accepted causal-store reflection -/

/-- Block provenance holds at every exact causal prefix, not only at the
ordinary per-second boundary stores. -/
theorem CausalStore.blockProvenance
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    BlockProvenance E store := by
  cases hstore with
  | genesis =>
      intro r hr
      exact Or.inl ⟨hr, rfl⟩
  | scheduledPrefix p =>
      apply blockProvenance_foldl cfg ext
      · intro b hb
        exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hb⟩
      · exact on_tick_blockProvenance cfg _ _
          (E.blockProvenance cfg ext p.node p.previousSecond)

/-- An exact accepted block carrier always exposes its accepted root. -/
theorem AcceptedBlockAt.acceptedRoot
    {r : Root} {b : BeaconBlock Root}
    (h : E.AcceptedBlockAt cfg ext r b) :
    E.AcceptedRoot cfg ext r := by
  obtain ⟨store, hstore, hr, _⟩ := h
  exact ⟨store, hstore, hr⟩

/-- Every accepted root has an exact accepted block carrier. -/
theorem AcceptedRoot.exists_blockAt
    {r : Root} (h : E.AcceptedRoot cfg ext r) :
    ∃ b : BeaconBlock Root, E.AcceptedBlockAt cfg ext r b := by
  obtain ⟨store, hstore, hr⟩ := h
  exact ⟨store.blocks r, store, hstore, hr, rfl⟩

/-- Well-formed executions give a unique concrete message to each accepted
root, even when its two witnesses come from different exact prefixes. -/
theorem AcceptedBlockAt.unique
    (hwf : WellFormedExecution E)
    {r : Root} {b b' : BeaconBlock Root}
    (hb : E.AcceptedBlockAt cfg ext r b)
    (hb' : E.AcceptedBlockAt cfg ext r b') :
    b = b' := by
  obtain ⟨store, hstore, hr, hblock⟩ := hb
  obtain ⟨store', hstore', hr', hblock'⟩ := hb'
  calc
    b = store.blocks r := hblock.symm
    _ = store'.blocks r := hwf.blocks_agree
      hstore.blockProvenance hstore'.blockProvenance hr hr'
    _ = b' := hblock'

/-- At a known root of one exact causal store, accepted block-carrier evidence
is equivalent to carrying that store's concrete message. -/
theorem CausalStore.acceptedBlockAt_iff_eq
    (hwf : WellFormedExecution E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {r : Root} (hr : r ∈ store.block_roots)
    {b : BeaconBlock Root} :
    E.AcceptedBlockAt cfg ext r b ↔ store.blocks r = b := by
  constructor
  · intro hb
    obtain ⟨carrierStore, hcarrierStore, hr', hblock⟩ := hb
    exact (hwf.blocks_agree hstore.blockProvenance
      hcarrierStore.blockProvenance hr hr').trans hblock
  · intro hblock
    exact ⟨store, hstore, hr, hblock⟩

/-- A root known in a reachable store is a concrete `BlockAt` root, with the
message carried by that store. -/
theorem blockAt_of_store_known
    {w : ValidatorIndex} {m : ℕ} {r : Root}
    (hr : r ∈ (E.store cfg ext w m).block_roots) :
    E.BlockAt r ((E.store cfg ext w m).blocks r) := by
  rcases E.blockProvenance cfg ext w m r hr with hgen | hsched
  · exact Or.inl ⟨hgen.1, hgen.2⟩
  · obtain ⟨sb, ⟨u, k, hscheduled⟩, hroot, hmessage⟩ := hsched
    exact Or.inr ⟨u, k, sb, hscheduled, hroot, hmessage.symm⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- Two concrete messages at one execution root agree. -/
theorem blockAt_unique_for_storeReflection
    (hwf : WellFormedExecution E)
    {r : Root} {b b' : BeaconBlock Root}
    (hb : E.BlockAt r b) (hb' : E.BlockAt r b') :
    b = b' := by
  rcases hb with ⟨hr, rfl⟩ | ⟨w, n, sb, hs, hroot, rfl⟩
  · rcases hb' with ⟨_hr', rfl⟩ | ⟨w', n', sb', hs', hroot', rfl⟩
    · rfl
    · have hagree := hwf.genesis_blocks_agree w' n' sb' hs'
          (by simpa only [hroot'] using hr)
      simpa only [hroot'] using hagree.symm
  · rcases hb' with ⟨hr', rfl⟩ | ⟨w', n', sb', hs', hroot', rfl⟩
    · have hagree := hwf.genesis_blocks_agree w n sb hs
          (by simpa only [hroot] using hr')
      simpa only [hroot] using hagree
    · apply hwf.blocks_root_injective w n sb hs w' n' sb' hs'
      exact hroot.trans hroot'.symm

omit [LinearOrder Root] [Inhabited Root] in
/-- Every semantic parent edge out of a root known in a reachable store uses
the same parent pointer as that store's concrete block message. -/
theorem parentEdge_parent_eq_of_store_known_for_storeReflection
    (hwf : WellFormedExecution E)
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    {child parent : Root}
    (hchild : child ∈ store.block_roots)
    (hedge : E.ParentEdge child parent) :
    parent = (store.blocks child).parent_root := by
  have hstoreAt : E.BlockAt child (store.blocks child) := by
    rcases hprovenance child hchild with hgen | hsched
    · exact Or.inl hgen
    · obtain ⟨sb, ⟨w, n, hs⟩, hroot, hblock⟩ := hsched
      exact Or.inr ⟨w, n, sb, hs, hroot, hblock.symm⟩
  rcases hedge with hgen | hsched
  · obtain ⟨r, hr, hchildEq, hparentEq⟩ := hgen
    subst child
    subst parent
    have heq := E.blockAt_unique_for_storeReflection hwf
      (show E.BlockAt r (E.genesis_store.blocks r) from Or.inl ⟨hr, rfl⟩)
      hstoreAt
    exact congrArg BeaconBlock.parent_root heq
  · obtain ⟨w, n, sb, hs, hchildEq, hparentEq⟩ := hsched
    subst child
    subst parent
    have heq := E.blockAt_unique_for_storeReflection hwf
      (show E.BlockAt sb.root sb.message from
        Or.inr ⟨w, n, sb, hs, rfl, rfl⟩)
      hstoreAt
    exact congrArg BeaconBlock.parent_root heq

omit [LinearOrder Root] [Inhabited Root] in
/-- The child of every concrete execution-parent edge is an execution root. -/
theorem ParentEdge.source_executionRoot_for_storeReflection
    {source parent : Root}
    (h : E.ParentEdge source parent) :
    E.ExecutionRoot source := by
  rcases h with ⟨r, hr, hsource, _⟩ | ⟨w, n, sb, hs, hsource, _⟩
  · refine ⟨E.genesis_store.blocks source, Or.inl ⟨?_, rfl⟩⟩
    simpa only [hsource] using hr
  · exact ⟨sb.message, Or.inr ⟨w, n, sb, hs, hsource.symm, rfl⟩⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- The source of a nontrivial execution-parent descent is an execution root;
in the reflexive case this follows from the target being an execution root. -/
theorem RootDescends.source_executionRoot_for_storeReflection
    {source target : Root}
    (h : E.RootDescends source target)
    (htarget : E.ExecutionRoot target) :
    E.ExecutionRoot source := by
  cases h with
  | refl => exact htarget
  | step hedge _ =>
      exact ParentEdge.source_executionRoot_for_storeReflection (E := E) hedge

/-- The dangling parent of the single trusted anchor is not a concrete
execution root. -/
theorem anchorParent_not_executionRoot_for_storeReflection
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) :
    ¬ E.ExecutionRoot ablk.message.parent_root := by
  intro hroot
  obtain ⟨b, hb⟩ := hroot
  rcases hb with hgenBlock | hsched
  · have hmem : ablk.message.parent_root ∈
        (get_forkchoice_store cfg ast ablk).block_roots := by
      simpa only [hgen] using hgenBlock.1
    simp only [get_forkchoice_store, List.mem_singleton] at hmem
    exact hparent hmem
  · obtain ⟨w, n, sb, hs, hrootEq, _⟩ := hsched
    have hgenBlock : E.genesis_store.blocks ablk.root = ablk.message := by
      rw [hgen]
      simp [get_forkchoice_store]
    have hgenParent : (E.genesis_store.blocks ablk.root).parent_root =
        ablk.message.parent_root := congrArg BeaconBlock.parent_root hgenBlock
    exact hwf.anchor_parent_unscheduled ablk.root
      (by rw [hgen]; simp only [get_forkchoice_store, List.mem_singleton])
      w n sb hs (by rw [hrootEq, hgenParent])

/-- A semantic execution ancestor of a known tip is itself known in that
reachable store, and semantic descent is represented by executable ancestry. -/
theorem store_known_ancestor_of_rootDescends_for_storeReflection
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {w : ValidatorIndex} {m : Nat}
    {tip ancestor : Root}
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (hancestorRoot : E.ExecutionRoot ancestor)
    (hdesc : E.RootDescends tip ancestor) :
    ancestor ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root tip) (get_node_for_root ancestor) = true := by
  let store := E.store cfg ext w m
  have hpsl : ParentSlotLt store :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgen, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgen, hslot, hparent⟩ w m
  have hnonAnchor : NonAnchorParentKnown ablk.root store :=
    E.store_nonAnchorParentKnown cfg ext hgen w m
  have hprovenance : BlockProvenance E store := E.blockProvenance cfg ext w m
  have hreflect : ∀ {a b : Root}, E.RootDescends a b →
      a ∈ store.block_roots → E.ExecutionRoot b →
      b ∈ store.block_roots ∧
        is_ancestor store (get_node_for_root a) (get_node_for_root b) = true := by
    intro a b hab
    induction hab with
    | refl r =>
        intro hr _
        exact ⟨hr, is_ancestor_refl store (get_node_for_root r)⟩
    | @step child parent target hedge hrest ih =>
        intro hchild htargetRoot
        have hparentRoot : E.ExecutionRoot parent :=
          RootDescends.source_executionRoot_for_storeReflection
            (E := E) hrest htargetRoot
        have hpEq : parent = (store.blocks child).parent_root :=
          E.parentEdge_parent_eq_of_store_known_for_storeReflection
            hwf hprovenance hchild hedge
        have hchildNeAnchor : child ≠ ablk.root := by
          intro hchildAnchor
          subst child
          have hanchorBlock := E.store_anchor_block cfg ext hwf hgen w m hchild
          have hpEq' : parent = ablk.message.parent_root := by
            change parent =
              ((E.store cfg ext w m).blocks ablk.root).parent_root at hpEq
            rw [hanchorBlock] at hpEq
            exact hpEq
          apply E.anchorParent_not_executionRoot_for_storeReflection
            cfg hwf hgen hparent
          rwa [← hpEq']
        have hparentKnown : parent ∈ store.block_roots := by
          have hp := (hnonAnchor child hchild).resolve_left hchildNeAnchor
          rwa [← hpEq] at hp
        have hstep : is_ancestor store (get_node_for_root child)
            (get_node_for_root parent) = true := by
          apply is_ancestor_of_parent hpsl hchild hparentKnown
          exact hpEq.symm
        obtain ⟨htargetKnown, hrestAncestor⟩ :=
          ih hparentKnown htargetRoot
        exact ⟨htargetKnown, is_ancestor_trans (a := get_node_for_root child)
          (b := get_node_for_root parent) (c := get_node_for_root target) hpsl
          (hwalkK target htargetKnown child hchild)
          (hwalkK target htargetKnown parent hparentKnown)
          hstep hrestAncestor⟩
  exact hreflect hdesc htip hancestorRoot

/-- Converse of `rootDescends_of_store_ancestor` on the actual reachable-store
domain, specialized to callers which already know both endpoints. -/
theorem store_ancestor_of_rootDescends_for_storeReflection
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {w : ValidatorIndex} {m : Nat}
    {tip ancestor : Root}
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (hancestor : ancestor ∈ (E.store cfg ext w m).block_roots)
    (hdesc : E.RootDescends tip ancestor) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root tip) (get_node_for_root ancestor) = true := by
  exact (E.store_known_ancestor_of_rootDescends_for_storeReflection
    cfg ext hwf hec
    hgen hslot hparent htip
    ⟨(E.store cfg ext w m).blocks ancestor,
      E.blockAt_of_store_known cfg ext hancestor⟩ hdesc).2

end Execution

end FastConfirmation.Spec

end
