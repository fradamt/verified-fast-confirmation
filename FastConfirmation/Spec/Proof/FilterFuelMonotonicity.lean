module
public import FastConfirmation.Spec.Proof.AnchorClose

@[expose] public section

/-!
# Fuel-monotone filtered-tree membership

Filtered-tree membership grows with the recursion fuel.  This removes the
incorrect requirement that the height of the entire justified subtree be
bounded by the length of one selected-tip chain: a taller sibling branch does
not invalidate membership already established along the selected branch.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

omit [Inhabited Root] in
/-- One more unit of filter fuel preserves both viability and membership. -/
theorem filter_block_tree_aux_mono {store : Store Root} :
    ∀ (fuel : ℕ) (r : Root),
      ((filter_block_tree_aux cfg store fuel r).1 = true →
        (filter_block_tree_aux cfg store (fuel + 1) r).1 = true) ∧
      (∀ x, x ∈ (filter_block_tree_aux cfg store fuel r).2 →
        x ∈ (filter_block_tree_aux cfg store (fuel + 1) r).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro r
    refine ⟨fun h => ?_, fun x hx => ?_⟩
    · exact absurd h (by
        simp [show filter_block_tree_aux cfg store 0 r = (false, []) from rfl])
    · simp only [show filter_block_tree_aux cfg store 0 r = (false, []) from rfl,
        List.not_mem_nil] at hx
  | succ f ih =>
    intro r
    by_cases hne : store.block_roots.filter
        (fun root => (store.blocks root).parent_root = r) = []
    · rw [filter_block_tree_aux_leaf cfg store f r hne,
          filter_block_tree_aux_leaf cfg store (f + 1) r hne]
      exact ⟨id, fun _ hx => hx⟩
    · simp only [filter_block_tree_aux_internal cfg store f r hne,
        filter_block_tree_aux_internal cfg store (f + 1) r hne]
      set C := store.block_roots.filter
        (fun root => (store.blocks root).parent_root = r) with hC
      have hflat : ∀ x,
          x ∈ ((C.map (fun c => filter_block_tree_aux cfg store f c)).map
            Prod.snd).flatten →
          x ∈ ((C.map (fun c => filter_block_tree_aux cfg store (f + 1) c)).map
            Prod.snd).flatten := by
        intro x hx
        rw [List.mem_flatten] at hx ⊢
        obtain ⟨l, hlmem, hxl⟩ := hx
        rw [List.mem_map] at hlmem
        obtain ⟨p, hpmem, hpl⟩ := hlmem
        rw [List.mem_map] at hpmem
        obtain ⟨c, hcC, hpc⟩ := hpmem
        have hxc : x ∈ (filter_block_tree_aux cfg store f c).2 := by
          rw [hpc, hpl]
          exact hxl
        refine ⟨(filter_block_tree_aux cfg store (f + 1) c).2, ?_,
          (ih c).2 x hxc⟩
        rw [List.mem_map]
        exact ⟨filter_block_tree_aux cfg store (f + 1) c,
          List.mem_map.mpr ⟨c, hcC, rfl⟩, rfl⟩
      have hany :
          (C.map (fun c => filter_block_tree_aux cfg store f c)).any Prod.fst = true →
          (C.map (fun c => filter_block_tree_aux cfg store (f + 1) c)).any
            Prod.fst = true := by
        intro h
        rw [List.any_eq_true] at h ⊢
        obtain ⟨p, hpmem, hp1⟩ := h
        rw [List.mem_map] at hpmem
        obtain ⟨c, hcC, hpc⟩ := hpmem
        have hc1 : (filter_block_tree_aux cfg store f c).1 = true := by
          rw [hpc]
          exact hp1
        exact ⟨filter_block_tree_aux cfg store (f + 1) c,
          List.mem_map.mpr ⟨c, hcC, rfl⟩, (ih c).1 hc1⟩
      by_cases hf :
          (C.map (fun c => filter_block_tree_aux cfg store f c)).any Prod.fst = true
      · rw [if_pos hf, if_pos (hany hf)]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        rw [List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (hflat x hx)
        · exact Or.inr hx
      · rw [if_neg hf]
        refine ⟨fun h => absurd h (by simp), fun x hx => ?_⟩
        have hxg := hflat x (by simpa using hx)
        by_cases hg :
            (C.map (fun c => filter_block_tree_aux cfg store (f + 1) c)).any
              Prod.fst = true
        · rw [if_pos hg]
          exact List.mem_append.mpr (Or.inl hxg)
        · rw [if_neg hg]
          exact hxg

omit [Inhabited Root] in
/-- Filter membership is monotone across an arbitrary fuel increase. -/
theorem filter_block_tree_aux_mem_mono {store : Store Root} {r x : Root}
    {fuel fuel' : ℕ} (hle : fuel ≤ fuel')
    (hx : x ∈ (filter_block_tree_aux cfg store fuel r).2) :
    x ∈ (filter_block_tree_aux cfg store fuel' r).2 := by
  induction fuel', hle using Nat.le_induction with
  | base => exact hx
  | succ m _ ih => exact (filter_block_tree_aux_mono cfg m r).2 x ih

omit [Inhabited Root] [LinearOrder Root] in
/-- A `ChainDown` run is parent-linked after its top element. -/
theorem chainDown_isChain {store : Store Root} :
    ∀ (L : List Root) (top : Root), ChainDown store top L →
      List.IsChain (fun a b => (store.blocks b).parent_root = a) L := by
  intro L
  induction L with
  | nil => intro _ _; exact List.IsChain.nil
  | cons c rest ih =>
      intro _ h
      obtain ⟨-, hrest⟩ := h
      cases rest with
      | nil => exact List.IsChain.singleton _
      | cons d rest' =>
          rw [List.isChain_cons_cons]
          exact ⟨hrest.1.2, ih c hrest⟩

omit [Inhabited Root] [LinearOrder Root] in
/-- Every listed root of a `ChainDown` run is known. -/
theorem chainDown_all_known {store : Store Root} :
    ∀ (L : List Root) (top : Root), ChainDown store top L →
      ∀ r ∈ L, r ∈ store.block_roots := by
  intro L
  induction L with
  | nil => simp
  | cons c rest ih =>
      intro top hchain r hr
      obtain ⟨hc, hrest⟩ := hchain
      rw [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hc.1
      · exact ih c hrest r hr

omit [Inhabited Root] in
/-- Filtered membership assembled without a false global-height bound.  The
only fuel comparison is between the duplicate-free selected chain and the
finite list of known block roots. -/
theorem confirmed_mem_filtered_mono {store : Store Root}
    {mids : List Root} {b t : Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot <
          (store.blocks r).slot)
    (hchain : ChainDown store store.justified_checkpoint.root (mids ++ [t]))
    (hb : b ∈ mids ∨ b = t ∨ b = store.justified_checkpoint.root)
    (hnil : store.block_roots.filter
      (fun x => (store.blocks x).parent_root = t) = [])
    (hcj : store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
      (get_voting_source cfg store t).epoch = store.justified_checkpoint.epoch ∨
      (get_voting_source cfg store t).epoch + 2 ≥
        get_current_store_epoch cfg store)
    (hcf : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store t store.finalized_checkpoint.epoch) :
    b ∈ get_filtered_block_tree cfg store := by
  have ht : filter_block_tree_aux cfg store 1 t = (true, [t]) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
      filter_block_tree_aux_leaf cfg store 0 t hnil]
    dsimp only
    split_ifs with hcond
    · rfl
    · refine absurd ?_ hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hcj, hcf⟩
  obtain ⟨L, hL, hsub, hmemtop, hmids⟩ :=
    filter_block_tree_aux_chain_lift cfg ht mids
      store.justified_checkpoint.root hchain
  have hbL : b ∈ L := by
    rcases hb with hb | rfl | rfl
    · exact hmids b hb
    · exact hsub (by simp)
    · exact hmemtop
  have hallknown : ∀ r ∈ mids ++ [t], r ∈ store.block_roots :=
    chainDown_all_known _ _ hchain
  have hLnodup : (mids ++ [t]).Nodup :=
    parentLinkChain_nodup hwf hallknown
      (chainDown_isChain _ _ hchain)
  have hlen : (mids ++ [t]).length ≤ store.block_roots.length :=
    (List.subperm_of_subset hLnodup hallknown).length_le
  have hfuelle : 1 + mids.length + 1 ≤ store.block_roots.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  have hbwrap : b ∈
      (filter_block_tree_aux cfg store (store.block_roots.length + 1)
        store.justified_checkpoint.root).2 := by
    apply filter_block_tree_aux_mem_mono cfg hfuelle
    rw [hL]
    exact hbL
  unfold get_filtered_block_tree
  exact hbwrap

end FastConfirmation.Spec

end
