import FastConfirmation.Spec.Proof.Forks
import FastConfirmation.Spec.Proof.FilterFuel

/-!
# Spec / Proof / FilterViability (E5, slice 1)

Layer 3, filter viability — the spec-side never-filtered argument: blocks on
the confirmed chain survive `filter_block_tree` in honest stores. This first
slice is the *chain-transport mechanics*: `get_checkpoint_block` is constant
along descendants (the walk to an epoch boundary factors through any chain
ancestor at-or-above that boundary), so the `correct_finalized` leaf check
transports from a block to all its descendants. The FFG-export consumption
(`correct_justified` recency at future honest stores) is the next slice.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

omit [Inhabited Root] in
/-- The epoch-boundary walk factors through a chain ancestor at-or-above the
boundary: descendants agree with their ancestors on `get_checkpoint_block`
at every epoch whose first slot is at most the ancestor's slot. -/
theorem get_checkpoint_block_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {d b : Root} {e : Epoch}
    (hanc : is_ancestor store (ForkChoiceNode.mk d) (ForkChoiceNode.mk b) = true)
    (hslot : compute_start_slot_at_epoch cfg e ≤ (store.blocks b).slot)
    (hw : WalkKnown store (compute_start_slot_at_epoch cfg e) d) :
    get_checkpoint_block cfg store d e = get_checkpoint_block cfg store b e := by
  have h1 : get_ancestor store (ForkChoiceNode.mk d) (store.blocks b).slot =
      ForkChoiceNode.mk b := by simpa [is_ancestor] using hanc
  have h2 := get_ancestor_comp hwf hslot hw
  simp only [get_checkpoint_block]
  rw [← h2, h1]

omit [Inhabited Root] in
/-- `correct_finalized` transport: if the finalized block is the finalized-
epoch checkpoint block of `b`'s chain, it is so for every descendant of `b`
(the second `filter_block_tree` leaf conjunct survives chain extension). -/
theorem finalized_check_of_ancestor {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {d b : Root}
    (hanc : is_ancestor store (ForkChoiceNode.mk d) (ForkChoiceNode.mk b) = true)
    (hslot : compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch ≤
      (store.blocks b).slot)
    (hw : WalkKnown store
      (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch) d)
    (hfin : store.finalized_checkpoint.root =
      get_checkpoint_block cfg store b store.finalized_checkpoint.epoch) :
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store d store.finalized_checkpoint.epoch := by
  rw [hfin]
  exact (get_checkpoint_block_of_ancestor cfg hwf hanc hslot hw).symm

/-!
## Filtered membership

The second slice: purely mechanical facts about which roots land in
`get_filtered_block_tree`. `filter_block_tree_aux` returns `(true, l)` exactly on
the viable subtrees, and — read off its two `true`-branches — the queried root is
always among the returned roots `l`, and a viable child's roots are carried up
into the parent's list. Composing that lift along a parent-linked known chain
from the justified root down to a viable tip places every chain element in the
filtered tree. The `TreeBounded` fuel witnesses are taken as hypotheses (they are
supplied downstream from `WellFormedStore`; deriving them is a separate concern).
-/

omit [Inhabited Root] in
/-- A viable `filter_block_tree_aux` result always contains its own query root:
both `true`-branches of the one-step unfold append `block_root` (the internal
branch as `… ++ [block_root]`, the leaf branch as the singleton `[block_root]`). -/
theorem filter_block_tree_aux_true_mem {store : Store Root} {fuel : ℕ} {r : Root}
    {l : List Root} (h : filter_block_tree_aux cfg store (fuel + 1) r = (true, l)) :
    r ∈ l := by
  simp only [filter_block_tree_aux] at h
  split_ifs at h with h1 h2 h3
  · injection h with _ hl; subst hl; simp
  · injection h with hb _; exact absurd hb (by decide)
  · injection h with _ hl; subst hl; simp
  · injection h with hb _; exact absurd hb (by decide)

omit [Inhabited Root] in
/-- A viable child lifts to a viable parent, carrying its root list up: if `c` is
a `block_roots` child of `r` with `filter_block_tree_aux … c = (true, lc)`, then
`filter_block_tree_aux … (fuel + 1) r = (true, lr)` for a list `lr ⊇ lc` that also
contains `r` (the internal `true`-branch: `c`'s viability witnesses
`res.any Prod.fst`, `lc` sits inside the flattened child lists, `r` is appended). -/
theorem filter_block_tree_aux_child_true {store : Store Root} {fuel : ℕ} {r c : Root}
    {lc : List Root}
    (hc_mem : c ∈ store.block_roots.filter (fun x => (store.blocks x).parent_root = r))
    (hc : filter_block_tree_aux cfg store fuel c = (true, lc)) :
    ∃ lr, filter_block_tree_aux cfg store (fuel + 1) r = (true, lr) ∧ lc ⊆ lr ∧ r ∈ lr := by
  have hne : store.block_roots.filter (fun root => (store.blocks root).parent_root = r) ≠ [] :=
    List.ne_nil_of_mem hc_mem
  have hresmem : (true, lc) ∈
      (store.block_roots.filter (fun root => (store.blocks root).parent_root = r)).map
        (fun child => filter_block_tree_aux cfg store fuel child) :=
    List.mem_map.mpr ⟨c, hc_mem, hc⟩
  have hany :
      ((store.block_roots.filter (fun root => (store.blocks root).parent_root = r)).map
        (fun child => filter_block_tree_aux cfg store fuel child)).any Prod.fst = true :=
    List.any_eq_true.mpr ⟨(true, lc), hresmem, rfl⟩
  have hval : filter_block_tree_aux cfg store (fuel + 1) r =
      (true, (((store.block_roots.filter (fun root => (store.blocks root).parent_root = r)).map
        (fun child => filter_block_tree_aux cfg store fuel child)).map Prod.snd).flatten
          ++ [r]) := by
    simp only [filter_block_tree_aux]
    rw [if_pos hne, if_pos hany]
  refine ⟨_, hval, ?_, ?_⟩
  · intro x hx
    refine List.mem_append.mpr (Or.inl ?_)
    exact List.mem_flatten.mpr ⟨lc, List.mem_map.mpr ⟨(true, lc), hresmem, rfl⟩, hx⟩
  · exact List.mem_append.mpr (Or.inr (by simp))

/-- A parent-linked descending run of known children below `top`: each successive
root is a `store.block_roots` child of the previous, the first a child of `top`.
`ChainDown store top (mids ++ [t])` is exactly the structure a `get_ancestor_roots`
chain from the justified root down to `t` provides (all roots known, oldest→newest
parent-linked). -/
def ChainDown (store : Store Root) : Root → List Root → Prop
  | _, [] => True
  | top, c :: rest => (c ∈ store.block_roots ∧ (store.blocks c).parent_root = top) ∧
      ChainDown store c rest

omit [Inhabited Root] in
/-- Chain lift: viability of a tip `t` propagates up a `ChainDown` run to `top`,
one `filter_block_tree_aux_child_true` step per link. The parent's list contains
the tip's list `lt`, `top` itself, and every intermediate `mids` root. Fuel grows
by one per link (`fuelt + mids.length + 1`); the wrapper realigns it downstream. -/
theorem filter_block_tree_aux_chain_lift {store : Store Root} {t : Root}
    {fuelt : ℕ} {lt : List Root}
    (ht : filter_block_tree_aux cfg store fuelt t = (true, lt)) :
    ∀ (mids : List Root) (top : Root), ChainDown store top (mids ++ [t]) →
      ∃ L, filter_block_tree_aux cfg store (fuelt + mids.length + 1) top = (true, L) ∧
        lt ⊆ L ∧ top ∈ L ∧ ∀ e ∈ mids, e ∈ L := by
  intro mids
  induction mids with
  | nil =>
    intro top hchain
    rw [List.nil_append] at hchain
    obtain ⟨⟨htmem, htpar⟩, -⟩ := hchain
    have hcm : t ∈ store.block_roots.filter (fun x => (store.blocks x).parent_root = top) :=
      List.mem_filter.mpr ⟨htmem, by simpa using htpar⟩
    obtain ⟨lr, hlr, hsub, hmemtop⟩ := filter_block_tree_aux_child_true cfg hcm ht
    refine ⟨lr, ?_, hsub, hmemtop, ?_⟩
    · simpa using hlr
    · simp
  | cons m ms ih =>
    intro top hchain
    rw [List.cons_append] at hchain
    obtain ⟨⟨hmmem, hmpar⟩, hrest⟩ := hchain
    obtain ⟨L', hL', hsub', hmemm, hmids'⟩ := ih m hrest
    have hcm : m ∈ store.block_roots.filter (fun x => (store.blocks x).parent_root = top) :=
      List.mem_filter.mpr ⟨hmmem, by simpa using hmpar⟩
    obtain ⟨lr, hlr, hsub, hmemtop⟩ := filter_block_tree_aux_child_true cfg hcm hL'
    refine ⟨lr, ?_, hsub'.trans hsub, hmemtop, ?_⟩
    · have hfuel : fuelt + (m :: ms).length + 1 = fuelt + ms.length + 1 + 1 := by
        simp only [List.length_cons]; omega
      rw [hfuel]; exact hlr
    · intro e he
      rw [List.mem_cons] at he
      rcases he with rfl | he
      · exact hsub hmemm
      · exact hsub (hmids' e he)

omit [Inhabited Root] in
/-- Chain composition to the justified root: given a `ChainDown` run from the
justified root down to a viable tip `t`, every root on the chain — the `mids`, the
tip `t`, and the justified root itself — lands in `get_filtered_block_tree`. Fuel
is realigned to the wrapper's `block_roots.length + 1` via
`filter_block_tree_aux_fuel_eq`, whose `TreeBounded` witness (and the two bounds)
are taken as hypotheses; discharging them from `WellFormedStore` is a separate
concern. -/
theorem chain_mem_get_filtered_block_tree {store : Store Root} {mids : List Root} {t : Root}
    {n fuelt : ℕ} {lt : List Root}
    (hchain : ChainDown store store.justified_checkpoint.root (mids ++ [t]))
    (ht : filter_block_tree_aux cfg store fuelt t = (true, lt))
    (hbound : TreeBounded store store.block_roots n store.justified_checkpoint.root)
    (hn1 : n ≤ store.block_roots.length + 1)
    (hn2 : n ≤ fuelt + mids.length + 1) :
    (∀ e ∈ mids, e ∈ get_filtered_block_tree cfg store) ∧
      t ∈ get_filtered_block_tree cfg store ∧
      store.justified_checkpoint.root ∈ get_filtered_block_tree cfg store := by
  have htmem : t ∈ lt := by
    cases fuelt with
    | zero =>
      have h0 : filter_block_tree_aux cfg store 0 t = (false, []) := rfl
      rw [h0, Prod.mk.injEq] at ht
      exact absurd ht.1 (by decide)
    | succ f => exact filter_block_tree_aux_true_mem cfg ht
  obtain ⟨L, hL, hsub, hmemtop, hmids⟩ :=
    filter_block_tree_aux_chain_lift cfg ht mids store.justified_checkpoint.root hchain
  have halign := filter_block_tree_aux_fuel_eq cfg hbound _ _ hn2 hn1
  rw [halign] at hL
  have hgft : get_filtered_block_tree cfg store = L := by
    unfold get_filtered_block_tree; rw [hL]
  rw [hgft]
  exact ⟨hmids, hsub htmem, hmemtop⟩

omit [Inhabited Root] in
/-- Viable-tip corollary: if `t` is a leaf (no `block_roots` children) whose
`correct_justified`/`correct_finalized` leaf checks hold, then every root on a
`ChainDown` run from the justified root down to `t` is in
`get_filtered_block_tree`. Instantiates `chain_mem_get_filtered_block_tree` with
the leaf's own viability witness `filter_block_tree_aux … 1 t = (true, [t])`. -/
theorem viable_tip_chain_mem {store : Store Root} {mids : List Root} {t : Root} {n : ℕ}
    (hchain : ChainDown store store.justified_checkpoint.root (mids ++ [t]))
    (hnil : store.block_roots.filter (fun x => (store.blocks x).parent_root = t) = [])
    (hcj : store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
      (get_voting_source cfg store t).epoch = store.justified_checkpoint.epoch ∨
      (get_voting_source cfg store t).epoch + 2 ≥ get_current_store_epoch cfg store)
    (hcf : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store t store.finalized_checkpoint.epoch)
    (hbound : TreeBounded store store.block_roots n store.justified_checkpoint.root)
    (hn1 : n ≤ store.block_roots.length + 1)
    (hn2 : n ≤ 1 + mids.length + 1) :
    (∀ e ∈ mids, e ∈ get_filtered_block_tree cfg store) ∧
      t ∈ get_filtered_block_tree cfg store ∧
      store.justified_checkpoint.root ∈ get_filtered_block_tree cfg store := by
  have ht : filter_block_tree_aux cfg store 1 t = (true, [t]) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, filter_block_tree_aux_leaf cfg store 0 t hnil]
    dsimp only
    split_ifs with hcond
    · rfl
    · refine absurd ?_ hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hcj, hcf⟩
  exact chain_mem_get_filtered_block_tree cfg hchain ht hbound hn1 hn2


/-! ## Slice 3: the confirmed block survives the filter (assembly) -/

omit [Inhabited Root] in
/-- E5 assembly: if a parent-linked known chain runs from the justified root
through `b` to a leaf tip `t` whose recency (`correct_justified`) holds — the
`TipRecency` obligation the L4 layer discharges from the FFG exports — and the
finalized leaf check holds at the tip, then the confirmed block `b` is in
`get_filtered_block_tree` (with every other chain element). Instantiates
`viable_tip_chain_mem` and locates `b` inside the run. -/
theorem confirmed_mem_filtered {store : Store Root} {mids : List Root} {b t : Root}
    {n : ℕ}
    (hchain : ChainDown store store.justified_checkpoint.root (mids ++ [t]))
    (hb : b ∈ mids ∨ b = t ∨ b = store.justified_checkpoint.root)
    (hnil : store.block_roots.filter (fun x => (store.blocks x).parent_root = t) = [])
    (hcj : store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
      (get_voting_source cfg store t).epoch = store.justified_checkpoint.epoch ∨
      (get_voting_source cfg store t).epoch + 2 ≥ get_current_store_epoch cfg store)
    (hcf : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store t store.finalized_checkpoint.epoch)
    (hbound : TreeBounded store store.block_roots n store.justified_checkpoint.root)
    (hn1 : n ≤ store.block_roots.length + 1)
    (hn2 : n ≤ 1 + mids.length + 1) :
    b ∈ get_filtered_block_tree cfg store := by
  obtain ⟨hmids, htmem, htop⟩ :=
    viable_tip_chain_mem cfg hchain hnil hcj hcf hbound hn1 hn2
  rcases hb with hb | rfl | rfl
  · exact hmids b hb
  · exact htmem
  · exact htop
end FastConfirmation.Spec
