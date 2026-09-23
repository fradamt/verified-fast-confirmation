module
public import FastConfirmationProofs.FFG.SourceHistory.LaterStoreSupport
public import FastConfirmationProofs.ForkChoice.Head.HeadMembership

@[expose] public section

/-!
# Spec / Proof / EngineStore

A Gloas beacon edge has two selections. The pending parent first selects
EMPTY or FULL. The resolved parent then selects a pending beacon child.
`DescendStep` records both selections, with the parent status determined by
the child's execution bid.

Strict weight domination among beacon siblings does not establish the
payload selection. Opposite-status children can contribute to one payload
branch together. The assembly lemma therefore takes the exact payload
selection as a separate local premise.

A chain of these actual edges gives a `DescendsTo` path. Its distinct beacon
roots fit within the filtered list, and the Gloas head fuel covers both node
steps per beacon edge. The filter-only branch uses root ancestry and permits
any payload status in the final head.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-! ## The per-fork child-choice relation -/

/-- A child's bid resolves its parent's payload as EMPTY or FULL. -/
theorem get_parent_payload_status_ne_pending (store : Store Root)
    (block : BeaconBlock Root) : get_parent_payload_status store block ≠ .pending := by
  simp only [get_parent_payload_status]
  split_ifs <;> decide

/-- One certified Gloas beacon edge. The full-key selection from the pending
parent must choose the status in the child's bid. The pending child must
then strictly dominate the other children of that resolved parent. -/
def DescendStep (store : Store Root) (blocks : List Root) (h c : Root) : Prop :=
  (get_node_children store blocks (ForkChoiceNode.mk h .pending)).argmax
      (fun child => toLex (get_weight cfg store child,
        toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
    some (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) ∧
  ForkChoiceNode.mk c .pending ∈ get_node_children store blocks
    (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) ∧
  ∀ child ∈ get_node_children store blocks
      (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))),
    child ≠ ForkChoiceNode.mk c .pending →
      get_weight cfg store child < get_weight cfg store (ForkChoiceNode.mk c .pending)

namespace DescendStep

variable {cfg : Config}

/-- The beacon child belongs to the candidate list. -/
theorem child_mem {store : Store Root} {blocks : List Root} {h c : Root}
    (hstep : DescendStep cfg store blocks h c) : c ∈ blocks := by
  have hmem := (mem_get_node_children_resolved
    (get_parent_payload_status_ne_pending store (store.blocks c))).mp hstep.2.1
  exact hmem.2.1


/-- Prepend the payload-resolution and beacon-child selections to a path. -/
theorem descendsTo {store : Store Root} {blocks : List Root} {b h c : Root} {n : ℕ}
    (hstep : DescendStep cfg store blocks h c)
    (hrec : DescendsTo cfg store blocks b n c) :
    DescendsTo cfg store blocks b (n + 1) h :=
  DescendsTo.step hstep.1 hstep.2.1 hstep.2.2 hrec

end DescendStep

/-- Assemble one beacon edge from dominance within its resolved payload
branch and an explicit selection of that branch. The payload premise uses
the full Gloas key; per-beacon-sibling dominance alone cannot supply it. -/
theorem descendStep_of_dom {store : Store Root} {blocks : List Root} {h c : Root}
    (hchild : ForkChoiceNode.mk c .pending ∈ get_node_children store blocks
      (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
    (hdom : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children store blocks
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
      c' ≠ c →
        get_weight cfg store (ForkChoiceNode.mk c' .pending) <
          get_weight cfg store (ForkChoiceNode.mk c .pending))
    (hresolve : (get_node_children store blocks (ForkChoiceNode.mk h .pending)).argmax
        (fun child => toLex (get_weight cfg store child,
          toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
      some (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c)))) :
    DescendStep cfg store blocks h c := by
  refine ⟨hresolve, hchild, ?_⟩
  rintro ⟨cr, status⟩ hmem hne
  have hstatus : status = .pending :=
    ((mem_get_node_children_resolved
      (get_parent_payload_status_ne_pending store (store.blocks c))).mp hmem).1
  subst status
  exact hdom cr hmem (fun heq => hne (by rw [heq]))

/-! ## The descent chain builds a `DescendsTo` path -/

/-- A `List.IsChain DescendStep` over `h :: ds` ending at `b` (the last node of
`h :: ds`) is a `Descent.DescendsTo … b ds.length h` path. Structural recursion on
`ds`, `h` general: the `nil` base forces `h = b` (`DescendsTo.here`); each `cons`
peels one dominant child (`DescendsTo.step`) and recurses. -/
theorem descendsTo_of_chain {store : Store Root} {blocks : List Root} {b : Root}
    (hb : b ∈ store.block_roots) :
    ∀ (ds : List Root) (h : Root),
      List.IsChain (DescendStep cfg store blocks) (h :: ds) →
      (h :: ds).getLast (List.cons_ne_nil h ds) = b →
      DescendsTo cfg store blocks b ds.length h := by
  intro ds
  induction ds with
  | nil =>
    intro h _ hlast
    have hhb : h = b := hlast
    subst hhb
    exact DescendsTo.here hb
  | cons a rest ih =>
    intro h hchain hlast
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hstep, hchain'⟩ := hchain
    have hlast' : (a :: rest).getLast (List.cons_ne_nil a rest) = b :=
      (List.getLast_cons (List.cons_ne_nil a rest)).symm.trans hlast
    exact hstep.descendsTo (ih a hchain' hlast')

/-! ## The descent nodes live in the filtered tree -/

/-- Every non-root node on a `DescendStep` chain sits in the candidate list
`blocks`: each is a chosen `get_node_children` member, whose root is drawn from
`blocks` (`mem_get_node_children`). This is the subset feeding the path-length /
fuel bound. -/
theorem chain_descendStep_mem {store : Store Root} {blocks : List Root} :
    ∀ (ds : List Root) (h : Root),
      List.IsChain (DescendStep cfg store blocks) (h :: ds) →
      ∀ c ∈ ds, c ∈ blocks := by
  intro ds
  induction ds with
  | nil => intro _ _ c hc; exact absurd hc List.not_mem_nil
  | cons a rest ih =>
    intro h hchain c hc
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hstep, hchain'⟩ := hchain
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hstep.child_mem
    · exact ih a hchain' c hc

omit [Inhabited Root] in
/-- A `Nodup` list injects into any list it is a subset of, so its length is
bounded (`toFinset` card comparison). The path-length discharge for the fuel
hypothesis of `Descent.is_ancestor_get_head`. -/
private theorem length_le_of_nodup_subset {l₁ l₂ : List Root}
    (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  have hfs : l₁.toFinset ⊆ l₂.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hsub hx
  exact le_trans (Finset.card_le_card hfs) (List.toFinset_card_le (l := l₂))

/-! ## The headline: the head descends from `b` -/

/-- A chain of actual payload selections and dominant beacon children from
the justified root to `b` forces the head to descend from `b`. Distinct chain
roots bound the beacon depth; the Gloas fuel then covers both node steps of
each edge. The statement uses the existing store and filter conditions. -/
theorem is_ancestor_get_head_of_chain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  have hdesc := descendsTo_of_chain cfg hb ds store.justified_checkpoint.root hchain hlast
  have hmem := chain_descendStep_mem cfg ds store.justified_checkpoint.root hchain
  have hfuel : ds.length ≤ (get_filtered_block_tree cfg store).length + 1 :=
    Nat.le_succ_of_le (length_le_of_nodup_subset hnd (fun c hc => hmem c hc))
  change is_ancestor store (get_head cfg store) (ForkChoiceNode.mk b .pending) = true
  exact is_ancestor_get_head cfg hwf hsub hdesc hfuel

/-! ## The filter complement: filtered roots descend from the justified root

The FFG branch uses the filter rather than the LMD margin. Once the justified checkpoint's block is
on `b`'s chain in an honest store, every filtered branch descends from the
justified root, so the head — itself a filtered root — descends from `b`, with
no weight accounting.

The walk-known plumbing enters as one blanket hypothesis `hwalk`: the store is
ancestor-closed, so every known root's parent-walk down to any terminal slot
stays known (the `WalkKnown` ∀-form the toolkit sanctions). -/

omit [Inhabited Root] in
/-- One parent step of `is_ancestor`: a known block whose `parent_root` is a
known block `base` descends from `base`. The walk from the child down to
`base`'s slot steps once (to `base`) and stops; the strict slot drop
`base.slot < child.slot` comes from `hwf` (`parent_slot_lt`). -/
theorem is_ancestor_of_parent {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {child base : Root}
    (hchild : child ∈ store.block_roots) (hbase : base ∈ store.block_roots)
    (hp : (store.blocks child).parent_root = base) :
    is_ancestor store (ForkChoiceNode.mk child .pending) (ForkChoiceNode.mk base .pending) = true := by
  rw [is_ancestor_pending, decide_eq_true_eq]
  have hlt : (store.blocks base).slot < (store.blocks child).slot := by
    have h := hwf child hchild (by rw [hp]; exact hbase)
    rwa [hp] at h
  rw [get_ancestor_step hwf hchild hlt
    (by rw [hp]; exact WalkKnown.stop hbase (le_refl _))]
  rw [hp, get_ancestor_stop (le_refl _)]





end FastConfirmation.Spec

end
