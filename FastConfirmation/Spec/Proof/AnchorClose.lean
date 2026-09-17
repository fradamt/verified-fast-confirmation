import FastConfirmation.Spec.Proof.AnchorThread
import FastConfirmation.Spec.Proof.Assembly
import FastConfirmation.Spec.Proof.Reanchor
import FastConfirmation.Spec.Proof.HeadRerootChain
import FastConfirmation.Spec.Proof.SameSlotProvenance
import FastConfirmation.Spec.Proof.Knownness

/-!
# Spec / Proof / AnchorClose: the closing composition

This module holds the anchor-scoped `SafeFrom` machinery for the `get_latest_confirmed` output:
the per-edge `DescendStep` supplies, the confirm-margin collapse, the anchor-scoped covering
supply, and the two glc folds `safeFromGlc_of_covSupply` / `safeFromGlc_of_chainSupply`.

The eight closing theorems that used to sit on top of them (`Spec_Safety_of_chainSupply`,
`_of_close`, `_of_confirmMargin`, `_of_chainConfirmMargin` and their `Spec_Monotonicity_*`
companions) are **deleted** (P-6): each refined `AnchorThread.Spec_Safety_of_anchored` and so
carried the never-produced ahead-regime head-tracking premise. See the section note below and
`docs/p6-justified-descends-derivation.md` §8.

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

omit [Inhabited Root] in
private theorem roots_isSome_of_ancestor_selected {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {t r : Root} (hw : WalkKnown store (store.blocks t).slot r) :
    get_ancestor store (ForkChoiceNode.mk r) (store.blocks t).slot = ForkChoiceNode.mk t →
    ∀ fuel : ℕ, (store.blocks r).slot < fuel →
      (get_ancestor_roots_aux store t fuel r).isSome = true ∨ r = t := by
  induction hw with
  | stop hr hle =>
    intro hanc _ _
    rw [get_ancestor_stop hle] at hanc
    exact Or.inr (by simpa using hanc)
  | @step r hr hgt hp ih =>
    intro hanc fuel hfuel
    rw [get_ancestor_step hwf hr hgt hp] at hanc
    cases fuel with
    | zero => exact absurd hfuel (Nat.not_lt_zero _)
    | succ f =>
      rw [get_ancestor_roots_aux_succ, if_pos hgt]
      by_cases hD : (store.blocks r).parent_root = t
      · rw [if_pos hD]; exact Or.inl rfl
      · rw [if_neg hD]
        have hbound : (store.blocks (store.blocks r).parent_root).slot < f :=
          Nat.lt_of_lt_of_le (hwf r hr hp.root_mem) (Nat.lt_succ_iff.mp hfuel)
        rcases ih hanc f hbound with hsome | hpeq
        · left
          obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
          rw [hl]
          rfl
        · exact absurd hpeq hD

omit [Inhabited Root] in
private theorem hcase_of_ancestor_selected {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {b jc : Root} (hwalk : WalkKnown store (store.blocks jc).slot b)
    (hanc : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk jc) = true) :
    get_ancestor_roots store b jc ≠ [] ∨ b = jc := by
  simp only [is_ancestor, decide_eq_true_eq] at hanc
  rcases roots_isSome_of_ancestor_selected hwf hwalk hanc
      ((store.blocks b).slot + 1) (Nat.lt_succ_self _) with hsome | heq
  · left
    rw [get_ancestor_roots]
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hsome
    rw [hl]
    change l ≠ []
    exact (get_ancestor_roots_aux_chain hwf hwalk _ (Nat.lt_succ_self _) l hl).1
  · exact Or.inr heq

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

/-- **Mid-walk head descent from the r₀-scoped edge supply.** Re-rooted at an arbitrary node `x`
on `b`'s chain with `x ⪰ jc.root`, `x ⪰ r₀`,
and `head ⪰ x`: the parent-link chain `x → b` (`parentChain_at`) lifts to a `DescendStep` chain
edge-wise (each edge child `c` descends from `x` by `get_ancestor_roots_descends`, hence from `r₀`
by transitivity — the scoping premise `hedge` consumes), which
`HeadRerootChain.head_ge_of_intermediate_ledger` folds to `head ⪰ b`. The mid-chain instance is
`x = jc.root` (`head ⪰ jc.root` from the filter takeover); the deleted covering fold also used
`x = r₀`. -/
theorem head_ge_of_scoped_terminal {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r₀ x b : Root} (hr₀ : r₀ ∈ store.block_roots) (hx : x ∈ store.block_roots)
    (hb : b ∈ store.block_roots)
    (hx_jc : is_ancestor store (get_node_for_root x)
      (get_node_for_root store.justified_checkpoint.root) = true)
    (hx_r₀ : is_ancestor store (get_node_for_root x) (get_node_for_root r₀) = true)
    (hhead_x : is_ancestor store (get_head cfg store) (get_node_for_root x) = true)
    (hbx : is_ancestor store (get_node_for_root b) (get_node_for_root x) = true)
    (hedge : ∀ a c : Root, a ∈ store.block_roots → c ∈ store.block_roots →
      (store.blocks c).parent_root = a →
      is_ancestor store (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
      DescendStep cfg store (get_filtered_block_tree cfg store) a c) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  have hbx' : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk x) = true := by
    simpa only [get_node_for_root] using hbx
  have hcase := hcase_of_ancestor_selected hwf (hwalkK x hx b hb) hbx'
  obtain ⟨hmem, hchainPL, hlast⟩ := parentChain_at hwf hwalkK hx hb hcase
  have hlast? : (x :: get_ancestor_roots store b x).getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast]
  have hchainDS : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (x :: get_ancestor_roots store b x) := by
    refine isChain_imp_of_mem hchainPL ?_
    intro a ha c hc hlink
    have hb_c := Execution.mem_isAncestor_of_parentChain hwf hwalkK hb hchainPL hmem hlast? c hc
    have hc_r₀ : is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true := by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hx_r₀
      · have hcx := get_ancestor_roots_descends hwf hwalkK hx hb hc'
        exact is_ancestor_trans hwf (hwalkK r₀ hr₀ c (hmem c hc))
          (hwalkK r₀ hr₀ x hx) hcx hx_r₀
    have hxLtC := parentChain_edge_child_slot_gt_head hwf hmem hchainPL ha hc hlink
    have hr₀LeX : (store.blocks r₀).slot ≤ (store.blocks x).slot := by
      have hsle := get_ancestor_slot_le hwf (hwalkK r₀ hr₀ x hx)
      have hlands : get_ancestor store (ForkChoiceNode.mk x)
          (store.blocks r₀).slot = ForkChoiceNode.mk r₀ := by
        simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hx_r₀
      rw [hlands] at hsle
      simpa using hsle
    have hcNeR₀ : c ≠ r₀ := by
      intro heq
      subst c
      exact (Nat.not_lt_of_ge hr₀LeX) hxLtC
    exact hedge a c (hmem a ha) (hmem c hc) hlink hb_c hc_r₀ hcNeR₀
  exact head_ge_of_intermediate_ledger cfg hwf hsub hwalkK hjust hx hx_jc hhead_x hb
    hchainDS hlast

/-- **Mid-walk head descent from an already-safe anchor.** If the current head already descends
from `r₀`, the `r₀`-scoped `DescendStep` chain from `r₀` to `b` carries that descent through to
`b`. When `r₀` itself descends from the store's justified root this is exactly
`head_ge_of_intermediate_ledger`. In the opposite orientation, the first dominant child is a
filtered root and hence descends from the justified root; the parent/child squeeze makes the
justified root either `r₀` or that first child, after which the same mid-walk lemma consumes the
whole chain or its tail. -/
theorem head_ge_of_safe_scoped_terminal {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    (hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hjust : store.justified_checkpoint.root ∈ store.block_roots)
    {r₀ b : Root} (hr₀ : r₀ ∈ store.block_roots) (hb : b ∈ store.block_roots)
    (hhead_r₀ : is_ancestor store (get_head cfg store) (get_node_for_root r₀) = true)
    (hb_r₀ : is_ancestor store (get_node_for_root b) (get_node_for_root r₀) = true)
    (hedge : ∀ a c : Root, a ∈ store.block_roots → c ∈ store.block_roots →
      (store.blocks c).parent_root = a →
      is_ancestor store (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
      DescendStep cfg store (get_filtered_block_tree cfg store) a c) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true := by
  have hb_r₀' : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk r₀) = true := by
    simpa only [get_node_for_root] using hb_r₀
  have hcase := hcase_of_ancestor_selected hwf (hwalkK r₀ hr₀ b hb) hb_r₀'
  obtain ⟨hmem, hchainPL, hlast⟩ := parentChain_at hwf hwalkK hr₀ hb hcase
  have hlast? : (r₀ :: get_ancestor_roots store b r₀).getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast]
  have hchainDS : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (r₀ :: get_ancestor_roots store b r₀) := by
    refine isChain_imp_of_mem hchainPL ?_
    intro a ha c hc hlink
    have hb_c := Execution.mem_isAncestor_of_parentChain hwf hwalkK hb hchainPL hmem hlast? c hc
    have hc_r₀ : is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true := by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact is_ancestor_refl store _
      · exact get_ancestor_roots_descends hwf hwalkK hr₀ hb hc'
    have hr₀LtC := parentChain_edge_child_slot_gt_head hwf hmem hchainPL ha hc hlink
    have hcNeR₀ : c ≠ r₀ := by
      intro heq
      subst c
      exact (lt_irrefl _) hr₀LtC
    exact hedge a c (hmem a ha) (hmem c hc) hlink hb_c hc_r₀ hcNeR₀
  have finish (hr₀_jc : is_ancestor store (get_node_for_root r₀)
      (get_node_for_root store.justified_checkpoint.root) = true) :
      is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
    head_ge_of_intermediate_ledger cfg hwf hsub hwalkK hjust hr₀ hr₀_jc hhead_r₀ hb
      hchainDS hlast
  cases hs : get_ancestor_roots store b r₀ with
  | nil =>
      have hr₀b : r₀ = b := by simpa [hs] using hlast
      simpa [hr₀b] using hhead_r₀
  | cons c ds =>
      have hchainDS' : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
          (r₀ :: c :: ds) := by simpa [hs] using hchainDS
      rw [List.isChain_cons_cons] at hchainDS'
      obtain ⟨hstep, hchainTail⟩ := hchainDS'
      have hchainPL' : List.IsChain (fun a c => (store.blocks c).parent_root = a)
          (r₀ :: c :: ds) := by simpa [hs] using hchainPL
      rw [List.isChain_cons_cons] at hchainPL'
      have hpar : (store.blocks c).parent_root = r₀ := hchainPL'.1
      have hcmem : c ∈ store.block_roots := hmem c (by simp [hs])
      have hcfilter : c ∈ get_filtered_block_tree cfg store :=
        (mem_get_node_children.mp hstep.1).1
      have hc_jc : is_ancestor store (get_node_for_root c)
          (get_node_for_root store.justified_checkpoint.root) = true :=
        filtered_through_justified_K cfg hwf hwalkK hjust hcfilter
      have hc_r₀ : is_ancestor store (get_node_for_root c) (get_node_for_root r₀) = true :=
        is_ancestor_of_parent hwf hcmem hr₀ hpar
      have hc_jc' : get_ancestor store (ForkChoiceNode.mk c)
          (store.blocks store.justified_checkpoint.root).slot =
            ForkChoiceNode.mk store.justified_checkpoint.root := by
        simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hc_jc
      have hc_r₀' : get_ancestor store (ForkChoiceNode.mk c) (store.blocks r₀).slot =
          ForkChoiceNode.mk r₀ := by
        simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hc_r₀
      rcases reroot_comparable hwf
          (hwalkK r₀ hr₀ c hcmem)
          (hwalkK store.justified_checkpoint.root hjust c hcmem) hc_r₀' hc_jc' with
        hjc_r₀ | hr₀_jc
      · rcases reroot_child_squeeze hwf hwalkK hjust hr₀ hcmem hpar hjc_r₀ hc_jc' with
          hjceq | hjceq
        · apply finish
          simpa only [hjceq] using is_ancestor_refl store (get_node_for_root r₀)
        · have hhead_c : is_ancestor store (get_head cfg store) (get_node_for_root c) = true :=
            head_ge_of_justified_ge_K cfg hwf hwalkK hjust hcmem (by
              simpa only [hjceq] using is_ancestor_refl store (get_node_for_root c))
          have hlastTail : (c :: ds).getLast (List.cons_ne_nil c ds) = b := by
            have hlast' := hlast
            rw [hs, List.getLast_cons (List.cons_ne_nil c ds)] at hlast'
            exact hlast'
          exact head_ge_of_intermediate_ledger cfg hwf hsub hwalkK hjust hcmem hc_jc hhead_c hb
            hchainTail hlastTail
      · apply finish
        simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hr₀_jc

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

/-- **The per-`b`-chain-edge `DescendStep` supply** — the transparent engine interface. The
`INVstarTrack.ForkEdgeGroundSupply` shape with the existential `ForkEdgeGroundInputs` per edge
replaced by the `DescendStep` it lifts to. Under the shell head-safety IH, every real parent edge
`a ← c` of known blocks **whose child `c` is on `b`'s chain** (`is_ancestor store b c`) carries a
fork-choice descent step `DescendStep cfg (store w m) (filtered) a c`. The `b`-chain scope is the
chain scope ensures that losing siblings appear only as `hsib` recorded-bound objects, never as descent subjects.
The confirm-margin collapse (`Dominance.descendStep_of_confirmMargin` /
`Assembly.descendStep_of_assemblyResidual`) is its per-edge producer.

The supply carries the **anchor-root parameter `r₀`**
and the **per-edge scoping premise** `c ⪰ r₀` (`is_ancestor (store w m) c r₀`) before the
`DescendStep` conclusion: the producer (the L4 `find_latest_confirmed_descendant` walk, whose
certificates live **only** on the segment `[r₀, glc]`) is faced **only** with edges whose child `c`
descends from the reset anchor `r₀` — never the cert-less deep edges above `r₀`. The 4-case fold
(`safeFromGlc_of_covSupply`) only ever demands `c ⪰ r₀` edges: case (ii) walks `[jc.root, b]` with
`jc.root ⪰ r₀`, case (iii) walks `[r₀, b]`. -/
def DescendStepChainSupply (E : Execution Root) (b r₀ : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
        DescendStep cfg (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m)) a c

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

/-- **The per-`b`-chain-edge confirm-margin supply** — the transparent, fully-unfolded
engine interface. Under the shell head-safety IH, every real
parent edge `a ← c` of known blocks whose child `c` is on `b`'s chain carries, **at the edge child
`c` as subject**: using terminal `b` as the subject would force `lo = parent(b).slot+1`,
incompatible with the per-edge confinement windows `lo ≤ sibling.slot`; subject `c` gives
`lo = parent(c).slot+1 = a.slot+1`, per-edge coherent — modelled on `ChainInput.LedgerCertInput`), a
**regime disjunction**, because the strong aggregate `hbudget` need not hold cross-epoch:

* **same-epoch arm** (`epochOf lo = epochOf σ`, the **whole** window `[lo, σ]` one epoch):
  `epochOf lo = epochOf σ` forces every slot of `[lo, σ]` to share
  `lo`'s epoch, exactly the per-slot `hsame` shape the growth producers
  `Growth.hbudget_sameEpoch`/`hgrowS_of_engine`/`hgrowX_of_engine` consume; a boundary-straddling
  edge — `epochOf lo < epochOf σ` — no longer qualifies here and routes through the crossing arm,
  which re-anchors at `slot(c)`): the plain confirm-margin strip `hstrip0`
  (`Base.weak_base_of_rule`, subject `c`) at a confirming anchor `(v₀, n₀')` over `[lo, es]`, the
  block-root containment `hsub`, the two walk-domain functions `hdomS`/`hdomA` (subject `c`), the
  three aggregate window-growth facts `hgrowS`/`hgrowX`/`hbudget` (`hbudget` producible by
  `Growth.hbudget_sameEpoch`), the child membership `hchild`, the recorded-support transport
  `hSmem`, and the sibling confinements `hHon`/`hByz`. Routed via
  `Assembly.descendStep_of_assemblyResidual`.
* **crossing arm**: the exact `Reanchor.crossing_ledger_descendStep` input bundle — the child lower
  bound `hbside`, the re-anchored endpoint inequality `hend` (subject `c`, over `[lo, σ]`, with the
  pre-region old-sibling backers `xP`/`Bpre`), and the per-sibling recorded upper bound `hsib`. This
  carries the taxed/re-anchored form that survives cross-epoch. Routed via
  `Reanchor.crossing_ledger_descendStep` directly.

Both arms produce the **same** `DescendStep cfg (store w m) (filtered) a c`. **No** arms disjunction
of the old `INVstar` kind, **no** min-reserve `INVstar`.

The bundle carries the anchor-root parameter `r₀` and the
per-edge scoping premise `c ⪰ r₀` before the regime existential, so the confirm-margin producer
(certificates on `[r₀, glc]` only, `CertExtract.edgeCert_of_confirmation`) is faced only with
`[r₀, glc]`-segment edges — never the cert-less deep edges above `r₀`. -/
def ForkEdgeConfirmMarginSupply (E : Execution Root) (b r₀ : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root c) = true →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root c) (get_node_for_root r₀) = true →
      c ≠ r₀ →
        -- same-epoch arm (subject `c`, `lo = a.slot+1`, plain strip + aggregate growth budget)
        (∃ (v₀ : ValidatorIndex) (n₀' : ℕ) (lo es σ : Slot),
          compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg σ ∧
          ((E.store cfg ext v₀ n₀').block_roots ⊆ (E.store cfg ext w m).block_roots) ∧
          c ∈ (E.store cfg ext v₀ n₀').block_roots ∧
          (∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀')
              (get_node_for_root r) (get_node_for_root c) = true →
            r ∈ (E.store cfg ext v₀ n₀').block_roots ∧
              WalkKnown (E.store cfg ext v₀ n₀') ((E.store cfg ext v₀ n₀').blocks c).slot r) ∧
          (∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀')
              (get_node_for_root c) (get_node_for_root r) = true →
            r ∈ (E.store cfg ext v₀ n₀').block_roots ∧
              WalkKnown (E.store cfg ext v₀ n₀') ((E.store cfg ext v₀ n₀').blocks r).slot c) ∧
          (E.Xval cfg ext v₀ n₀' c lo es + E.Bval lo es
              + get_proposer_score cfg (E.store cfg ext w m) + 1
            ≤ E.Sval cfg ext v₀ n₀' c lo es) ∧
          (E.Sval cfg ext w m c lo es + (E.Jspec lo σ - E.Jspec lo es)
            ≤ E.Sval cfg ext w m c lo σ) ∧
          (E.Xval cfg ext w m c lo σ ≤ E.Xval cfg ext w m c lo es) ∧
          ((100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
            ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es)) ∧
          (ForkChoiceNode.mk c ∈ get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a)) ∧
          (∀ i ∈ E.Sclass cfg ext w m c lo σ,
            i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
              ((E.store cfg ext w m).checkpoint_states
                (E.store cfg ext w m).justified_checkpoint)) ∧
          (∀ c' : Root,
            ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
              (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a) →
            c' ≠ c →
            ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
              ((E.store cfg ext w m).checkpoint_states
                (E.store cfg ext w m).justified_checkpoint),
              i ∈ E.honest → i ∈ E.Xclass cfg ext w m c lo σ) ∧
          (∀ c' : Root,
            ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
              (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a) →
            c' ≠ c →
            ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
              ((E.store cfg ext w m).checkpoint_states
                (E.store cfg ext w m).justified_checkpoint),
              i ∉ E.honest → i ∈ E.Bwin lo σ)) ∨
        -- crossing arm (subject `c`, re-anchored `[lo, σ]`; via crossing_ledger_descendStep)
        (∃ (v₀ : ValidatorIndex) (n₀' : ℕ) (lo σ : Slot) (xP Bpre : ℕ),
          (ForkChoiceNode.mk c ∈ get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a)) ∧
          (E.Sval cfg ext v₀ n₀' c lo σ ≤
            get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
              ((E.store cfg ext w m).checkpoint_states
                (E.store cfg ext w m).justified_checkpoint)) ∧
          (xP + E.Xval cfg ext v₀ n₀' c lo σ + Bpre + E.Bval lo σ
              + get_proposer_score cfg (E.store cfg ext w m) + 1
            ≤ E.Sval cfg ext v₀ n₀' c lo σ) ∧
          (∀ c' : Root,
            ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
              (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk a) →
            c' ≠ c →
            get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
                ((E.store cfg ext w m).checkpoint_states
                  (E.store cfg ext w m).justified_checkpoint)
              ≤ xP + E.Xval cfg ext v₀ n₀' c lo σ + Bpre + E.Bval lo σ))

/-- **`ForkEdgeConfirmMarginSupply ⟹ DescendStepChainSupply`** — the confirm-margin
collapse wired, both regimes. Each `b`-chain edge's residual bundle is composed to a `DescendStep`:
the **same-epoch arm** through `Assembly.descendStep_of_assemblyResidual` (the plain confirm-margin
strip at subject `c` + the three aggregate growth facts, no arms, no min-reserve `INVstar`), the
**crossing arm** through `Reanchor.crossing_ledger_descendStep` directly (the re-anchored/taxed form
that survives cross-epoch). Both arms yield the identical `(a, c)`-edge `DescendStep` the chain fold
consumes. The endpoint/edge quantification and the shell head-safety IH pass through unchanged. -/
theorem descendStepChainSupply_of_confirmMargin (hSA : SpecAssumptions cfg ext E)
    {b r₀ : Root} {n₀ : ℕ}
    (hsupply : E.ForkEdgeConfirmMarginSupply cfg ext b r₀ n₀) :
    E.DescendStepChainSupply cfg ext b r₀ n₀ := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, _hsv, hbb, hji⟩ := hSA
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _, _⟩ := hgen
    exact ⟨ast, ablk, hgeq⟩
  intro w hw m hm hH hIH a c ha hc hlink hscope hscope_r₀ hcne
  rcases hsupply w hw m hm hH hIH a c ha hc hlink hscope hscope_r₀ hcne with
    ⟨v₀, n₀', lo, es, σ, _hsame, hsub, hb', hdomS, hdomA, hstrip0, hgrowS, hgrowX, hbudget,
      hchild, hSmem, hHon, hByz⟩
    | ⟨v₀, n₀', lo, σ, xP, Bpre, hchild, hbside, hend, hsib⟩
  · exact E.descendStep_of_assemblyResidual cfg ext hec hgen0 hji hwfE hw hH
      hsub hb' hdomS hdomA hstrip0 hgrowS hgrowX hbudget hchild hSmem hHon hByz
  · exact E.crossing_ledger_descendStep cfg ext hchild hbside hend hsib

/-! ## Section 2 — the anchor-scoped covering supply and `hdisj_glc`

`hdisj_glc` is discharged through the **anchoring covering route**: at the confirming store the
`get_latest_confirmed` block descends from one of the three reset anchors
(`Anchoring.get_latest_confirmed_ge`, hence `AnchorThread.confirmedWithAnchor_of_advance`), so the
`b ⪰ jcb.root` conjunct of `Execution.CoveringFFG` is the transported anchoring, not a free
hypothesis. The three reset-anchor knownness facts and the confirmed-block knownness are discharged
internally; the covering flag shrinks to the **anchor-scoped** supply `AnchorCovSupply`. -/

/-- **The anchor-scoped covering supply** — the `hcov` hypothesis of
the covering advance leg, DRY-named. For every confirmed `get_latest_confirmed` block `glc` at a
foreign endpoint `(w, m)` and the actual reset anchor `r₀`, it carries the block-root containment
transport and reverse walk, followed by one of three kind-tagged routes. The confirmed and
finalized routes contain `head ⪰ r₀`, produced directly by the two threaded `SafeFrom` witnesses;
the observed route retains the covering checkpoint `jcb` (`jcb.root = r₀`, `JustifiedIn`/known)
and **the covering disjunction** `glc ⪰ jc.root ∨ jc.root ⪰ glc`. The `glc ⪰ r₀` conjunct is
transported separately from `hanc.b_ge_r₀` in `safeFromGlc_of_covSupply`.

The two case-(i) instruments —
the unconditional head witness (`get_checkpoint_block head jc.epoch = jc.root`) and the slot bound
(`glc.slot ≤ start_slot(jc.epoch)`, **FALSE for a fresh `glc` at a store with an older `jc`**) — are
**deleted**: they were wrongly demanded globally. In their place the derivable **covering
disjunction** drove case (i) of the (now deleted) covering fold: `jc.root ⪰ glc` off the
disjunction gives `head ⪰ jc.root ⪰ glc` with no geometry, and `glc ⪰ jc.root` drives the chain
branch. The observed route no longer consumes it (it finishes from the threaded `hobs`).

For the observed route, the disjunction is derivable under the **head-safety IH clause**
(`∀ w' m', n+1 ≤ m' → slot_at m' < slot_at m → head(w',m') ⪰ glc`), added as a hypothesis
**before** the route result, so a producer may assume head-safety at strictly-earlier slots (the
quorum route:
`justified_requires_targets` → an honest quorum member's earlier-slot head ⪰ `glc` via the IH →
`Delivery.honest_attestation_data_target_root` ties their FFG target to their head-chain boundary).
The confirmed/finalized routes do not consume that quorum route: the fold threads their `SafeFrom`
witnesses to this production point. Consumption runs **inside** the head-safety induction, where
the IH remains available for the observed route and the per-edge supply. The endpoint relay
premise is exact: endpoints that have not reached the one-slot delivery deadline bypass this
supply and use selected-candidate support/vote provenance plus the three threaded `SafeFrom`
witnesses. -/
def AnchorCovSupply (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ,
    get_current_slot cfg (E.store cfg ext v (n + 1)) > get_current_slot cfg (E.store cfg ext v n) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n))
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true →
    E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1) →
    E.SafeFrom cfg ext (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1) →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1) →
      ∀ r₀ : Root,
        (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
          r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
          r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
        E.ConfirmedWithAnchor cfg ext
          (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) →
        (∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
          E.WithinHorizon cfg m' →
          is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
            (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true) →
        ((E.store cfg ext v (n + 1)).block_roots ⊆ (E.store cfg ext w m).block_roots) ∧
        WalkKnown (E.store cfg ext v (n + 1))
            ((E.store cfg ext v (n + 1)).blocks r₀).slot
            (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) ∧
        ((r₀ = (E.fcrStep cfg ext v n).confirmed_root ∧
            is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
              (get_node_for_root r₀) = true) ∨
          (r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∧
            is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
              (get_node_for_root r₀) = true) ∨
          (r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∧
            ∃ jcb : Checkpoint Root,
              jcb.root = r₀ ∧
              JustifiedIn (E.store cfg ext w m) jcb ∧
              jcb.root ∈ (E.store cfg ext w m).block_roots ∧
              -- **The covering disjunction**, retained only for the
              -- observed-anchor route. The confirmed/finalized routes use their threaded
              -- `SafeFrom` witnesses above and do not demand this quorum-derived comparison.
              (is_ancestor (E.store cfg ext w m)
                  (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)))
                  (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true ∨
                is_ancestor (E.store cfg ext w m)
                  (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
                  (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) =
                    true)))

/-- **Confirmed-anchor covering from the trajectory invariant.** At every later honest endpoint,
the fold's pre-update confirmed-root `SafeFrom` witness is exactly `head ⪰ r₀` when the actual
L4 anchor is the confirmed root. This is the no-quorum covering producer for that anchor kind. -/
theorem confirmedAnchorCov_of_safeFrom
    {v : ValidatorIndex} {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hm : n + 1 ≤ m) (hH : E.WithinHorizon cfg m) {r₀ : Root}
    (hkind : r₀ = (E.fcrStep cfg ext v n).confirmed_root)
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1)) :
    r₀ = (E.fcrStep cfg ext v n).confirmed_root ∧
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root r₀) = true := by
  refine ⟨hkind, ?_⟩
  simpa only [hkind] using hprev w hw m hm hH

/-- **Finalized-anchor covering from the trajectory invariant.** At every later honest endpoint,
the fold's finalized-root `SafeFrom` witness is exactly `head ⪰ r₀` when the actual L4 anchor is
the finalized root. This is the no-quorum covering producer for that anchor kind. -/
theorem finalizedAnchorCov_of_safeFrom
    {v : ValidatorIndex} {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hm : n + 1 ≤ m) (hH : E.WithinHorizon cfg m) {r₀ : Root}
    (hkind : r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root)
    (hfin : E.SafeFrom cfg ext
      (E.store cfg ext v (n + 1)).finalized_checkpoint.root (n + 1)) :
    r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∧
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root r₀) = true := by
  refine ⟨hkind, ?_⟩
  simpa only [hkind] using hfin w hw m hm hH

/-- **The confirming-store reset-anchor knownness, discharged.** At the update store `(v, n+1)`, the
three reset anchors — the previous confirmed root, the finalized root, and the observed-justified
reset root — and the `get_latest_confirmed` block itself are all known blocks. The confirmed root is
`hck_of_genesisStart` + within-node `StoreLE`; the finalized root is `checkpoint_known`; the
observed reset root is `fcrStep_observed_known`; the `get_latest_confirmed` block is
`hbconf_of_genesisStart` (the support-vote route). No flags. -/
theorem anchorRoots_known (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n))
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true) :
    get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈ (E.store cfg ext v (n + 1)).block_roots ∧
    (E.fcrStep cfg ext v n).confirmed_root ∈ (E.store cfg ext v (n + 1)).block_roots ∧
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots ∧
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  refine ⟨E.hbconf_of_genesisStart cfg ext hSA hanchor0 v n _ hHn1 hconf, ?_,
    (hji.checkpoint_known v hv (n + 1) hHn1).2,
    E.fcrStep_observed_known cfg ext hji v hv n hHn1⟩
  rw [E.fcrStep_confirmed_root]
  exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1
    (E.hck_of_genesisStart cfg ext hSA hanchor0 v hv n hHn)

/-- **Same-slot anchoring through the honest past descendant.** The support-vote
route used by `hb_sameslot_of_pastDescendant` carries more than endpoint
knownness of `b`: the honest supporter's past store contains the whole walked
segment from `b` to the actual reset anchor `r₀`.  Transporting that past store
to `(w,m)` therefore preserves both endpoint knownness and `b ⪰ r₀`, without
using the one-slot relay from the confirming store. -/
theorem anchor_ge_of_pastDescendant (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (hpast : E.HonestPastDescendant cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) {b r₀ : Root}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true)
    (hanc : E.ConfirmedWithAnchor cfg ext b r₀ v (n + 1))
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    r₀ ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r₀) = true := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  obtain ⟨u, n_u, d, hu, hHnu, hslot_lt, hd_u, hdb_v⟩ :=
    hpast v hv n b hHn1 hconf
  have hgate_uv : E.slot_at cfg n_u + 1 ≤ E.slot_at cfg (n + 1 + 1) :=
    le_trans hslot_lt (E.slot_at_mono cfg (Nat.le_succ (n + 1)))
  have hsub_uv : (E.store cfg ext u n_u).block_roots ⊆
      (E.store cfg ext v (n + 1)).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hsync hu hv hHnu hHn1 hgate_uv
  have hagree_uv : ∀ x ∈ (E.store cfg ext u n_u).block_roots,
      (E.store cfg ext u n_u).blocks x = (E.store cfg ext v (n + 1)).blocks x :=
    fun x hx => hwfE.blocks_agree (E.blockProvenance cfg ext u n_u)
      (E.blockProvenance cfg ext v (n + 1)) hx (hsub_uv hx)
  obtain ⟨hwf_u, hwalk_u, _hjust_u⟩ :=
    E.store_domainK cfg ext hwfE hec hgen' hji u hu n_u hHnu
  obtain ⟨hwf_v, hwalk_v, _hjust_v⟩ :=
    E.store_domainK cfg ext hwfE hec hgen' hji v hv (n + 1) hHn1
  have hanchor_mem0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor_mem : ablk.root ∈ (E.store cfg ext u n_u).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le n_u)).1 hanchor_mem0
  have hanchor_slot : ((E.store cfg ext u n_u).blocks ablk.root).slot = 0 := by
    rw [E.store_anchor_block cfg ext hwfE hgeq u n_u hanchor_mem,
      hanchor0 ast ablk hgeq, GENESIS_SLOT]
  have hwalk0 : WalkKnown (E.store cfg ext u n_u) 0 d := by
    have hwalk := hwalk_u ablk.root hanchor_mem d hd_u
    rwa [hanchor_slot] at hwalk
  have hd_v : d ∈ (E.store cfg ext v (n + 1)).block_roots := hsub_uv hd_u
  have hdr₀_v : is_ancestor (E.store cfg ext v (n + 1))
      (get_node_for_root d) (get_node_for_root r₀) = true :=
    is_ancestor_trans hwf_v
      (hwalk_v r₀ hanc.r₀_known d hd_v)
      (hwalk_v r₀ hanc.r₀_known b hanc.b_known) hdb_v hanc.b_ge_r₀
  have mem_past (x : Root) (hx_v : x ∈ (E.store cfg ext v (n + 1)).block_roots)
      (hdx_v : is_ancestor (E.store cfg ext v (n + 1))
        (get_node_for_root d) (get_node_for_root x) = true) :
      x ∈ (E.store cfg ext u n_u).block_roots := by
    let sx := ((E.store cfg ext v (n + 1)).blocks x).slot
    have hwalk_x : WalkKnown (E.store cfg ext u n_u) sx d :=
      hwalk0.mono (Nat.zero_le _)
    have hv_lands : get_ancestor (E.store cfg ext v (n + 1))
        (ForkChoiceNode.mk d) sx = ForkChoiceNode.mk x := by
      simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq, sx] using hdx_v
    have hu_lands : get_ancestor (E.store cfg ext u n_u)
        (ForkChoiceNode.mk d) sx = ForkChoiceNode.mk x := by
      rw [get_ancestor_congr hagree_uv hd_u hwalk_x]
      exact hv_lands
    have hspec := (get_ancestor_spec hwf_u hwalk_x).1
    rw [hu_lands] at hspec
    exact hspec
  have hb_u : b ∈ (E.store cfg ext u n_u).block_roots :=
    mem_past b hanc.b_known hdb_v
  have hr₀_u : r₀ ∈ (E.store cfg ext u n_u).block_roots :=
    mem_past r₀ hanc.r₀_known hdr₀_v
  have hwalk_br_u : WalkKnown (E.store cfg ext u n_u)
      ((E.store cfg ext u n_u).blocks r₀).slot b := hwalk_u r₀ hr₀_u b hb_u
  have hbr_u : is_ancestor (E.store cfg ext u n_u)
      (get_node_for_root b) (get_node_for_root r₀) = true := by
    simp only [get_node_for_root]
    rw [is_ancestor_congr hagree_uv hb_u hr₀_u hwalk_br_u]
    simpa only [get_node_for_root] using hanc.b_ge_r₀
  have hgate_uw : E.slot_at cfg n_u + 1 ≤ E.slot_at cfg (m + 1) :=
    le_trans (le_trans hslot_lt (E.slot_at_mono cfg hm))
      (E.slot_at_mono cfg (Nat.le_succ m))
  have hsub_uw : (E.store cfg ext u n_u).block_roots ⊆
      (E.store cfg ext w m).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hsync hu hw hHnu hHm hgate_uw
  exact ⟨hsub_uw hr₀_u, hsub_uw hb_u,
    E.is_ancestor_transport_rev cfg ext hwfE hsub_uw hr₀_u hb_u hwalk_br_u hbr_u⟩

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



/-- **The `get_latest_confirmed`-scoped advance leg.** Threads the **existential** anchor through
the four-case argument and produces the full `SafeFrom` of the confirmed block from the
anchor-scoped covering supply `hcov` and the r₀-scoped per-edge `DescendStep` supply `hsupply`.

**Anchor scoping.** The supply is demanded only for the selected anchor, rather than **universally** over all
three reset-anchor kinds (`∀ r₀, kind → …`): the L4 confirm-margin certificates
(`CertExtract.edgeCert_of_confirmation`) live **only** on the segment `[r₀, glc]` above the
*actual* walk anchor, so the demand for the other two kinds is unproducible. Instead `hsupply`
provides the **existential** anchor `∃ r₀, kind ∧ ConfirmedWithAnchor ∧ DescendStepChainSupply` —
the very `(r₀, kind, ConfirmedWithAnchor)` package `confirmedWithAnchor_of_advance` /
`get_latest_confirmed_ge` produce (a single `r₀` for **both** the covering `jcb.root = r₀` and the
supply scoping). The fold extracts that one `r₀` (+ its `ConfirmedWithAnchor` `hanc`, feeding
`hcov`) and the supply `hsup` in a single `obtain`. The head-safety strong-induction shell
`safeFrom_of_headStep` supplies the IH. Once the confirming-store relay deadline holds, the
all three routes start from their threaded `head ⪰ r₀` fact — for the observed kind that
is the `hobs` witness, the route tag identifying `r₀` with the observed justified root.
The 4-case covering fold this branch used to run is deleted. Before that deadline
(including same-slot endpoints), all three kinds use the executable selected-candidate
transport of `glc ⪰ r₀` and their threaded `SafeFrom` facts, then fold the cert-carrying `[r₀, glc]` segment directly. Every
demanded edge still satisfies `c ⪰ r₀`. -/
theorem safeFromGlc_of_covSupply (hSA : SpecAssumptions cfg ext E)
    (hcov : E.AnchorCovSupply cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hadvslot : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
        (get_current_balance_source (E.fcrStep cfg ext v n))
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) = true)
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1))
    (hfin : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hobs : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1))
    (hsupply : ∃ r₀ : Root,
      (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
        r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
        r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) ∧
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) ∧
      E.DescendStepChainSupply cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ (n + 1)) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) (n + 1) := by
  have hwfE : WellFormedExecution E := hSA.2.1
  obtain ⟨r₀, hkind, hanc, hsup⟩ := hsupply
  refine E.safeFrom_of_headStep cfg ext ?_
  intro w hw m hm hH hIH
  have hHn1 : E.WithinHorizon cfg (n + 1) := E.withinHorizon_mono cfg hm hH
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_trans (Nat.le_succ n) hm) hH
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  have hconfirmed : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1
      (E.confirmed_root_known_selected cfg ext hSA v hv n hHn)
  have hfinalized : (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact (hji.checkpoint_known v hv (n + 1) hHn1).2
  have hobserved :
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.fcrStep_observed_known_selected cfg ext hji v hv n hHn1
  rcases E.get_latest_confirmed_selected cfg ext hSA v hv (n + 1) hHn1
      (E.fcrStep cfg ext v n) (E.fcrStep_store cfg ext v n)
      hconfirmed hfinalized hobserved with hreset | ⟨hselected, hbSelected, hpSelected⟩
  · rcases hreset with h | h | h
    · rw [h]
      exact hprev w hw m hm hH
    · rw [h]
      exact hfin w hw m hm hH
    · rw [h]
      exact hobs w hw m hm hH
  have hbConfirm : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hbSelected
  have hpConfirm : ((E.store cfg ext v (n + 1)).blocks
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))).parent_root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hpSelected
  have hbEndpoint : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints cfg ext hSA v hv n _ hHn1
      hbConfirm hpConfirm hselected w hw m (E.slot_at_mono cfg hm) hH
  by_cases hrelay : E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)
  · obtain ⟨hsub_t, hw_walk, hroute⟩ :=
      hcov v hv n hadvslot hconf hprev hfin w hw m hm hH hrelay r₀ hkind hanc hIH
    have hbge_r₀ := E.is_ancestor_transport_rev cfg ext hwfE hsub_t hanc.r₀_known hanc.b_known
      hw_walk hanc.b_ge_r₀
    have finishDirect (hhead_r₀ : is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m)) (get_node_for_root r₀) = true) :
        is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))) = true := by
      obtain ⟨hwf, hwalkK, hjc⟩ := E.store_domainK cfg ext hwfE hSA.2.2.2.2.2.1 hSA.1
        hSA.2.2.2.2.2.2.2.2 w hw m hH
      exact head_ge_of_safe_scoped_terminal cfg hwf
        (filtered_subset_block_roots cfg (E.store cfg ext w m) hjc) hwalkK hjc
        (hsub_t hanc.r₀_known) hbEndpoint hhead_r₀ hbge_r₀
        (fun a c ha hc hlink hbc hcr => hsup w hw m hm hH hIH a c ha hc hlink hbc hcr)
    rcases hroute with hconfirmed | hfinalized | hobserved
    · exact finishDirect hconfirmed.2
    · exact finishDirect hfinalized.2
    · -- **Observed kind, post-deadline.** The threaded observed-anchor `SafeFrom` witness
      -- `hobs` *is* `head ⪰ r₀` here, exactly as in the pre-deadline branch below: the route
      -- tag says `r₀` is the FCR's `current_epoch_observed_justified_checkpoint.root`, and
      -- `hobs` is that root's `SafeFrom` from `n + 1`. So this kind finishes through
      -- `finishDirect` like the other two, with no covering fold and no head-tracking premise.
      -- (The route's `jcb` covering payload is therefore unused here; it is retained in
      -- `AnchorCovSupply` for the flag's producers.)
      exact finishDirect (by
        simpa only [hobserved.1] using hobs w hw m hm hH)
  · obtain ⟨hr₀mem, hbmem, hbge_r₀⟩ :=
      E.confirmed_ancestry_at_all_honest_endpoints cfg ext hSA v hv n _ r₀ hHn1
        hbConfirm hpConfirm hanc.r₀_known hanc.b_ge_r₀ hselected w hw m
          (E.slot_at_mono cfg hm) hH
    have hhead_r₀ : is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m)) (get_node_for_root r₀) = true := by
      rcases hkind with hconfirmed | hfinalized | hobserved
      · simpa only [hconfirmed] using hprev w hw m hm hH
      · have hfin' : E.SafeFrom cfg ext
            (E.store cfg ext v (n + 1)).finalized_checkpoint.root (n + 1) := by
          simpa only [E.fcrStep_store] using hfin
        simpa only [hfinalized] using hfin' w hw m hm hH
      · simpa only [hobserved] using hobs w hw m hm hH
    obtain ⟨hwf, hwalkK, hjc⟩ := E.store_domainK cfg ext hwfE hSA.2.2.2.2.2.1 hSA.1
      hSA.2.2.2.2.2.2.2.2 w hw m hH
    exact head_ge_of_safe_scoped_terminal cfg hwf
      (filtered_subset_block_roots cfg (E.store cfg ext w m) hjc) hwalkK hjc
      hr₀mem hbmem hhead_r₀ hbge_r₀
      (fun a c ha hc hlink hbc hcr => hsup w hw m hm hH hIH a c ha hc hlink hbc hcr)

/-- **Selected-result closing from the anchor-scoped chain supply alone.**
The concrete selected-candidate certificate transports `glc`, the actual reset
anchor `r₀`, and `glc ⪰ r₀` to every honest endpoint, including endpoints before
the ordinary one-slot relay deadline.  The anchor-kind `SafeFrom` invariant then
gives `head ⪰ r₀`, and the supplied `[r₀, glc]` `DescendStep` chain closes the
endpoint.  Thus the selected advance path needs neither `AnchorCovSupply` nor any
covering/FFG geometry. -/
theorem safeFromGlc_of_chainSupply (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hprev : E.SafeFrom cfg ext (E.fcrStep cfg ext v n).confirmed_root (n + 1))
    (hfin : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1))
    (hobs : E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1))
    (hsupply : ∃ r₀ : Root,
      (r₀ = (E.fcrStep cfg ext v n).confirmed_root ∨
        r₀ = (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∨
        r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) ∧
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ v (n + 1) ∧
      E.DescendStepChainSupply cfg ext
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) r₀ (n + 1)) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n)) (n + 1) := by
  have hwfE : WellFormedExecution E := hSA.2.1
  obtain ⟨r₀, hkind, hanc, hsup⟩ := hsupply
  refine E.safeFrom_of_headStep cfg ext ?_
  intro w hw m hm hH hIH
  have hHn1 : E.WithinHorizon cfg (n + 1) := E.withinHorizon_mono cfg hm hH
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_trans (Nat.le_succ n) hm) hH
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  have hconfirmed : (E.fcrStep cfg ext v n).confirmed_root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1
      (E.confirmed_root_known_selected cfg ext hSA v hv n hHn)
  have hfinalized : (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact (hji.checkpoint_known v hv (n + 1) hHn1).2
  have hobserved :
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.fcrStep_observed_known_selected cfg ext hji v hv n hHn1
  rcases E.get_latest_confirmed_selected cfg ext hSA v hv (n + 1) hHn1
      (E.fcrStep cfg ext v n) (E.fcrStep_store cfg ext v n)
      hconfirmed hfinalized hobserved with hreset | ⟨hselected, hbSelected, hpSelected⟩
  · rcases hreset with h | h | h
    · rw [h]
      exact hprev w hw m hm hH
    · rw [h]
      exact hfin w hw m hm hH
    · rw [h]
      exact hobs w hw m hm hH
  have hbConfirm : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hbSelected
  have hpConfirm : ((E.store cfg ext v (n + 1)).blocks
        (get_latest_confirmed cfg ext (E.fcrStep cfg ext v n))).parent_root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hpSelected
  obtain ⟨hr₀mem, hbmem, hbge_r₀⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints cfg ext hSA v hv n _ r₀ hHn1
      hbConfirm hpConfirm hanc.r₀_known hanc.b_ge_r₀ hselected w hw m
        (E.slot_at_mono cfg hm) hH
  have hhead_r₀ : is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m)) (get_node_for_root r₀) = true := by
    rcases hkind with hconfirmed | hfinalized | hobserved
    · simpa only [hconfirmed] using hprev w hw m hm hH
    · have hfin' : E.SafeFrom cfg ext
          (E.store cfg ext v (n + 1)).finalized_checkpoint.root (n + 1) := by
        simpa only [E.fcrStep_store] using hfin
      simpa only [hfinalized] using hfin' w hw m hm hH
    · simpa only [hobserved] using hobs w hw m hm hH
  obtain ⟨hwf, hwalkK, hjc⟩ := E.store_domainK cfg ext hwfE hSA.2.2.2.2.2.1 hSA.1
    hji w hw m hH
  exact head_ge_of_safe_scoped_terminal cfg hwf
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjc) hwalkK hjc
    hr₀mem hbmem hhead_r₀ hbge_r₀
    (fun a c ha hc hlink hbc hcr => hsup w hw m hm hH hIH a c ha hc hlink hbc hcr)

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
