module
public import FastConfirmation.Spec.Proof.MicroSteps
public import FastConfirmation.Spec.Proof.CoveringFFG
public import FastConfirmation.Spec.Proof.Confinement
public import FastConfirmation.Spec.Proof.INVstarTrack

@[expose] public section

/-!
# Spec / Proof / Anchoring: the additive anchoring lemma and `coveringFFG_of_anchor`

This module supplies the **anchoring** half of the `CoveringFFG` covering package:
the fact that the block `get_latest_confirmed` returns descends, *at the confirming store*,
from one of the three reset anchors (`confirmed_root` / `finalized.root` /
`observed.root`), and the assembly of that fact — transported to a foreign endpoint
`(w, m)` — into `Execution.CoveringFFG`.

Two independent pieces:

* **Section 1 — the additive anchoring lemma.** `find_latest_confirmed_descendant`
  only ever advances its accumulator through members of `get_ancestor_roots store head lcr`,
  each a descendant of the reset input `lcr`. `find_latest_confirmed_descendant_ge` proves the
  result `⪰ lcr` at the confirming store (the loop inversions
  `L4Fold.{prev_epoch_loop_spec,tentative_loop_spec}` + the `get_ancestor_roots`
  characterisation of `Proof/AncestryRoots.lean`, threaded through a "descends from the
  terminal" chain lemma `chain_descends_terminal`). `get_latest_confirmed_ge` composes it with
  the `get_latest_confirmed` reset case analysis: the returned `b` descends from an `r₀ ∈
  {confirmed_root, finalized.root, observed.root}`.

* **Section 2 — `ConfirmedWithAnchor` and `coveringFFG_of_anchor`.**
  `ConfirmedWithAnchor` bundles the confirming-store anchoring (`b ⪰ r₀` + both known).
  `coveringFFG_of_anchor` assembles `Execution.CoveringFFG` from it: the `b ⪰ jcb` conjunct is
  the transported anchoring (`EdgeDynamics.is_ancestor_transport_rev` on the reverse
  orientation, using `Synchrony.block_relay`'s block-root containment);
  `jcb`'s `JustifiedIn`/knownness and the
  head-witness geometry (the three `EngineCore.hadv_hi_of_head` inputs) enter as the covering
  FFG hypotheses in the exact export shapes.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-! ## Section 1 — the additive anchoring lemma -/

omit [Inhabited Root] in
/-- **Chain members descend from the terminal.** Along a parent-linked chain `L` of known
roots whose oldest element's parent is `t` (`L.head? = some x → (blocks x).parent_root = t`),
every member `x` is a descendant of `t` (`is_ancestor store x t`): the oldest element steps
once to `t` (`is_ancestor_of_parent`), and each later element descends from the previous by the
chain relation, composed by `is_ancestor_trans` (walk domains from the blanket `hwalk`). The
`t`-generalised dual of `INVstarTrack.mem_isAncestor_of_parentChain` (which walks toward the
*last* element). -/
theorem chain_descends_terminal {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ {L : List Root}, List.IsChain (fun a c => (store.blocks c).parent_root = a) L →
      (∀ x ∈ L, x ∈ store.block_roots) →
      ∀ {t : Root}, t ∈ store.block_roots →
      (∀ x, L.head? = some x → (store.blocks x).parent_root = t) →
      ∀ x ∈ L, is_ancestor store (get_node_for_root x) (get_node_for_root t) = true := by
  intro L hchain
  induction hchain with
  | nil => intro _ t _ _ x hx; simp at hx
  | singleton a =>
    intro hmem t ht hhd x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact is_ancestor_of_parent hwf (hmem a (by simp)) ht (hhd a rfl)
  | @cons_cons a d rest hr _ ih =>
    intro hmem t ht hhd x hx
    have hamem : a ∈ store.block_roots := hmem a (by simp)
    have hpar_a : (store.blocks a).parent_root = t := hhd a rfl
    have ha_t : is_ancestor store (get_node_for_root a) (get_node_for_root t) = true :=
      is_ancestor_of_parent hwf hamem ht hpar_a
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha_t
    · have hmem' : ∀ y ∈ d :: rest, y ∈ store.block_roots :=
        fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      have hhd' : ∀ y, (d :: rest).head? = some y → (store.blocks y).parent_root = a := by
        intro y hy; rw [List.head?_cons, Option.some_inj] at hy; subst hy; exact hr
      have hx_a := ih hmem' hamem hhd' x hx'
      exact is_ancestor_trans hwf (hwalk t ht x (hmem x (List.mem_cons_of_mem _ hx')))
        (hwalk t ht a hamem) hx_a ha_t

omit [Inhabited Root] in
/-- **`get_ancestor_roots` members descend from the terminal.** Every root of
`get_ancestor_roots store head t` is a descendant of `t` at the store: the list is the
parent-linked known chain from `t` toward `head`, so `chain_descends_terminal` applies. -/
theorem get_ancestor_roots_descends {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {t head : Root} (ht : t ∈ store.block_roots) (hhead : head ∈ store.block_roots)
    {x : Root} (hx : x ∈ get_ancestor_roots store head t) :
    is_ancestor store (get_node_for_root x) (get_node_for_root t) = true := by
  have hw : WalkKnown store (store.blocks t).slot head := hwalk t ht head hhead
  exact chain_descends_terminal hwf hwalk (get_ancestor_roots_isChain hwf hw)
    (fun y hy => get_ancestor_roots_mem hwf hw hy) ht
    (fun y hy => get_ancestor_roots_head? hwf hw hy) x hx

variable (cfg : Config) (ext : Externals Root)

/-- **The additive anchoring lemma.** At the querying store, the block
`find_latest_confirmed_descendant` returns descends from the input `lcr`
(`is_ancestor store result lcr`) and is a known block. Both advancement stages advance the
accumulator only through `get_ancestor_roots store head acc` (`get_ancestor_roots_descends` ⟹
each advance is a descendant), so the "descends from `lcr` and is known" predicate is preserved
from the reflexive base `P lcr` through the two loops (`L4Fold.prev_epoch_loop_spec` /
`tentative_loop_spec` return `r ∈ roots`). Needs `lcr` and the head known + the fork-choice
domain conditions (`hwf` the `parent_slot_lt` shape, `hwalk` the blanket walk domain). -/
theorem find_latest_confirmed_descendant_ge (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    is_ancestor fcr_store.store
        (get_node_for_root (find_latest_confirmed_descendant cfg ext fcr_store lcr))
        (get_node_for_root lcr) = true ∧
      find_latest_confirmed_descendant cfg ext fcr_store lcr ∈ fcr_store.store.block_roots := by
  set P : Root → Prop := fun r =>
    is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root lcr) = true ∧
      r ∈ fcr_store.store.block_roots with hP
  have base : P lcr := ⟨is_ancestor_refl _ _, hlcr⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro ce acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases prev_epoch_loop_spec cfg ext fcr_store ce
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans hwf (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
  have htent : ∀ (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc) := by
    intro acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases tentative_loop_spec cfg ext fcr_store
        (get_ancestor_roots fcr_store.store (get_head cfg fcr_store.store).root acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans hwf (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
  change P (find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact base
      | (apply htent; first | exact base | exact hprev _ _ base)
      | exact hprev _ _ base

/-- **`get_latest_confirmed` anchoring.** The block `get_latest_confirmed` returns
descends, at the querying store, from one of the three reset anchors `r₀ ∈ {confirmed_root,
finalized.root, observed.root}` (and `r₀` is a known block). Case analysis on
`get_latest_confirmed`'s two reset branches and the final advance: the reset value is one of the
three anchors, and the advance (`find_latest_confirmed_descendant_ge`) descends from it (the
no-advance leaf is reflexive). Needs the three anchors known + the fork-choice domain
conditions. -/
theorem get_latest_confirmed_ge (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (h0 : fcr_store.confirmed_root ∈ fcr_store.store.block_roots)
    (h1 : fcr_store.store.finalized_checkpoint.root ∈ fcr_store.store.block_roots)
    (h2 : fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      fcr_store.store.block_roots) :
    ∃ r₀ : Root,
      (r₀ = fcr_store.confirmed_root ∨ r₀ = fcr_store.store.finalized_checkpoint.root ∨
        r₀ = fcr_store.current_epoch_observed_justified_checkpoint.root) ∧
      r₀ ∈ fcr_store.store.block_roots ∧
      is_ancestor fcr_store.store
        (get_node_for_root (get_latest_confirmed cfg ext fcr_store))
        (get_node_for_root r₀) = true := by
  generalize hX : get_latest_confirmed cfg ext fcr_store = X
  simp only [get_latest_confirmed] at hX
  split_ifs at hX <;>
    subst hX <;>
      first
      | exact ⟨_, Or.inl rfl, h0, is_ancestor_refl _ _⟩
      | exact ⟨_, Or.inr (Or.inl rfl), h1, is_ancestor_refl _ _⟩
      | exact ⟨_, Or.inr (Or.inr rfl), h2, is_ancestor_refl _ _⟩
      | exact ⟨_, Or.inl rfl, h0,
          (find_latest_confirmed_descendant_ge cfg ext fcr_store hwf hwalk hhead _ h0).1⟩
      | exact ⟨_, Or.inr (Or.inl rfl), h1,
          (find_latest_confirmed_descendant_ge cfg ext fcr_store hwf hwalk hhead _ h1).1⟩
      | exact ⟨_, Or.inr (Or.inr rfl), h2,
          (find_latest_confirmed_descendant_ge cfg ext fcr_store hwf hwalk hhead _ h2).1⟩

/-! ## Section 2 — `ConfirmedWithAnchor` and `coveringFFG_of_anchor`

`ConfirmedWithAnchor cfg ext E b r₀ vc nc` is the confirming-store output of Section 1: at the
confirming anchor `(vc, nc)` the block `b` descends from the reset anchor `r₀` (both known).
`r₀` is one of the three anchors `get_latest_confirmed_ge` returns — its `JustifiedIn` "kind"
(finalized via `finalized_justified_ancestry`, observed via `observed_justified`) is supplied to
`coveringFFG_of_anchor` as the transported `JustifiedIn` conjunct, so the def stays kind-agnostic.

`coveringFFG_of_anchor` assembles `Execution.CoveringFFG cfg ext b w m` at a foreign endpoint
`(w, m)`. The `b ⪰ jcb.root` conjunct is the **transported anchoring** — `b ⪰ r₀` at `(vc, nc)`
carried to `(w, m)` by `EdgeDynamics.is_ancestor_transport_rev` off the block-root containment
`hsub` (`Synchrony.block_relay`) and the reverse walk domain `hw`; `jcb`'s `JustifiedIn` +
knownness and the head-witness geometry (the three `hadv_hi_of_head` inputs) enter as the
covering-FFG hypotheses. -/

namespace Execution

variable (E : Execution Root)

/-- **The confirming-store anchoring bundle.** At the confirming anchor `(vc, nc)`,
`b` descends from the reset anchor `r₀` and both are known blocks. This is exactly Section 1's
`get_latest_confirmed_ge` output (with the endpoint fixed at the confirming store `nc`), packaged
for `coveringFFG_of_anchor`. `r₀`'s "kind" (finalized / observed) is not recorded here — the
`JustifiedIn` propagation it seeds enters `coveringFFG_of_anchor` as a hypothesis. -/
structure ConfirmedWithAnchor (b r₀ : Root) (vc : ValidatorIndex) (nc : ℕ) : Prop where
  /-- `b` is a known block at the confirming store. -/
  b_known : b ∈ (E.store cfg ext vc nc).block_roots
  /-- the reset anchor `r₀` is a known block at the confirming store. -/
  r₀_known : r₀ ∈ (E.store cfg ext vc nc).block_roots
  /-- `b ⪰ r₀` at the confirming store (the additive anchoring). -/
  b_ge_r₀ : is_ancestor (E.store cfg ext vc nc)
    (get_node_for_root b) (get_node_for_root r₀) = true

/-- **`CoveringFFG` from the confirming-store anchor.** Assembles
`Execution.CoveringFFG cfg ext b w m` at a foreign endpoint `(w, m)` from the confirming-store
anchoring `ConfirmedWithAnchor` plus the transport / export hypotheses:

* the anchoring `b ⪰ jcb.root` (`jcb.root = r₀`) is the **transported** confirming-store fact —
  `is_ancestor_transport_rev` carries `b ⪰ r₀` from `(vc, nc)` to `(w, m)` off the block-root
  containment `hsub` (the `Synchrony.block_relay` deadline) and the reverse walk domain `hw`;
* `jcb`'s `JustifiedIn (store w m)` (`hjust`) and knownness (`hjcb_known`) are the
  `observed_justified` / `finalized_justified_ancestry` + `observed_checkpoint_known` /
  `checkpoint_known` exports (the `<=`-epoch branch);
* the head witness `head` and its geometry (`hHk`, `hHb`, `hckpt`, `hbslot`) are the three
  `EngineCore.hadv_hi_of_head` inputs (the strict branch).

The `hsub`/`hw` transport inputs and the export/geometry conjuncts are carried as hypotheses —
their per-endpoint discharge (block-relay slot gate, the FFG exports, the head witness from a
relayed `HonestPastDescendant`) is the covering supply this lemma feeds, not re-derived here. -/
theorem coveringFFG_of_anchor (hwfE : WellFormedExecution E)
    {b r₀ : Root} {vc w : ValidatorIndex} {nc m : ℕ}
    (hanc : E.ConfirmedWithAnchor cfg ext b r₀ vc nc)
    (hsub : (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hw : WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks r₀).slot b)
    (jcb : Checkpoint Root) (hjcb_root : jcb.root = r₀)
    (hjust : JustifiedIn (E.store cfg ext w m) jcb)
    (hjcb_known : jcb.root ∈ (E.store cfg ext w m).block_roots)
    (head : Root)
    (hHk : head ∈ (E.store cfg ext w m).block_roots)
    (hHb : is_ancestor (E.store cfg ext w m)
      (get_node_for_root head) (get_node_for_root b) = true)
    (hckpt : get_checkpoint_block cfg (E.store cfg ext w m) head
        (E.store cfg ext w m).justified_checkpoint.epoch =
      (E.store cfg ext w m).justified_checkpoint.root)
    (hbslot : ((E.store cfg ext w m).blocks b).slot ≤
      compute_start_slot_at_epoch cfg (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.CoveringFFG cfg ext b w m := by
  refine ⟨jcb, head, hjust, hjcb_known, ?_, hHk, hHb, hckpt, hbslot⟩
  rw [hjcb_root]
  exact E.is_ancestor_transport_rev cfg ext hwfE hsub hanc.r₀_known hanc.b_known hw hanc.b_ge_r₀

end Execution

end FastConfirmation.Spec

end
