module
public import FastConfirmation.Spec.Proof.MinimalSelectedDomain
public import FastConfirmation.Spec.Proof.Anchoring
public import FastConfirmation.Spec.Proof.WeakRulePredicateBridge

@[expose] public section

/-!
# Spec / Proof / WeakSelectorInversion

Weak-selector clones of the strong `find_latest_confirmed_descendant` inversion
lemmas (Stage 6 of the weak-synchrony migration, `docs/weak-synchrony.md`):
the loop-membership spec (`MicroSteps.find_latest_confirmed_descendant_mem`),
the additive anchoring spec (`Anchoring.find_latest_confirmed_descendant_ge`),
and the two `MinimalSelectedDomain` results
(`canonical_member_parent_known_minimal`,
`find_latest_confirmed_descendant_selected_minimal`), all re-targeted at
`Weak.find_latest_confirmed_descendant`
(`Spec/Model/WeakSynchrony.lean`).

The weak rule differs from the strong one in exactly two ways relevant here:

* the two loop bodies (`Weak.find_latest_confirmed_descendant_prev_epoch_loop`
  / `_tentative_loop`) are verbatim copies of the strong loops, over the weak
  predicates (`Weak.is_one_confirmed`, `Weak.will_current_target_be_justified`)
  — so their structural inversions (`weak_prev_epoch_loop_spec`,
  `weak_tentative_loop_spec` below) are line-for-line clones of
  `L4Fold.prev_epoch_loop_spec` / `tentative_loop_spec`;
* the wrapper `Weak.find_latest_confirmed_descendant`'s previous-epoch
  advancement guard has one extra conjunct,
  `Weak.has_justification_witness_certificate cfg ext fcr_store`, gating entry
  into the previous-epoch loop.

The first three clones below (`weak_find_latest_confirmed_descendant_mem`,
`weak_find_latest_confirmed_descendant_ge`,
`canonical_member_parent_known_minimal_weak`) do not need to look inside that
guard at all — they only ever consume "the result is the input, or it passed
`is_one_confirmed`", which is insensitive to the extra conjunct. The last
clone, `find_latest_confirmed_descendant_selected_minimal_weak`, is the
selector inversion proper and *does* need the certificate: its conclusion
upgrades every extracted `Weak.is_one_confirmed` witness to the strong
`is_one_confirmed` (via `is_one_confirmed_of_weak`,
`WeakRulePredicateBridge.lean`) while also keeping the weak witness, and
additionally exposes `Weak.has_justification_witness_certificate` as a third
disjunct precisely when the previous-epoch stage could have contributed to the
returned block (i.e. whenever the certificate held at all — a global fact,
independent of `r`, that is sound to attach to *every* confirmed result in
that case).

**S6 obligation (rule delta 4 site sweep, `docs/weak-synchrony.md`).** The
tentative loop's own voting-source read, `(get_voting_source cfg store
tentative_confirmed_root).epoch + 2 ≥ current_epoch` (the `h3`/`h4`-leaf
condition below, `find_latest_confirmed_descendant`'s final `if`), is not
separately certificate-gated. It does not need to be: `tentative_confirmed_root`
is only ever a candidate that already passed `Weak.is_one_confirmed`
(`weak_tentative_loop_spec`'s only advance case), and a `Weak.is_one_confirmed`
`true` result is itself a broadcast certificate for that root (`is_one_confirmed`'s
own docstring in `Spec/Model/WeakSynchrony.lean`). So this site is gated
*implicitly*, through the loop invariant, rather than by an explicit conjunct —
recorded here since it is easy to mistake for an ungated read.

`canonical_member_parent_known_minimal`'s only honesty-derived ingredient is
`SelectedMarginDomain.justified_root_known` (used once, to fall back to the
justified root when `get_head` degenerates); the weak twin takes that single
fact as an explicit hypothesis `hjrk` and drops `hv : v ∈ E.honest` — the weak
selector's confirming node is the observer of `Weak.ObserverContext`, which is
by construction *not* a member of `E.honest`. No other hypothesis of either
`MinimalSelectedDomain` original is honesty-derived: every store-domain lemma
they call (`store_parentSlotLt`, `store_walkKnownK`, `store_nonAnchorParentKnown`,
`store_anchor_min_slot`, `store_anchor_block`, `store_storeLE`,
`get_head_root_mem_or`) is already proved for an arbitrary node, honest or not.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 0 — weak loop equation lemmas and structural inversions

Verbatim clones of `L4Fold.prev_epoch_loop_cons_eq` / `prev_epoch_loop_spec`
and `tentative_loop_cons_eq` / `tentative_loop_spec`, over
`Weak.find_latest_confirmed_descendant_prev_epoch_loop` /
`_tentative_loop` and `Weak.is_one_confirmed`. The loop bodies are verbatim
copies of the strong ones (module docstring), so the inductions are identical;
these are private prerequisites (the strong lemmas they mirror are not
reusable here — they are stated about the strong loop functions — and are not
exported for reuse elsewhere by name, so they are reproduced locally). -/

private theorem weak_prev_epoch_loop_cons_eq (fcr_store : FastConfirmationStore Root)
    (ce : Epoch) (b : Root) (rest : List Root) (acc : Root) :
    Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b = ce then acc
       else if ¬ is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
              (get_node_for_root b) then acc
       else if ¬ Weak.is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce rest b) :=
  rfl

/-- **Prev-epoch loop inversion, weak twin.** Same structure as
`L4Fold.prev_epoch_loop_spec`: the loop returns the input accumulator, or a
list element that passed `Weak.is_one_confirmed`. -/
theorem weak_prev_epoch_loop_spec (fcr_store : FastConfirmationStore Root)
    (ce : Epoch) :
    ∀ (roots : List Root) (acc : Root),
      Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc = acc ∨
      ∃ r, r ∈ roots ∧
        Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc = r ∧
        Weak.is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) r = true := by
  intro roots
  induction roots with
  | nil => intro acc; left; rfl
  | cons b rest ih =>
    intro acc
    rw [weak_prev_epoch_loop_cons_eq]
    by_cases h1 : get_block_epoch cfg fcr_store.store b = ce
    · rw [if_pos h1]; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h2 : is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
          (get_node_for_root b) = true
      · rw [if_neg (not_not_intro h2)]
        by_cases h3 : Weak.is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store) b = true
        · rw [if_neg (not_not_intro h3)]
          rcases ih b with hacc | ⟨r, hr, heq, hrc⟩
          · exact Or.inr ⟨b, List.mem_cons_self, hacc, h3⟩
          · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, heq, hrc⟩
        · rw [if_pos h3]; exact Or.inl rfl
      · rw [if_pos h2]; exact Or.inl rfl

private theorem weak_tentative_loop_cons_eq (fcr_store : FastConfirmationStore Root)
    (b : Root) (rest : List Root) (acc : Root) :
    Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
            ¬ Weak.will_current_target_be_justified cfg ext fcr_store.store then acc
       else if ¬ Weak.is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store rest b) :=
  rfl

/-- **Tentative loop inversion, weak twin.** Same structure as
`L4Fold.tentative_loop_spec`. -/
theorem weak_tentative_loop_spec (fcr_store : FastConfirmationStore Root) :
    ∀ (roots : List Root) (acc : Root),
      Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc = acc ∨
      ∃ r, r ∈ roots ∧
        Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc = r ∧
        Weak.is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) r = true := by
  intro roots
  induction roots with
  | nil => intro acc; left; rfl
  | cons b rest ih =>
    intro acc
    rw [weak_tentative_loop_cons_eq]
    by_cases h1 : get_block_epoch cfg fcr_store.store b >
          get_block_epoch cfg fcr_store.store acc ∧
        ¬ Weak.will_current_target_be_justified cfg ext fcr_store.store
    · rw [if_pos h1]; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h2 : Weak.is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) b = true
      · rw [if_neg (not_not_intro h2)]
        rcases ih b with hacc | ⟨r, hr, heq, hrc⟩
        · exact Or.inr ⟨b, List.mem_cons_self, hacc, h2⟩
        · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, heq, hrc⟩
      · rw [if_pos h2]; exact Or.inl rfl

/-! ## Section 1 — `weak_find_latest_confirmed_descendant_mem`

Weak twin of `MicroSteps.find_latest_confirmed_descendant_mem`. The extra
certificate conjunct in the wrapper's previous-epoch guard is irrelevant here:
the invariant only tracks "is the input, or passed `Weak.is_one_confirmed` and
lies on `get_ancestor_roots … base` for some loop base", which the guard does
not affect (it only ever *blocks* entry to the previous-epoch loop, never
manufactures an advance). -/

theorem weak_find_latest_confirmed_descendant_mem (fcr_store : FastConfirmationStore Root)
    (lcr : Root) :
    Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr = lcr ∨
    (Weak.is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store)
        (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) = true ∧
      ∃ base : Root,
        Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
          get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base) := by
  set P : Root → Prop := fun r => r = lcr ∨
    (Weak.is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) r = true ∧
      ∃ base : Root, r ∈
        get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base)
    with hP
  have hprev : ∀ (ce : Epoch) (base acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base) acc) := by
    intro ce base acc hacc
    rcases weak_prev_epoch_loop_spec cfg ext fcr_store ce
        (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base) acc with
      h | ⟨r, hr, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ ⟨hc, base, hr⟩)
  have htent : ∀ (base acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base) acc) := by
    intro base acc hacc
    rcases weak_tentative_loop_spec cfg ext fcr_store
        (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) base) acc with
      h | ⟨r, hr, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ ⟨hc, base, hr⟩)
  change P (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [Weak.find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact Or.inl rfl
      | (apply htent; first | exact Or.inl rfl | exact hprev _ _ _ (Or.inl rfl))
      | exact hprev _ _ _ (Or.inl rfl)

/-! ## Section 2 — `weak_find_latest_confirmed_descendant_ge`

Weak twin of `Anchoring.find_latest_confirmed_descendant_ge`. Reuses the
generic (selector-independent) ancestry facts `get_ancestor_roots_descends`,
`is_ancestor_trans`, `is_ancestor_refl` directly from `Anchoring`/`Ancestry`. -/

theorem weak_find_latest_confirmed_descendant_ge (fcr_store : FastConfirmationStore Root)
    (hwf : ∀ r ∈ fcr_store.store.block_roots,
      (fcr_store.store.blocks r).parent_root ∈ fcr_store.store.block_roots →
        (fcr_store.store.blocks (fcr_store.store.blocks r).parent_root).slot <
          (fcr_store.store.blocks r).slot)
    (hwalk : ∀ t ∈ fcr_store.store.block_roots, ∀ r ∈ fcr_store.store.block_roots,
      WalkKnown fcr_store.store (fcr_store.store.blocks t).slot r)
    (hhead : (get_head cfg fcr_store.store).root ∈ fcr_store.store.block_roots)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots) :
    is_ancestor fcr_store.store
        (get_node_for_root (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr))
        (get_node_for_root lcr) = true ∧
      Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
        fcr_store.store.block_roots := by
  have hhead := Weak.get_certified_head_known cfg ext fcr_store.store
    (get_current_balance_source fcr_store) hhead
  set P : Root → Prop := fun r =>
    is_ancestor fcr_store.store (get_node_for_root r) (get_node_for_root lcr) = true ∧
      r ∈ fcr_store.store.block_roots with hP
  have base : P lcr := ⟨is_ancestor_refl _ _, hlcr⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc) := by
    intro ce acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases weak_prev_epoch_loop_spec cfg ext fcr_store ce
        (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans hwf
        (a := get_node_for_root r) (b := get_node_for_root acc)
        (c := get_node_for_root lcr) (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
  have htent : ∀ (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store
          (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc) := by
    intro acc hacc
    obtain ⟨hacc_anc, hacc_mem⟩ := hacc
    rcases weak_tentative_loop_spec cfg ext fcr_store
        (get_ancestor_roots fcr_store.store (Weak.get_certified_head cfg ext fcr_store.store (get_current_balance_source fcr_store)) acc) acc with
      h | ⟨r, hr, heq, _hc⟩
    · rw [h]; exact ⟨hacc_anc, hacc_mem⟩
    · rw [heq]
      have hr_anc := get_ancestor_roots_descends hwf hwalk hacc_mem hhead hr
      have hr_mem := get_ancestor_roots_mem hwf (hwalk acc hacc_mem _ hhead) hr
      exact ⟨is_ancestor_trans hwf
        (a := get_node_for_root r) (b := get_node_for_root acc)
        (c := get_node_for_root lcr) (hwalk lcr hlcr r hr_mem)
        (hwalk lcr hlcr acc hacc_mem) hr_anc hacc_anc, hr_mem⟩
  change P (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [Weak.find_latest_confirmed_descendant] at hX
  simp only at hX
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact base
      | (apply htent; first | exact base | exact hprev _ _ base)
      | exact hprev _ _ base

/-! ## Section 3 — local duplicate of `chain_member_slot_gt_terminal_minimal`

`MinimalSelectedDomain.lean` marks this helper `private`, so it is not
nameable from this file; it is reproduced verbatim (same proof) since
`canonical_member_parent_known_minimal_weak` needs it. -/

omit [LinearOrder Root] [Inhabited Root] in
private theorem chain_member_slot_gt_terminal_minimal_weak {store : Store Root}
    (hwf : ParentSlotLt store) :
    ∀ {roots : List Root},
      List.IsChain (fun a b => (store.blocks b).parent_root = a) roots →
      (∀ r ∈ roots, r ∈ store.block_roots) →
      ∀ {terminal : Root}, terminal ∈ store.block_roots →
      (∀ r, roots.head? = some r → (store.blocks r).parent_root = terminal) →
      ∀ r ∈ roots, (store.blocks terminal).slot < (store.blocks r).slot := by
  intro roots hchain
  induction hchain with
  | nil => intro _ terminal _ _ r hr; simp at hr
  | singleton a =>
      intro hmem terminal ht hhead r hr
      rw [List.mem_singleton] at hr
      subst r
      have hpa := hhead a rfl
      have hpMem : (store.blocks a).parent_root ∈ store.block_roots := by
        rw [hpa]
        exact ht
      have hlt := hwf a (hmem a (by simp)) hpMem
      rw [hpa] at hlt
      exact hlt
  | @cons_cons a d rest hparent _ ih =>
      intro hmem terminal ht hhead r hr
      have ha : a ∈ store.block_roots := hmem a (by simp)
      have hta : (store.blocks terminal).slot < (store.blocks a).slot := by
        have hpa := hhead a rfl
        have hpMem : (store.blocks a).parent_root ∈ store.block_roots := by
          rw [hpa]
          exact ht
        have hlt := hwf a ha hpMem
        rw [hpa] at hlt
        exact hlt
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hta
      · have hmem' : ∀ x ∈ d :: rest, x ∈ store.block_roots :=
          fun x hx => hmem x (List.mem_cons_of_mem a hx)
        have hhead' : ∀ x, (d :: rest).head? = some x →
            (store.blocks x).parent_root = a := by
          intro x hx
          rw [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact hparent
        exact hta.trans (ih hmem' ha hhead' r hr)

namespace Execution

variable (E : Execution Root)

/-! ## Section 4 — `canonical_member_parent_known_minimal_weak`

Weak twin of `MinimalSelectedDomain.canonical_member_parent_known_minimal`.
Drops `hv : v ∈ E.honest` (the weak selector's confirming node is the
`Weak.ObserverContext` observer, which is by construction *not* honest) and
takes the single honesty-derived fact the original consumes —
`SelectedMarginDomain.justified_root_known v hv n hHn`, used only to fall back
to the justified root when `get_head`'s totalized default fires — as an
explicit hypothesis `hjrk`. Everything else in the original proof
(`store_parentSlotLt`, `store_walkKnownK`, `store_nonAnchorParentKnown`,
`store_anchor_min_slot`, `store_anchor_block`, `store_storeLE`) is already
proved for an arbitrary node. -/

theorem canonical_member_parent_known_minimal_weak
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (hjrk : (E.store cfg ext v n).justified_checkpoint.root ∈
      (E.store cfg ext v n).block_roots)
    (bs : BeaconState Root) (base b : Root)
    (hbase : base ∈ (E.store cfg ext v n).block_roots)
    (hmem : b ∈ get_ancestor_roots (E.store cfg ext v n)
      (Weak.get_certified_head cfg ext (E.store cfg ext v n) bs) base) :
    b ∈ (E.store cfg ext v n).block_roots ∧
      ((E.store cfg ext v n).blocks b).parent_root ∈
        (E.store cfg ext v n).block_roots := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hwf : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen'
      hA.wellFormed.anchor_parent_unscheduled v n
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen' v n
  have hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v n) with h | h
    · exact h
    · rw [h]
      exact hjrk
  have hhead := Weak.get_certified_head_known cfg ext (E.store cfg ext v n) bs hhead
  have hb : b ∈ (E.store cfg ext v n).block_roots :=
    get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hmem
  have hstrict : ((E.store cfg ext v n).blocks base).slot <
      ((E.store cfg ext v n).blocks b).slot :=
    chain_member_slot_gt_terminal_minimal_weak hwf
      (get_ancestor_roots_isChain hwf (hwalkK base hbase _ hhead))
      (fun r hr => get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hr)
      hbase
      (fun r hr => get_ancestor_roots_head? hwf (hwalkK base hbase _ hhead) hr)
      b hmem
  rcases E.store_nonAnchorParentKnown cfg ext hgeq v n b hb with heq | hp
  · subst b
    have hbaseMin :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hstateSlot hroot v n base hbase
    have hanchorRecord := E.store_anchor_block cfg ext hA.wellFormed hgeq v n
      (by
        have h0 : ablk.root ∈ (E.store cfg ext v 0).block_roots := by
          change ablk.root ∈ E.genesis_store.block_roots
          rw [hgeq]
          simp [get_forkchoice_store]
        exact (E.store_storeLE cfg ext v (Nat.zero_le n)).1 h0)
    rw [hanchorRecord] at hstrict
    exact absurd hstrict (not_lt_of_ge hbaseMin)
  · exact ⟨hb, hp⟩

/-- Guard evidence carried by a strict weak-selector advance (rule delta 4).
The wrapper's previous-epoch guard requires
`Weak.has_justification_witness_certificate`; its tentative-loop entry gate
requires either the start of an epoch or `Weak.has_head_broadcast_certificate`
on the fork-choice head (`Spec/Model/WeakSynchrony.lean`, S3/S4). Every strict
advance goes through one of the two gates, so one of these three always
backs it. -/
def WeakSelectorGuardEvidence (fcrStore : FastConfirmationStore Root) : Prop :=
  Weak.has_justification_witness_certificate cfg ext fcrStore = true ∨
  is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
  Weak.has_head_broadcast_certificate cfg ext fcrStore.store
    (get_current_balance_source fcrStore) = true

/-! ## Section 5 — `find_latest_confirmed_descendant_selected_minimal_weak`

Weak twin of `MinimalSelectedDomain.find_latest_confirmed_descendant_selected_minimal`
— the selector inversion proper.

**Design of the guard evidence.** Both `Weak.has_justification_witness_certificate`
and `Weak.has_head_broadcast_certificate cfg ext fcrStore.store
(get_current_balance_source fcrStore)` are root-independent: each is either
true or false for the whole call. Splitting on the witness certificate first
(`by_cases hcertb`) makes the two cases easy:

* if it is *true*, it is available unconditionally, so `WeakSelectorGuardEvidence`
  (its left disjunct) can be attached to *every* confirmed result — the same
  four-way case split used by the strong original suffices, each leaf ending
  in `finishGuard _ _ (Or.inl hcertb)`;
* if it is *false*, the previous-epoch guard can never hold (it needs the
  certificate as a conjunct), so any hypothetical `split_ifs` leaf that
  assumes it does is contradictory (dismissed by `absurd`). The only real
  leaves left are ones where the *tentative* loop's own entry gate fired,
  which is itself `is_start_slot_at_epoch ∨ (… ∧ has_head_broadcast_certificate)`
  (`h2`): splitting the head certificate too (`by_cases hheadcertb`) lets the
  `hheadcertb`-true case reuse `Or.inr (Or.inr hheadcertb)` uniformly, while
  the `hheadcertb`-false case falls back to reading `h2` directly
  (`rcases h2 with hstart | ⟨_, hcert⟩`, the second branch then contradicting
  `hheadcertb`).

This keeps the strong `is_one_confirmed`-upgrade (`is_one_confirmed_of_weak`)
and the `Weak.is_one_confirmed` witness both present in every confirmed case,
as required. -/

theorem find_latest_confirmed_descendant_selected_minimal_weak
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (hjrk : (E.store cfg ext v n).justified_checkpoint.root ∈
      (E.store cfg ext v n).block_roots)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n)
    (lcr : Root) (hlcr : lcr ∈ fcrStore.store.block_roots) :
    Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr = lcr ∨
      (is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore)
          (Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr) = true ∧
        Weak.is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore)
          (Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr) = true ∧
        Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr ∈
          fcrStore.store.block_roots ∧
        (fcrStore.store.blocks
            (Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr)).parent_root ∈
          fcrStore.store.block_roots ∧
        WeakSelectorGuardEvidence cfg ext fcrStore) := by
  set P : Root → Prop := fun r => r = lcr ∨
    (Weak.is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true ∧
      r ∈ fcrStore.store.block_roots ∧
      (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots)
  have fresh : ∀ (base r : Root), base ∈ fcrStore.store.block_roots →
      r ∈ get_ancestor_roots fcrStore.store (Weak.get_certified_head cfg ext fcrStore.store (get_current_balance_source fcrStore)) base →
      Weak.is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true →
      P r := by
    intro base r hbase hr hconf
    have hbaseE : base ∈ (E.store cfg ext v n).block_roots := by
      simpa only [hstore] using hbase
    have hrE : r ∈ get_ancestor_roots (E.store cfg ext v n)
        (Weak.get_certified_head cfg ext (E.store cfg ext v n)
          (get_current_balance_source fcrStore)) base := by
      simpa only [hstore] using hr
    have hp := E.canonical_member_parent_known_minimal_weak cfg ext hA v n hHn hjrk
      (get_current_balance_source fcrStore) base r
      hbaseE hrE
    have hp' : r ∈ fcrStore.store.block_roots ∧
        (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots := by
      simpa only [hstore] using hp
    exact Or.inr ⟨hconf, hp'⟩
  have known_of_P : ∀ r, P r → r ∈ fcrStore.store.block_roots := by
    intro r hr
    rcases hr with heq | hright
    · rw [heq]
      exact hlcr
    · exact hright.2.1
  have hprev : ∀ (ce : Epoch) (base acc : Root),
      base ∈ fcrStore.store.block_roots → P acc →
      P (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore ce
        (get_ancestor_roots fcrStore.store (Weak.get_certified_head cfg ext fcrStore.store (get_current_balance_source fcrStore)) base) acc) := by
    intro ce base acc hbase hacc
    rcases weak_prev_epoch_loop_spec cfg ext fcrStore ce
      (get_ancestor_roots fcrStore.store (Weak.get_certified_head cfg ext fcrStore.store (get_current_balance_source fcrStore)) base) acc with
      heq | ⟨r, hr, heq, hconf⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      exact fresh base r hbase hr hconf
  have htent : ∀ (base acc : Root),
      base ∈ fcrStore.store.block_roots → P acc →
      P (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots fcrStore.store (Weak.get_certified_head cfg ext fcrStore.store (get_current_balance_source fcrStore)) base) acc) := by
    intro base acc hbase hacc
    rcases weak_tentative_loop_spec cfg ext fcrStore
      (get_ancestor_roots fcrStore.store (Weak.get_certified_head cfg ext fcrStore.store (get_current_balance_source fcrStore)) base) acc with
      heq | ⟨r, hr, heq, hconf⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      exact fresh base r hbase hr hconf
  -- Package a `P`-witness into the theorem's goal at `r`, given guard
  -- evidence for the whole call.
  have finishGuard : ∀ r, P r → WeakSelectorGuardEvidence cfg ext fcrStore →
      (r = lcr ∨
        (is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true ∧
          Weak.is_one_confirmed cfg ext fcrStore.store
            (get_current_balance_source fcrStore) r = true ∧
          r ∈ fcrStore.store.block_roots ∧
          (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots ∧
          WeakSelectorGuardEvidence cfg ext fcrStore)) := by
    intro r hr hguard
    rcases hr with heq | ⟨hconf, hmem, hpar⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨is_one_confirmed_of_weak cfg ext fcrStore.store
            (get_current_balance_source fcrStore) r hconf,
          hconf, hmem, hpar, hguard⟩
  by_cases hcertb : Weak.has_justification_witness_certificate cfg ext fcrStore = true
  · -- witness certificate globally available: attach it to every confirmed
    -- result. None of the six `split_ifs` leaves need to be told apart by
    -- name — each candidate term below is tried by unification against
    -- whichever leaf's (already-substituted) goal it actually matches.
    generalize hout : Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr = result
    rw [Weak.find_latest_confirmed_descendant] at hout
    simp only at hout
    split_ifs at hout with h1 h2 h3 h4 h5 <;>
      subst hout <;>
        first
        | exact Or.inl rfl
        | (have hp := hprev (get_current_store_epoch cfg fcrStore.store)
              lcr lcr hlcr (Or.inl rfl)
           exact finishGuard _ (htent _ _ (known_of_P _ hp) hp) (Or.inl hcertb))
        | exact finishGuard _ (htent _ _ hlcr (Or.inl rfl)) (Or.inl hcertb)
        | exact finishGuard _ (hprev _ lcr lcr hlcr (Or.inl rfl)) (Or.inl hcertb)
  · -- witness certificate globally unavailable: the previous-epoch guard can
    -- never hold (it needs the certificate as a conjunct, projected out as
    -- `_.2.2.1` — named `h2` or `h5` depending on the leaf, both dismissed by
    -- `absurd`), so every confirmed result must instead have advanced through
    -- the tentative loop's own entry gate, named `h1` in every leaf (it is
    -- the selector's outermost condition). Split further on the head
    -- broadcast certificate, the other source of guard evidence.
    by_cases hheadcertb : Weak.has_head_broadcast_certificate cfg ext fcrStore.store
        (get_current_balance_source fcrStore) = true
    · generalize hout : Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr = result
      rw [Weak.find_latest_confirmed_descendant] at hout
      simp only at hout
      split_ifs at hout with h1 h2 h3 h4 h5 <;>
        subst hout <;>
          first
          | exact Or.inl rfl
          | exact absurd h2.2.2.1 hcertb
          | exact absurd h5.2.2.1 hcertb
          | exact finishGuard _ (htent _ _ hlcr (Or.inl rfl)) (Or.inr (Or.inr hheadcertb))
    · generalize hout : Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr = result
      rw [Weak.find_latest_confirmed_descendant] at hout
      simp only at hout
      split_ifs at hout with h1 h2 h3 h4 h5 <;>
        subst hout <;>
          first
          | exact Or.inl rfl
          | exact absurd h2.2.2.1 hcertb
          | exact absurd h5.2.2.1 hcertb
          | (rcases h1 with hstart | ⟨_, hcert⟩
             · exact finishGuard _ (htent _ _ hlcr (Or.inl rfl)) (Or.inr (Or.inl hstart))
             · exact absurd hcert hheadcertb)

end Execution

end FastConfirmation.Spec

end
