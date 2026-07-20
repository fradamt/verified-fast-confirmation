import FastConfirmation.Spec.Proof.CertExtract
import FastConfirmation.Spec.Proof.FFGAccountability
import FastConfirmation.Spec.Proof.FilterViability
import FastConfirmation.Spec.Proof.FilterFuelMonotonicity

/-!
# Spec / Proof / SelectedFilter: executable gate traces and the filter boundary

This module records, without strengthening the executable rule, the FFG facts
that are actually retained when either loop in
`find_latest_confirmed_descendant` advances.

* A previous-epoch step passed all three loop guards: it is not in the current
  epoch, the previous-slot head descends from it, and it passed
  `is_one_confirmed`.
* A tentative step passed `is_one_confirmed`; when that step crosses to a
  strictly later block epoch, the same executable branch proves
  `will_current_target_be_justified = true`.

The trace functions below are ghost instrumentation only.  Their first
projection is proved equal to the corresponding executable loop, while their
edge list retains the guards that the result-only inversions necessarily erase.

The final section states the exact finite-tree certificate sufficient for the
`child_filtered` field used by the selected-margin producer.  It is deliberately
mechanical: the concrete FFG certificate layer proves quorum intersection,
same-epoch uniqueness, no-surround, and finalized prefix, but currently has no
bridge from an honest `Store`'s realized/unrealized checkpoint fields and
`get_voting_source` reads to those certificates.  Nor does it turn the local
`will_*` booleans into future store-visible certificates at the actual loop call
sites.  Consequently this module does not manufacture that missing bridge.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Exact ghost traces of the two executable loops -/

/-- Ghost-instrumented previous-epoch loop.  The edge list is oldest to newest
and contains exactly the accumulator transitions that the executable loop
took. -/
def prevEpochLoopTrace (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b = currentEpoch then
        (acc, [])
      else if ¬ is_ancestor fcrStore.store
          (get_node_for_root fcrStore.previous_slot_head) (get_node_for_root b) then
        (acc, [])
      else if ¬ is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := prevEpochLoopTrace fcrStore currentEpoch rest b
        (tail.1, (acc, b) :: tail.2)

/-- Ghost-instrumented tentative loop. -/
def tentativeLoopTrace (fcrStore : FastConfirmationStore Root) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ will_current_target_be_justified cfg ext fcrStore.store then
        (acc, [])
      else if ¬ is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := tentativeLoopTrace fcrStore rest b
        (tail.1, (acc, b) :: tail.2)

/-- Erasing the previous-epoch ghost edge list gives the executable loop. -/
theorem prevEpochLoopTrace_fst (fcrStore : FastConfirmationStore Root)
    (currentEpoch : Epoch) : ∀ roots acc,
    (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).1 =
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore
        currentEpoch roots acc := by
  intro roots
  induction roots with
  | nil => intro acc; rfl
  | cons b rest ih =>
      intro acc
      simp only [prevEpochLoopTrace,
        find_latest_confirmed_descendant_prev_epoch_loop]
      split_ifs <;> simp only [ih]

/-- Erasing the tentative ghost edge list gives the executable loop. -/
theorem tentativeLoopTrace_fst (fcrStore : FastConfirmationStore Root) : ∀ roots acc,
    (tentativeLoopTrace cfg ext fcrStore roots acc).1 =
      find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore roots acc := by
  intro roots
  induction roots with
  | nil => intro acc; rfl
  | cons b rest ih =>
      intro acc
      simp only [tentativeLoopTrace,
        find_latest_confirmed_descendant_tentative_loop]
      split_ifs <;> simp only [ih]

/-- Every recorded previous-epoch transition retains all three executable
guards.  In particular, this is stronger than the result-only
`prev_epoch_loop_spec`: it applies to every accepted edge. -/
theorem mem_prevEpochLoopTrace (fcrStore : FastConfirmationStore Root)
    (currentEpoch : Epoch) : ∀ roots acc a b,
    (a, b) ∈ (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).2 →
      get_block_epoch cfg fcrStore.store b ≠ currentEpoch ∧
      is_ancestor fcrStore.store (get_node_for_root fcrStore.previous_slot_head)
        (get_node_for_root b) = true ∧
      is_one_confirmed cfg ext fcrStore.store
        (get_current_balance_source fcrStore) b = true := by
  intro roots
  induction roots with
  | nil => simp [prevEpochLoopTrace]
  | cons x rest ih =>
      intro acc a b hab
      simp only [prevEpochLoopTrace] at hab
      by_cases hEpoch : get_block_epoch cfg fcrStore.store x = currentEpoch
      · rw [if_pos hEpoch] at hab
        simp at hab
      · rw [if_neg hEpoch] at hab
        by_cases hAncestor : is_ancestor fcrStore.store
            (get_node_for_root fcrStore.previous_slot_head) (get_node_for_root x) = true
        · rw [if_neg (not_not_intro hAncestor)] at hab
          by_cases hConfirmed : is_one_confirmed cfg ext fcrStore.store
              (get_current_balance_source fcrStore) x = true
          · rw [if_neg (not_not_intro hConfirmed)] at hab
            rw [List.mem_cons] at hab
            rcases hab with hab | hab
            · simp only [Prod.mk.injEq] at hab
              rcases hab with ⟨rfl, rfl⟩
              exact ⟨hEpoch, hAncestor, hConfirmed⟩
            · exact ih x a b hab
          · rw [if_pos hConfirmed] at hab
            simp at hab
        · rw [if_pos hAncestor] at hab
          simp at hab

/-- Every recorded tentative transition passed confirmation.  If it raised
the block epoch, the negated break guard retained by that transition forces
the local `will_current_target_be_justified` boolean to be true. -/
theorem mem_tentativeLoopTrace (fcrStore : FastConfirmationStore Root) :
    ∀ roots acc a b,
    (a, b) ∈ (tentativeLoopTrace cfg ext fcrStore roots acc).2 →
      is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b = true ∧
      (get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store b →
        will_current_target_be_justified cfg ext fcrStore.store = true) := by
  intro roots
  induction roots with
  | nil => simp [tentativeLoopTrace]
  | cons x rest ih =>
      intro acc a b hab
      simp only [tentativeLoopTrace] at hab
      by_cases hGate : get_block_epoch cfg fcrStore.store x >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ will_current_target_be_justified cfg ext fcrStore.store
      · rw [if_pos hGate] at hab
        simp at hab
      · rw [if_neg hGate] at hab
        by_cases hConfirmed : is_one_confirmed cfg ext fcrStore.store
            (get_current_balance_source fcrStore) x = true
        · rw [if_neg (not_not_intro hConfirmed)] at hab
          rw [List.mem_cons] at hab
          rcases hab with hab | hab
          · simp only [Prod.mk.injEq] at hab
            rcases hab with ⟨rfl, rfl⟩
            refine ⟨hConfirmed, ?_⟩
            intro hEpoch
            by_contra hWill
            exact hGate ⟨hEpoch, hWill⟩
          · exact ih x a b hab
        · rw [if_pos hConfirmed] at hab
          simp at hab

/-- A strict result which is not in the current epoch necessarily retained
the executable no-conflict protection: either the call is at an epoch-start
slot, or `will_no_conflicting_checkpoint_be_justified` evaluated to true.

This guard is not attached to either recursive loop.  It comes from the outer
previous-epoch entry condition and from the final acceptance condition for a
tentative result that remains in the previous epoch. -/
theorem selected_previous_result_outer_gate
    (fcrStore : FastConfirmationStore Root) (lcr result : Root)
    (hout : find_latest_confirmed_descendant cfg ext fcrStore lcr = result)
    (hstrict : result ≠ lcr)
    (hprevious : get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store) :
    is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
      will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true := by
  have entry_gate :
      (get_block_epoch cfg fcrStore.store lcr + 1 =
          get_current_store_epoch cfg fcrStore.store ∧
        (get_voting_source cfg fcrStore.store fcrStore.previous_slot_head).epoch + 2 ≥
          get_current_store_epoch cfg fcrStore.store ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
          (will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true ∧
            ((fcrStore.store.unrealized_justifications
                  fcrStore.previous_slot_head).epoch + 1 ≥
                get_current_store_epoch cfg fcrStore.store ∨
              (fcrStore.store.unrealized_justifications
                  (get_head cfg fcrStore.store).root).epoch + 1 ≥
                get_current_store_epoch cfg fcrStore.store)))) →
        is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
          will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true := by
    rintro ⟨_, _, hstart | ⟨hwill, _⟩⟩
    · exact Or.inl hstart
    · exact Or.inr hwill
  rw [find_latest_confirmed_descendant] at hout
  simp only at hout
  split_ifs at hout <;> subst result <;> simp_all

/-! ## The concrete selected-margin regime gap -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The sufficient side conditions of the two currently implemented concrete
selected-margin producers are not exhaustive.  If the selected edge itself is
intra-epoch, but its future contest window spans epochs, then neither the
same-window-epoch producer nor the edge-crossing producer applies.

This arithmetic lemma does not claim that `SelectedEdgeMarginInputs` is empty:
that sum type accepts already-built certificates.  It records the gap between
the side conditions of `FreshProducer` (same window epoch) and
`CrossingCert.crossing_endpoint_of_confirmed` (crossing edge) that must be
closed by a third, window-crossing/saturation producer. -/
theorem concrete_selected_margin_regime_gap
    {store : Store Root} {a c : Root} {lo σ : Slot}
    (hedge : get_block_epoch cfg store c = get_block_epoch cfg store a)
    (hwindow : compute_epoch_at_slot cfg lo < compute_epoch_at_slot cfg σ) :
    compute_epoch_at_slot cfg lo ≠ compute_epoch_at_slot cfg σ ∧
      ¬ get_block_epoch cfg store c > get_block_epoch cfg store a := by
  exact ⟨ne_of_lt hwindow, by simp [hedge]⟩

/-! ## The exact mechanical certificate for `child_filtered` -/

/-- A finite-tree certificate that a selected-chain child survives an endpoint
store's FFG filter.  The non-mechanical proof obligation is precisely the
production of `justified_ok`, `finalized_ok`, and the chain placement from the
actual FCR gates and store-visible FFG certificates. -/
structure FilterTipCertificate (store : Store Root) (c : Root) where
  mids : List Root
  tip : Root
  chain : ChainDown store store.justified_checkpoint.root (mids ++ [tip])
  child_on_chain : c ∈ mids ∨ c = tip ∨ c = store.justified_checkpoint.root
  tip_is_leaf : store.block_roots.filter
    (fun x => (store.blocks x).parent_root = tip) = []
  parent_slot_lt : ∀ r ∈ store.block_roots,
    (store.blocks r).parent_root ∈ store.block_roots →
      (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot
  justified_ok : store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
    (get_voting_source cfg store tip).epoch = store.justified_checkpoint.epoch ∨
    (get_voting_source cfg store tip).epoch + 2 ≥ get_current_store_epoch cfg store
  finalized_ok : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
    store.finalized_checkpoint.root =
      get_checkpoint_block cfg store tip store.finalized_checkpoint.epoch

omit [Inhabited Root] in
/-- Filtered-list membership from the exact viable-tip certificate. -/
theorem FilterTipCertificate.mem_filtered {store : Store Root} {c : Root}
    (h : FilterTipCertificate cfg store c) :
    c ∈ get_filtered_block_tree cfg store := by
  exact confirmed_mem_filtered_mono cfg h.parent_slot_lt h.chain
    h.child_on_chain h.tip_is_leaf h.justified_ok h.finalized_ok

omit [Inhabited Root] in
/-- The `MarginProducer.SameEpochSelectedMarginInputs.child_filtered` shape,
obtained once the endpoint FFG visibility proof has produced a viable-tip
certificate. -/
theorem FilterTipCertificate.child_filtered {store : Store Root} {a c : Root}
    (h : FilterTipCertificate cfg store c)
    (hparent : (store.blocks c).parent_root = a) :
    ForkChoiceNode.mk c ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk a) := by
  simp only [get_node_children, List.mem_map]
  refine ⟨c, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨h.mem_filtered cfg, by simp [hparent]⟩

end FastConfirmation.Spec
