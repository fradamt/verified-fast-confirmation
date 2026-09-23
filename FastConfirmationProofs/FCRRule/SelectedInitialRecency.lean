module
public import FastConfirmationProofs.FCRRule.SelectedTraceCoverage

@[expose] public section

/-!
# Query-local initial source recency from the selected wrapper

This module extracts the source-recency facts which are already present in the
exact executable guards of `find_latest_confirmed_descendant` and its complete
ghost trace `findLatestSelectedTrace`.

All conclusions are local to the queried `FastConfirmationStore`:

* retaining any previous-loop edge proves the complete previous-entry guard,
  hence recency of `previous_slot_head`'s voting source, and proves that the
  previous-slot head descends from the retained edge's child;
* any strict wrapper result is classified either by that previous-entry
  witness or by the wrapper's final tentative-result witness; and
* the latter witness says exactly that the final result is in the current
  block epoch, or that the result's own voting source is recent (together with
  the executable epoch-start/no-conflict disjunction).

Nothing here transports a source, checkpoint, or ancestry fact to another
validator's store or a later endpoint.  Such persistence remains a separate
state-transition/trajectory obligation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The exact outer guard which permits entry into the previous-epoch loop.
Naming it exposes the strongest query-local witness carried by any retained
previous edge without weakening away its additional epoch/no-conflict facts. -/
def PreviousSelectedEntryWitness (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop :=
  get_block_epoch cfg fcrStore.store latestConfirmedRoot + 1 =
      get_current_store_epoch cfg fcrStore.store ∧
    (get_voting_source cfg fcrStore.store
        fcrStore.previous_slot_head).epoch + 2 ≥
      get_current_store_epoch cfg fcrStore.store ∧
    (is_start_slot_at_epoch cfg
        (get_current_slot cfg fcrStore.store) = true ∨
      (will_no_conflicting_checkpoint_be_justified cfg ext
          fcrStore.store = true ∧
        ((fcrStore.store.unrealized_justifications
              fcrStore.previous_slot_head).epoch + 1 ≥
            get_current_store_epoch cfg fcrStore.store ∨
          (fcrStore.store.unrealized_justifications
              (get_head cfg fcrStore.store).root).epoch + 1 ≥
            get_current_store_epoch cfg fcrStore.store)))

/-- The exact final acceptance witness for a tentative accumulator, with the
irrelevant fact that the tentative stage was entered omitted.  It is the
strongest source statement the final guard makes about the actual result. -/
def TentativeSelectedResultWitness (fcrStore : FastConfirmationStore Root)
    (result : Root) : Prop :=
  get_block_epoch cfg fcrStore.store result =
      get_current_store_epoch cfg fcrStore.store ∨
    ((get_voting_source cfg fcrStore.store result).epoch + 2 ≥
        get_current_store_epoch cfg fcrStore.store ∧
      (is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) = true ∨
        will_no_conflicting_checkpoint_be_justified cfg ext
          fcrStore.store = true))

/-- The exact outer guard which permits entry into the tentative loop. -/
def TentativeSelectedEntryWitness (fcrStore : FastConfirmationStore Root) : Prop :=
  is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) = true ∨
    (fcrStore.store.unrealized_justifications
        (get_head cfg fcrStore.store).root).epoch + 1 ≥
      get_current_store_epoch cfg fcrStore.store

namespace SelectedParentTrace

omit [LinearOrder Root] [Inhabited Root] in
/-- A nontrivial parent trace contains an edge whose child is its final
result.  This is the structural fact needed to distinguish which retained
wrapper trace actually produced a strict result. -/
theorem last_edge_mem_of_ne
    {store : Store Root} {start result : Root}
    {edges : List (Root × Root)}
    (h : SelectedParentTrace store start result edges)
    (hne : result ≠ start) :
    ∃ a, (a, result) ∈ edges := by
  induction h with
  | nil _ => exact False.elim (hne rfl)
  | @cons start next result rest _hstart _hnext _hparent tail ih =>
      by_cases hresult : result = next
      · subst result
        exact ⟨start, by simp⟩
      · obtain ⟨a, ha⟩ := ih hresult
        exact ⟨a, List.mem_cons_of_mem _ ha⟩

end SelectedParentTrace

namespace PreviousAcceptedEdge

/-- Membership in the retained previous trace mechanically proves the exact
wrapper-entry guard. -/
theorem entry_witness
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    PreviousSelectedEntryWitness cfg ext fcrStore latestConfirmedRoot := by
  simp only [PreviousAcceptedEdge, findLatestSelectedTrace] at h
  split_ifs at h with hentry <;> try simp at h
  exact hentry

/-- Every retained previous edge carries the previous-slot-head source
recency conjunct from the exact outer guard. -/
theorem previous_slot_head_source_recent
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    (get_voting_source cfg fcrStore.store
        fcrStore.previous_slot_head).epoch + 2 ≥
      get_current_store_epoch cfg fcrStore.store :=
  (h.entry_witness cfg ext).2.1

/-- The previous loop's per-entry ancestry guard: the query store's previous
slot head descends from every retained previous-edge child. -/
theorem previous_slot_head_descends_child
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    is_ancestor fcrStore.store
      (get_node_for_root fcrStore.previous_slot_head)
      (get_node_for_root c) = true :=
  (h.gates cfg ext).2.1

/-- Combined early-source and chain-placement witness supplied by one retained
previous edge.  Both facts concern only the query store. -/
theorem previous_slot_head_recency_and_ancestry
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    (get_voting_source cfg fcrStore.store
        fcrStore.previous_slot_head).epoch + 2 ≥
        get_current_store_epoch cfg fcrStore.store ∧
      is_ancestor fcrStore.store
        (get_node_for_root fcrStore.previous_slot_head)
        (get_node_for_root c) = true :=
  ⟨h.previous_slot_head_source_recent cfg ext,
    h.previous_slot_head_descends_child cfg ext⟩

end PreviousAcceptedEdge

/-- Retaining even one tentative edge proves both outer facts surrounding that
trace: the tentative stage was entered, and its final accumulator passed the
current-epoch/result-source-recency acceptance guard. -/
theorem retained_tentative_edge_entry_and_result_witness
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root)
    (h : (a, c) ∈
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) :
    TentativeSelectedEntryWitness cfg fcrStore ∧
      TentativeSelectedResultWitness cfg ext fcrStore
        (find_latest_confirmed_descendant cfg ext fcrStore
          latestConfirmedRoot) := by
  simp only [findLatestSelectedTrace] at h
  unfold TentativeSelectedEntryWitness TentativeSelectedResultWitness
  rw [find_latest_confirmed_descendant]
  simp only
  split_ifs at h ⊢ <;> simp_all

/-- Strong origin-and-placement classification for a strict selected result.

Under the ordinary query-store parent-domain facts, the final edge into the
actual result occurs in exactly one of the retained trace lists.  A previous
origin therefore supplies both previous-slot-head source recency and
`previous_slot_head ⩾c result` in the query store.  A tentative origin
supplies both the tentative-entry guard and the final result's exact
current-epoch/source-recency guard.
-/
theorem selected_strict_result_origin_recency_classification
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (latestConfirmedRoot : Root)
    (hlcr : latestConfirmedRoot ∈ fcrStore.store.block_roots)
    (result : Root)
    (hout : find_latest_confirmed_descendant cfg ext fcrStore
      latestConfirmedRoot = result)
    (hstrict : result ≠ latestConfirmedRoot) :
    (∃ a,
      PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a result ∧
        ((get_voting_source cfg fcrStore.store
            fcrStore.previous_slot_head).epoch + 2 ≥
            get_current_store_epoch cfg fcrStore.store ∧
          is_ancestor fcrStore.store
            (get_node_for_root fcrStore.previous_slot_head)
            (get_node_for_root result) = true)) ∨
      (∃ a,
        (a, result) ∈
            (findLatestSelectedTrace cfg ext fcrStore
              latestConfirmedRoot).2.2 ∧
          TentativeSelectedEntryWitness cfg fcrStore ∧
          TentativeSelectedResultWitness cfg ext fcrStore result) := by
  have htrace := findLatestSelectedTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead latestConfirmedRoot hlcr
  rw [findLatestSelectedTrace_fst cfg ext fcrStore latestConfirmedRoot,
    hout] at htrace
  obtain ⟨a, ha⟩ := htrace.last_edge_mem_of_ne hstrict
  rcases List.mem_append.mp ha with hprevious | htentative
  · left
    have haccepted : PreviousAcceptedEdge cfg ext fcrStore
        latestConfirmedRoot a result := hprevious
    exact ⟨a, haccepted,
      haccepted.previous_slot_head_recency_and_ancestry cfg ext⟩
  · right
    have hwitness := retained_tentative_edge_entry_and_result_witness
      cfg ext fcrStore latestConfirmedRoot a result htentative
    rw [hout] at hwitness
    exact ⟨a, htentative, hwitness⟩




end FastConfirmation.Spec

end
