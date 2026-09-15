import FastConfirmation.Spec.Proof.WeakSourceHistory
import FastConfirmation.Spec.Proof.SelectedPreQuerySIR

/-!
# Spec / Proof / WeakSelectedTrace

Stage S2 of the `hfilter`-discharge wave (`/tmp/hfilter-wave-design.md`): the
weak-selector clones of `SelectedFilterBridge.lean`'s executable ghost trace
(`findLatestSelectedTrace` / `prevEpochLoopTrace` / `PreviousAcceptedEdge` /
`PreviousAcceptedEdge.gates`), `SelectedFilter.lean`'s trace helpers, and
`SelectedInitialRecency.lean`'s query-local entry/result witnesses, all
re-targeted at `Weak.find_latest_confirmed_descendant`
(`Spec/Model/WeakSynchrony.lean`), plus the weak twin of
`SelectedPreQuerySIR.lean`'s `StrictSelectedResultMechanicalFacts` bracket and
its producer.

**Correction to the original hfilter S1/S2 plan, recorded in
`/tmp/delta5-proposal.md` §5** ("Correction to hfilter S1/S2"): rule delta 5
(certified bookkeeping of `Weak.update_fast_confirmation_variables`) replaced
the originally proposed delta 5′ (which would have gated the selector's own
epoch-start escape). The selector `Weak.find_latest_confirmed_descendant` is
therefore **untouched** by delta 5: `Weak.WeakSelectorGuardEvidence`
(`WeakSelectorInversion.lean`) stays a three-way disjunction, and
`Weak.TentativeSelectedEntryWitness` below stays the disjunction
`is_start_slot_at_epoch = true ∨ (… ∧ has_head_broadcast_certificate … =
true)` exactly as the committed rule's tentative-entry guard reads. Every
`split_ifs` leaf count below is unchanged from the committed rule; this file
must stay definitionally in lockstep with `Weak.find_latest_confirmed_descendant`
(`docs/weak-synchrony.md`'s "things that will bite").

**Design of `Weak.PreviousSelectedEntryWitness`.** The weak previous-epoch
advancement guard is a 4-conjunct `A ∧ B ∧ jwc ∧ D`:

* `A` — the input's block epoch is one behind the current epoch;
* `B` — the previous-slot head's voting source is recent;
* `jwc` — `Weak.has_justification_witness_certificate` (rule delta 2);
* `D` — the epoch-start escape or the no-conflict/unrealized-justification
  disjunction (rule delta 4's `has_head_broadcast_certificate` sits nested
  inside `D`'s right disjunct).

Unlike the strong `PreviousSelectedEntryWitness` (a bare nested `∧`,
`SelectedInitialRecency.lean`), the weak twin is a **structure** with a named
`witness_certificate` field so `jwc` is directly projectable instead of being
buried at a fixed nesting depth — the concrete need flagged by
`/tmp/hfilter-wave-design.md` §(C) site 3: "the guard must be
branch-indexed… `Weak.PreviousSelectedEntryWitness` carrying
`has_justification_witness_certificate = true` is needed." `Weak
.PreviousAcceptedEdge.gates` is widened to a 5-conjunct conclusion (the
strong 4-conjunct shape plus `jwc`) for the same reason.

Everything below that does not mention a certificate at all
(`findLatestSelectedTrace`, `prevEpochLoopTrace`, `tentativeLoopTrace`, their
`_fst`/`mem_*` lemmas, the parent-trace coverage lemmas, and
`TentativeSelectedResultWitness`) is a verbatim clone of its strong
counterpart over the weak predicates, exactly as `WeakSelectorBetween.lean`'s
module docstring already observes for the two loop bodies: the certificate
conjuncts only ever add width to an existing guard, never change how many
`if`s there are or their nesting, so `split_ifs` dispatches identically.

`Weak.StrictSelectedResultMechanicalFacts`'s producer replaces the strong
`hv : v ∈ E.honest` domain facts (`store_domainK_of_selectedMarginDomain`,
`head_root_known_of_selectedMarginDomain`) by the honesty-free
`Execution.observerStoreDomainK` / `Execution.head_root_known_at_observer`
(`WeakObserverDomain.lean`, stage S0), and the strong selector inversion
(`find_latest_confirmed_descendant_selected_minimal`,
`find_latest_confirmed_descendant_ge`) by their weak twins already landed in
`WeakSelectorInversion.lean` (`find_latest_confirmed_descendant_selected_minimal_weak`,
`weak_find_latest_confirmed_descendant_ge`). No bookkeeping function
(`Weak.update_fast_confirmation_variables`/`E.weakFcrStep`) is unfolded
anywhere in this file: the producer is stated over a bare query
`FastConfirmationStore`, exactly as the strong original is.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Section 0 — ghost-instrumented loop traces (weak twin of `SelectedFilter.lean`) -/

/-- Ghost-instrumented weak previous-epoch loop. Verbatim clone of
`prevEpochLoopTrace` over `Weak.is_one_confirmed`. -/
def prevEpochLoopTrace (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b = currentEpoch then
        (acc, [])
      else if ¬ is_ancestor fcrStore.store
          (get_node_for_root fcrStore.previous_slot_head) (get_node_for_root b) then
        (acc, [])
      else if ¬ Weak.is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := prevEpochLoopTrace fcrStore currentEpoch rest b
        (tail.1, (acc, b) :: tail.2)

/-- Ghost-instrumented weak tentative loop. Verbatim clone of
`tentativeLoopTrace` over `Weak.is_one_confirmed` / `Weak.will_current_target_be_justified`. -/
def tentativeLoopTrace (fcrStore : FastConfirmationStore Root) :
    List Root → Root → Root × List (Root × Root)
  | [], acc => (acc, [])
  | b :: rest, acc =>
      if get_block_epoch cfg fcrStore.store b >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ Weak.will_current_target_be_justified cfg ext fcrStore.store then
        (acc, [])
      else if ¬ Weak.is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b then
        (acc, [])
      else
        let tail := tentativeLoopTrace fcrStore rest b
        (tail.1, (acc, b) :: tail.2)

theorem prevEpochLoopTrace_fst (fcrStore : FastConfirmationStore Root)
    (currentEpoch : Epoch) : ∀ roots acc,
    (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).1 =
      Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore
        currentEpoch roots acc := by
  intro roots
  induction roots with
  | nil => intro acc; rfl
  | cons b rest ih =>
      intro acc
      simp only [prevEpochLoopTrace,
        Weak.find_latest_confirmed_descendant_prev_epoch_loop]
      split_ifs <;> simp only [ih]

theorem tentativeLoopTrace_fst (fcrStore : FastConfirmationStore Root) : ∀ roots acc,
    (tentativeLoopTrace cfg ext fcrStore roots acc).1 =
      Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore roots acc := by
  intro roots
  induction roots with
  | nil => intro acc; rfl
  | cons b rest ih =>
      intro acc
      simp only [tentativeLoopTrace,
        Weak.find_latest_confirmed_descendant_tentative_loop]
      split_ifs <;> simp only [ih]

theorem mem_prevEpochLoopTrace (fcrStore : FastConfirmationStore Root)
    (currentEpoch : Epoch) : ∀ roots acc a b,
    (a, b) ∈ (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).2 →
      get_block_epoch cfg fcrStore.store b ≠ currentEpoch ∧
      is_ancestor fcrStore.store (get_node_for_root fcrStore.previous_slot_head)
        (get_node_for_root b) = true ∧
      Weak.is_one_confirmed cfg ext fcrStore.store
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
          by_cases hConfirmed : Weak.is_one_confirmed cfg ext fcrStore.store
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

theorem mem_tentativeLoopTrace (fcrStore : FastConfirmationStore Root) :
    ∀ roots acc a b,
    (a, b) ∈ (tentativeLoopTrace cfg ext fcrStore roots acc).2 →
      Weak.is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b = true ∧
      (get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store b →
        Weak.will_current_target_be_justified cfg ext fcrStore.store = true) := by
  intro roots
  induction roots with
  | nil => simp [tentativeLoopTrace]
  | cons x rest ih =>
      intro acc a b hab
      simp only [tentativeLoopTrace] at hab
      by_cases hGate : get_block_epoch cfg fcrStore.store x >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ Weak.will_current_target_be_justified cfg ext fcrStore.store
      · rw [if_pos hGate] at hab
        simp at hab
      · rw [if_neg hGate] at hab
        by_cases hConfirmed : Weak.is_one_confirmed cfg ext fcrStore.store
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

/-- Weak twin of `selected_previous_result_outer_gate`. A strict previous-epoch
result not in the current epoch retained the executable no-conflict
protection (epoch-start escape or `Weak.will_no_conflicting_checkpoint_be_justified`).
The certificate conjunct of the entry guard is destructured and discarded. -/
theorem selected_previous_result_outer_gate
    (fcrStore : FastConfirmationStore Root) (lcr result : Root)
    (hout : Weak.find_latest_confirmed_descendant cfg ext fcrStore lcr = result)
    (hstrict : result ≠ lcr)
    (hprevious : get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store) :
    is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
      Weak.will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store
        (get_current_balance_source fcrStore) = true := by
  have entry_gate :
      (get_block_epoch cfg fcrStore.store lcr + 1 =
          get_current_store_epoch cfg fcrStore.store ∧
        (get_voting_source cfg fcrStore.store fcrStore.previous_slot_head).epoch + 2 ≥
          get_current_store_epoch cfg fcrStore.store ∧
        Weak.has_justification_witness_certificate cfg ext fcrStore = true ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
          (Weak.will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store
              (get_current_balance_source fcrStore) = true ∧
            ((fcrStore.store.unrealized_justifications
                  fcrStore.previous_slot_head).epoch + 1 ≥
                get_current_store_epoch cfg fcrStore.store ∨
              ((fcrStore.store.unrealized_justifications
                    (get_head cfg fcrStore.store).root).epoch + 1 ≥
                  get_current_store_epoch cfg fcrStore.store ∧
                Weak.has_head_broadcast_certificate cfg ext fcrStore.store
                  (get_current_balance_source fcrStore) = true))))) →
        is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true ∨
          Weak.will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store
            (get_current_balance_source fcrStore) = true := by
    rintro ⟨_, _, _, hstart | ⟨hwill, _⟩⟩
    · exact Or.inl hstart
    · exact Or.inr hwill
  rw [Weak.find_latest_confirmed_descendant] at hout
  simp only at hout
  split_ifs at hout <;> subst result <;> simp_all

/-! ## Section 1 — the complete wrapper trace (weak twin of `SelectedFilterBridge.lean`) -/

/-- Weak twin of `findLatestSelectedTrace`. Kept definitionally in lockstep
with `Weak.find_latest_confirmed_descendant` (module docstring): every guard
below is copied verbatim from the committed rule's `if`s
(`Spec/Model/WeakSynchrony.lean`), including the rule delta 2/4 certificate
conjuncts. -/
def findLatestSelectedTrace (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Root × (List (Root × Root) × List (Root × Root)) :=
  let store := fcrStore.store
  let head := (get_head cfg store).root
  let currentEpoch := get_current_store_epoch cfg store
  let bs := get_current_balance_source fcrStore
  let previousGuard :=
    get_block_epoch cfg store latestConfirmedRoot + 1 = currentEpoch ∧
        (get_voting_source cfg store fcrStore.previous_slot_head).epoch + 2 ≥
          currentEpoch ∧
        Weak.has_justification_witness_certificate cfg ext fcrStore = true ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
          (Weak.will_no_conflicting_checkpoint_be_justified cfg ext store bs = true ∧
            ((store.unrealized_justifications fcrStore.previous_slot_head).epoch + 1 ≥
                currentEpoch ∨
              ((store.unrealized_justifications head).epoch + 1 ≥ currentEpoch ∧
                Weak.has_head_broadcast_certificate cfg ext store bs = true))))
  let previousRoot :=
    if previousGuard then
      Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot
    else
      latestConfirmedRoot
  let previousEdges :=
    if previousGuard then
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot).2
    else
      []
  let tentativeGuard :=
    is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
      ((store.unrealized_justifications head).epoch + 1 ≥ currentEpoch ∧
        Weak.has_head_broadcast_certificate cfg ext store bs = true)
  let tentativeRoot :=
    if tentativeGuard then
      Weak.find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot
    else
      previousRoot
  let tentativeAccepted :=
    tentativeGuard ∧
      (get_block_epoch cfg store tentativeRoot = currentEpoch ∨
        ((get_voting_source cfg store tentativeRoot).epoch + 2 ≥ currentEpoch ∧
            (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
              Weak.will_no_conflicting_checkpoint_be_justified cfg ext store bs = true)))
  let tentativeEdges :=
    if tentativeAccepted then
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot).2
    else
      []
  (Weak.find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot,
    (previousEdges, tentativeEdges))

/-- Erasing both ghost edge lists gives the exact weak wrapper result. -/
theorem findLatestSelectedTrace_fst
    (fcrStore : FastConfirmationStore Root) (latestConfirmedRoot : Root) :
    (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).1 =
      Weak.find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot := by
  rfl

/-- A previous-loop edge retained by the complete weak wrapper trace. -/
def PreviousAcceptedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1

/-- Every retained previous-loop edge passed weak confirmation; its wrapper
entry also passed the justification-witness certificate and either the
epoch-start escape or the no-conflict prediction. The certificate conjunct is
threaded through explicitly (unlike the strong 4-conjunct `.gates`, this is a
5-conjunct conclusion) so it is directly projectable, per
`Weak.PreviousSelectedEntryWitness`. -/
theorem PreviousAcceptedEdge.gates
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    get_block_epoch cfg fcrStore.store c ≠
        get_current_store_epoch cfg fcrStore.store ∧
      is_ancestor fcrStore.store
        (get_node_for_root fcrStore.previous_slot_head)
        (get_node_for_root c) = true ∧
      Weak.is_one_confirmed cfg ext fcrStore.store
        (get_current_balance_source fcrStore) c = true ∧
      Weak.has_justification_witness_certificate cfg ext fcrStore = true ∧
      (is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) = true ∨
        Weak.will_no_conflicting_checkpoint_be_justified cfg ext
          fcrStore.store (get_current_balance_source fcrStore) = true) := by
  simp only [PreviousAcceptedEdge, findLatestSelectedTrace] at h
  split_ifs at h with hentry <;> try simp at h
  have hm := mem_prevEpochLoopTrace cfg ext fcrStore _ _ _ a c h
  refine ⟨hm.1, hm.2.1, hm.2.2, hentry.2.2.1, ?_⟩
  rcases hentry.2.2.2 with hstart | ⟨hwill, _⟩
  · exact Or.inl hstart
  · exact Or.inr hwill

/-! ## Section 2 — query-local entry/result witnesses (weak twin of
`SelectedInitialRecency.lean`) -/

/-- The exact outer guard which permits entry into the weak previous-epoch
loop, as a structure so the justification-witness certificate (rule delta 2)
is a named, directly projectable field instead of being buried inside a fixed
nested-`∧` position. -/
structure PreviousSelectedEntryWitness (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Prop where
  epoch_gate : get_block_epoch cfg fcrStore.store latestConfirmedRoot + 1 =
    get_current_store_epoch cfg fcrStore.store
  voting_source_recent : (get_voting_source cfg fcrStore.store
      fcrStore.previous_slot_head).epoch + 2 ≥
    get_current_store_epoch cfg fcrStore.store
  witness_certificate : Weak.has_justification_witness_certificate cfg ext fcrStore = true
  inner_gate : is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) = true ∨
    (Weak.will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store
        (get_current_balance_source fcrStore) = true ∧
      ((fcrStore.store.unrealized_justifications
            fcrStore.previous_slot_head).epoch + 1 ≥
          get_current_store_epoch cfg fcrStore.store ∨
        ((fcrStore.store.unrealized_justifications
              (get_head cfg fcrStore.store).root).epoch + 1 ≥
            get_current_store_epoch cfg fcrStore.store ∧
          Weak.has_head_broadcast_certificate cfg ext fcrStore.store
            (get_current_balance_source fcrStore) = true)))

/-- The exact final acceptance witness for a weak tentative accumulator.
Verbatim clone of the strong `TentativeSelectedResultWitness`, over
`Weak.will_no_conflicting_checkpoint_be_justified` (which additionally reads
the current balance source). -/
def TentativeSelectedResultWitness (fcrStore : FastConfirmationStore Root)
    (result : Root) : Prop :=
  get_block_epoch cfg fcrStore.store result =
      get_current_store_epoch cfg fcrStore.store ∨
    ((get_voting_source cfg fcrStore.store result).epoch + 2 ≥
        get_current_store_epoch cfg fcrStore.store ∧
      (is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) = true ∨
        Weak.will_no_conflicting_checkpoint_be_justified cfg ext
          fcrStore.store (get_current_balance_source fcrStore) = true))

/-- The exact outer guard which permits entry into the weak tentative loop.
Per the delta-5 correction (`/tmp/delta5-proposal.md` §5): the selector is
untouched, so this stays the disjunction `is_start_slot_at_epoch = true ∨
(unrealized-justification-recency ∧ has_head_broadcast_certificate = true)`
exactly as the committed rule (rule delta 4) reads — not collapsed to a bare
two-way disjunction. -/
def TentativeSelectedEntryWitness (fcrStore : FastConfirmationStore Root) : Prop :=
  is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) = true ∨
    ((fcrStore.store.unrealized_justifications
        (get_head cfg fcrStore.store).root).epoch + 1 ≥
      get_current_store_epoch cfg fcrStore.store ∧
    Weak.has_head_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) = true)

namespace PreviousAcceptedEdge

/-- Membership in the retained weak previous trace mechanically proves the
exact wrapper-entry guard. -/
theorem entry_witness
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    PreviousSelectedEntryWitness cfg ext fcrStore latestConfirmedRoot := by
  simp only [PreviousAcceptedEdge, findLatestSelectedTrace] at h
  split_ifs at h with hentry <;> try simp at h
  exact ⟨hentry.1, hentry.2.1, hentry.2.2.1, hentry.2.2.2⟩

/-- Every retained previous edge carries the previous-slot-head source
recency conjunct from the exact outer guard. -/
theorem previous_slot_head_source_recent
    {fcrStore : FastConfirmationStore Root}
    {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    (get_voting_source cfg fcrStore.store
        fcrStore.previous_slot_head).epoch + 2 ≥
      get_current_store_epoch cfg fcrStore.store :=
  (h.entry_witness cfg ext).voting_source_recent

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

/-- Combined early-source and chain-placement witness supplied by one
retained previous edge. -/
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

/-- Retaining even one weak tentative edge proves both outer facts
surrounding that trace. Weak twin of
`retained_tentative_edge_entry_and_result_witness`. -/
theorem retained_tentative_edge_entry_and_result_witness
    (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root)
    (h : (a, c) ∈
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) :
    TentativeSelectedEntryWitness cfg ext fcrStore ∧
      TentativeSelectedResultWitness cfg ext fcrStore
        (Weak.find_latest_confirmed_descendant cfg ext fcrStore
          latestConfirmedRoot) := by
  simp only [findLatestSelectedTrace] at h
  unfold TentativeSelectedEntryWitness TentativeSelectedResultWitness
  rw [Weak.find_latest_confirmed_descendant]
  simp only
  split_ifs at h ⊢ <;> simp_all

/-! ## Section 3 — complete parent-trace coverage (weak twin of
`SelectedTraceCoverage.lean`). The generic `SelectedParentTrace` inductive is
reused verbatim (`SelectedPreQuerySIR.lean`): it mentions only an ordinary
store, not any selector. -/

theorem prevEpochLoopTrace_parentTrace
    (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcrStore.store.block_roots) →
      List.IsChain
        (fun a c => (fcrStore.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x →
        (fcrStore.store.blocks x).parent_root = acc) →
      acc ∈ fcrStore.store.block_roots →
      SelectedParentTrace fcrStore.store acc
        (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).1
        (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots acc).2 := by
  intro roots
  induction roots with
  | nil =>
      intro acc _ _ _ hacc
      exact .nil hacc
  | cons b rest ih =>
      intro acc hmem hchain hhead hacc
      simp only [prevEpochLoopTrace]
      by_cases hEpoch : get_block_epoch cfg fcrStore.store b = currentEpoch
      · rw [if_pos hEpoch]
        exact .nil hacc
      · rw [if_neg hEpoch]
        by_cases hAncestor : is_ancestor fcrStore.store
            (get_node_for_root fcrStore.previous_slot_head)
            (get_node_for_root b) = true
        · rw [if_neg (not_not_intro hAncestor)]
          by_cases hConfirmed : Weak.is_one_confirmed cfg ext fcrStore.store
              (get_current_balance_source fcrStore) b = true
          · rw [if_neg (not_not_intro hConfirmed)]
            apply SelectedParentTrace.cons hacc
              (hmem b List.mem_cons_self) (hhead b rfl)
            exact ih b
              (fun x hx => hmem x (List.mem_cons_of_mem b hx))
              (List.isChain_cons.mp hchain).2
              (fun x hx => (List.isChain_cons.mp hchain).1 x
                (Option.mem_def.mpr hx))
              (hmem b List.mem_cons_self)
          · rw [if_pos hConfirmed]
            exact .nil hacc
        · rw [if_pos hAncestor]
          exact .nil hacc

theorem tentativeLoopTrace_parentTrace
    (fcrStore : FastConfirmationStore Root) :
    ∀ (roots : List Root) (acc : Root),
      (∀ x ∈ roots, x ∈ fcrStore.store.block_roots) →
      List.IsChain
        (fun a c => (fcrStore.store.blocks c).parent_root = a) roots →
      (∀ x, roots.head? = some x →
        (fcrStore.store.blocks x).parent_root = acc) →
      acc ∈ fcrStore.store.block_roots →
      SelectedParentTrace fcrStore.store acc
        (tentativeLoopTrace cfg ext fcrStore roots acc).1
        (tentativeLoopTrace cfg ext fcrStore roots acc).2 := by
  intro roots
  induction roots with
  | nil =>
      intro acc _ _ _ hacc
      exact .nil hacc
  | cons b rest ih =>
      intro acc hmem hchain hhead hacc
      simp only [tentativeLoopTrace]
      by_cases hGate : get_block_epoch cfg fcrStore.store b >
          get_block_epoch cfg fcrStore.store acc ∧
          ¬ Weak.will_current_target_be_justified cfg ext fcrStore.store
      · rw [if_pos hGate]
        exact .nil hacc
      · rw [if_neg hGate]
        by_cases hConfirmed : Weak.is_one_confirmed cfg ext fcrStore.store
            (get_current_balance_source fcrStore) b = true
        · rw [if_neg (not_not_intro hConfirmed)]
          apply SelectedParentTrace.cons hacc
            (hmem b List.mem_cons_self) (hhead b rfl)
          exact ih b
            (fun x hx => hmem x (List.mem_cons_of_mem b hx))
            (List.isChain_cons.mp hchain).2
            (fun x hx => (List.isChain_cons.mp hchain).1 x
              (Option.mem_def.mpr hx))
            (hmem b List.mem_cons_self)
        · rw [if_pos hConfirmed]
          exact .nil hacc

theorem prevEpochCanonicalTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (currentEpoch : Epoch) (acc : Root)
    (hacc : acc ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store acc
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).1
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).2 := by
  have hw := hwalk acc hacc _ hhead
  exact prevEpochLoopTrace_parentTrace cfg ext fcrStore currentEpoch _ acc
    (fun x hx => get_ancestor_roots_mem hwf hw hx)
    (get_ancestor_roots_isChain hwf hw)
    (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc

theorem tentativeCanonicalTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (acc : Root) (hacc : acc ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store acc
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).1
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots fcrStore.store
          (get_head cfg fcrStore.store).root acc) acc).2 := by
  have hw := hwalk acc hacc _ hhead
  exact tentativeLoopTrace_parentTrace cfg ext fcrStore _ acc
    (fun x hx => get_ancestor_roots_mem hwf hw hx)
    (get_ancestor_roots_isChain hwf hw)
    (fun x hx => get_ancestor_roots_head? hwf hw hx) hacc

/-- The two retained lists form a complete parent trace from the weak
wrapper's input to its executable result. Weak twin of
`findLatestSelectedTrace_parentTrace`. -/
theorem findLatestSelectedTrace_parentTrace
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (latestConfirmedRoot : Root)
    (hlcr : latestConfirmedRoot ∈ fcrStore.store.block_roots) :
    SelectedParentTrace fcrStore.store latestConfirmedRoot
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).1
      ((findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1 ++
        (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) := by
  let store := fcrStore.store
  let head := (get_head cfg store).root
  let currentEpoch := get_current_store_epoch cfg store
  let bs := get_current_balance_source fcrStore
  let pRoots := get_ancestor_roots store head latestConfirmedRoot
  let pExec := Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext
    fcrStore currentEpoch pRoots latestConfirmedRoot
  let pTrace := prevEpochLoopTrace cfg ext fcrStore currentEpoch pRoots
    latestConfirmedRoot
  let pGuard :=
    get_block_epoch cfg store latestConfirmedRoot + 1 = currentEpoch ∧
      (get_voting_source cfg store fcrStore.previous_slot_head).epoch + 2 ≥
        currentEpoch ∧
      Weak.has_justification_witness_certificate cfg ext fcrStore = true ∧
      (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
        (Weak.will_no_conflicting_checkpoint_be_justified cfg ext store bs = true ∧
          ((store.unrealized_justifications fcrStore.previous_slot_head).epoch + 1 ≥
              currentEpoch ∨
            ((store.unrealized_justifications head).epoch + 1 ≥ currentEpoch ∧
              Weak.has_head_broadcast_certificate cfg ext store bs = true))))
  let previousRoot := if pGuard then pExec else latestConfirmedRoot
  let previousEdges := if pGuard then pTrace.2 else []
  have hpRaw := prevEpochCanonicalTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead currentEpoch latestConfirmedRoot hlcr
  have hpExec : SelectedParentTrace store latestConfirmedRoot pExec pTrace.2 := by
    simpa only [store, head, currentEpoch, pRoots, pExec, pTrace,
      prevEpochLoopTrace_fst] using hpRaw
  have hp : SelectedParentTrace store latestConfirmedRoot
      previousRoot previousEdges := by
    by_cases hpg : pGuard
    · simpa only [previousRoot, previousEdges, if_pos hpg] using hpExec
    · simpa only [previousRoot, previousEdges, if_neg hpg] using
        (SelectedParentTrace.nil hlcr)
  let tRoots := get_ancestor_roots store head previousRoot
  let tExec := Weak.find_latest_confirmed_descendant_tentative_loop cfg ext
    fcrStore tRoots previousRoot
  let tTrace := tentativeLoopTrace cfg ext fcrStore tRoots previousRoot
  have htRaw := tentativeCanonicalTrace_parentTrace cfg ext fcrStore hwf
    hwalk hhead previousRoot hp.result_known
  have htExec : SelectedParentTrace store previousRoot tExec tTrace.2 := by
    simpa only [store, head, tRoots, tExec, tTrace,
      tentativeLoopTrace_fst] using htRaw
  let tGuard := is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
    ((store.unrealized_justifications head).epoch + 1 ≥ currentEpoch ∧
      Weak.has_head_broadcast_certificate cfg ext store bs = true)
  let finalGuard :=
    get_block_epoch cfg store tExec = currentEpoch ∨
      ((get_voting_source cfg store tExec).epoch + 2 ≥ currentEpoch ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
          Weak.will_no_conflicting_checkpoint_be_justified cfg ext store bs = true))
  by_cases htg : tGuard
  · by_cases hfg : finalGuard
    · have hall := hp.append htExec
      simpa [findLatestSelectedTrace, Weak.find_latest_confirmed_descendant,
        store, head, currentEpoch, bs, pRoots, pExec, pTrace, pGuard,
        previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
        finalGuard, htg, hfg] using hall
    · simpa [findLatestSelectedTrace, Weak.find_latest_confirmed_descendant,
        store, head, currentEpoch, bs, pRoots, pExec, pTrace, pGuard,
        previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
        finalGuard, htg, hfg] using hp
  · simpa [findLatestSelectedTrace, Weak.find_latest_confirmed_descendant,
      store, head, currentEpoch, bs, pRoots, pExec, pTrace, pGuard,
      previousRoot, previousEdges, tRoots, tExec, tTrace, tGuard,
      finalGuard, htg] using hp

/-- Weak twin of `selected_strict_result_origin_recency_classification`: a
strict weak-selector result was produced either by a retained previous-loop
edge (carrying previous-slot-head source recency and ancestry) or by a
retained tentative edge (carrying the tentative entry/result witnesses). -/
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
    (hout : Weak.find_latest_confirmed_descendant cfg ext fcrStore
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
          TentativeSelectedEntryWitness cfg ext fcrStore ∧
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

end Weak

end FastConfirmation.Spec
