module
public import FastConfirmation.Spec.Proof.SelectedPreQueryHistoricalSIR
public import FastConfirmation.Spec.Proof.FCRCallContracts
public import FastConfirmation.Spec.Proof.TrustedAnchorGeometry

@[expose] public section

/-!
# Historical current-target certificates along the concrete FCR trajectory

Paper Lemma 27 is temporal: a current-epoch candidate which did not enter the
current epoch in the present `find_latest_confirmed_descendant` invocation must
have inherited that epoch checkpoint from an earlier invocation.  Consequently
this obligation cannot faithfully be proved for two arbitrary lookalike
`FastConfirmationStore`s.

The execution model does retain the required history without adding a mutable
certificate field.  `Execution.fcr` is a recursive trajectory, `fcrStep v n`
is the exact state on which the invocation from second `n` to `n+1` runs, and
`confirmed_succ_of_advance` identifies its executable output.  Certificate
history can therefore be a ghost invariant over the earlier indices of this
existing trajectory.

This file first proves the local fact which makes the temporal case exact: if
the selected result is current-epoch and the present retained trace has no
epoch-crossing tentative edge, then the invocation input was already
current-epoch.  The proof uses the complete executable parent trace, not a
result-only lookalike.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace SelectedParentTrace

omit [LinearOrder Root] [Inhabited Root] in
/-- A parent trace never moves backwards in slot: its start is no later than
its result. -/
theorem start_slot_le_result {store : Store Root}
    (hwf : ParentSlotLt store)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges) :
    (store.blocks start).slot ≤ (store.blocks result).slot := by
  induction htrace with
  | nil _ => exact Nat.le_refl _
  | @cons start next result rest hstart hnext hparent tail ih =>
      have hlt := hwf next hnext (by rw [hparent]; exact hstart)
      rw [hparent] at hlt
      exact (Nat.le_of_lt hlt).trans ih

omit [LinearOrder Root] [Inhabited Root] in
/-- The child of every recorded edge is no later than the trace result. -/
theorem edge_child_slot_le_result {store : Store Root}
    (hwf : ParentSlotLt store)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges)
    {a c : Root} (hm : (a, c) ∈ edges) :
    (store.blocks c).slot ≤ (store.blocks result).slot := by
  induction htrace with
  | nil _ => simp at hm
  | @cons start next result rest hstart hnext hparent tail ih =>
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact tail.start_slot_le_result hwf
      · exact ih hm

omit [LinearOrder Root] [Inhabited Root] in
/-- The parent of every recorded edge is no earlier than the trace start. -/
theorem start_slot_le_edge_parent {store : Store Root}
    (hwf : ParentSlotLt store)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges)
    {a c : Root} (hm : (a, c) ∈ edges) :
    (store.blocks start).slot ≤ (store.blocks a).slot := by
  induction htrace with
  | nil _ => simp at hm
  | @cons start next result rest hstart hnext hparent tail ih =>
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact Nat.le_refl _
      · have hlt := hwf next hnext (by rw [hparent]; exact hstart)
        rw [hparent] at hlt
        exact (Nat.le_of_lt hlt).trans (ih hm)

omit [Inhabited Root] in
/-- The trace result descends from the child of each recorded edge. -/
theorem result_descends_edge_child {store : Store Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges)
    {a c : Root} (hm : (a, c) ∈ edges) :
    is_ancestor store (get_node_for_root result)
      (get_node_for_root c) = true := by
  induction htrace with
  | nil _ => simp at hm
  | @cons start next result rest hstart hnext hparent tail ih =>
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact tail.result_descends_start hwf hwalk
      · exact ih hm

omit [LinearOrder Root] [Inhabited Root] in
/-- If the trace starts exactly one epoch before its result, some recorded
direct edge is the transition into the result epoch. -/
theorem exists_edge_entering_next_epoch {store : Store Root}
    (hwf : ParentSlotLt store)
    {start result : Root} {edges : List (Root × Root)}
    (htrace : SelectedParentTrace store start result edges)
    (hepoch : get_block_epoch cfg store start + 1 =
      get_block_epoch cfg store result) :
    ∃ a c : Root,
      (a, c) ∈ edges ∧
      get_block_epoch cfg store a < get_block_epoch cfg store c ∧
      get_block_epoch cfg store c = get_block_epoch cfg store result := by
  revert hepoch
  induction htrace with
  | nil _ =>
      intro hepoch
      exact False.elim
        ((Nat.not_succ_le_self _) (Nat.le_of_eq hepoch))
  | @cons start next result rest hstart hnext hparent tail ih =>
      intro hepoch
      have hslotLt := hwf next hnext (by rw [hparent]; exact hstart)
      rw [hparent] at hslotLt
      have hstartNext : get_block_epoch cfg store start ≤
          get_block_epoch cfg store next := by
        simp only [get_block_epoch, compute_epoch_at_slot]
        exact Nat.div_le_div_right (Nat.le_of_lt hslotLt)
      have hnextResult : get_block_epoch cfg store next ≤
          get_block_epoch cfg store result := by
        simp only [get_block_epoch, compute_epoch_at_slot]
        exact Nat.div_le_div_right (tail.start_slot_le_result hwf)
      have hcases : get_block_epoch cfg store next =
            get_block_epoch cfg store start ∨
          get_block_epoch cfg store next =
            get_block_epoch cfg store result := by
        by_cases hsame : get_block_epoch cfg store next =
            get_block_epoch cfg store start
        · exact Or.inl hsame
        · right
          apply Nat.le_antisymm hnextResult
          calc
            get_block_epoch cfg store result =
                get_block_epoch cfg store start + 1 := hepoch.symm
            _ ≤ get_block_epoch cfg store next :=
              Nat.succ_le_of_lt
                (Nat.lt_of_le_of_ne hstartNext (Ne.symm hsame))
      rcases hcases with hsame | henters
      · have htailEpoch : get_block_epoch cfg store next + 1 =
            get_block_epoch cfg store result := by
          simpa only [hsame] using hepoch
        obtain ⟨a, c, hm, hac, hc⟩ := ih htailEpoch
        exact ⟨a, c, List.mem_cons_of_mem _ hm, hac, hc⟩
      · refine ⟨start, next, List.mem_cons_self, ?_, henters⟩
        apply Nat.lt_of_succ_le
        apply Nat.le_of_eq
        calc
          Nat.succ (get_block_epoch cfg store start) =
              get_block_epoch cfg store start + 1 := rfl
          _ = get_block_epoch cfg store result := hepoch
          _ = get_block_epoch cfg store next := henters.symm

end SelectedParentTrace

namespace Execution

variable (E : Execution Root)

/-! ## The exact local inheritance split -/

/-- A current selected result with no retained epoch-crossing edge necessarily
started from a current-epoch input.  Thus the `currentHistorical` call site is
genuinely an inherited input, rather than an unrecorded crossing in the same
invocation. -/
theorem selectedInput_current_of_result_current_no_crossing
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hresultCurrent : get_block_epoch cfg query.store
      (find_latest_confirmed_descendant cfg ext query input) =
        get_current_store_epoch cfg query.store)
    (hnoCrossing : ¬ ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query input a c) :
    get_block_epoch cfg query.store input =
      get_current_store_epoch cfg query.store := by
  rcases hinputEpoch with hcurrent | hprevious
  · exact hcurrent
  · have htrace := findLatestSelectedTrace_parentTrace cfg ext query
        hwf hwalk hhead input hinput
    have hghostCurrent : get_block_epoch cfg query.store
        (findLatestSelectedTrace cfg ext query input).1 =
          get_current_store_epoch cfg query.store := by
      simpa only [findLatestSelectedTrace_fst] using hresultCurrent
    have hstep : get_block_epoch cfg query.store input + 1 =
        get_block_epoch cfg query.store
          (findLatestSelectedTrace cfg ext query input).1 := by
      exact hprevious.trans hghostCurrent.symm
    obtain ⟨a, c, hm, hac, hcCurrent⟩ :=
      htrace.exists_edge_entering_next_epoch cfg hwf hstep
    rcases List.mem_append.mp hm with hprev | htent
    · have hcNotCurrent :=
        (show PreviousAcceptedEdge cfg ext query input a c from hprev).gates cfg ext
      exact False.elim (hcNotCurrent.1 (hcCurrent.trans hghostCurrent))
    · exact False.elim (hnoCrossing ⟨a, c, htent, hac⟩)

/-- A strict selector output is on the query head chain even without assuming
that the input is.  The input alternative is retained through each loop and
then eliminated by strictness; every genuine advance is a member of the
canonical `get_ancestor_roots` segment. -/
theorem strictSelectedResult_below_head
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input) :
    is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext query input)) = true := by
  let head := (get_head cfg query.store).root
  set P : Root → Prop := fun r =>
    r ∈ query.store.block_roots ∧
      (r = input ∨ is_ancestor query.store (get_node_for_root head)
        (get_node_for_root r) = true) with hP
  have base : P input := ⟨hinput, Or.inl rfl⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext query ce
        (get_ancestor_roots query.store head acc) acc) := by
    intro ce acc hacc
    rcases prev_epoch_loop_spec cfg ext query ce
        (get_ancestor_roots query.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ query.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown, Or.inr
        (ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr)⟩
  have htent : ∀ (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext query
        (get_ancestor_roots query.store head acc) acc) := by
    intro acc hacc
    rcases tentative_loop_spec cfg ext query
        (get_ancestor_roots query.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ query.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown, Or.inr
        (ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr)⟩
  have hresult : P
      (find_latest_confirmed_descendant cfg ext query input) := by
    generalize hout : find_latest_confirmed_descendant cfg ext query input = result
    rw [find_latest_confirmed_descendant] at hout
    simp only at hout
    split_ifs at hout with hc1 hc2 hc3 hc4 hc5 <;>
      subst hout <;>
        first
        | exact base
        | (apply htent; first | exact base | exact hprev _ _ base)
        | exact hprev _ _ base
  rcases hresult.2 with heq | hbelow
  · exact False.elim (hstrict heq)
  · have hbelow' := hbelow
    simp only [head, get_node_for_root] at hbelow'
    exact (congrArg (· = true) (is_ancestor_pending_root_eq query.store
      (get_head cfg query.store).root
      (find_latest_confirmed_descendant cfg ext query input) .pending
      (get_head cfg query.store).payload_status)).mp hbelow'

/-- A retained current-target edge makes the wrapper result strict. -/
theorem CurrentTargetAcceptedEdge.result_ne_input
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input a c : Root} (hinput : input ∈ query.store.block_roots)
    (hedge : CurrentTargetAcceptedEdge cfg ext query input a c) :
    find_latest_confirmed_descendant cfg ext query input ≠ input := by
  have htrace := findLatestSelectedTrace_parentTrace cfg ext query
    hwf hwalk hhead input hinput
  have hm : (a, c) ∈
      (findLatestSelectedTrace cfg ext query input).2.1 ++
        (findLatestSelectedTrace cfg ext query input).2.2 :=
    List.mem_append.mpr (Or.inr hedge.1)
  have hstartChild := htrace.edge_child_slot_gt_start hwf hm
  have hchildResult := htrace.edge_child_slot_le_result hwf hm
  intro heq
  have hslotLt : (query.store.blocks input).slot <
      (query.store.blocks
        (findLatestSelectedTrace cfg ext query input).1).slot :=
    hstartChild.trans_le hchildResult
  rw [findLatestSelectedTrace_fst, heq] at hslotLt
  exact (Nat.lt_irrefl _ hslotLt)

/-! ## One-call certificate inheritance -/

/-- For one concrete selector call, the current-result checkpoint is certified
either by the crossing producer in this call or by the certified current input.
The no-crossing branch is reduced to input inheritance by
`selectedInput_current_of_result_current_no_crossing`; checkpoint equality is
then ordinary parent-trace geometry. -/
theorem selectedCurrentCheckpointCertified_of_input_or_crossing
    {anchor : Checkpoint Root}
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hcurrentWalk : ∀ r ∈ query.store.block_roots,
      WalkKnown query.store
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store)) r)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hresultCurrent : get_block_epoch cfg query.store
      (find_latest_confirmed_descendant cfg ext query input) =
        get_current_store_epoch cfg query.store)
    (hinputCertificate :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store →
        Nonempty (CertifiedJustified cfg E anchor
          (get_checkpoint_for_block cfg query.store input
            (get_block_epoch cfg query.store input))))
    (hcrossingCertificate : ∀ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query input a c →
        Nonempty (CertifiedJustified cfg E anchor
          (get_current_target cfg query.store))) :
    Nonempty (CertifiedJustified cfg E anchor
      (get_checkpoint_for_block cfg query.store
        (find_latest_confirmed_descendant cfg ext query input)
        (get_block_epoch cfg query.store
          (find_latest_confirmed_descendant cfg ext query input)))) := by
  let result := find_latest_confirmed_descendant cfg ext query input
  have hresultKnown : result ∈ query.store.block_roots :=
    (find_latest_confirmed_descendant_ge cfg ext query hwf hwalk hhead
      input hinput).2
  by_cases hcrossing : ∃ a c : Root,
      CurrentTargetAcceptedEdge cfg ext query input a c
  · obtain ⟨a, c, hedge⟩ := hcrossing
    have hstrict : result ≠ input := by
      simpa only [result] using
        CurrentTargetAcceptedEdge.result_ne_input cfg ext
          hwf hwalk hhead hinput hedge
    have hbelow : is_ancestor query.store (get_head cfg query.store)
        (get_node_for_root result) = true := by
      simpa only [result] using strictSelectedResult_below_head cfg ext
        hwf hwalk hhead hinput (by simpa only [result] using hstrict)
    have hboundary : compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) ≤
          (query.store.blocks result).slot := by
      rw [← hresultCurrent]
      exact start_slot_at_block_epoch_le cfg query.store result
    have hboundaryWalk : WalkKnown query.store
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store))
        (get_head cfg query.store).root :=
      hcurrentWalk _ hhead
    have htargetEq := current_target_eq_checkpoint_of_current_epoch_ancestor
      cfg hwf hbelow (by simpa only [result] using hresultCurrent) hboundaryWalk
    obtain ⟨hcert⟩ := hcrossingCertificate a c hedge
    exact ⟨by simpa only [result, htargetEq] using hcert⟩
  · have hinputCurrent :=
      selectedInput_current_of_result_current_no_crossing cfg ext
        hwf hwalk hhead hinput hinputEpoch
          (by simpa only [result] using hresultCurrent) hcrossing
    obtain ⟨hcert⟩ := hinputCertificate hinputCurrent
    have hresultInput : is_ancestor query.store
        (get_node_for_root result) (get_node_for_root input) = true :=
      (find_latest_confirmed_descendant_ge cfg ext query hwf hwalk hhead
        input hinput).1
    have hboundary : compute_start_slot_at_epoch cfg
        (get_block_epoch cfg query.store input) ≤
          (query.store.blocks input).slot :=
      start_slot_at_block_epoch_le cfg query.store input
    have hboundaryWalk : WalkKnown query.store
        (compute_start_slot_at_epoch cfg
          (get_block_epoch cfg query.store input)) result :=
      by
        rw [hinputCurrent]
        exact hcurrentWalk result hresultKnown
    have hcheckpointRoot := get_checkpoint_block_of_ancestor cfg hwf
      hresultInput hboundary hboundaryWalk
    have hresultEpoch : get_block_epoch cfg query.store result =
        get_block_epoch cfg query.store input := by
      rw [hresultCurrent, hinputCurrent]
    have hcheckpoint : get_checkpoint_for_block cfg query.store result
        (get_block_epoch cfg query.store result) =
      get_checkpoint_for_block cfg query.store input
        (get_block_epoch cfg query.store input) := by
      simp only [get_checkpoint_for_block]
      rw [hresultEpoch]
      exact congrArg
        (Checkpoint.mk (get_block_epoch cfg query.store input)) hcheckpointRoot
    exact ⟨by simpa only [result, hcheckpoint] using hcert⟩

/-! ## Concrete trajectory interfaces

These predicates mention only the actual `E.fcrStep`/`E.confirmed` recurrence.
They deliberately do not quantify over arbitrary `FastConfirmationStore`s.
-/

/-- Exact strengthening of `get_latest_confirmed_call_cases_minimal`: when the
handler actually calls the selector, retain both its concrete reset input and
the executable recency guard which enabled that call. -/
theorem getLatestConfirmed_actualCallCases
    (query : FastConfirmationStore Root) :
    (get_latest_confirmed cfg ext query = query.confirmed_root ∨
      get_latest_confirmed cfg ext query =
        query.store.finalized_checkpoint.root ∨
      get_latest_confirmed cfg ext query =
        query.current_epoch_observed_justified_checkpoint.root) ∨
    ∃ input : Root,
      (input = query.confirmed_root ∨
        input = query.store.finalized_checkpoint.root ∨
        input = query.current_epoch_observed_justified_checkpoint.root) ∧
      get_block_epoch cfg query.store input + 1 ≥
        get_current_store_epoch cfg query.store ∧
      get_latest_confirmed cfg ext query =
        find_latest_confirmed_descendant cfg ext query input := by
  generalize hout : get_latest_confirmed cfg ext query = result
  simp only [get_latest_confirmed] at hout
  split_ifs at hout <;>
    subst hout <;>
      first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr (Or.inl rfl))
      | exact Or.inl (Or.inr (Or.inr rfl))
      | exact Or.inr ⟨_, Or.inl rfl, by assumption, rfl⟩
      | exact Or.inr ⟨_, Or.inr (Or.inl rfl), by assumption, rfl⟩
      | exact Or.inr ⟨_, Or.inr (Or.inr rfl), by assumption, rfl⟩

/-- Auxiliary reset-free branch provenance.  This is used only by the
specialized helper induction below; the final trajectory theorem classifies
all three actual reset inputs and does not assume this predicate. -/
def UsesCarriedConfirmedInputAt (v : ValidatorIndex) (n : ℕ) : Prop :=
  get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) =
    find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v n)
      (E.confirmed cfg ext v n)

def CarriedConfirmedInputRecentAt (v : ValidatorIndex) (n : ℕ) : Prop :=
  get_block_epoch cfg (E.fcrStep cfg ext v n).store
      (E.confirmed cfg ext v n) + 1 ≥
    get_current_store_epoch cfg (E.fcrStep cfg ext v n).store

def CurrentCarriedSelectorTrajectory (v : ValidatorIndex) : Prop :=
  ∀ n : ℕ, E.IsFCRCallAt cfg ext v n →
    get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v (n + 1)) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) →
    E.UsesCarriedConfirmedInputAt cfg ext v n ∧
      E.CarriedConfirmedInputRecentAt cfg ext v n

/-- Faithful per-call certificate semantics permitted as the external input to
Lemma 27: a retained crossing in an actual honest FCR invocation receives a
concrete certificate for that invocation's helper target. -/
def ActualCrossingCurrentTargetCertificateProducer
    (anchor : Checkpoint Root) (v : ValidatorIndex) : Prop :=
  ∀ n : ℕ, ∀ input : Root,
    (input = (E.fcrStep cfg ext v n).confirmed_root ∨
      input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
      input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
    E.IsFCRCallAt cfg ext v n →
    ∀ a c : Root,
      CurrentTargetAcceptedEdge cfg ext (E.fcrStep cfg ext v n)
        input a c →
      Nonempty (CertifiedJustified cfg E anchor
        (get_current_target cfg (E.fcrStep cfg ext v n).store))

/-- Ghost certificate invariant attached to the checkpoint of the concrete
confirmed root.  It is conditional on that root being current-epoch; previous
epoch confirmed blocks need not themselves have a justified checkpoint. -/
structure CurrentConfirmedCheckpointCertifiedAt
    (anchor : Checkpoint Root) (v : ValidatorIndex) (n : ℕ) : Prop where
  confirmed_known : E.confirmed cfg ext v n ∈
    (E.store cfg ext v n).block_roots
  certificate :
    get_block_epoch cfg (E.store cfg ext v n) (E.confirmed cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v n) →
      Nonempty (CertifiedJustified cfg E anchor
        (get_checkpoint_for_block cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n)
          (get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n))))

/-! ## The concrete trajectory induction -/

/-
/-- Paper Lemma 27 as a ghost invariant over the actual execution trajectory.

At a slot call whose confirmed output is current-epoch, executable provenance
identifies the carried confirmed root as the selector input.  A crossing in
that invocation uses `hcrossing`; otherwise the local trace theorem proves the
input was already current and the induction hypothesis is transported through
the growing store.  Between calls, the same transport carries the witness.

The sole base certificate is the trusted anchor constructor, with the
checkpoint-sync-safe boundary alignment proved above. -/
theorem currentConfirmedCheckpointCertified_of_carriedTrajectory
    (hSA : SpecAssumptions cfg ext E)
    (hpayload : PayloadEnvelopeRelay cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (htrajectory : E.CurrentCarriedSelectorTrajectory cfg ext v)
    (hcrossing : E.ActualCrossingCurrentTargetCertificateProducer
      cfg ext anchor v) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.CurrentConfirmedCheckpointCertifiedAt cfg ext anchor v n := by
  have hA : SelectedMarginAssumptions cfg ext E :=
    hSA.toSelectedMarginAssumptions cfg ext hpayload
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgenSlots : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  intro n
  induction n with
  | zero =>
      intro _hH0
      intro _hcurrent
      have hconfirmedAnchor : E.confirmed cfg ext v 0 = anchor.root := by
        rw [E.confirmed_zero, hanchor]
        change E.genesis_store.finalized_checkpoint.root =
          E.genesis_store.justified_checkpoint.root
        rw [hgenEq]
        rfl
      have hcheckpoint := E.trustedAnchor_checkpointForBlock cfg ext hA
        hanchor hboundary
      rw [hconfirmedAnchor]
      change Nonempty (CertifiedJustified cfg E anchor
        (get_checkpoint_for_block cfg E.genesis_store anchor.root
          (get_block_epoch cfg E.genesis_store anchor.root)))
      rw [hcheckpoint]
      exact ⟨CertifiedJustified.anchor⟩
  | succ n ih =>
      intro hHn1
      intro hcurrentN1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hknownN : E.confirmed cfg ext v n ∈
          (E.store cfg ext v n).block_roots :=
        E.confirmed_root_known_selected cfg ext hSA v hv n hHn
      have hknownN1 : E.confirmed cfg ext v n ∈
          (E.store cfg ext v (n + 1)).block_roots :=
        (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
      have hblockAgree :
          (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
            (E.store cfg ext v (n + 1)).blocks
              (E.confirmed cfg ext v n) :=
        hA.wellFormed.blocks_agree
          (E.blockProvenance cfg ext v n)
          (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
      by_cases hadv : E.IsFCRCallAt cfg ext v n
      · have hcall := htrajectory n hadv hcurrentN1
        have hconfirmedOut : E.confirmed cfg ext v (n + 1) =
            find_latest_confirmed_descendant cfg ext
              (E.fcrStep cfg ext v n) (E.confirmed cfg ext v n) := by
          calc
            E.confirmed cfg ext v (n + 1) =
                get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) :=
              E.confirmed_succ_of_advance cfg ext v n hadv
            _ = find_latest_confirmed_descendant cfg ext
                (E.fcrStep cfg ext v n) (E.confirmed cfg ext v n) := hcall.1
        obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
          E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
            hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
        have hheadQ : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
            (E.fcrStep cfg ext v n).store.block_roots := by
          rw [E.fcrStep_store]
          exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
            hv (n + 1) hHn1
        have hwfQuery : ParentSlotLt (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store] using hwfQ
        have hwalkQuery : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
            ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
              WalkKnown (E.fcrStep cfg ext v n).store
                ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
          simpa only [E.fcrStep_store] using hwalkQ
        have hinputQ : E.confirmed cfg ext v n ∈
            (E.fcrStep cfg ext v n).store.block_roots := by
          simpa only [E.fcrStep_store] using hknownN1
        have hinputSlotUpperQ :
            ((E.fcrStep cfg ext v n).store.blocks
              (E.confirmed cfg ext v n)).slot ≤
              get_current_slot cfg (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store] using
            E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots
              v (n + 1) (E.confirmed cfg ext v n) hknownN1
        have hinputEpochUpper : get_block_epoch cfg
              (E.fcrStep cfg ext v n).store (E.confirmed cfg ext v n) ≤
            get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          simp only [get_block_epoch, get_current_store_epoch,
            compute_epoch_at_slot]
          exact Nat.div_le_div_right hinputSlotUpperQ
        have hinputEpoch :
            get_block_epoch cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.fcrStep cfg ext v n).store ∨
            get_block_epoch cfg (E.fcrStep cfg ext v n).store
                  (E.confirmed cfg ext v n) + 1 =
              get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          have hrecent := hcall.2
          omega
        have hresultCurrent : get_block_epoch cfg
              (E.fcrStep cfg ext v n).store
              (find_latest_confirmed_descendant cfg ext
                (E.fcrStep cfg ext v n) (E.confirmed cfg ext v n)) =
            get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store, ← hconfirmedOut] using hcurrentN1
        have hinputCertificate :
            get_block_epoch cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.fcrStep cfg ext v n).store →
            Nonempty (CertifiedJustified cfg E anchor
              (get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n)
                (get_block_epoch cfg (E.fcrStep cfg ext v n).store
                  (E.confirmed cfg ext v n)))) := by
          intro hcurrentInputQ
          have hinputSlotUpperN :
              ((E.store cfg ext v n).blocks
                (E.confirmed cfg ext v n)).slot ≤
                get_current_slot cfg (E.store cfg ext v n) :=
            E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots
              v n (E.confirmed cfg ext v n) hknownN
          have hcurrentMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
              get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
            simp only [get_current_store_epoch, E.store_current_slot cfg ext,
              compute_epoch_at_slot]
            exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
          have hblockEpochNUpper : get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) ≤
              get_current_store_epoch cfg (E.store cfg ext v n) := by
            simp only [get_block_epoch, get_current_store_epoch,
              compute_epoch_at_slot]
            exact Nat.div_le_div_right hinputSlotUpperN
          have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) =
              get_block_epoch cfg (E.store cfg ext v (n + 1))
                (E.confirmed cfg ext v n) := by
            simp only [get_block_epoch, hblockAgree]
          have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
              get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
            have hreverse : get_current_store_epoch cfg
                (E.store cfg ext v (n + 1)) ≤
                  get_current_store_epoch cfg (E.store cfg ext v n) := by
              rw [← E.fcrStep_store] at hblockEpochAgree
              rw [← hcurrentInputQ, ← hblockEpochAgree]
              exact hblockEpochNUpper
            exact Nat.le_antisymm hcurrentMono hreverse
          have hcurrentInputN : get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.store cfg ext v n) := by
            calc
              get_block_epoch cfg (E.store cfg ext v n)
                  (E.confirmed cfg ext v n) =
                  get_block_epoch cfg (E.store cfg ext v (n + 1))
                    (E.confirmed cfg ext v n) := hblockEpochAgree
              _ = get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
                simpa only [E.fcrStep_store] using hcurrentInputQ
              _ = get_current_store_epoch cfg (E.store cfg ext v n) := hcurrentEq.symm
          obtain ⟨hcert⟩ := ih hHn hcurrentInputN
          have hstart : compute_start_slot_at_epoch cfg
                (get_block_epoch cfg (E.store cfg ext v n)
                  (E.confirmed cfg ext v n)) ≤
              ((E.store cfg ext v n).blocks
                (E.confirmed cfg ext v n)).slot :=
            start_slot_at_block_epoch_le cfg (E.store cfg ext v n)
              (E.confirmed cfg ext v n)
          have htransport := E.checkpointForBlock_storeLE cfg ext hA hv
            (Nat.le_succ n) hHn hknownN hstart
          have hcheckpointEq : get_checkpoint_for_block cfg
                (E.store cfg ext v n) (E.confirmed cfg ext v n)
                  (get_block_epoch cfg (E.store cfg ext v n)
                    (E.confirmed cfg ext v n)) =
              get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n)
                  (get_block_epoch cfg (E.fcrStep cfg ext v n).store
                    (E.confirmed cfg ext v n)) := by
            rw [E.fcrStep_store, ← hblockEpochAgree]
            exact htransport
          exact ⟨by simpa only [hcheckpointEq] using hcert⟩
        have hcert := E.selectedCurrentCheckpointCertified_of_input_or_crossing
          cfg ext hwfQuery hwalkQuery hheadQ hinputQ hinputEpoch
            hresultCurrent hinputCertificate
            (fun a c hedge => hcrossing n (E.confirmed cfg ext v n)
              (Or.inl (E.fcrStep_confirmed_root cfg ext v n).symm)
              hadv a c hedge)
        simpa only [E.fcrStep_store, ← hconfirmedOut] using hcert
      · have hconfirmedEq : E.confirmed cfg ext v (n + 1) =
            E.confirmed cfg ext v n :=
          E.confirmed_succ_of_no_advance cfg ext v n hadv
        have hslotEq : get_current_slot cfg (E.store cfg ext v n) =
            get_current_slot cfg (E.store cfg ext v (n + 1)) := by
          have hmono : get_current_slot cfg (E.store cfg ext v n) ≤
              get_current_slot cfg (E.store cfg ext v (n + 1)) := by
            simpa only [E.store_current_slot cfg ext] using
              E.slot_at_mono cfg (Nat.le_succ n)
          exact Nat.le_antisymm hmono (Nat.le_of_not_gt hadv)
        have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
              (E.confirmed cfg ext v n) =
            get_block_epoch cfg (E.store cfg ext v (n + 1))
              (E.confirmed cfg ext v n) := by
          simp only [get_block_epoch, hblockAgree]
        have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
            get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
          simp only [get_current_store_epoch, hslotEq]
        have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
              (E.confirmed cfg ext v n) =
            get_current_store_epoch cfg (E.store cfg ext v n) := by
          rw [hblockEpochAgree, hcurrentEq, ← hconfirmedEq]
          exact hcurrentN1
        obtain ⟨hcert⟩ := ih hHn hcurrentN
        have hstart : compute_start_slot_at_epoch cfg
              (get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n)) ≤
            ((E.store cfg ext v n).blocks
              (E.confirmed cfg ext v n)).slot :=
          start_slot_at_block_epoch_le cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n)
        have htransport := E.checkpointForBlock_storeLE cfg ext hA hv
          (Nat.le_succ n) hHn hknownN hstart
        have hcheckpointEq : get_checkpoint_for_block cfg
              (E.store cfg ext v n) (E.confirmed cfg ext v n)
                (get_block_epoch cfg (E.store cfg ext v n)
                  (E.confirmed cfg ext v n)) =
            get_checkpoint_for_block cfg (E.store cfg ext v (n + 1))
              (E.confirmed cfg ext v (n + 1))
                (get_block_epoch cfg (E.store cfg ext v (n + 1))
                  (E.confirmed cfg ext v (n + 1))) := by
          rw [hconfirmedEq, ← hblockEpochAgree]
          exact htransport
        exact ⟨by simpa only [hcheckpointEq] using hcert⟩

-/

/-! ## Full actual-call induction, including reset inputs -/

/-- One recurrence step of the Lemma-27 invariant.  The executable
`get_latest_confirmed` classification chooses a direct return or the exact
selector input.  Carried inputs consume `hprevious`; finalized/observed inputs
consume only `hreset`. -/
theorem currentConfirmedCheckpointCertified_succ
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hreset : E.ActualResetInputCheckpointRealization
      cfg ext anchor v)
    (hcrossing : E.ActualCrossingCurrentTargetCertificateProducer
      cfg ext anchor v)
    (hprevious : E.CurrentConfirmedCheckpointCertifiedAt
      cfg ext anchor v n) :
    E.CurrentConfirmedCheckpointCertifiedAt cfg ext anchor v (n + 1) := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgenSlots : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hanchorSlot⟩
  have hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots := hprevious.confirmed_known
  have hanchorEpochLeConfirmed : anchor.epoch ≤
      get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) :=
    E.trustedAnchor_epoch_le_blockEpoch cfg ext hA hanchor hboundary
      v n hknownN
  have hconfirmedBoundaryWalkN : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (get_block_epoch cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n)))
      (E.confirmed cfg ext v n) :=
    E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      v n hanchorEpochLeConfirmed hknownN
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks (E.confirmed cfg ext v n) :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  by_cases hadv : E.IsFCRCallAt cfg ext v n
  · have hconfirmedLatest : E.confirmed cfg ext v (n + 1) =
        get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) :=
      E.confirmed_succ_of_advance cfg ext v n hadv
    obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
      E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
    have hwfQuery : ParentSlotLt (E.fcrStep cfg ext v n).store := by
      simpa only [E.fcrStep_store] using hwfQ
    have hwalkQuery : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
        ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
          WalkKnown (E.fcrStep cfg ext v n).store
            ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
      simpa only [E.fcrStep_store] using hwalkQ
    have hheadQ : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
        (E.fcrStep cfg ext v n).store.block_roots := by
      rw [E.fcrStep_store]
      exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
        hv (n + 1) hHn1
    have hanchorEpochLeCurrent : anchor.epoch ≤
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
      E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
        v (n + 1)
    have hcurrentWalkQuery : ∀ r ∈
        (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg
              (E.fcrStep cfg ext v n).store)) r := by
      intro r hr
      have hrStore : r ∈ (E.store cfg ext v (n + 1)).block_roots := by
        simpa only [E.fcrStep_store] using hr
      have hwalk := E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA
        hanchor hboundary v (n + 1) hanchorEpochLeCurrent hrStore
      simpa only [E.fcrStep_store] using hwalk
    have hcarriedQ : E.confirmed cfg ext v n ∈
        (E.fcrStep cfg ext v n).store.block_roots := by
      simpa only [E.fcrStep_store] using hknownN1
    have hinputKnown : ∀ input : Root,
        (input = (E.fcrStep cfg ext v n).confirmed_root ∨
          input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
          input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
        input ∈ (E.fcrStep cfg ext v n).store.block_roots := by
      intro input hkind
      rcases hkind with hcarried | hfinalized | hobserved
      · rw [hcarried, E.fcrStep_confirmed_root]
        exact hcarriedQ
      · exact (hreset n hHn1 input (Or.inl hfinalized)).1
      · exact (hreset n hHn1 input (Or.inr hobserved)).1
    have hcarriedCertificate :
        get_block_epoch cfg (E.fcrStep cfg ext v n).store
            (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.fcrStep cfg ext v n).store →
        Nonempty (CertifiedJustified cfg E anchor
          (get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store
            (E.confirmed cfg ext v n)
            (get_block_epoch cfg (E.fcrStep cfg ext v n).store
              (E.confirmed cfg ext v n)))) := by
      intro hcurrentInputQ
      have hinputSlotUpperN :
          ((E.store cfg ext v n).blocks (E.confirmed cfg ext v n)).slot ≤
            get_current_slot cfg (E.store cfg ext v n) :=
        E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots
          v n (E.confirmed cfg ext v n) hknownN
      have hblockEpochNUpper : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) ≤
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        simp only [get_block_epoch, get_current_store_epoch,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right hinputSlotUpperN
      have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_block_epoch cfg (E.store cfg ext v (n + 1))
            (E.confirmed cfg ext v n) := by
        simp only [get_block_epoch, hblockAgree]
      have hcurrentMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        simp only [get_current_store_epoch, E.store_current_slot cfg ext,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
      have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        apply Nat.le_antisymm hcurrentMono
        calc
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) =
              get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
            rw [E.fcrStep_store]
          _ = get_block_epoch cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n) := hcurrentInputQ.symm
          _ = get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) := by
            rw [E.fcrStep_store, ← hblockEpochAgree]
          _ ≤ get_current_store_epoch cfg (E.store cfg ext v n) :=
            hblockEpochNUpper
      have hcurrentInputN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        calc
          get_block_epoch cfg (E.store cfg ext v n)
              (E.confirmed cfg ext v n) =
              get_block_epoch cfg (E.store cfg ext v (n + 1))
                (E.confirmed cfg ext v n) := hblockEpochAgree
          _ = get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
            simpa only [E.fcrStep_store] using hcurrentInputQ
          _ = get_current_store_epoch cfg (E.store cfg ext v n) := hcurrentEq.symm
      obtain ⟨hcert⟩ := hprevious.certificate hcurrentInputN
      have htransport := E.checkpointForBlock_storeLE cfg ext hA
        (Nat.le_succ n) hknownN hconfirmedBoundaryWalkN
      have hcheckpointEq : get_checkpoint_for_block cfg
            (E.store cfg ext v n) (E.confirmed cfg ext v n)
              (get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n)) =
          get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store
            (E.confirmed cfg ext v n)
              (get_block_epoch cfg (E.fcrStep cfg ext v n).store
                (E.confirmed cfg ext v n)) := by
        rw [E.fcrStep_store, ← hblockEpochAgree]
        exact htransport
      exact ⟨by simpa only [hcheckpointEq] using hcert⟩
    have hinputCertificate : ∀ input : Root,
        (input = (E.fcrStep cfg ext v n).confirmed_root ∨
          input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
          input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
        get_block_epoch cfg (E.fcrStep cfg ext v n).store input =
            get_current_store_epoch cfg (E.fcrStep cfg ext v n).store →
          Nonempty (CertifiedJustified cfg E anchor
            (get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store input
              (get_block_epoch cfg (E.fcrStep cfg ext v n).store input))) := by
      intro input hkind hcurrentInput
      rcases hkind with hcarried | hfinalized | hobserved
      · subst input
        simpa only [E.fcrStep_confirmed_root] using
          hcarriedCertificate (by
            simpa only [E.fcrStep_confirmed_root] using hcurrentInput)
      · exact (hreset n hHn1 input (Or.inl hfinalized)).2 hcurrentInput
      · exact (hreset n hHn1 input (Or.inr hobserved)).2 hcurrentInput
    have hdirectInvariant : ∀ input : Root,
        (input = (E.fcrStep cfg ext v n).confirmed_root ∨
          input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
          input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
        get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) = input →
        E.CurrentConfirmedCheckpointCertifiedAt cfg ext anchor v (n + 1) := by
      intro input hkind hlatest
      have houtput : E.confirmed cfg ext v (n + 1) = input :=
        hconfirmedLatest.trans hlatest
      have hknownInput := hinputKnown input hkind
      refine {
        confirmed_known := ?_
        certificate := ?_
      }
      · simpa only [E.fcrStep_store, ← houtput] using hknownInput
      · intro hcurrentN1
        have hcurrentInput : get_block_epoch cfg
              (E.fcrStep cfg ext v n).store input =
            get_current_store_epoch cfg
              (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store, ← houtput] using hcurrentN1
        have hcert := hinputCertificate input hkind hcurrentInput
        simpa only [E.fcrStep_store, ← houtput] using hcert
    have hselectedInvariant : ∀ input : Root,
        (input = (E.fcrStep cfg ext v n).confirmed_root ∨
          input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
          input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) →
        get_block_epoch cfg (E.fcrStep cfg ext v n).store input + 1 ≥
          get_current_store_epoch cfg (E.fcrStep cfg ext v n).store →
        get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) =
          find_latest_confirmed_descendant cfg ext
            (E.fcrStep cfg ext v n) input →
        E.CurrentConfirmedCheckpointCertifiedAt cfg ext anchor v (n + 1) := by
      intro input hkind hrecent hselected
      have houtput : E.confirmed cfg ext v (n + 1) =
          find_latest_confirmed_descendant cfg ext
            (E.fcrStep cfg ext v n) input :=
        hconfirmedLatest.trans hselected
      have hinputKnownQ := hinputKnown input hkind
      have hresultKnown : find_latest_confirmed_descendant cfg ext
            (E.fcrStep cfg ext v n) input ∈
          (E.fcrStep cfg ext v n).store.block_roots :=
        (find_latest_confirmed_descendant_ge cfg ext
          (E.fcrStep cfg ext v n) hwfQuery hwalkQuery hheadQ
          input hinputKnownQ).2
      refine {
        confirmed_known := ?_
        certificate := ?_
      }
      · simpa only [E.fcrStep_store, ← houtput] using hresultKnown
      · intro hcurrentN1
        have hinputSlotUpper :
            ((E.fcrStep cfg ext v n).store.blocks input).slot ≤
              get_current_slot cfg (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store] using
            E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots
              v (n + 1) input (by
                simpa only [E.fcrStep_store] using hinputKnownQ)
        have hinputEpochUpper : get_block_epoch cfg
              (E.fcrStep cfg ext v n).store input ≤
            get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          simp only [get_block_epoch, get_current_store_epoch,
            compute_epoch_at_slot]
          exact Nat.div_le_div_right hinputSlotUpper
        have hinputEpoch :
            get_block_epoch cfg (E.fcrStep cfg ext v n).store input =
                get_current_store_epoch cfg (E.fcrStep cfg ext v n).store ∨
              get_block_epoch cfg (E.fcrStep cfg ext v n).store input + 1 =
                get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          by_cases heq : get_block_epoch cfg (E.fcrStep cfg ext v n).store input =
              get_current_store_epoch cfg (E.fcrStep cfg ext v n).store
          · exact Or.inl heq
          · right
            apply Nat.le_antisymm
            · exact Nat.succ_le_of_lt
                (Nat.lt_of_le_of_ne hinputEpochUpper heq)
            · exact hrecent
        have hresultCurrent : get_block_epoch cfg
              (E.fcrStep cfg ext v n).store
                (find_latest_confirmed_descendant cfg ext
                  (E.fcrStep cfg ext v n) input) =
            get_current_store_epoch cfg (E.fcrStep cfg ext v n).store := by
          simpa only [E.fcrStep_store, ← houtput] using hcurrentN1
        have hcert := E.selectedCurrentCheckpointCertified_of_input_or_crossing
          cfg ext hwfQuery hwalkQuery hheadQ hcurrentWalkQuery
            hinputKnownQ hinputEpoch
            hresultCurrent (hinputCertificate input hkind)
            (fun a c hedge => hcrossing n input hkind hadv a c hedge)
        simpa only [E.fcrStep_store, ← houtput] using hcert
    rcases getLatestConfirmed_actualCallCases cfg ext
        (E.fcrStep cfg ext v n) with hdirect | hselected
    · rcases hdirect with hcarried | hfinalized | hobserved
      · exact hdirectInvariant _ (Or.inl rfl) hcarried
      · exact hdirectInvariant _ (Or.inr (Or.inl rfl)) hfinalized
      · exact hdirectInvariant _ (Or.inr (Or.inr rfl)) hobserved
    · obtain ⟨input, hkind, hrecent, hselected⟩ := hselected
      exact hselectedInvariant input hkind hrecent hselected
  · have hconfirmedEq : E.confirmed cfg ext v (n + 1) =
        E.confirmed cfg ext v n :=
      E.confirmed_succ_of_no_advance cfg ext v n hadv
    have hslotEq : get_current_slot cfg (E.store cfg ext v n) =
        get_current_slot cfg (E.store cfg ext v (n + 1)) := by
      have hmono : get_current_slot cfg (E.store cfg ext v n) ≤
          get_current_slot cfg (E.store cfg ext v (n + 1)) := by
        simpa only [E.store_current_slot cfg ext] using
          E.slot_at_mono cfg (Nat.le_succ n)
      exact Nat.le_antisymm hmono (Nat.le_of_not_gt hadv)
    have hblockEpochAgree : get_block_epoch cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n) =
        get_block_epoch cfg (E.store cfg ext v (n + 1))
          (E.confirmed cfg ext v n) := by
      simp only [get_block_epoch, hblockAgree]
    have hcurrentEq : get_current_store_epoch cfg (E.store cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
      simp only [get_current_store_epoch, hslotEq]
    refine {
      confirmed_known := ?_
      certificate := ?_
    }
    · rw [hconfirmedEq]
      exact hknownN1
    · intro hcurrentN1
      have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochAgree, hcurrentEq, ← hconfirmedEq]
        exact hcurrentN1
      obtain ⟨hcert⟩ := hprevious.certificate hcurrentN
      have htransport := E.checkpointForBlock_storeLE cfg ext hA
        (Nat.le_succ n) hknownN hconfirmedBoundaryWalkN
      have hcheckpointEq : get_checkpoint_for_block cfg
            (E.store cfg ext v n) (E.confirmed cfg ext v n)
              (get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n)) =
          get_checkpoint_for_block cfg (E.store cfg ext v (n + 1))
            (E.confirmed cfg ext v (n + 1))
              (get_block_epoch cfg (E.store cfg ext v (n + 1))
                (E.confirmed cfg ext v (n + 1))) := by
        rw [hconfirmedEq, ← hblockEpochAgree]
        exact htransport
      exact ⟨by simpa only [hcheckpointEq] using hcert⟩

/-- Full Lemma-27 trajectory invariant.  Unlike the carried-only
helper, this theorem consumes the executable three-way reset classification
at every call.  Its only semantic inputs are concrete certificates for actual
reset checkpoints and the Lemma-9 certificate producer for actual retained
crossings. -/
theorem currentConfirmedCheckpointCertified_of_actualTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (hreset : E.ActualResetInputCheckpointRealization
      cfg ext anchor v)
    (hcrossing : E.ActualCrossingCurrentTargetCertificateProducer
      cfg ext anchor v) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.CurrentConfirmedCheckpointCertifiedAt cfg ext anchor v n := by
  intro n
  induction n with
  | zero =>
      intro _hH0
      obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
      have hconfirmedAnchor : E.confirmed cfg ext v 0 = anchor.root := by
        rw [E.confirmed_zero, hanchor]
        change E.genesis_store.finalized_checkpoint.root =
          E.genesis_store.justified_checkpoint.root
        rw [hgenEq]
        rfl
      have hanchorRoot : anchor.root = ablk.root := by
        rw [hanchor, hgenEq]
        rfl
      have hanchorKnown : anchor.root ∈ E.genesis_store.block_roots := by
        rw [hgenEq, hanchorRoot]
        simp only [get_forkchoice_store, List.mem_singleton]
      have hcheckpoint := E.trustedAnchor_checkpointForBlock cfg ext hA
        hanchor hboundary
      refine {
        confirmed_known := ?_
        certificate := ?_
      }
      · change E.confirmed cfg ext v 0 ∈ E.genesis_store.block_roots
        simpa only [hconfirmedAnchor] using hanchorKnown
      · intro _hcurrent
        change Nonempty (CertifiedJustified cfg E anchor
          (get_checkpoint_for_block cfg E.genesis_store
            (E.confirmed cfg ext v 0)
            (get_block_epoch cfg E.genesis_store
              (E.confirmed cfg ext v 0))))
        rw [hconfirmedAnchor, hcheckpoint]
        exact ⟨CertifiedJustified.anchor⟩
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      exact E.currentConfirmedCheckpointCertified_succ cfg ext hA
        hanchor hboundary hv
        hHn1 hreset hcrossing (ih hHn)

/-! ## Discharging the historical producer at an actual selector call -/

/-- An actual strict selector call receives the historical current-target
producer from the trajectory invariant.  `hkind` and `hselected` are precisely
the witnesses returned by `getLatestConfirmed_actualCallCases`; no ancestry or
safety relation is supplied by the caller. -/
theorem historicalCurrentTargetCertificateProducerAt_of_actualTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hreset : E.ActualResetInputCheckpointRealization
      cfg ext anchor v)
    (hcrossing : E.ActualCrossingCurrentTargetCertificateProducer
      cfg ext anchor v)
    (hadv : E.IsFCRCallAt cfg ext v n)
    {input : Root}
    (hkind : input = (E.fcrStep cfg ext v n).confirmed_root ∨
      input = (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∨
      input = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root)
    (hselected : get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) =
      find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v n) input)
    (hstrict : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v n) input ≠ input) :
    E.HistoricalCurrentTargetCertificateProducerAt cfg ext anchor (n + 1)
      (E.fcrStep cfg ext v n) input
      (find_latest_confirmed_descendant cfg ext
          (E.fcrStep cfg ext v n) input) := by
  have hHn : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hinvariantN :=
    E.currentConfirmedCheckpointCertified_of_actualTrajectory cfg ext hA
      hanchor hboundary hv hreset hcrossing n hHn
  have hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots := hinvariantN.confirmed_known
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hinputKnown : input ∈ (E.fcrStep cfg ext v n).store.block_roots := by
    rcases hkind with hcarried | hfinalized | hobserved
    · rw [hcarried, E.fcrStep_confirmed_root, E.fcrStep_store]
      exact hknownN1
    · exact (hreset n hHn1 input (Or.inl hfinalized)).1
    · exact (hreset n hHn1 input (Or.inr hobserved)).1
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
  have hwfQuery : ParentSlotLt (E.fcrStep cfg ext v n).store := by
    simpa only [E.fcrStep_store] using hwfQ
  have hwalkQuery : ∀ t ∈ (E.fcrStep cfg ext v n).store.block_roots,
      ∀ r ∈ (E.fcrStep cfg ext v n).store.block_roots,
        WalkKnown (E.fcrStep cfg ext v n).store
          ((E.fcrStep cfg ext v n).store.blocks t).slot r := by
    simpa only [E.fcrStep_store] using hwalkQ
  have hheadQ : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
      (E.fcrStep cfg ext v n).store.block_roots := by
    rw [E.fcrStep_store]
    exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hv (n + 1) hHn1
  have hanchorEpochLeCurrent : anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
    E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor hboundary
      v (n + 1)
  have hboundaryWalk : WalkKnown (E.fcrStep cfg ext v n).store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store))
      (get_head cfg (E.fcrStep cfg ext v n).store).root := by
    have hheadStore : (get_head cfg (E.fcrStep cfg ext v n).store).root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
      simpa only [E.fcrStep_store] using hheadQ
    have hwalk := E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA
      hanchor hboundary v (n + 1) hanchorEpochLeCurrent hheadStore
    simpa only [E.fcrStep_store] using hwalk
  intro hresultCurrent _hnoCrossing
  have houtput : E.confirmed cfg ext v (n + 1) =
      find_latest_confirmed_descendant cfg ext
        (E.fcrStep cfg ext v n) input :=
    (E.confirmed_succ_of_advance cfg ext v n hadv).trans hselected
  have hconfirmedCurrent : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v (n + 1)) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.fcrStep_store, ← houtput] using hresultCurrent
  have hinvariantN1 :=
    E.currentConfirmedCheckpointCertified_of_actualTrajectory cfg ext hA
      hanchor hboundary hv hreset hcrossing (n + 1) hHn1
  obtain ⟨hcert⟩ := hinvariantN1.certificate hconfirmedCurrent
  have hcertResult : CertifiedJustified cfg E anchor
      (get_checkpoint_for_block cfg (E.fcrStep cfg ext v n).store
        (find_latest_confirmed_descendant cfg ext
          (E.fcrStep cfg ext v n) input)
        (get_block_epoch cfg (E.fcrStep cfg ext v n).store
          (find_latest_confirmed_descendant cfg ext
            (E.fcrStep cfg ext v n) input))) := by
    simpa only [E.fcrStep_store, ← houtput] using hcert
  have hresultKnown : find_latest_confirmed_descendant cfg ext
        (E.fcrStep cfg ext v n) input ∈
      (E.fcrStep cfg ext v n).store.block_roots :=
    (find_latest_confirmed_descendant_ge cfg ext (E.fcrStep cfg ext v n)
      hwfQuery hwalkQuery hheadQ input hinputKnown).2
  have hbelow := strictSelectedResult_below_head cfg ext hwfQuery
    hwalkQuery hheadQ hinputKnown hstrict
  have htargetEq := current_target_eq_checkpoint_of_current_epoch_ancestor
    cfg hwfQuery hbelow hresultCurrent hboundaryWalk
  exact ⟨by simpa only [htargetEq] using hcertResult⟩

end Execution

end FastConfirmation.Spec

end
