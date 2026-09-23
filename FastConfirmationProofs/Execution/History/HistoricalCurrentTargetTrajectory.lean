module
public import FastConfirmationProofs.Execution.History.SelectedPreQueryHistoricalSIR
public import FastConfirmationProofs.FCRRule.FCRCallContracts
public import FastConfirmationProofs.Checkpoints.TrustedAnchorGeometry

@[expose] public section

/-!
# Historical current-target certificates along the concrete FCR trajectory

Paper Lemma 27 is temporal: a current-epoch candidate which did not enter the
current epoch in the present `find_latest_confirmed_descendant` invocation must
have inherited that epoch checkpoint from an earlier invocation.  Consequently
this obligation cannot faithfully be proved for two arbitrary lookalike
`FastConfirmationStore`s.

The execution model does retain the required history without adding a mutable
certificate field.  `Execution.fcr` is a recursive trajectory, `fcrStoreAtCall v n`
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
      CurrentTargetSelectedEdge cfg ext query input a c) :
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
        (show PreviousEpochSelectedEdge cfg ext query input a c from hprev).gates cfg ext
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
theorem CurrentTargetSelectedEdge.result_ne_input
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input a c : Root} (hinput : input ∈ query.store.block_roots)
    (hedge : CurrentTargetSelectedEdge cfg ext query input a c) :
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


/-! ## Concrete trajectory interfaces

These predicates mention only the actual `E.fcrStoreAtCall`/`E.confirmed` recurrence.
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
      by_cases hadv : E.IsScheduledFCRCallAt cfg ext v n
      · have hcall := htrajectory n hadv hcurrentN1
        have hconfirmedOut : E.confirmed cfg ext v (n + 1) =
            find_latest_confirmed_descendant cfg ext
              (E.fcrStoreAtCall cfg ext v n) (E.confirmed cfg ext v n) := by
          calc
            E.confirmed cfg ext v (n + 1) =
                get_latest_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n) :=
              E.confirmed_succ_of_advance cfg ext v n hadv
            _ = find_latest_confirmed_descendant cfg ext
                (E.fcrStoreAtCall cfg ext v n) (E.confirmed cfg ext v n) := hcall.1
        obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
          E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
            hA.externals_coherence hA.genesis hA.domain v hv (n + 1) hHn1
        have hheadQ : (get_head cfg (E.fcrStoreAtCall cfg ext v n).store).root ∈
            (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
          rw [E.fcrStep_store]
          exact E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
            hv (n + 1) hHn1
        have hwfQuery : ParentSlotLt (E.fcrStoreAtCall cfg ext v n).store := by
          simpa only [E.fcrStep_store] using hwfQ
        have hwalkQuery : ∀ t ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
            ∀ r ∈ (E.fcrStoreAtCall cfg ext v n).store.block_roots,
              WalkKnown (E.fcrStoreAtCall cfg ext v n).store
                ((E.fcrStoreAtCall cfg ext v n).store.blocks t).slot r := by
          simpa only [E.fcrStep_store] using hwalkQ
        have hinputQ : E.confirmed cfg ext v n ∈
            (E.fcrStoreAtCall cfg ext v n).store.block_roots := by
          simpa only [E.fcrStep_store] using hknownN1
        have hinputSlotUpperQ :
            ((E.fcrStoreAtCall cfg ext v n).store.blocks
              (E.confirmed cfg ext v n)).slot ≤
              get_current_slot cfg (E.fcrStoreAtCall cfg ext v n).store := by
          simpa only [E.fcrStep_store] using
            E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlots
              v (n + 1) (E.confirmed cfg ext v n) hknownN1
        have hinputEpochUpper : get_block_epoch cfg
              (E.fcrStoreAtCall cfg ext v n).store (E.confirmed cfg ext v n) ≤
            get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store := by
          simp only [get_block_epoch, get_current_store_epoch,
            compute_epoch_at_slot]
          exact Nat.div_le_div_right hinputSlotUpperQ
        have hinputEpoch :
            get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store ∨
            get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
                  (E.confirmed cfg ext v n) + 1 =
              get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store := by
          have hrecent := hcall.2
          omega
        have hresultCurrent : get_block_epoch cfg
              (E.fcrStoreAtCall cfg ext v n).store
              (find_latest_confirmed_descendant cfg ext
                (E.fcrStoreAtCall cfg ext v n) (E.confirmed cfg ext v n)) =
            get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store := by
          simpa only [E.fcrStep_store, ← hconfirmedOut] using hcurrentN1
        have hinputCertificate :
            get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
                (E.confirmed cfg ext v n) =
              get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext v n).store →
            Nonempty (CertifiedJustified cfg E anchor
              (get_checkpoint_for_block cfg (E.fcrStoreAtCall cfg ext v n).store
                (E.confirmed cfg ext v n)
                (get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
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
              get_checkpoint_for_block cfg (E.fcrStoreAtCall cfg ext v n).store
                (E.confirmed cfg ext v n)
                  (get_block_epoch cfg (E.fcrStoreAtCall cfg ext v n).store
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



/-! ## Discharging the historical producer at an actual selector call -/


end Execution

end FastConfirmation.Spec

end
