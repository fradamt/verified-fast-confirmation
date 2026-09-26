module
public import FastConfirmationInternal.FCRRule.PredictionSupport
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.Checkpoints.SelectedPreQueryAnchor
public import FastConfirmationProofs.FCRRule.SelectedCheckpointInclusionSupport
public import FastConfirmationProofs.Execution.History.CausalCheckpointEpochBound
public import FastConfirmationProofs.Checkpoints.CheckpointGeometry

@[expose] public section

/-!
# Historical, non-anchor pre-query SIR producers

`SelectedPreQueryAnchor` discharges the trusted-anchor disjunct of
`PreQueryTargetOriginAt`.  This file handles the remaining disjunct: an honest
ground vote, cast strictly before the selected query, targets the endpoint's
non-anchor justified checkpoint.

There are three materially different layers.

* Honest-vote geometry is executable.  For a post-anchor vote, the target is
  the epoch-boundary checkpoint of the voter's actual head.  In particular its
  declared epoch is the vote-slot epoch and its root is no later than that
  boundary in every store which knows it.
* The selector's exact call-site split is executable.  A previous-epoch result
  is either at epoch start or carries the actual no-conflict gate and its
  `FCRPredictionSupportAt` support premise.  A current-epoch result either
  has a retained crossing edge, which carries the actual current-target gate,
  or needs the historical gate propagation of paper Lemma 27.
* Turning those gates into historical checkpoint ordering is the paper SIR
  work.  Current-target certification can be consumed mechanically by concrete
  Casper same-epoch uniqueness.  The required producers are stated below as
  certificate-producing helper semantics, not as assumptions of the
  desired selected/justified ancestry.  The epoch-start short circuit is
  stronger: causal timing makes the middle and upper regions impossible, so
  it needs no certificate producer.

The post-anchor qualification is essential.  `Execution.vote` is deliberately
unconstrained before `E.slot_at cfg 0`.  The causal-origin interfaces now carry
the explicit lower bound `E.slot_at cfg 0 ≤ s`; every producer in this file
consumes that bound when invoking `HonestBehavior.votes_head`.  This prevents a
pre-anchor totalized vote from masquerading as historical FFG evidence.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Exact helper/call-site classification -/

/-- The three exact SIR call sites for a strict selected result.

The `currentHistorical` branch is not an invented failure case.  A strict
same-epoch advance can inherit a current-epoch input for which the relevant
`will_current_target_be_justified` call occurred in an earlier FCR invocation.
That is precisely paper Lemma 27's trajectory obligation.

The other two semantic branches retain the executable booleans and their exact
normative support premises.  Thus downstream work cannot silently invoke a
helper on an epoch-start short circuit or forget the final-result no-conflict
call site. -/
inductive StrictSelectedHistoricalSIRCallSite
    (q : ℕ) (query : FastConfirmationStore Root) (input result : Root) : Prop
  | currentCrossing
      (result_current : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store)
      (a c : Root)
      (edge : CurrentTargetSelectedEdge cfg ext query input a c)
      (gate : will_current_target_be_justified cfg ext query.store = true)
      (support : HonestVotesSupportTarget cfg E
        (get_current_target cfg query.store) q)
  | currentHistorical
      (result_current : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store)
      (no_crossing : ¬ ∃ a c : Root,
        CurrentTargetSelectedEdge cfg ext query input a c)
  | previousEpochStart
      (result_previous : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store)
      (at_start : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) = true)
  | previousNoConflict
      (result_previous : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store)
      (not_start : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) ≠ true)
      (gate : will_no_conflicting_checkpoint_be_justified cfg ext
        query.store = true)
      (support : HonestVotesTargetDescendFrom cfg E result
        (get_current_store_epoch cfg query.store) q)

/-- The exact selector and proviso facts classify a strict result into the
paper's historical-current, epoch-boundary, and mid-epoch no-conflict cases.

The support premise is stored by `FCRPredictionSupportAt` at execution index
`q`, whereas the executable query store's current slot is `E.slot_at cfg q`.
The equality premise below performs only that clock rewrite. -/
theorem strictSelectedHistoricalSIRCallSite
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    (hprovisos : FCRPredictionSupportAt cfg ext E v q query input) :
    StrictSelectedHistoricalSIRCallSite cfg ext E q query input
      (find_latest_confirmed_descendant cfg ext query input) := by
  let result := find_latest_confirmed_descendant cfg ext query input
  have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
    query hquery input hinput hinputEpoch hstrict
  rcases hfacts.current_or_previous_epoch with hcurrent | hprevious
  · by_cases hcross : ∃ a c : Root,
        CurrentTargetSelectedEdge cfg ext query input a c
    · obtain ⟨a, c, hedge⟩ := hcross
      obtain ⟨hgate, hsupport⟩ :=
        E.currentTargetAcceptedEdge_gate_and_support cfg ext hprovisos hedge
      exact .currentCrossing hcurrent a c hedge hgate hsupport
    · exact .currentHistorical hcurrent hcross
  · have hnotCurrent : get_block_epoch cfg query.store result ≠
        get_current_store_epoch cfg query.store := by
      intro heq
      rw [heq] at hprevious
      exact Nat.succ_ne_self _ hprevious
    by_cases hstart : is_start_slot_at_epoch cfg
        (get_current_slot cfg query.store) = true
    · exact .previousEpochStart hprevious hstart
    · obtain ⟨hgate, hsupport⟩ :=
        E.selectedPreviousResult_noConflict_gate_and_support cfg ext
          hprovisos rfl (by simpa only [result] using hstrict)
            hnotCurrent hstart
      exact .previousNoConflict hprevious hstart hgate hsupport

/-! ## Honest target geometry -/

/-- Store-local geometry of an honest post-anchor FFG target.  This is the
useful output of unwinding `HonestBehavior.votes_head`; it is independent of a
selected result and contains no compatibility conclusion. -/
structure PostAnchorHonestTargetGeometryAt
    (voteSlot : Slot) (store : Store Root)
    (target : Checkpoint Root) : Prop where
  target_epoch : target.epoch = compute_epoch_at_slot cfg voteSlot
  target_known : target.root ∈ store.block_roots
  target_root_before_boundary :
    (store.blocks target.root).slot ≤
      compute_start_slot_at_epoch cfg target.epoch

/-- Unwind a genuine post-anchor honest vote into endpoint checkpoint
geometry.  Block agreement is enough to transport the target root's slot: the
endpoint already knows its own justified root, so no forward-in-time premise
between the voting store and endpoint is needed. -/
theorem postAnchorHonestTargetGeometryAt_of_vote
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (htarget₀ : a₀.data.target =
      (E.store cfg ext w m).justified_checkpoint) :
    PostAnchorHonestTargetGeometryAt cfg s (E.store cfg ext w m)
      (E.store cfg ext w m).justified_checkpoint := by
  let J := (E.store cfg ext w m).justified_checkpoint
  have hcomm : i ∈ E.committee s :=
    hA.honest_behavior.votes_assigned i hi s
      (by rw [hvote₀]; exact Option.some_ne_none _)
  obtain ⟨k, index, hHk, hk, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi s hcomm hsH hs0
  have hvoteEq := hvote₀
  rw [hvoteHead] at hvoteEq
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
  obtain ⟨_, hattestation⟩ := hvoteEq
  have htarget :
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target =
        J := by
    rw [hattestation]
    exact htarget₀
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  obtain ⟨hwfK, hwalkK, _hjustK⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain i hi k hHk
  have hheadK : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi k hHk
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk
      hanchorSlot hanchorParent
  have hcore := E.store_wellFormedStoreCore cfg ext
    hA.externals_coherence.state_transition_slot hgws.core i k
  have hheadStateSlot :
      ((E.store cfg ext i k).block_states
        (get_head cfg (E.store cfg ext i k)).root).slot ≤ s := by
    rw [hcore.2 _ hheadK]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      hA.whole_seconds ⟨ast, ablk, hgenEq, hanchorSlot⟩ i k _ hheadK
    rwa [E.store_current_slot cfg ext i k, hk] at hblockSlot
  have htargetEpoch : J.epoch = compute_epoch_at_slot cfg s := by
    rw [← htarget]
    exact honest_attestation_data_target_epoch cfg ext
      (E.store cfg ext i k) s index
        hA.externals_coherence.process_slots_slot hheadStateSlot
  have htargetWalk : WalkKnown (E.store cfg ext i k)
      (compute_start_slot_at_epoch cfg J.epoch)
      (get_head cfg (E.store cfg ext i k)).root := by
    simpa only [htarget] using
      hwalkDomain i hi s k index hs0 hHk hk hvoteHead
  have htargetRoot : get_checkpoint_block cfg
      (E.store cfg ext i k) (get_head cfg (E.store cfg ext i k)).root J.epoch =
        J.root := by
    have htargetData : (honest_attestation_data cfg ext
        (E.store cfg ext i k) s index).target = J := by
      simpa only [honest_attestation_data_eq] using htarget
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext i k) s index
    rw [htargetData] at hroot
    exact hroot.symm
  have heta : (get_ancestor (E.store cfg ext i k)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (compute_start_slot_at_epoch cfg J.epoch)).root = J.root := by
    simpa only [get_checkpoint_block, get_node_for_root] using htargetRoot
  have htargetSpec := get_ancestor_spec hwfK htargetWalk
  simp only [get_node_for_root] at heta
  rw [heta] at htargetSpec
  have hJK : J.root ∈ (E.store cfg ext i k).block_roots :=
    htargetSpec.1
  have hJslotK : ((E.store cfg ext i k).blocks J.root).slot ≤
      compute_start_slot_at_epoch cfg J.epoch := htargetSpec.2
  have hJM : J.root ∈ (E.store cfg ext w m).block_roots :=
    hA.domain.justified_root_known w hw m hHm
  have hJagree : (E.store cfg ext i k).blocks J.root =
      (E.store cfg ext w m).blocks J.root :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext i k) (E.blockProvenance cfg ext w m)
      hJK hJM
  exact {
    target_epoch := by simpa only [J] using htargetEpoch
    target_known := by simpa only [J] using hJM
    target_root_before_boundary := by
      simpa only [J, ← hJagree] using hJslotK
  }

/-- A post-anchor honest target cast before the query cannot declare an epoch
after the query store's current epoch.  This is the first useful narrowing of
the three-region bracket: only a current-epoch checkpoint can lie strictly
above a current/previous-epoch selector input. -/
theorem postAnchorPreQueryTarget_epoch_le_query
    {v : ValidatorIndex} {q : ℕ}
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    {s : Slot} {store : Store Root} {target : Checkpoint Root}
    (hgeom : PostAnchorHonestTargetGeometryAt cfg s store target)
    (hsq : s < E.slot_at cfg q) :
    target.epoch ≤ get_current_store_epoch cfg query.store := by
  rw [hgeom.target_epoch]
  have hepoch := ce_mono cfg (Nat.le_of_lt hsq)
  simpa only [hquery, get_current_store_epoch,
    E.store_current_slot cfg ext v q] using hepoch

/-- At an exact query epoch boundary, a target vote strictly before the query
has a strictly earlier target epoch.  This is the key reason the selector's
epoch-start short circuit needs no historical current-target certificate in
the causal pre-query bracket. -/
theorem preQueryTarget_epoch_lt_query_of_epochStart
    {v : ValidatorIndex} {q : ℕ}
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    {s : Slot} {store : Store Root} {target : Checkpoint Root}
    (hgeom : PostAnchorHonestTargetGeometryAt cfg s store target)
    (hsq : s < E.slot_at cfg q)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = true) :
    target.epoch < get_current_store_epoch cfg query.store := by
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg q) = 0 := by
    simpa only [hquery, E.store_current_slot cfg ext v q,
      is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hboundary : E.slot_at cfg q =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg q)) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    have hle : E.slot_at cfg q ≤
        E.slot_at cfg q / cfg.slots_per_epoch * cfg.slots_per_epoch :=
      Nat.le_of_sub_eq_zero hstartZero
    exact Nat.le_antisymm hle
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  rw [hgeom.target_epoch]
  have hepoch : compute_epoch_at_slot cfg s <
      compute_epoch_at_slot cfg (E.slot_at cfg q) := by
    simp only [compute_epoch_at_slot]
    apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
    simpa only [compute_start_slot_at_epoch] using
      (hsq.trans_le (Nat.le_of_eq hboundary))
  simpa only [hquery, get_current_store_epoch,
    E.store_current_slot cfg ext v q] using hepoch

/-! ## Query-head geometry of the executable selector -/

omit [Inhabited Root] in
/-- Every member of the canonical segment enumerated from `terminal` toward
`head` is an ancestor of `head`.  `get_ancestor_roots_descends` records the
opposite end of the segment; this is its `getLast?` dual. -/
theorem ancestorRoots_member_below_head
    {store : Store Root} {head terminal x : Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hhead : head ∈ store.block_roots)
    (hterminal : terminal ∈ store.block_roots)
    (hx : x ∈ get_ancestor_roots store head terminal) :
    is_ancestor store (get_node_for_root head)
      (get_node_for_root x) = true := by
  have hw : WalkKnown store (store.blocks terminal).slot head :=
    hwalk terminal hterminal head hhead
  have hne : get_ancestor_roots store head terminal ≠ [] :=
    List.ne_nil_of_mem hx
  exact mem_isAncestor_of_parentChain hwf hwalk hhead
    (get_ancestor_roots_isChain hwf hw)
    (fun r hr => get_ancestor_roots_mem hwf hw hr)
    (get_ancestor_roots_getLast? hwf hw hne) x hx

/-- If the selector input is already on the query head chain, every executable
selector output is on that same chain.  This is proved directly through both
loops: every advance is chosen from `get_ancestor_roots ... head accumulator`.

The theorem is deliberately independent of confirmation and FFG semantics;
it only states the chain geometry erased by the result-only selector API. -/
theorem findLatestSelectedResult_below_head
    (fcrStore : FastConfirmationStore Root)
    (hwf : ParentSlotLt fcrStore.store)
    (hwalk : ∀ t ∈ fcrStore.store.block_roots,
      ∀ r ∈ fcrStore.store.block_roots,
        WalkKnown fcrStore.store (fcrStore.store.blocks t).slot r)
    (hhead : (get_head cfg fcrStore.store).root ∈
      fcrStore.store.block_roots)
    (input : Root) (hinput : input ∈ fcrStore.store.block_roots)
    (hheadInput : is_ancestor fcrStore.store (get_head cfg fcrStore.store)
      (get_node_for_root input) = true) :
    is_ancestor fcrStore.store (get_head cfg fcrStore.store)
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext fcrStore input)) = true := by
  let head := (get_head cfg fcrStore.store).root
  set P : Root → Prop := fun r =>
    r ∈ fcrStore.store.block_roots ∧
      is_ancestor fcrStore.store (get_node_for_root head)
        (get_node_for_root r) = true with hP
  have base : P input := by
    exact ⟨hinput, by
      rw [is_ancestor_node_root] at hheadInput
      simpa only [head] using hheadInput⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore ce
        (get_ancestor_roots fcrStore.store head acc) acc) := by
    intro ce acc hacc
    rcases prev_epoch_loop_spec cfg ext fcrStore ce
        (get_ancestor_roots fcrStore.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ fcrStore.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown,
        ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr⟩
  have htent : ∀ (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots fcrStore.store head acc) acc) := by
    intro acc hacc
    rcases tentative_loop_spec cfg ext fcrStore
        (get_ancestor_roots fcrStore.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ fcrStore.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown,
        ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr⟩
  have hresult : P
      (find_latest_confirmed_descendant cfg ext fcrStore input) := by
    generalize hX : find_latest_confirmed_descendant cfg ext fcrStore input = X
    rw [find_latest_confirmed_descendant] at hX
    simp only at hX
    split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
      subst hX <;>
        first
        | exact base
        | (apply htent; first | exact base | exact hprev _ _ base)
        | exact hprev _ _ base
  rw [is_ancestor_node_root]
  simpa only [head] using hresult.2

/-! ## The actual pre-query vote as an ancestry-transport witness -/

/-- Unwinding a post-anchor honest vote which names `target` produces a
strictly earlier honest-store head below which `target` lies.  Synchrony
relays that whole source store to the query, so the same source head is a
concrete earlier descendant of `target` in the query store.

This is exactly the witness shape consumed by
`ancestry_of_known_honest_past_descendant_minimal`; it contains no relation
between `target` and the selector input/result. -/
theorem preQueryHonestTarget_sourceWitnessAtQuery
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsq : s < E.slot_at cfg q)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    {target : Checkpoint Root}
    (htarget₀ : a₀.data.target = target) :
    ∃ (k : ℕ) (d : Root),
      E.WithinHorizon cfg k ∧
      E.slot_at cfg k = s ∧
      E.slot_at cfg k < E.slot_at cfg q ∧
      k ≤ E.slot_start cfg (E.slot_at cfg k) +
        get_attestation_due_ms cfg / 1000 ∧
      d = (get_head cfg (E.store cfg ext i k)).root ∧
      d ∈ (E.store cfg ext i k).block_roots ∧
      target.root ∈ (E.store cfg ext i k).block_roots ∧
      d ∈ (E.store cfg ext v q).block_roots ∧
      target.root ∈ (E.store cfg ext v q).block_roots ∧
      is_ancestor (E.store cfg ext v q)
        (get_node_for_root d) (get_node_for_root target.root) = true := by
  have hcomm : i ∈ E.committee s :=
    hA.honest_behavior.votes_assigned i hi s
      (by rw [hvote₀]; exact Option.some_ne_none _)
  obtain ⟨k, index, hHk, hk, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi s hcomm hsH hs0
  have hvoteEq := hvote₀
  rw [hvoteHead] at hvoteEq
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
  obtain ⟨_, hattestation⟩ := hvoteEq
  have htarget :
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target =
        target := by
    rw [hattestation]
    exact htarget₀
  have htargetWalk : WalkKnown (E.store cfg ext i k)
      (compute_start_slot_at_epoch cfg target.epoch)
      (get_head cfg (E.store cfg ext i k)).root := by
    simpa only [htarget] using
      hwalkDomain i hi s k index hs0 hHk hk hvoteHead
  obtain ⟨hwfK, hwalkK, _hjustK⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain i hi k hHk
  have hheadK : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi k hHk
  have htargetRoot : get_checkpoint_block cfg (E.store cfg ext i k)
      (get_head cfg (E.store cfg ext i k)).root target.epoch = target.root := by
    have htargetData : (honest_attestation_data cfg ext
        (E.store cfg ext i k) s index).target = target := by
      simpa only [honest_attestation_data_eq] using htarget
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext i k) s index
    rw [htargetData] at hroot
    exact hroot.symm
  have heta : (get_ancestor (E.store cfg ext i k)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (compute_start_slot_at_epoch cfg target.epoch)).root = target.root := by
    simpa only [get_checkpoint_block, get_node_for_root] using htargetRoot
  have htargetSpec := get_ancestor_spec hwfK htargetWalk
  simp only [get_node_for_root] at heta
  rw [heta] at htargetSpec
  have hTK : target.root ∈ (E.store cfg ext i k).block_roots :=
    htargetSpec.1
  have hTslot : ((E.store cfg ext i k).blocks target.root).slot ≤
      compute_start_slot_at_epoch cfg target.epoch := htargetSpec.2
  have hheadT_K : is_ancestor (E.store cfg ext i k)
      (get_head cfg (E.store cfg ext i k))
      (get_node_for_root target.root) = true := by
    have hcomp := get_ancestor_comp_root hwfK hTslot
      (hwalkK target.root hTK _ hheadK)
    rw [heta] at hcomp
    have hstop : get_ancestor (E.store cfg ext i k)
        (get_node_for_root target.root)
        ((E.store cfg ext i k).blocks target.root).slot =
          get_node_for_root target.root :=
      get_ancestor_stop (Nat.le_refl _)
    simp only [get_node_for_root] at hstop
    rw [hstop] at hcomp
    rw [is_ancestor_node_root]
    simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
    exact hcomp.symm
  have hdue : k ≤ E.slot_start cfg (E.slot_at cfg k) +
      get_attestation_due_ms cfg / 1000 := by
    simpa only [hk] using (hA.honest_behavior.vote_deadline i hi s k _ hvoteHead).2
  let d := (get_head cfg (E.store cfg ext i k)).root
  have hdQ : d ∈ (E.store cfg ext v q).block_roots :=
    E.honest_head_known_at_later_slot_minimal cfg ext hA hi hv hHk hqH
      hdue (by simpa only [hk] using hsq)
  obtain ⟨hTQ, hheadT_Q⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    hheadK hdQ hTK (by rwa [is_ancestor_node_root] at hheadT_K)
  exact ⟨k, d, hHk, hk, by simpa only [hk] using hsq,
    hdue, rfl, hheadK, hTK, hdQ, hTQ, hheadT_Q⟩

/-- A query-store ancestry `target.root ⩾c b` can be transported to any
slot-ordered endpoint using the actual pre-query target vote as the required
strictly earlier honest descendant.  This closes the direction needed by the
middle bracket's lower side and by the upper bracket. -/
theorem preQueryTarget_descends_queryBlock_at_endpoint
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {target : Checkpoint Root} {b : Root}
    (hTQ : target.root ∈ (E.store cfg ext v q).block_roots)
    (hbQ : b ∈ (E.store cfg ext v q).block_roots)
    (hTbQ : is_ancestor (E.store cfg ext v q)
      (get_node_for_root target.root) (get_node_for_root b) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsq : s < E.slot_at cfg q)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    (htarget₀ : a₀.data.target = target) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root target.root) (get_node_for_root b) = true := by
  obtain ⟨k, d, hHk, _hk, hkq, hdeadline, hhead, hdK, _hTK, hdQ,
      _hTQ, hdTQ⟩ :=
    E.preQueryHonestTarget_sourceWitnessAtQuery cfg ext hA hwalkDomain
      hv hqH hi hs0 hsq hsH hvote₀ htarget₀
  exact (E.ancestry_of_known_honest_past_descendant_minimal cfg ext hA
    v hv q target.root b hqH hTQ hbQ hTbQ w hw m hslotQM hHm
      i hi k hHk d hkq hdeadline hhead hdK hdQ hdTQ).2.2

/-- The complete **below-input** region is mechanical once the already-carried
input safety and honest-target geometry are made visible.

This is not the desired selected-result safety used circularly: `hbase` is the
public selector precondition saying the input was already safe at the start of
the query slot.  It places the input on the endpoint head.  Fork-choice places
the endpoint head above its own justified root.  If the checkpoint's declared
epoch is no later than the input block epoch, the honest-target boundary bound
rules out the reverse strict orientation. -/
theorem preQueryVote_belowInput_of_safeInput
    (hA : SelectedMarginAssumptions cfg ext E)
    {q : ℕ} {input : Root}
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hinput : input ∈ (E.store cfg ext w m).block_roots)
    {s : Slot}
    (hgeom : PostAnchorHonestTargetGeometryAt cfg s
      (E.store cfg ext w m)
      (E.store cfg ext w m).justified_checkpoint)
    (hbelow : (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.store cfg ext w m) input) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root input)
      (get_node_for_root
        (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let store := E.store cfg ext w m
  let J := store.justified_checkpoint
  have hstartM : E.slot_start cfg (E.slot_at cfg q) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hheadInput : is_ancestor store (get_head cfg store)
      (get_node_for_root input) = true := by
    simpa only [store] using hbase w hw m hstartM hHm
  obtain ⟨hwfM, hwalkM, hJM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have hheadM : (get_head cfg store).root ∈ store.block_roots := by
    simpa only [store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hw m hHm
  have hheadJ : is_ancestor store (get_head cfg store)
      (get_node_for_root J.root) = true := by
    exact head_ge_of_justified_ge_K cfg hwfM hwalkM hJM hJM
      (is_ancestor_refl store (get_node_for_root J.root))
  rcases is_ancestor_comparable hwfM
      (hwalkM J.root hJM _ hheadM)
      (hwalkM input (by simpa only [store] using hinput) _ hheadM)
      (by rwa [is_ancestor_node_root] at hheadJ)
      (by rwa [is_ancestor_node_root] at hheadInput) with hinputJ | hJinput
  · simpa only [store, J] using hinputJ
  · have hinputSlotLeJ : (store.blocks input).slot ≤
        (store.blocks J.root).slot :=
      ancestor_slot_le hwfM
        (hwalkM input (by simpa only [store] using hinput) J.root hJM)
        hJinput
    have hboundaryMono : compute_start_slot_at_epoch cfg J.epoch ≤
        compute_start_slot_at_epoch cfg (get_block_epoch cfg store input) := by
      simp only [compute_start_slot_at_epoch]
      exact Nat.mul_le_mul_right cfg.slots_per_epoch (by
        simpa only [store, J] using hbelow)
    have hboundaryInput : compute_start_slot_at_epoch cfg
        (get_block_epoch cfg store input) ≤ (store.blocks input).slot :=
      start_slot_at_block_epoch_le cfg store input
    have hJBoundary : (store.blocks J.root).slot ≤
        compute_start_slot_at_epoch cfg J.epoch := by
      simpa only [store, J] using hgeom.target_root_before_boundary
    have hJSlotLeInput : (store.blocks J.root).slot ≤
        (store.blocks input).slot :=
      hJBoundary.trans (hboundaryMono.trans hboundaryInput)
    have hstop : get_ancestor store (get_node_for_root J.root)
        (store.blocks input).slot = get_node_for_root J.root :=
      get_ancestor_stop hJSlotLeInput
    have hroot : J.root = input := by
      simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hJinput
      rw [hstop] at hJinput
      exact hJinput
    rw [hroot]
    exact is_ancestor_refl store (get_node_for_root input)

/-! ## Region arithmetic and certificate-producing semantics -/

/-- The selected-margin assumptions already contain every economic and
behavioral premise used by concrete Casper accountability. -/
theorem certificateAccountability_of_selectedMarginAssumptions
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} :
    CertificateAccountability cfg E anchor := by
  apply CertificateAccountability.of_assumptions cfg ext
  refine {
    genesis_store := ?_
    whole_seconds := hA.whole_seconds
    honest_behavior := hA.honest_behavior
    externals_coherence := hA.externals_coherence
    static_validator_set := hA.static_validators
    byzantine_bound := hA.byzantine_bound
  }
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hA.genesis
  exact ⟨ast, ablk, hgen⟩

/-- In the middle region, a current/previous-epoch strict result must be a
current-epoch result, and the pre-query target itself has the query's current
epoch.  This is the exact case in which paper Lemma 27 (or a retained crossing
gate) must produce the current-target FFG certificate. -/
theorem middleRegion_forces_current
    {store : Store Root} {input result : Root}
    {targetEpoch currentEpoch : Epoch}
    (hinput : get_block_epoch cfg store input = currentEpoch ∨
      get_block_epoch cfg store input + 1 = currentEpoch)
    (hresult : get_block_epoch cfg store result = currentEpoch ∨
      get_block_epoch cfg store result + 1 = currentEpoch)
    (htargetUpper : targetEpoch ≤ currentEpoch)
    (haboveInput : get_block_epoch cfg store input < targetEpoch)
    (hbelowResult : targetEpoch ≤ get_block_epoch cfg store result) :
    get_block_epoch cfg store result = currentEpoch ∧
      targetEpoch = currentEpoch := by
  rcases hinput with hinputCurrent | hinputPrevious
  · have hcurrentLtTarget : currentEpoch < targetEpoch := by
      rw [← hinputCurrent]
      exact haboveInput
    exact False.elim ((Nat.not_lt_of_ge htargetUpper) hcurrentLtTarget)
  · rcases hresult with hresultCurrent | hresultPrevious
    · refine ⟨hresultCurrent, Nat.le_antisymm htargetUpper ?_⟩
      rw [← hinputPrevious]
      exact Nat.succ_le_of_lt haboveInput
    · have hinputEqResult : get_block_epoch cfg store input =
          get_block_epoch cfg store result := by
        exact Nat.add_right_cancel (hinputPrevious.trans hresultPrevious.symm)
      have hbad : get_block_epoch cfg store result < targetEpoch := by
        simpa only [hinputEqResult] using haboveInput
      exact False.elim ((Nat.not_lt_of_ge hbelowResult) hbad)

/-- In the upper region, a current/previous-epoch strict result is necessarily
from the previous epoch and the pre-query target is from the current epoch.
This is exactly the epoch-boundary/no-conflict split of the paper. -/
theorem aboveSelectedRegion_forces_previous
    {store : Store Root} {result : Root}
    {targetEpoch currentEpoch : Epoch}
    (hresult : get_block_epoch cfg store result = currentEpoch ∨
      get_block_epoch cfg store result + 1 = currentEpoch)
    (htargetUpper : targetEpoch ≤ currentEpoch)
    (haboveResult : get_block_epoch cfg store result < targetEpoch) :
    get_block_epoch cfg store result + 1 = currentEpoch ∧
      targetEpoch = currentEpoch := by
  rcases hresult with hcurrent | hprevious
  · rw [hcurrent] at haboveResult
    exact False.elim ((Nat.not_lt_of_ge htargetUpper) haboveResult)
  · refine ⟨hprevious, Nat.le_antisymm htargetUpper ?_⟩
    rw [← hprevious]
    exact Nat.succ_le_of_lt haboveResult

/-- Certificate-level semantics of the exact current-target helper.

This is the faithful result that paper Lemma 9 plus source coherence must
produce.  It is intentionally not a selected/justified ancestry premise: its
conclusion is a concrete, vote-backed `CertifiedJustified` object. -/
def CurrentTargetCertificateProducerAt
    (anchor : Checkpoint Root) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop :=
  will_current_target_be_justified cfg ext query.store = true →
  HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q →
    Nonempty (CertifiedJustified cfg E anchor
      (get_current_target cfg query.store))

/-- Historical propagation of a current-epoch target certificate when the
strict selector has no retained epoch-crossing edge in this invocation.

This is the certificate-level contract of paper Lemma 27: the relevant
current-target helper/certificate was established by an earlier FCR call and
survives into the inherited-current input.  The interface does not mention an
endpoint or any selected/checkpoint ancestry. -/
def HistoricalCurrentTargetCertificateProducerAt
    (anchor : Checkpoint Root) (q : ℕ)
    (query : FastConfirmationStore Root) (input result : Root) : Prop :=
  get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store →
  (¬ ∃ a c : Root, CurrentTargetSelectedEdge cfg ext query input a c) →
    Nonempty (CertifiedJustified cfg E anchor
      (get_current_target cfg query.store))

/-- Paper Lemma 42 in descendant form. Observed supporters use the query
current target, which descends from `result`. Future honest targets can
differ, but each must descend from `result`. More than one third of the
weight then pins every certified checkpoint of that epoch below `result`. -/
def NoConflictCertificatePinningProducerAt
    (anchor : Checkpoint Root) (q : ℕ)
    (query : FastConfirmationStore Root) : Prop :=
  ∀ result : Root,
  E.RootDescends (get_current_target cfg query.store).root result →
  will_no_conflicting_checkpoint_be_justified cfg ext query.store = true →
  HonestVotesTargetDescendFrom cfg E result
    (get_current_store_epoch cfg query.store) q →
  ∀ c : Checkpoint Root,
    CertifiedJustified cfg E anchor c →
    c.epoch = (get_current_target cfg query.store).epoch →
      E.RootDescends c.root result

/-! ## Current-target chain geometry -/

/-- A current-epoch block on the query head chain descends from the query's
current target.  The result also proves that the totalized target root is an
actual known block. -/
theorem currentEpochBlock_descends_currentTarget
    {store : Store Root} {b : Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hhead : (get_head cfg store).root ∈ store.block_roots)
    (hb : b ∈ store.block_roots)
    (hheadB : is_ancestor store (get_head cfg store)
      (get_node_for_root b) = true)
    (hboundaryWalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
      (get_head cfg store).root)
    (hbEpoch : get_block_epoch cfg store b =
      get_current_store_epoch cfg store) :
    (get_current_target cfg store).root ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root b)
        (get_node_for_root (get_current_target cfg store).root) = true := by
  let T := get_current_target cfg store
  have heta : (get_ancestor store (get_node_for_root (get_head cfg store).root)
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))).root =
        T.root := by
    rfl
  have htargetSpec := get_ancestor_spec hwf hboundaryWalk
  simp only [get_node_for_root] at heta
  rw [heta] at htargetSpec
  have hT : T.root ∈ store.block_roots := htargetSpec.1
  have hTslot : (store.blocks T.root).slot ≤
      compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store) :=
    htargetSpec.2
  have hheadT : is_ancestor store (get_head cfg store)
      (get_node_for_root T.root) = true := by
    have hcomp := get_ancestor_comp_root hwf hTslot
      (hwalk T.root hT _ hhead)
    rw [heta] at hcomp
    have hstop : get_ancestor store (get_node_for_root T.root)
        (store.blocks T.root).slot = get_node_for_root T.root :=
      get_ancestor_stop (Nat.le_refl _)
    simp only [get_node_for_root] at hstop
    rw [hstop] at hcomp
    rw [is_ancestor_node_root]
    simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
    exact hcomp.symm
  rcases is_ancestor_comparable hwf
      (hwalk T.root hT _ hhead) (hwalk b hb _ hhead)
      (by rwa [is_ancestor_node_root] at hheadT)
      (by rwa [is_ancestor_node_root] at hheadB) with hbT | hTb
  · exact ⟨by simpa only [T] using hT, by simpa only [T] using hbT⟩
  · have hboundaryB : compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg store) ≤ (store.blocks b).slot := by
      rw [← hbEpoch]
      exact start_slot_at_block_epoch_le cfg store b
    have hTslotLeB : (store.blocks T.root).slot ≤
        (store.blocks b).slot := hTslot.trans hboundaryB
    have hstop : get_ancestor store (get_node_for_root T.root)
        (store.blocks b).slot = get_node_for_root T.root :=
      get_ancestor_stop hTslotLeB
    have hroot : T.root = b := by
      simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hTb
      rw [hstop] at hTb
      exact hTb
    refine ⟨by simpa only [T] using hT, ?_⟩
    rw [hroot]
    exact is_ancestor_refl store (get_node_for_root b)

/-- A previous-epoch block on the query head chain is below the query's
current target.  This is direct walk composition across the current epoch
boundary. -/
theorem currentTarget_descends_previousEpochBlock
    {store : Store Root} {b : Root}
    (hwf : ParentSlotLt store)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hhead : (get_head cfg store).root ∈ store.block_roots)
    (hb : b ∈ store.block_roots)
    (hheadB : is_ancestor store (get_head cfg store)
      (get_node_for_root b) = true)
    (hboundaryWalk : WalkKnown store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))
      (get_head cfg store).root)
    (hbEpoch : get_block_epoch cfg store b + 1 =
      get_current_store_epoch cfg store) :
    (get_current_target cfg store).root ∈ store.block_roots ∧
      is_ancestor store
        (get_node_for_root (get_current_target cfg store).root)
        (get_node_for_root b) = true := by
  let T := get_current_target cfg store
  have heta : (get_ancestor store (get_node_for_root (get_head cfg store).root)
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store))).root =
        T.root := by
    rfl
  have htargetSpec := get_ancestor_spec hwf hboundaryWalk
  simp only [get_node_for_root] at heta
  rw [heta] at htargetSpec
  have hT : T.root ∈ store.block_roots := htargetSpec.1
  have hbEpochLt : get_block_epoch cfg store b <
      get_current_store_epoch cfg store := by
    rw [← hbEpoch]
    exact Nat.lt_succ_self _
  have hbSlotLt : (store.blocks b).slot <
      compute_start_slot_at_epoch cfg (get_current_store_epoch cfg store) := by
    simp only [get_block_epoch, compute_epoch_at_slot,
      compute_start_slot_at_epoch] at hbEpochLt ⊢
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp hbEpochLt
  have hcomp := get_ancestor_comp_root hwf (Nat.le_of_lt hbSlotLt)
    (hwalk b hb _ hhead)
  rw [is_ancestor_node_root] at hheadB
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hheadB ⊢
  simp only [get_node_for_root] at hheadB
  rw [heta, hheadB] at hcomp
  exact ⟨by simpa only [T] using hT, by simpa only [T] using hcomp⟩

/-- The current-epoch boundary walk is derivable whenever the query knows one
block from a strictly earlier epoch.  Such a block proves that the current
epoch boundary is later than the concrete trusted anchor slot; the ordinary
execution walk from that anchor can therefore be weakened to the boundary.

This removes a tempting extra totalization/domain assumption from the SIR
producer.  The middle region supplies `b := input`; the upper region supplies
`b := selected`. -/
theorem currentEpochBoundaryWalk_of_knownEarlierEpochBlock
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    {b : Root} (hb : b ∈ query.store.block_roots)
    (hbEarlier : get_block_epoch cfg query.store b <
      get_current_store_epoch cfg query.store) :
    WalkKnown query.store
      (compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root := by
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hanchor0 : ablk.root ∈ (E.store cfg ext v 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgenEq]
    simp [get_forkchoice_store]
  have hanchorE : ablk.root ∈ (E.store cfg ext v q).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le q)).1 hanchor0
  have hanchorQ : ablk.root ∈ query.store.block_roots := by
    simpa only [hquery] using hanchorE
  have hanchorRecord : query.store.blocks ablk.root = ablk.message := by
    simpa only [hquery] using
      E.store_anchor_block cfg ext hA.wellFormed hgenEq v q hanchorE
  have hanchorEpoch : get_block_epoch cfg query.store ablk.root =
      get_current_epoch cfg ast := by
    simp only [get_block_epoch, get_current_epoch, hanchorRecord, hanchorSlot]
  have hanchorBelow := E.known_descends_trustedAnchor cfg ext hA
    (anchor := E.genesis_store.justified_checkpoint) rfl v q
      (by simpa only [hquery] using hb)
  have hanchorCheckpointEpoch :
      E.genesis_store.justified_checkpoint.epoch =
        get_current_epoch cfg ast := by
    rw [hgenEq]
    rfl
  have hbEarlierE : get_block_epoch cfg (E.store cfg ext v q) b <
      get_current_store_epoch cfg (E.store cfg ext v q) := by
    simpa only [← hquery] using hbEarlier
  have hanchorEpochLt : get_block_epoch cfg query.store ablk.root <
      get_current_store_epoch cfg query.store := by
    rw [hanchorEpoch, ← hanchorCheckpointEpoch]
    simpa only [← hquery] using hanchorBelow.2.trans_lt hbEarlierE
  have hanchorSlotLt : (query.store.blocks ablk.root).slot <
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) := by
    simp only [get_block_epoch, compute_epoch_at_slot,
      compute_start_slot_at_epoch] at hanchorEpochLt ⊢
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp hanchorEpochLt
  have hheadE : (get_head cfg (E.store cfg ext v q)).root ∈
      (E.store cfg ext v q).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  have hwalkAnchorE := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen v q ablk.root hanchorE
      (get_head cfg (E.store cfg ext v q)).root hheadE
  have hwalkAnchorQ : WalkKnown query.store
      (query.store.blocks ablk.root).slot (get_head cfg query.store).root := by
    simpa only [hquery] using hwalkAnchorE
  exact hwalkAnchorQ.mono (Nat.le_of_lt hanchorSlotLt)

/-! ## Completing the three regions from certificate pinning -/

/-- Once current-result certificates have exact target pinning and
previous-result certificates have descendant pinning, the three SIR clauses
follow from executable geometry.

The below-input clause uses only the carried input safety.  In the middle
clause, confirmation transports `selected ⩾c currentTarget`, while the actual
pre-query target vote transports `currentTarget ⩾c input`.  In the upper
clause the certified root descends from the selected result directly.

The final premise is either the executable epoch-start branch or certificate
pinning, derived from the helper and its vote support. The call-site theorem
derives this disjunction. -/
theorem selectedSIRThreeRegionBracket_of_preQueryVote_and_pinning
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (input : Root) (hinput : input ∈ query.store.block_roots)
    (hinputEpoch :
      get_block_epoch cfg query.store input =
          get_current_store_epoch cfg query.store ∨
        get_block_epoch cfg query.store input + 1 =
          get_current_store_epoch cfg query.store)
    (hbase : E.SafeFrom cfg ext input
      (E.slot_start cfg (E.slot_at cfg q)))
    (hstrict : find_latest_confirmed_descendant cfg ext query input ≠ input)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hs0 : E.slot_at cfg 0 ≤ s)
    (hsq : s < E.slot_at cfg q)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    (htarget₀ : a₀.data.target =
      (E.store cfg ext w m).justified_checkpoint)
    (hstartOrPin :
      is_start_slot_at_epoch cfg (get_current_slot cfg query.store) = true ∨
        ((get_block_epoch cfg query.store
              (find_latest_confirmed_descendant cfg ext query input) =
            get_current_store_epoch cfg query.store →
          (E.store cfg ext w m).justified_checkpoint.epoch =
              (get_current_target cfg query.store).epoch →
            (E.store cfg ext w m).justified_checkpoint.root =
              (get_current_target cfg query.store).root) ∧
        (get_block_epoch cfg query.store
              (find_latest_confirmed_descendant cfg ext query input) + 1 =
            get_current_store_epoch cfg query.store →
          (E.store cfg ext w m).justified_checkpoint.epoch =
              (get_current_target cfg query.store).epoch →
            E.RootDescends (E.store cfg ext w m).justified_checkpoint.root
              (find_latest_confirmed_descendant cfg ext query input)))) :
    SelectedSIRThreeRegionBracket cfg (E.store cfg ext w m) input
      (find_latest_confirmed_descendant cfg ext query input)
      (E.store cfg ext w m).justified_checkpoint := by
  let result := find_latest_confirmed_descendant cfg ext query input
  let store := E.store cfg ext w m
  let J := store.justified_checkpoint
  let T := get_current_target cfg query.store
  obtain ⟨hwfQ, hwalkQ, _hjustQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain v hv q hqH
  have hheadQ : (get_head cfg query.store).root ∈
      query.store.block_roots := by
    have hhead := E.head_root_known_of_selectedMarginDomain cfg ext
      hA.domain hv q hqH
    simpa only [hquery] using hhead
  have hwfQuery : ParentSlotLt query.store := by
    simpa only [hquery] using hwfQ
  have hwalkQuery : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [hquery] using hwalkQ
  have hstartQ : E.slot_start cfg (E.slot_at cfg q) ≤ q :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (Nat.le_refl _)
  have hheadInputQ : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root input) = true := by
    simpa only [hquery] using hbase v hv q hstartQ hqH
  have hheadResultQ : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root result) = true := by
    simpa only [result] using findLatestSelectedResult_below_head cfg ext query
      hwfQuery hwalkQuery hheadQ input hinput hheadInputQ
  have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
    query hquery input hinput hinputEpoch hstrict
  have hresultQ : result ∈ query.store.block_roots := by
    simpa only [result] using hfacts.result_known
  have hparentQ : (query.store.blocks result).parent_root ∈
      query.store.block_roots := by
    simpa only [result] using hfacts.parent_known
  have hresultInputQ : is_ancestor query.store
      (get_node_for_root result) (get_node_for_root input) = true := by
    simpa only [result] using hfacts.descends_input
  have hresultE : result ∈ (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hresultQ
  have hparentE : ((E.store cfg ext v q).blocks result).parent_root ∈
      (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hparentQ
  have hinputE : input ∈ (E.store cfg ext v q).block_roots := by
    simpa only [← hquery] using hinput
  have hresultInputE : is_ancestor (E.store cfg ext v q)
      (get_node_for_root result) (get_node_for_root input) = true := by
    simpa only [← hquery] using hresultInputQ
  obtain ⟨hinputM, hresultM, _hresultInputM⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
      v hv q query hquery result input hqH hresultE hparentE hinputE
      hresultInputE (by simpa only [result] using hfacts.confirmed)
      w hw m hslotQM hHm
  have hgeom := E.postAnchorHonestTargetGeometryAt_of_vote cfg ext hA
    hwalkDomain hi hs0 hsH hvote₀ hw hHm htarget₀
  have htargetUpper : J.epoch ≤
      get_current_store_epoch cfg query.store := by
    simpa only [store, J] using
      E.postAnchorPreQueryTarget_epoch_le_query cfg ext query hquery hgeom hsq
  have hinputAgree : query.store.blocks input = store.blocks input := by
    rw [hquery]
    exact hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w m)
      hinputE (by simpa only [store] using hinputM)
  have hresultAgree : query.store.blocks result = store.blocks result := by
    rw [hquery]
    exact hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w m)
      hresultE (by simpa only [store] using hresultM)
  constructor
  · intro hbelow
    simpa only [result, store, J] using
      E.preQueryVote_belowInput_of_safeInput cfg ext hA hbase hw hslotQM
        hHm hinputM hgeom hbelow
  · intro haboveInputM hbelowResultM
    have haboveInputQ : get_block_epoch cfg query.store input < J.epoch := by
      simpa only [get_block_epoch, hinputAgree] using haboveInputM
    have hbelowResultQ : J.epoch ≤
        get_block_epoch cfg query.store result := by
      simpa only [get_block_epoch, hresultAgree] using hbelowResultM
    have hforce := middleRegion_forces_current cfg hinputEpoch
      (by simpa only [result] using hfacts.current_or_previous_epoch)
      htargetUpper haboveInputQ hbelowResultQ
    have hresultCurrent : get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store := hforce.1
    have hJEpoch : J.epoch = get_current_store_epoch cfg query.store :=
      hforce.2
    have hpin : store.justified_checkpoint.epoch = T.epoch →
        store.justified_checkpoint.root = T.root := by
      rcases hstartOrPin with hstart | hpin
      · have htargetLt := E.preQueryTarget_epoch_lt_query_of_epochStart
          cfg ext query hquery hgeom hsq hstart
        have hbad : J.epoch < J.epoch := by
          calc
            J.epoch < get_current_store_epoch cfg query.store := by
              simpa only [store, J] using htargetLt
            _ = J.epoch := hJEpoch.symm
        exact False.elim (Nat.lt_irrefl _ hbad)
      · simpa only [store, T] using hpin.1 hresultCurrent
    have hsameEpoch : J.epoch = T.epoch := by
      simpa only [T, get_current_target] using hJEpoch
    have hroot : J.root = T.root := by
      simpa only [store, J, T] using hpin (by
        simpa only [store, J, T] using hsameEpoch)
    have hJT : J = T := checkpoint_eq_of_epoch_root_eq hsameEpoch hroot
    have htargetT : a₀.data.target = T := by
      have htargetJ : a₀.data.target = J := by
        simpa only [store, J] using htarget₀
      exact htargetJ.trans hJT
    have hinputPrevious : get_block_epoch cfg query.store input + 1 =
        get_current_store_epoch cfg query.store := by
      rcases hinputEpoch with hcurrent | hprevious
      · have hbad : get_current_store_epoch cfg query.store < J.epoch := by
          simpa only [hcurrent] using haboveInputQ
        exact False.elim ((Nat.not_lt_of_ge htargetUpper) hbad)
      · exact hprevious
    have hinputEarlier : get_block_epoch cfg query.store input <
        get_current_store_epoch cfg query.store := by
      rw [← hinputPrevious]
      exact Nat.lt_succ_self _
    have hboundaryWalk :=
      E.currentEpochBoundaryWalk_of_knownEarlierEpochBlock cfg ext hA hv hqH
        query hquery hinput hinputEarlier
    obtain ⟨hTQ, hresultTQ⟩ :=
      currentEpochBlock_descends_currentTarget cfg hwfQuery hwalkQuery
        hheadQ hresultQ hheadResultQ hboundaryWalk hresultCurrent
    obtain ⟨_hTQ', hTinputQ⟩ :=
      currentTarget_descends_previousEpochBlock cfg hwfQuery hwalkQuery
        hheadQ hinput hheadInputQ hboundaryWalk hinputPrevious
    have hTE : T.root ∈ (E.store cfg ext v q).block_roots := by
      simpa only [← hquery] using hTQ
    have hresultTE : is_ancestor (E.store cfg ext v q)
        (get_node_for_root result) (get_node_for_root T.root) = true := by
      simpa only [← hquery] using hresultTQ
    obtain ⟨_hTM, _hresultM', hresultTM⟩ :=
      E.confirmed_ancestry_at_all_honest_endpoints_minimal cfg ext hA
        v hv q query hquery result T.root hqH hresultE hparentE hTE
        hresultTE (by simpa only [result] using hfacts.confirmed)
        w hw m hslotQM hHm
    have hTinputE : is_ancestor (E.store cfg ext v q)
        (get_node_for_root T.root) (get_node_for_root input) = true := by
      simpa only [← hquery] using hTinputQ
    have hTinputM := E.preQueryTarget_descends_queryBlock_at_endpoint
      cfg ext hA hwalkDomain hv hqH hTE hinputE hTinputE hw hslotQM hHm
        hi hs0 hsq hsH hvote₀ htargetT
    constructor
    · simpa only [result, store, J, T, hroot] using hresultTM
    · simpa only [store, J, T, hroot] using hTinputM
  · intro haboveResultM
    have haboveResultQ : get_block_epoch cfg query.store result < J.epoch := by
      simpa only [get_block_epoch, hresultAgree] using haboveResultM
    have hforce := aboveSelectedRegion_forces_previous cfg
      (by simpa only [result] using hfacts.current_or_previous_epoch)
      htargetUpper haboveResultQ
    have hresultPrevious : get_block_epoch cfg query.store result + 1 =
        get_current_store_epoch cfg query.store := hforce.1
    have hJEpoch : J.epoch = get_current_store_epoch cfg query.store :=
      hforce.2
    have hdesc : E.RootDescends J.root result := by
      rcases hstartOrPin with hstart | hpin
      · have htargetLt := E.preQueryTarget_epoch_lt_query_of_epochStart
          cfg ext query hquery hgeom hsq hstart
        have hbad : J.epoch < J.epoch := by
          calc
            J.epoch < get_current_store_epoch cfg query.store := by
              simpa only [store, J] using htargetLt
            _ = J.epoch := hJEpoch.symm
        exact False.elim (Nat.lt_irrefl _ hbad)
      · exact hpin.2 hresultPrevious hJEpoch
    obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hA.genesis
    have hJM := (E.store_domainK_of_selectedMarginDomain cfg ext
      hA.wellFormed hA.externals_coherence hA.genesis hA.domain
      w hw m hHm).2.2
    exact E.store_ancestor_of_rootDescends_for_storeReflection cfg ext
      hA.wellFormed hA.externals_coherence hgen hslot hparent
      hJM hresultM hdesc




end Execution

end FastConfirmation.Spec

end
