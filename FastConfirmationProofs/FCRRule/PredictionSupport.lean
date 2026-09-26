module
public import FastConfirmationProofs.FCRRule.ConfirmedCacheInvariant
public import FastConfirmationProofs.FCRRule.SelectedTraceCoverage
public import FastConfirmationProofs.FFG.State.PathLocalFinalizedTransport

/-!
Prediction support follows from canonicity at honest vote times.

These lemmas separate checkpoint geometry from the open within-epoch
canonicity induction. They do not use the guarded prediction-support fields.
The previous-result conclusion uses execution descent, as in paper Lemma 42.
The current-target conclusion uses a common current-epoch block, as in paper
Lemmas 44 and 45. Support before a later endpoint slot is sufficient once
that slot is after the end of the target epoch.
-/

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Two stores whose heads both descend from a common block `c` of epoch at
least `e` compute the same epoch-`e` checkpoint block for their heads. -/
theorem head_checkpoint_eq_of_common_block
    {V W : Store Root} (hV : ParentSlotLt V) (hW : ParentSlotLt W)
    (hagree : ∀ r, r ∈ V.block_roots → r ∈ W.block_roots →
      V.blocks r = W.blocks r)
    {c : Root} {e : Epoch}
    (hcV : c ∈ V.block_roots) (hcW : c ∈ W.block_roots)
    (hslot : compute_start_slot_at_epoch cfg e ≤ (V.blocks c).slot)
    (hVanc : is_ancestor V (get_head cfg V) (get_node_for_root c) = true)
    (hWanc : is_ancestor W (get_head cfg W) (get_node_for_root c) = true)
    (hVwalk : WalkKnown V (compute_start_slot_at_epoch cfg e)
      (get_head cfg V).root)
    (hWwalk : WalkKnown W (compute_start_slot_at_epoch cfg e)
      (get_head cfg W).root)
    (hcVwalk : WalkKnown V (compute_start_slot_at_epoch cfg e) c)
    (hcWwalk : WalkKnown W (compute_start_slot_at_epoch cfg e) c) :
    get_checkpoint_block cfg W (get_head cfg W).root e =
      get_checkpoint_block cfg V (get_head cfg V).root e := by
  have hslotW : compute_start_slot_at_epoch cfg e ≤ (W.blocks c).slot := by
    rw [← hagree c hcV hcW]
    exact hslot
  have hVanc' : is_ancestor V (get_node_for_root (get_head cfg V).root)
      (get_node_for_root c) = true :=
    (congrArg (· = true) (is_ancestor_pending_root_eq V
      (get_head cfg V).root c .pending
      (get_head cfg V).payload_status)).mpr hVanc
  have hWanc' : is_ancestor W (get_node_for_root (get_head cfg W).root)
      (get_node_for_root c) = true :=
    (congrArg (· = true) (is_ancestor_pending_root_eq W
      (get_head cfg W).root c .pending
      (get_head cfg W).payload_status)).mpr hWanc
  rw [get_checkpoint_block_of_ancestor cfg hW hWanc' hslotW hWwalk,
    get_checkpoint_block_of_ancestor cfg hV hVanc' hslot hVwalk]
  exact (get_checkpoint_block_eq_of_paired_walks cfg hV hW hagree
    hcVwalk hcWwalk).symm

namespace Execution

variable (E : Execution Root)

/-- Canonicity of `c` at every honest vote of epoch `e` whose slot is at
least the slot of execution second `q`. -/
def CanonicalAtHonestVotesFrom (c : Root) (e : Epoch) (q : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
    compute_epoch_at_slot cfg s = e → E.slot_at cfg q ≤ s →
    ∀ k a, E.vote w s = some (k, a) →
      c ∈ (E.store cfg ext w k).block_roots ∧
        is_ancestor (E.store cfg ext w k)
          (get_head cfg (E.store cfg ext w k))
          (get_node_for_root c) = true

private theorem currentTarget_vote_support_of_canonical
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q) {c : Root}
    (hcV : c ∈ (E.store cfg ext v q).block_roots)
    (hcEpoch : get_block_epoch cfg (E.store cfg ext v q) c =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hVanc : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q)) (get_node_for_root c) = true)
    (hwalkBoundary : ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg (E.store cfg ext v q))) r)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {s : Slot}
    (hepoch : compute_epoch_at_slot cfg s =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hsH : E.SlotWithinHorizon cfg s) (hsq : E.slot_at cfg q ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote w s = some (k, a))
    (hcanon : c ∈ (E.store cfg ext w k).block_roots ∧
      is_ancestor (E.store cfg ext w k)
        (get_head cfg (E.store cfg ext w k)) (get_node_for_root c) = true) :
    a.data.target = get_current_target cfg (E.store cfg ext v q) := by
  let V := E.store cfg ext v q
  let e := get_current_store_epoch cfg V
  have hepoch' : compute_epoch_at_slot cfg s = e := hepoch
  have hs0 : E.slot_at cfg 0 ≤ s :=
    (E.slot_at_mono cfg (Nat.zero_le q)).trans hsq
  have hcomm : w ∈ E.committee s :=
    hA.honest_behavior.votes_assigned w hw s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨k', index, hHk, hk, hvoteHead⟩ :=
    hA.honest_behavior.votes_head w hw s hcomm hsH hs0
  have hvoteEq := hvote
  rw [hvoteHead] at hvoteEq
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
  obtain ⟨hkk, ha⟩ := hvoteEq
  subst hkk
  subst ha
  obtain ⟨hcW, hWanc⟩ := hcanon
  let W := E.store cfg ext w k'
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hVpar : ParentSlotLt V :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled v q
  have hWpar : ParentSlotLt W :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled w k'
  have hagree : ∀ r, r ∈ V.block_roots → r ∈ W.block_roots →
      V.blocks r = W.blocks r := fun r hrV hrW =>
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w k')
      hrV hrW
  have hheadV : (get_head cfg V).root ∈ V.block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hv q hqH
  have hheadW : (get_head cfg W).root ∈ W.block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hw k' hHk
  -- the honest target epoch is the vote-slot epoch
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk
      hanchorSlot hanchorParent
  have hcore := E.store_wellFormedStoreCore cfg ext
    hA.externals_coherence.state_transition_slot hgws.core w k'
  have hheadStateSlot :
      (W.block_states (get_head cfg W).root).slot ≤ s := by
    rw [hcore.2 _ hheadW]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      hA.whole_seconds ⟨ast, ablk, hgenEq, hanchorSlot⟩ w k' _ hheadW
    rwa [E.store_current_slot cfg ext w k', hk] at hblockSlot
  have htargetEpoch :
      (honest_attestation_data cfg ext W s index).target.epoch = e := by
    rw [honest_attestation_data_target_epoch cfg ext W s index
      hA.externals_coherence.process_slots_slot hheadStateSlot]
    exact hepoch'
  have hroot := head_checkpoint_eq_of_common_block cfg hVpar hWpar hagree
    hcV hcW (by rw [← hcEpoch]; exact start_slot_at_block_epoch_le cfg V c)
    hVanc hWanc (hwalkBoundary v hv q hqH _ hheadV)
    (hwalkBoundary w hw k' hHk _ hheadW)
    (hwalkBoundary v hv q hqH _ hcV) (hwalkBoundary w hw k' hHk _ hcW)
  change (honest_attestation_data cfg ext W s index).target =
    get_checkpoint_for_block cfg V (get_head cfg V).root e
  have hrootData := honest_attestation_data_target_root cfg ext W s index
  rw [htargetEpoch] at hrootData
  cases htarget : (honest_attestation_data cfg ext W s index).target with
  | mk tepoch troot =>
    rw [htarget] at htargetEpoch hrootData
    simp only at htargetEpoch hrootData
    simp only [get_checkpoint_for_block, htargetEpoch, hrootData]
    exact congrArg (Checkpoint.mk e) hroot


/-- The current-target proviso follows from canonicity of any current-epoch
block on the caller's head chain, at every later honest vote of the epoch. -/
theorem currentTarget_support_of_canonical
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q) {c : Root}
    (hcV : c ∈ (E.store cfg ext v q).block_roots)
    (hcEpoch : get_block_epoch cfg (E.store cfg ext v q) c =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hVanc : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q)) (get_node_for_root c) = true)
    (hwalkBoundary : ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg (E.store cfg ext v q))) r)
    (hcanon : E.CanonicalAtHonestVotesFrom cfg ext c
      (get_current_store_epoch cfg (E.store cfg ext v q)) q) :
    HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v q)) q := by
  refine ⟨hqH, ?_⟩
  intro w hw sl hsH hepoch hsq k a hvote
  exact E.currentTarget_vote_support_of_canonical cfg ext hA hv hqH
    hcV hcEpoch hVanc hwalkBoundary hw hepoch hsH hsq hvote
    (hcanon w hw sl hsH hepoch hsq k a hvote)

end Execution

end FastConfirmation.Spec

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A head descending from `r` has an epoch-`e` checkpoint block that also
descends from `r`, when `r` is at or before the epoch-`e` boundary. -/
theorem checkpoint_block_descends_of_head_descends
    {W : Store Root} (hW : ParentSlotLt W) {r : Root} {e : Epoch}
    (hanc : is_ancestor W (get_head cfg W) (get_node_for_root r) = true)
    (hslot : (W.blocks r).slot ≤ compute_start_slot_at_epoch cfg e)
    (hwalk : WalkKnown W (W.blocks r).slot (get_head cfg W).root) :
    is_ancestor W
      (get_node_for_root (get_checkpoint_block cfg W (get_head cfg W).root e))
      (get_node_for_root r) = true := by
  have hanc' : is_ancestor W (get_node_for_root (get_head cfg W).root)
      (get_node_for_root r) = true :=
    (congrArg (· = true) (is_ancestor_pending_root_eq W
      (get_head cfg W).root r .pending
      (get_head cfg W).payload_status)).mpr hanc
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq] at hanc' ⊢
  have hcomp := get_ancestor_comp_root hW hslot hwalk
  simp only [get_checkpoint_block, get_node_for_root] at hcomp hanc' ⊢
  rw [hcomp]
  exact hanc'

namespace Execution

variable (E : Execution Root)

/-- The Lemma 42 form follows from canonicity of the previous-epoch result
at the later honest votes of the epoch.  Unlike `HonestVotesSupportTarget`,
it does not name the caller's own head checkpoint. -/
theorem previousResult_descendSupport_of_canonical
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    {r : Root} {e : Epoch}
    (hrV : r ∈ (E.store cfg ext v q).block_roots)
    (hrslot : ((E.store cfg ext v q).blocks r).slot ≤
      compute_start_slot_at_epoch cfg e)
    (hcanon : E.CanonicalAtHonestVotesFrom cfg ext r e q) :
    HonestVotesTargetDescendFrom cfg E r e q := by
  refine ⟨hqH, ?_⟩
  intro w hw s hsH hepoch hsq k a hvote
  have hs0 : E.slot_at cfg 0 ≤ s :=
    (E.slot_at_mono cfg (Nat.zero_le q)).trans hsq
  have hcomm : w ∈ E.committee s :=
    hA.honest_behavior.votes_assigned w hw s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨k', index, hHk, hk, hvoteHead⟩ :=
    hA.honest_behavior.votes_head w hw s hcomm hsH hs0
  have hvoteEq := hvote
  rw [hvoteHead] at hvoteEq
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
  obtain ⟨hkk, ha⟩ := hvoteEq
  subst hkk
  subst ha
  obtain ⟨hrW, hWanc⟩ := hcanon w hw s hsH hepoch hsq k'
    (honest_attestation cfg ext (E.store cfg ext w k') s index w) hvote
  let W := E.store cfg ext w k'
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hWpar : ParentSlotLt W :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled w k'
  have hheadW : (get_head cfg W).root ∈ W.block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hw k' hHk
  have hagree : (E.store cfg ext v q).blocks r = W.blocks r :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w k')
      hrV hrW
  have hwalk : WalkKnown W (W.blocks r).slot (get_head cfg W).root :=
    E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence hgen
      w k' r hrW _ hheadW
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgenEq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk
      hanchorSlot hanchorParent
  have hcore := E.store_wellFormedStoreCore cfg ext
    hA.externals_coherence.state_transition_slot hgws.core w k'
  have hheadStateSlot :
      (W.block_states (get_head cfg W).root).slot ≤ s := by
    rw [hcore.2 _ hheadW]
    have hblockSlot := E.store_blocks_slot_le_current cfg ext
      hA.whole_seconds ⟨ast, ablk, hgenEq, hanchorSlot⟩ w k' _ hheadW
    rwa [E.store_current_slot cfg ext w k', hk] at hblockSlot
  have htargetEpoch :
      (honest_attestation_data cfg ext W s index).target.epoch = e := by
    rw [honest_attestation_data_target_epoch cfg ext W s index
      hA.externals_coherence.process_slots_slot hheadStateSlot]
    exact hepoch
  have hrootData := honest_attestation_data_target_root cfg ext W s index
  rw [htargetEpoch] at hrootData
  have hdesc := checkpoint_block_descends_of_head_descends cfg hWpar
    hWanc (by rw [← hagree]; exact hrslot) hwalk
  have hrslotW : (W.blocks r).slot ≤ compute_start_slot_at_epoch cfg e := by
    rw [← hagree]
    exact hrslot
  have htargetKnown : get_checkpoint_block cfg W (get_head cfg W).root e ∈
      W.block_roots :=
    (get_ancestor_spec hWpar (hwalk.mono hrslotW)).1
  have hsemantic := E.rootDescends_of_store_ancestor
    (E.blockProvenance cfg ext w k') hWpar
    (E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence hgen
      w k' r hrW _ htargetKnown) hdesc
  change (honest_attestation_data cfg ext W s index).target.epoch = e ∧
    E.RootDescends (honest_attestation_data cfg ext W s index).target.root r
  rw [hrootData]
  exact ⟨htargetEpoch, hsemantic⟩

end Execution

end FastConfirmation.Spec


namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Support truncated at an endpoint slot `sl`: only votes of slots before
`sl` are constrained.  This is what an endpoint-slot induction hypothesis
can supply at endpoint slot `sl`. -/
def HonestVotesSupportTargetBefore (T : Checkpoint Root) (q : ℕ)
    (sl : Slot) : Prop :=
  E.WithinHorizon cfg q ∧
    ∀ v ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
      compute_epoch_at_slot cfg s = T.epoch → E.slot_at cfg q ≤ s →
      s < sl → ∀ k a, E.vote v s = some (k, a) → a.data.target = T

/-- Canonicity is required only at honest votes strictly before `cutoff`.
This is the exact time range of the endpoint-slot induction hypothesis. -/
def CanonicalAtHonestVotesBefore (c : Root) (e : Epoch) (q : ℕ)
    (cutoff : Slot) : Prop :=
  ∀ w ∈ E.honest, ∀ s : Slot, E.SlotWithinHorizon cfg s →
    compute_epoch_at_slot cfg s = e → E.slot_at cfg q ≤ s → s < cutoff →
    ∀ k a, E.vote w s = some (k, a) →
      c ∈ (E.store cfg ext w k).block_roots ∧
        is_ancestor (E.store cfg ext w k)
          (get_head cfg (E.store cfg ext w k)) (get_node_for_root c) = true

/-- The endpoint induction supplies canonicity at all earlier honest votes.
Knownness is the independent selected-result delivery invariant. -/
theorem canonicalAtHonestVotesBefore_of_endpoint_induction
    (hA : SelectedMarginAssumptions cfg ext E)
    {c : Root} {e : Epoch} {q : ℕ} {cutoff : Slot}
    (hknown : ∀ w ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ k → E.WithinHorizon cfg k →
        c ∈ (E.store cfg ext w k).block_roots)
    (hIH : ∀ w ∈ E.honest, ∀ k : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ k → E.slot_at cfg k < cutoff →
      E.WithinHorizon cfg k →
        is_ancestor (E.store cfg ext w k) (get_head cfg (E.store cfg ext w k))
          (get_node_for_root c) = true) :
    E.CanonicalAtHonestVotesBefore cfg ext c e q cutoff := by
  intro w hw sl hsH _hepoch hsq hbefore k a hvote
  have hcomm := hA.honest_behavior.votes_assigned w hw sl
    (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨k', index, hkH, hkSlot, hvoteHead⟩ :=
    hA.honest_behavior.votes_head w hw sl hcomm hsH
      ((E.slot_at_mono cfg (Nat.zero_le q)).trans hsq)
  have heq := hvote
  rw [hvoteHead] at heq
  simp only [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, _⟩ := heq
  have hstart : E.slot_start cfg (E.slot_at cfg q) ≤ k' :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (by rwa [hkSlot])
  exact ⟨hknown w hw k' hstart hkH,
    hIH w hw k' hstart (by rwa [hkSlot]) hkH⟩

/-- A current-epoch common block fixes the target of each honest vote before
an endpoint, without any condition on votes at or after that endpoint. -/
theorem currentTarget_supportBefore_of_canonical
    (hA : SelectedMarginAssumptions cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q) {c : Root} {cutoff : Slot}
    (hcV : c ∈ (E.store cfg ext v q).block_roots)
    (hcEpoch : get_block_epoch cfg (E.store cfg ext v q) c =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hVanc : is_ancestor (E.store cfg ext v q)
      (get_head cfg (E.store cfg ext v q)) (get_node_for_root c) = true)
    (hwalkBoundary : ∀ w ∈ E.honest, ∀ m, E.WithinHorizon cfg m →
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          (compute_start_slot_at_epoch cfg
            (get_current_store_epoch cfg (E.store cfg ext v q))) r)
    (hcanon : E.CanonicalAtHonestVotesBefore cfg ext c
      (get_current_store_epoch cfg (E.store cfg ext v q)) q cutoff) :
    E.HonestVotesSupportTargetBefore cfg
      (get_current_target cfg (E.store cfg ext v q)) q cutoff := by
  refine ⟨hqH, ?_⟩
  intro w hw sl hsH hepoch hsq hbefore k a hvote
  exact E.currentTarget_vote_support_of_canonical cfg ext hA hv hqH
    hcV hcEpoch hVanc hwalkBoundary hw hepoch hsH hsq hvote
    (hcanon w hw sl hsH hepoch hsq hbefore k a hvote)

/-- At any endpoint slot after the target epoch, the truncated support is
the full proviso.  So the proviso is available, from the endpoint-slot
induction, exactly at the endpoints where an epoch-`T.epoch` justified
checkpoint can first be in a store. -/
theorem support_of_before_epoch_end {T : Checkpoint Root} {q : ℕ}
    {sl : Slot} (hsl : compute_start_slot_at_epoch cfg (T.epoch + 1) ≤ sl)
    (h : E.HonestVotesSupportTargetBefore cfg T q sl) :
    HonestVotesSupportTarget cfg E T q := by
  refine ⟨h.1, ?_⟩
  intro v hv s hsH hepoch hsq k a hvote
  refine h.2 v hv s hsH hepoch hsq ?_ k a hvote
  refine lt_of_lt_of_le ?_ hsl
  have hpos : 0 < cfg.slots_per_epoch := cfg.slots_per_epoch_pos
  simp only [compute_epoch_at_slot] at hepoch
  simp only [compute_start_slot_at_epoch]
  exact Nat.lt_mul_of_div_lt (by rw [hepoch]; exact Nat.lt_succ_self _) hpos

end Execution

end FastConfirmation.Spec

end
