module
public import FastConfirmation.Spec.Proof.CausalCheckpointCompatibility

@[expose] public section

/-!
# Causal checkpoint epoch bound

This module isolates the geometric fact used by the late available-unrealized
case.  An honest attestation target is the checkpoint block of its source
head at the target epoch boundary.  If that boundary were strictly after a
selected block on the same head chain, walk composition would put the target
checkpoint above (descendant from) the selected block.  Excluding exactly that
orientation therefore bounds the target epoch by the selected block's epoch.

The execution theorem below obtains the source head from the actual honest
ground vote, uses the earlier-slot head-safety induction only at that causal
source store, and transports the contradiction to the endpoint using ordinary
block relay and block provenance.  No FFG inclusion, filter placement, future
head property, or desired selected-result compatibility is assumed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Pure checkpoint geometry -/

/-- If `J` is the epoch-boundary checkpoint of `H`, `H` descends from `glc`,
and `J` does not descend from `glc`, then `J`'s epoch is no later than the
epoch of `glc`.

The proof is just `get_ancestor_comp`.  Were `epoch(glc) < J.epoch`, the slot
of `glc` would be below the `J.epoch` boundary, so walking `H` first to that
boundary and then to `glc.slot` would be the same as walking directly to
`glc.slot`.  The two supplied identities turn this into `J ⩾c glc`, contrary
to `hnotJGlc`. -/
theorem checkpointTarget_epoch_le_of_head_descent_and_reverse_exclusion
    {store : Store Root} {J : Checkpoint Root} {H glc : Root}
    (hwf : ParentSlotLt store)
    (hwalkGlc : WalkKnown store (store.blocks glc).slot H)
    (htarget : get_checkpoint_block cfg store H J.epoch = J.root)
    (hHGlc : is_ancestor store
      (get_node_for_root H) (get_node_for_root glc) = true)
    (hnotJGlc : is_ancestor store
      (get_node_for_root J.root) (get_node_for_root glc) ≠ true) :
    J.epoch ≤ get_block_epoch cfg store glc := by
  by_contra hbound
  have hepoch : get_block_epoch cfg store glc < J.epoch :=
    Nat.lt_of_not_ge hbound
  have hslot : (store.blocks glc).slot <
      compute_start_slot_at_epoch cfg J.epoch := by
    simp only [get_block_epoch, compute_epoch_at_slot,
      compute_start_slot_at_epoch] at hepoch ⊢
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp hepoch
  simp only [get_checkpoint_block] at htarget
  have hcomp := get_ancestor_comp_root hwf (Nat.le_of_lt hslot) hwalkGlc
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hHGlc
  rw [htarget, hHGlc] at hcomp
  apply hnotJGlc
  simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hcomp

namespace Execution

variable (E : Execution Root)

/-! ## Causal source to endpoint -/

/-- A causal post-query honest vote targeting the endpoint justified
checkpoint bounds that checkpoint's epoch by the selected block's epoch in
the endpoint store, whenever the reverse orientation `J ⩾c glc` is excluded.

Unlike the companion branch-compatibility theorem, no selected child or
selected-child ancestry premise is needed.  The only chain fact is the
earlier-slot induction conclusion for the actual source head of the vote. -/
theorem endpoint_justified_epoch_le_of_causal_honest_target_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {q : ℕ} {glc : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hqs : E.slot_at cfg q ≤ s)
    (hsm : s < E.slot_at cfg m)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    (htarget₀ : a₀.data.target =
      (E.store cfg ext w m).justified_checkpoint)
    (hnotJGlc : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root glc) ≠ true) :
    (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg (E.store cfg ext w m) glc := by
  let J := (E.store cfg ext w m).justified_checkpoint
  have hcomm : i ∈ E.committee s :=
    hA.honest_behavior.votes_assigned i hi s
      (by rw [hvote₀]; exact Option.some_ne_none _)
  have hs0 : E.slot_at cfg 0 ≤ s :=
    (E.slot_at_mono cfg (Nat.zero_le q)).trans hqs
  obtain ⟨k, index, hHk, hk, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi s hcomm hsH hs0
  have hvoteEq := hvote₀
  rw [hvoteHead] at hvoteEq
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteEq
  obtain ⟨_, hattestation⟩ := hvoteEq
  have htarget :
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target = J := by
    rw [hattestation]
    exact htarget₀
  have htargetWalk : WalkKnown (E.store cfg ext i k)
      (compute_start_slot_at_epoch cfg J.epoch)
      (get_head cfg (E.store cfg ext i k)).root := by
    simpa only [htarget] using
      hwalkDomain i hi s k index hs0 hHk hk hvoteHead
  obtain ⟨hwfK, hwalkK, _hjustK⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain i hi k hHk
  have hheadK : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots :=
    E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi k hHk
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
  have htargetSpec := get_ancestor_spec hwfK htargetWalk
  have hrootWalk : (get_ancestor (E.store cfg ext i k)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (compute_start_slot_at_epoch cfg J.epoch)).root = J.root := by
    simpa only [get_checkpoint_block] using htargetRoot
  rw [hrootWalk] at htargetSpec
  have hJK : J.root ∈ (E.store cfg ext i k).block_roots := htargetSpec.1
  have hkLower : E.slot_start cfg (E.slot_at cfg q) ≤ k :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (by
      rw [hk]
      exact hqs)
  have hkSlotLt : E.slot_at cfg k < E.slot_at cfg m := by
    rw [hk]
    exact hsm
  have hheadGlcK : is_ancestor (E.store cfg ext i k)
      (get_head cfg (E.store cfg ext i k)) (get_node_for_root glc) = true :=
    hIH i hi k hkLower hkSlotLt hHk
  have hglcK : glc ∈ (E.store cfg ext i k).block_roots :=
    hglcKnown i hi k hkLower hHk
  have hgate : E.slot_at cfg k + 1 ≤ E.slot_at cfg (m + 1) := by
    calc
      E.slot_at cfg k + 1 = s + 1 := by rw [hk]
      _ ≤ E.slot_at cfg m := Nat.succ_le_of_lt hsm
      _ ≤ E.slot_at cfg (m + 1) := E.slot_at_mono cfg (Nat.le_succ m)
  have hsub : (E.store cfg ext i k).block_roots ⊆
      (E.store cfg ext w m).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hA.synchrony hi hw hHk hHm hgate
  have hnotJGlcK : is_ancestor (E.store cfg ext i k)
      (get_node_for_root J.root) (get_node_for_root glc) ≠ true := by
    intro hJGlcK
    have hJGlcM : is_ancestor (E.store cfg ext w m)
        (get_node_for_root J.root) (get_node_for_root glc) = true :=
      is_ancestor_transport cfg ext hA.wellFormed hsub hJK hglcK
        (hwalkK glc hglcK J.root hJK) hJGlcK
    exact hnotJGlc (by simpa only [J] using hJGlcM)
  have hboundK : J.epoch ≤
      get_block_epoch cfg (E.store cfg ext i k) glc :=
    checkpointTarget_epoch_le_of_head_descent_and_reverse_exclusion cfg
      hwfK (hwalkK glc hglcK _ hheadK) htargetRoot
      ((is_ancestor_node_root _ _ _).symm.trans hheadGlcK) hnotJGlcK
  have hglcAgree : (E.store cfg ext i k).blocks glc =
      (E.store cfg ext w m).blocks glc :=
    hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext i k) (E.blockProvenance cfg ext w m)
      hglcK (hsub hglcK)
  simpa only [J, get_block_epoch, hglcAgree] using hboundK

/-! ## Query-store projection -/

/-- Query-store form of the causal epoch bound.  The query need not precede
the endpoint in execution index: commonly-known roots have identical block
messages by execution provenance, so the endpoint bound rewrites to the query
store as soon as `glc` is known in that exact query store. -/
theorem query_justified_epoch_le_of_causal_honest_target_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {v : ValidatorIndex} {q : ℕ}
    {query : FastConfirmationStore Root} {glc : Root}
    (hquery : query.store = E.store cfg ext v q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hglcQ : glc ∈ query.store.block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {s : Slot} (hqs : E.slot_at cfg q ≤ s)
    (hsm : s < E.slot_at cfg m)
    (hsH : E.SlotWithinHorizon cfg s)
    {k₀ : ℕ} {a₀ : Attestation Root}
    (hvote₀ : E.vote i s = some (k₀, a₀))
    (htarget₀ : a₀.data.target =
      (E.store cfg ext w m).justified_checkpoint)
    (hnotJGlc : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root glc) ≠ true) :
    (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_block_epoch cfg query.store glc := by
  have hboundM := E.endpoint_justified_epoch_le_of_causal_honest_target_minimal
    cfg ext hA hwalkDomain hw hHm hglcKnown hIH hi hqs hsm hsH
      hvote₀ htarget₀ hnotJGlc
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m :=
    hqs.trans (Nat.le_of_lt hsm)
  have hstartM : E.slot_start cfg (E.slot_at cfg q) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hglcM : glc ∈ (E.store cfg ext w m).block_roots :=
    hglcKnown w hw m hstartM hHm
  have hglcAgree : query.store.blocks glc =
      (E.store cfg ext w m).blocks glc :=
    by
      rw [hquery]
      exact hA.wellFormed.blocks_agree
        (E.blockProvenance cfg ext v q) (E.blockProvenance cfg ext w m)
        (by simpa only [← hquery] using hglcQ) hglcM
  rw [get_block_epoch, hglcAgree] at ⊢
  simpa only [get_block_epoch] using hboundM

end Execution

end FastConfirmation.Spec

end
