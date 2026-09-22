module
public import FastConfirmation.Spec.Proof.SelectedCommitteeSupport
public import FastConfirmation.Spec.Proof.CertExtract

@[expose] public section

/-!
# Causal checkpoint compatibility for a post-query selected edge

This file isolates the branch-compatibility step used by the coupled safety
induction.  Suppose an honest validator casts a vote after the selected query
slot has begun and before an endpoint.  If that vote targets the endpoint's
realized justified checkpoint, then the ordinary vote-your-head rule, the
earlier-slot head-safety induction, and block relay put both the selected child
and the justified root below the same honest source head at the endpoint.
Comparability therefore forces the justified root to lie on the selected
child's chain whenever the opposite (already-covered) orientation is excluded.

The theorem deliberately takes the causal ground vote and its target identity
as premises.  It does not assume retained-filter placement, filter membership,
or any future/global justified-placement property.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- A causal post-query honest vote targeting the endpoint's justified
checkpoint makes that checkpoint branch-compatible with a selected child.

The conclusion is the non-covered orientation: the selected child descends
from the endpoint's justified root.  The excluded orientation is exactly the
ordinary direct-coverage test used by `SelectedCoveredMarginSupplyAt`.
-/
theorem endpoint_justified_ancestor_of_causal_honest_target_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {q : ℕ} {glc c : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
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
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root c)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true := by
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
  have htargetRoot : J.root = get_checkpoint_block cfg
      (E.store cfg ext i k) (get_head cfg (E.store cfg ext i k)).root J.epoch := by
    have htargetData : (honest_attestation_data cfg ext
        (E.store cfg ext i k) s index).target = J := by
      simpa only [honest_attestation_data_eq] using htarget
    have hroot := honest_attestation_data_target_root cfg ext
      (E.store cfg ext i k) s index
    rw [htargetData] at hroot
    exact hroot
  have hrootWalk : (get_ancestor (E.store cfg ext i k)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (compute_start_slot_at_epoch cfg J.epoch)).root = J.root := by
    simpa only [get_checkpoint_block] using htargetRoot.symm
  have htargetSpec := get_ancestor_spec hwfK htargetWalk
  rw [hrootWalk] at htargetSpec
  have hJK : J.root ∈ (E.store cfg ext i k).block_roots := htargetSpec.1
  have hJslot : ((E.store cfg ext i k).blocks J.root).slot ≤
      compute_start_slot_at_epoch cfg J.epoch := htargetSpec.2
  have hheadJ_K : is_ancestor (E.store cfg ext i k)
      (get_head cfg (E.store cfg ext i k)) (get_node_for_root J.root) = true := by
    rw [is_ancestor_node_root]
    simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq]
    have hcomp := get_ancestor_comp_root hwfK hJslot
      (hwalkK J.root hJK _ hheadK)
    rw [hrootWalk, get_ancestor_stop (le_refl _)] at hcomp
    exact hcomp.symm
  have hkLower : E.slot_start cfg (E.slot_at cfg q) ≤ k :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (by
      rw [hk]
      exact hqs)
  have hkSlotLt : E.slot_at cfg k < E.slot_at cfg m := by
    rw [hk]
    exact hsm
  have hheadGlc_K : is_ancestor (E.store cfg ext i k)
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
  have hheadM : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext w m).block_roots := hsub hheadK
  have hglcM : glc ∈ (E.store cfg ext w m).block_roots := hsub hglcK
  have hJM : J.root ∈ (E.store cfg ext w m).block_roots := hsub hJK
  have hheadGlc_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (get_node_for_root glc) = true :=
    is_ancestor_transport cfg ext hA.wellFormed hsub hheadK hglcK
      (hwalkK glc hglcK _ hheadK) ((is_ancestor_node_root _ _ _).symm.trans hheadGlc_K)
  have hheadJ_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (get_node_for_root J.root) = true :=
    is_ancestor_transport cfg ext hA.wellFormed hsub hheadK hJK
      (hwalkK J.root hJK _ hheadK) ((is_ancestor_node_root _ _ _).symm.trans hheadJ_K)
  obtain ⟨hwfM, hwalkM, _hjustM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have hheadC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (get_head cfg (E.store cfg ext i k)).root)
      (get_node_for_root c) = true :=
    is_ancestor_trans hwfM
      (hwalkM c hcM _ hheadM) (hwalkM c hcM glc hglcM)
      hheadGlc_M hglcC_M
  rcases is_ancestor_comparable hwfM
      (hwalkM J.root hJM _ hheadM) (hwalkM c hcM _ hheadM)
      hheadJ_M hheadC_M with hchildJ | hJchild
  · exact hchildJ
  · exact False.elim (hnotCovered (by simpa only [J] using hJchild))

end Execution

end FastConfirmation.Spec

end
