module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunReads

/-! One trusted FFG interpretation covers the actual non-honest observer run. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- Causal membership has a boundary-store witness. -/
theorem causal_known {store : Store Root} (hs : E.CausalStore cfg ext store)
    {r} (hr : r ∈ store.block_roots) : ∃ w n, r ∈ (E.store cfg ext w n).block_roots := by
  cases hs with
  | genesis => exact ⟨0, 0, hr⟩
  | scheduledPrefix p => exact ⟨p.node, p.previousSecond + 1, (prefix_le_boundary p).1 hr⟩

theorem shared_values (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r} (hr : (E.withoutObserver obs).AcceptedRoot cfg ext r) :
    (state hobs core localInputs B).GJ r = core.semantics.state.GJ r ∧
    (state hobs core localInputs B).GF r = core.semantics.state.GF r ∧
    (state hobs core localInputs B).GU r = core.semantics.state.GU r ∧
    (state hobs core localInputs B).GUF r = core.semantics.state.GUF r ∧
    ∀ e, (state hobs core localInputs B).C r e = core.semantics.state.C r e := by
  simp only [state, content, ObserverFFGContent.union, sharedContent,
    if_pos hr, true_and, implies_true]

theorem local_values (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r} (hr : B.state.domain r) :
    (state hobs core localInputs B).GJ r = B.state.GJ r ∧
    (state hobs core localInputs B).GF r = B.state.GF r ∧
    (state hobs core localInputs B).GU r = B.state.GU r ∧
    (state hobs core localInputs B).GUF r = B.state.GUF r ∧
    ∀ e, (state hobs core localInputs B).C r e = B.state.C r e := by
  classical
  by_cases hs : (E.withoutObserver obs).AcceptedRoot cfg ext r
  · have h := shared_values hobs core localInputs B hs
    have h' := selectors_agree core localInputs B hs hr
    exact ⟨h.1.trans h'.1.symm, h.2.1.trans h'.2.1.symm,
      h.2.2.1.trans h'.2.2.1.symm, h.2.2.2.1.trans h'.2.2.2.symm,
      fun e => (h.2.2.2.2 e).trans (checkpoints_agree core localInputs B hs hr e).symm⟩
  · simp only [state, content, ObserverFFGContent.union, sharedContent,
      if_neg hs, true_and, implies_true]

/-- The chosen checkpoint selector reflects every actual causal store. -/
theorem checkpoint_of_known (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {store : Store Root} (hs : E.CausalStore cfg ext store) {r}
    (hr : r ∈ store.block_roots) (e) :
    (state hobs core localInputs B).C r e = get_checkpoint_for_block cfg store r e := by
  rcases accepted_cases ⟨store, hs, hr⟩ with hshared | hlocal
  · obtain ⟨w, hw, n, hk⟩ := shared_known hshared
    rw [(shared_values hobs core localInputs B hshared).2.2.2.2 e]
    have hC := core.semantics.coherence.checkpoint_of_known
      ((E.withoutObserver obs).store_causal cfg ext w n) r
      (by simpa only [withoutObserver_store cfg ext E obs w hw n] using hk) e
    rw [withoutObserver_store cfg ext E obs w hw n] at hC
    exact hC.trans (checkpoint_reads_agree core localInputs
      (E.store_causal cfg ext w n) hs hk hr e)
  · obtain ⟨n, hk⟩ := local_known hlocal
    rw [(local_values hobs core localInputs B ((B.domain_local r).mpr hlocal)).2.2.2.2 e]
    exact (B.checkpoint_of_known (store_observerCausal n) r hk e).trans
      (checkpoint_reads_agree core localInputs (E.store_causal cfg ext obs n) hs hk hr e)

/-- A union formed entry is its carrier's exact checkpoint. -/
theorem formed_checkpoint (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r c} (hf : (state hobs core localInputs B).formed r c) :
    c = (state hobs core localInputs B).C r c.epoch := by
  rcases hf with hf | hf
  · have hr := core.semantics.state.formed_carrier_accepted hf
    obtain ⟨w, hw, n, hk⟩ := shared_known hr
    have hC := core.semantics.coherence.au_checkpoint_of_known
      ((E.withoutObserver obs).store_causal cfg ext w n) r
      (by simpa only [withoutObserver_store cfg ext E obs w hw n] using hk) c
      ⟨r, .refl _, hf⟩
    rw [withoutObserver_store cfg ext E obs w hw n] at hC
    exact hC.trans (checkpoint_of_known hobs core localInputs B
      (E.store_causal cfg ext w n) hk c.epoch).symm
  · obtain ⟨n, hk⟩ := local_known (B.formed_local hf)
    exact (B.au_checkpoint_of_known (store_observerCausal n) r hk c ⟨r, .refl _, hf⟩).trans
      (checkpoint_of_known hobs core localInputs B (E.store_causal cfg ext obs n) hk c.epoch).symm

/-- Every known tip reaches a boundary at or after the trusted anchor. -/
theorem boundary_walk (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {w n r e} (hr : r ∈ (E.store cfg ext w n).block_roots)
    (he : E.genesis_store.justified_checkpoint.epoch ≤ e) :
    WalkKnown (E.store cfg ext w n) (compute_start_slot_at_epoch cfg e) r := by
  obtain ⟨ast, ablk, hg, hslot, _, hp⟩ := core.genesis
  have hgE : E.genesis_store = get_forkchoice_store cfg ast ablk := hg
  have hwf := localInputs.wellFormed cfg ext core.base.wellFormed
  have hk0 : ablk.root ∈ E.genesis_store.block_roots := by simp [hgE, get_forkchoice_store]
  have hk := (E.store_storeLE cfg ext w (Nat.zero_le n)).1 hk0
  have hb := E.store_anchor_block cfg ext hwf hgE w n hk
  have ha : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg E.genesis_store.justified_checkpoint.epoch := by
    have ha := core.anchor_boundary
    rw [core.anchor_eq] at ha
    simpa only [TrustedAnchorBoundaryAligned, withoutObserver, hgE,
      get_forkchoice_store, Function.update_self] using ha
  have hwalk := E.store_walkKnownK cfg ext hwf (nonhonest_externals hobs core)
    ⟨ast, ablk, hgE, hslot, hp⟩ w n ablk.root hk r hr
  apply hwalk.mono
  rw [hb]
  exact ha.trans (Nat.mul_le_mul_right cfg.slots_per_epoch he)

/-- A descendant preserves the checkpoint of an ancestor above the epoch boundary. -/
theorem checkpoint_descends (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r carrier b e} (hr : E.AcceptedRoot cfg ext r)
    (hc : E.AcceptedBlockAt cfg ext carrier b) (hd : E.RootDescends r carrier)
    (he : E.genesis_store.justified_checkpoint.epoch ≤ e)
    (hb : compute_start_slot_at_epoch cfg e ≤ b.slot) :
    (state hobs core localInputs B).C r e = (state hobs core localInputs B).C carrier e := by
  obtain ⟨store, hs, hk⟩ := hr
  obtain ⟨w, n, hkr⟩ := causal_known hs hk
  obtain ⟨hkc, hanc⟩ := known_ancestor hobs core localInputs hkr hc.acceptedRoot hd
  obtain ⟨ast, ablk, hg, hslot, _, hp⟩ := core.genesis
  have hwf := localInputs.wellFormed cfg ext core.base.wellFormed
  have hps := E.store_parentSlotLt cfg ext hwf (nonhonest_externals hobs core)
    ⟨ast, ablk, hg, hslot, hp⟩ hwf.anchor_parent_unscheduled w n
  have hbc := (E.store_causal cfg ext w n).acceptedBlockAt_iff_eq cfg ext E hwf hkc |>.mp hc
  rw [checkpoint_of_known hobs core localInputs B (E.store_causal cfg ext w n) hkr e,
    checkpoint_of_known hobs core localInputs B (E.store_causal cfg ext w n) hkc e]
  exact congrArg (fun x => Checkpoint.mk e x)
    (get_checkpoint_block_of_ancestor cfg hps hanc (by rwa [hbc])
      (boundary_walk hobs core localInputs hkr he))

/-- Union AU reflects at every actual causal store. -/
theorem au_checkpoint_of_known (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {store : Store Root} (hs : E.CausalStore cfg ext store) {r c}
    (hr : r ∈ store.block_roots) (hau : (state hobs core localInputs B).AU cfg ext r c) :
    c = get_checkpoint_for_block cfg store r c.epoch := by
  obtain ⟨carrier, hd, hf⟩ := hau
  let S := state hobs core localInputs B
  have hc := S.formed_carrier_accepted hf
  obtain ⟨bc, hbc⟩ := hc.exists_blockAt
  have hepoch := S.au_epoch_le_block hbc ⟨carrier, .refl _, hf⟩
  have hboundary : compute_start_slot_at_epoch cfg c.epoch ≤ bc.slot :=
    (Nat.mul_le_mul_right cfg.slots_per_epoch hepoch).trans (Nat.div_mul_le_self _ _)
  obtain ⟨hcert⟩ := (S.formed_evidence hf).certified
  have hanchor := IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hcert
  exact (formed_checkpoint hobs core localInputs B hf).trans
    ((checkpoint_descends hobs core localInputs B
      ⟨store, hs, hr⟩ hbc hd hanchor hboundary).symm.trans
      (checkpoint_of_known hobs core localInputs B hs hr c.epoch))

/-- A successful non-observer transition is the same exact shared call. -/
def sharedTransition (t : E.AcceptedBlockTransition cfg ext) (ht : t.atPrefix.node ≠ obs) :
    (E.withoutObserver obs).AcceptedBlockTransition cfg ext where
  atPrefix := sharedPrefix t.atPrefix ht
  signedBlock := t.signedBlock
  event_at := by simpa only [sharedPrefix, withoutObserver, if_neg ht] using t.event_at
  postStore := t.postStore
  accepted := by rw [sharedPrefix_store]; exact t.accepted

/-- Actual transitions and checkpoint reads agree with the combined state. -/
def coherence (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext
      (state hobs core localInputs B) where
  attestation_validity := rfl
  genesis_gj := by
    intro r hr
    exact (core.semantics.coherence.genesis_gj r hr).trans
      (shared_values hobs core localInputs B ⟨_, .genesis, hr⟩).1.symm
  genesis_gf := by
    intro r hr
    exact (core.semantics.coherence.genesis_gf r hr).trans
      (shared_values hobs core localInputs B ⟨_, .genesis, hr⟩).2.1.symm
  genesis_gu := by
    intro r hr
    exact (core.semantics.coherence.genesis_gu r hr).trans
      (shared_values hobs core localInputs B ⟨_, .genesis, hr⟩).2.2.1.symm
  genesis_guf := by
    intro r hr
    exact (core.semantics.coherence.genesis_guf r hr).trans
      (shared_values hobs core localInputs B ⟨_, .genesis, hr⟩).2.2.2.1.symm
  genesis_unrealized_justification := by
    intro r hr
    exact (core.semantics.coherence.genesis_unrealized_justification r hr).trans
      (shared_values hobs core localInputs B ⟨_, .genesis, hr⟩).2.2.1.symm
  transition_gj := by
    intro t
    by_cases ht : t.atPrefix.node = obs
    · exact (B.selectors.transition_gj t ht).trans
        (local_values hobs core localInputs B
          (B.known_domain (B.transition_local t ht) t.root_known)).1.symm
    · let t' := sharedTransition t ht
      exact (core.semantics.coherence.transition_gj t').trans
        (shared_values hobs core localInputs B
          ⟨t'.postStore, t'.post_causal, t'.root_known⟩).1.symm
  transition_gf := by
    intro t
    by_cases ht : t.atPrefix.node = obs
    · exact (B.selectors.transition_gf t ht).trans
        (local_values hobs core localInputs B
          (B.known_domain (B.transition_local t ht) t.root_known)).2.1.symm
    · let t' := sharedTransition t ht
      exact (core.semantics.coherence.transition_gf t').trans
        (shared_values hobs core localInputs B
          ⟨t'.postStore, t'.post_causal, t'.root_known⟩).2.1.symm
  transition_gu := by
    intro t
    by_cases ht : t.atPrefix.node = obs
    · exact (B.selectors.transition_gu t ht).trans
        (local_values hobs core localInputs B
          (B.known_domain (B.transition_local t ht) t.root_known)).2.2.1.symm
    · let t' := sharedTransition t ht
      exact (core.semantics.coherence.transition_gu t').trans
        (shared_values hobs core localInputs B
          ⟨t'.postStore, t'.post_causal, t'.root_known⟩).2.2.1.symm
  transition_guf := by
    intro t
    by_cases ht : t.atPrefix.node = obs
    · exact (B.selectors.transition_guf t ht).trans
        (local_values hobs core localInputs B
          (B.known_domain (B.transition_local t ht) t.root_known)).2.2.2.1.symm
    · let t' := sharedTransition t ht
      exact (core.semantics.coherence.transition_guf t').trans
        (shared_values hobs core localInputs B
          ⟨t'.postStore, t'.post_causal, t'.root_known⟩).2.2.2.1.symm
  checkpoint_of_known := fun hs _ hr e => checkpoint_of_known hobs core localInputs B hs hr e
  au_checkpoint_of_known := fun hs _ hr _ hau =>
    au_checkpoint_of_known hobs core localInputs B hs hr hau

/-- The full actual run has one trusted interpretation from the restricted premises. -/
noncomputable def interpretation (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) where
  anchor := E.genesis_store.justified_checkpoint
  state := state hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)
  coherence := coherence hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)

/-- Existence form of the actual-run interpretation. -/
theorem actualRun_interpretation (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    Nonempty (TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs)) :=
  ⟨interpretation hobs premises⟩

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
