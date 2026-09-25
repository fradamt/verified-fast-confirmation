module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunExactInterpretation
public import FastConfirmationProofs.Checkpoints.FinalizedBeforeVoteJustification

/-! Paper A3.2 transfers through the raw body relation of the actual run. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- A shared slashing pair remains present in the raw union. Equality of the
relations is not required, since a larger slashing set strengthens support. -/
theorem shared_slashable_subset (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    (tip : Root) :
    (core.semantics.state.paperA32Inputs cfg ext).slashableOnChain cfg tip ⊆
      ((exactState hobs core localInputs B).paperA32Inputs cfg ext).slashableOnChain cfg tip := by
  classical
  intro i hi
  obtain ⟨hir, a, a', ⟨r, hd, ha⟩, ⟨r', hd', ha'⟩, hia, hia', hs⟩ :=
    Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  exact ⟨hir, a, a', ⟨r, withoutObserver_descends hd, Or.inl ha⟩,
    ⟨r', withoutObserver_descends hd', Or.inl ha'⟩, hia, hia', hs⟩

/-- Honest stores and their support votes are unchanged by observer erasure. -/
def shared_support (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {w m tip source target} (hw : w ∈ E.honest)
    (Q : PaperA32LinkSupportAtCore cfg ext
      ((exactState hobs core localInputs B).paperA32Inputs cfg ext) w m tip source target) :
    PaperA32LinkSupportAtCore cfg ext
      (core.semantics.state.paperA32Inputs cfg ext) w m tip source target := by
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hstore := withoutObserver_store cfg ext E obs w hwne m
  exact {
    view_within_horizon := Q.view_within_horizon
    source_before_target := Q.source_before_target
    target_epoch_within := Q.target_epoch_within
    target_known := hstore.symm ▸ Q.target_known
    target_state_keyed := hstore.symm ▸ Q.target_state_keyed
    signers := Q.signers
    signers_not_slashable := fun i hi hs => Q.signers_not_slashable i hi
      (shared_slashable_subset hobs core localInputs B tip hs)
    signers_in_registry := Q.signers_in_registry
    signer_attestation := by
      intro i hi
      obtain ⟨a, ⟨k, hkm, fb, hs⟩, hia, hv, hrest⟩ := Q.signer_attestation i hi
      exact ⟨a, ⟨k, hkm, fb, by simpa only [withoutObserver, if_neg hwne] using hs⟩,
        hia, hstore.symm ▸ hv, hrest⟩
    supermajority := Q.supermajority }

/-- A3.2 holds for the actual interpretation. Its slashing set reads raw body
evidence; its AU relation and checkpoint selectors are unchanged by filtering. -/
theorem exactState_paperA32 (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    (exactState hobs core localInputs B).PaperA32Inclusion cfg ext := by
  constructor
  intro b bb e hb hbe hcan hsupport w hw m hm hboundary
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hwR : w ∈ (E.withoutObserver obs).honest := (withoutObserver_honest hobs).symm ▸ hw
  let S := state hobs core localInputs B
  have hb' : E.AcceptedBlockAt cfg ext b bb := hb
  obtain ⟨carrier, hd, hf⟩ := S.gu_mem b hb'.acceptedRoot
  have hae : E.genesis_store.justified_checkpoint.epoch ≤ e :=
    (IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg)
      (Classical.choice (S.formed_evidence hf).certified)).trans
      ((S.au_epoch_le_block hb' ⟨carrier, hd, hf⟩).trans hbe)
  let T := nonhonest_scheduledPrefix hobs core localInputs
  have hbound : E.TrustedAnchorBoundaryAligned (cfg := cfg)
      (anchor := E.genesis_store.justified_checkpoint) := by
    have h := core.anchor_boundary
    rw [core.anchor_eq] at h
    exact h
  have hstart : E.slot_at cfg 0 ≤ compute_start_slot_at_epoch cfg (e + 1) :=
    (E.initial_slot_le_anchor_boundary cfg ext T rfl hbound).trans
      (Nat.mul_le_mul_right cfg.slots_per_epoch (hae.trans (Nat.le_succ e)))
  obtain ⟨ast, ablk, hg, hslot, _, hp⟩ := core.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    have hgE : E.genesis_store = get_forkchoice_store cfg ast ablk := hg
    rw [hgE]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot hp).time_ge_genesis
  let q := E.slot_start cfg (compute_start_slot_at_epoch cfg (e + 1))
  have hqslot : E.slot_at cfg q = compute_start_slot_at_epoch cfg (e + 1) :=
    E.slot_at_slot_start cfg core.base.whole_seconds hstart hgenTime
  have he12 : e + 1 ≤ e + 2 := Nat.le_succ _
  have hqm : q ≤ m :=
    (E.slot_start_mono cfg
      ((Nat.mul_le_mul_right cfg.slots_per_epoch he12).trans
        hboundary)).trans
      (E.slot_start_le_of_slot_at cfg core.base.whole_seconds hgenTime rfl)
  have hqepoch : compute_epoch_at_slot cfg (E.slot_at cfg q) = e + 1 := by
    rw [hqslot]
    exact Nat.mul_div_cancel _ cfg.slots_per_epoch_pos
  have hknown := (hcan w hw q (E.withinHorizon_mono cfg hqm hm) hqepoch).1
  have hbR : (E.withoutObserver obs).AcceptedBlockAt cfg ext b bb := by
    have hk : b ∈ ((E.withoutObserver obs).store cfg ext w q).block_roots := by
      rwa [withoutObserver_store cfg ext E obs w hwne q]
    refine ⟨_, (E.withoutObserver obs).store_causal cfg ext w q, hk, ?_⟩
    rw [withoutObserver_store cfg ext E obs w hwne q]
    exact (E.store_causal cfg ext w q).acceptedBlockAt_iff_eq cfg ext E
      (localInputs.wellFormed cfg ext core.base.wellFormed) hknown |>.mp hb'
  have hvalues := shared_values hobs core localInputs B hbR.acceptedRoot
  have hcanR : (E.withoutObserver obs).CanonicalThroughoutEpoch cfg ext b (e + 1) := by
    intro v hv k hk he
    have hvE : v ∈ E.honest := (Finset.mem_erase.mp hv).2
    have hvne : v ≠ obs := (Finset.mem_erase.mp hv).1
    simpa only [withoutObserver_store cfg ext E obs v hvne k] using hcan v hvE k hk he
  have hsR : core.semantics.state.PaperA32SupportThroughoutEpoch cfg ext b e := by
    intro v hv k hk he
    have hvE : v ∈ E.honest := (Finset.mem_erase.mp hv).2
    have hvne : v ≠ obs := (Finset.mem_erase.mp hv).1
    have hst := withoutObserver_store cfg ext E obs v hvne k
    obtain ⟨hbk, hbek, hs⟩ := hsupport v hvE k hk he
    refine ⟨hst.symm ▸ hbk, hst.symm ▸ hbek, ?_⟩
    intro tip htip ha
    rw [hst] at htip ha
    have hC : ((exactState hobs core localInputs B).paperA32Inputs cfg ext).C b e =
        (core.semantics.state.paperA32Inputs cfg ext).C b e :=
      hvalues.2.2.2.2 e
    have hVS : ((exactState hobs core localInputs B).paperA32Inputs cfg ext).VSAt cfg
        (E.store cfg ext v k) b e =
        (core.semantics.state.paperA32Inputs cfg ext).VSAt cfg
          ((E.withoutObserver obs).store cfg ext v k) b e := by
      simp only [PaperA32StateView.VSAt, TrustedCausalCarrierFFGState.paperA32Inputs,
        CausalCarrierFFGState.paperA32Inputs, hst]
      split <;> first | exact hvalues.1 | exact hvalues.2.2.1
    obtain ⟨Q⟩ := hs tip htip (by simpa only [hC] using ha)
    have QR := shared_support hobs core localInputs B hvE Q
    rw [hVS, hC] at QR
    exact ⟨QR⟩
  obtain ⟨tip, htip, hbk, ha, he, carrier', hd', hf'⟩ :=
    core.paper_a32.included hbR hbe hcanR hsR w hwR m hm hboundary
  rw [withoutObserver_store cfg ext E obs w hwne m] at htip hbk ha he
  refine ⟨tip, htip, hbk, ha, he, carrier', withoutObserver_descends hd', ?_⟩
  change S.formed carrier' (S.C b e)
  rw [hvalues.2.2.2.2 e]
  exact Or.inl hf'

theorem exactInterpretation_paperA32 (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    (exactInterpretation hobs premises).state.PaperA32Inclusion cfg ext :=
  exactState_paperA32 hobs premises.core premises.local_inputs
    (Classical.choice premises.local_inputs.ffg)

/-- Each successful transition uses its own local or shared delay law. -/
theorem exactInterpretation_finalizationDelay (hobs : obs ∉ E.honest)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    E.TrustedRealizedFinalizationDelay cfg ext (exactInterpretation hobs premises) := by
  intro t
  by_cases ht : t.atPrefix.node = obs
  · exact (Classical.choice premises.local_inputs.ffg).finalization_delay t ht
  · have h := premises.core.finalization_delay (sharedTransition t ht)
    simpa only [sharedTransition, premises.core.anchor_eq] using h

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
