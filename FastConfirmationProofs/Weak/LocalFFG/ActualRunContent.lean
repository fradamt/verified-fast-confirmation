module
public import FastConfirmationInternal.Weak.FFGContentUnion
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunGeometry

/-! The actual-run FFG content combines both accepted domains and their selectors. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- The shared accepted block map, with arbitrary values outside its domain. -/
noncomputable def sharedBlock (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (obs : ValidatorIndex) (r : Root) : BeaconBlock Root := by
  classical
  exact if h : (E.withoutObserver obs).AcceptedRoot cfg ext r then
    Classical.choose h.exists_blockAt else default

theorem sharedBlock_at {r} (h : (E.withoutObserver obs).AcceptedRoot cfg ext r) :
    (E.withoutObserver obs).AcceptedBlockAt cfg ext r (sharedBlock cfg ext E obs r) := by
  classical
  simpa only [sharedBlock, dif_pos h] using Classical.choose_spec h.exists_blockAt

/-- Shared FFG content transported to actual execution ancestry. -/
noncomputable def sharedContent (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    ObserverFFGContent cfg ext E E.genesis_store.justified_checkpoint where
  domain := (E.withoutObserver obs).AcceptedRoot cfg ext
  blocks := sharedBlock cfg ext E obs
  included := core.semantics.state.includedAttestations.Included
  formed := core.semantics.state.formed
  C := core.semantics.state.C
  GJ := core.semantics.state.GJ
  GU := core.semantics.state.GU
  GF := core.semantics.state.GF
  GUF := core.semantics.state.GUF
  checkpoint_epoch := core.semantics.state.checkpoint_epoch
  formed_domain := core.semantics.state.formed_carrier_accepted
  formed_certificate := by
    intro r c hf
    obtain ⟨hc⟩ := (core.semantics.state.formed_evidence hf).certified
    have hc' := shared_justified (fun h => h) hc
    simpa only [core.anchor_eq] using hc'
  formed_on_chain := fun hf =>
    withoutObserver_descends (core.semantics.state.formed_evidence hf).on_chain
  gj_mem := by
    intro r hr
    obtain ⟨carrier, hd, hf⟩ := core.semantics.state.gj_mem r hr
    exact ⟨carrier, withoutObserver_descends hd, hf⟩
  gu_mem := by
    intro r hr
    obtain ⟨carrier, hd, hf⟩ := core.semantics.state.gu_mem r hr
    exact ⟨carrier, withoutObserver_descends hd, hf⟩
  gf_mem := by
    intro r hr
    obtain ⟨carrier, hd, hf⟩ := core.semantics.state.gf_mem r hr
    exact ⟨carrier, withoutObserver_descends hd, hf⟩
  guf_mem := by
    intro r hr
    obtain ⟨carrier, hd, hf⟩ := core.semantics.state.guf_mem r hr
    exact ⟨carrier, withoutObserver_descends hd, hf⟩
  gj_anchor_or_before := by
    intro r hr
    simpa only [core.anchor_eq] using core.semantics.state.gj_anchor_or_before (sharedBlock_at hr)
  gj_max := by
    intro r c hr ⟨carrier, hd, hf⟩ he
    exact core.semantics.state.gj_max (sharedBlock_at hr)
      ⟨carrier, (shared_descends hobs core localInputs hr
        (shared_acceptedRoot (core.semantics.state.formed_carrier_accepted hf)) hd).2, hf⟩ he
  gu_max := by
    intro r c hr ⟨carrier, hd, hf⟩
    exact core.semantics.state.gu_max hr
      ⟨carrier, (shared_descends hobs core localInputs hr
        (shared_acceptedRoot (core.semantics.state.formed_carrier_accepted hf)) hd).2, hf⟩
  au_epoch_le_block := by
    intro r c hr ⟨carrier, hd, hf⟩
    exact core.semantics.state.au_epoch_le_block (sharedBlock_at hr)
      ⟨carrier, (shared_descends hobs core localInputs hr
        (shared_acceptedRoot (core.semantics.state.formed_carrier_accepted hf)) hd).2, hf⟩
  gf_evidence := by
    intro r hr
    rcases core.semantics.state.gf_evidence r hr with ha | hF
    · exact Or.inl (ha.trans core.anchor_eq)
    · right
      obtain ⟨F⟩ := hF
      have hF' := shared_finalized (fun h => h) F
      exact ⟨by simpa only [core.anchor_eq] using hF'⟩
  guf_evidence := by
    intro r hr
    rcases core.semantics.state.guf_evidence r hr with ha | hF
    · exact Or.inl (ha.trans core.anchor_eq)
    · right
      obtain ⟨F⟩ := hF
      have hF' := shared_finalized (fun h => h) F
      exact ⟨by simpa only [core.anchor_eq] using hF'⟩
  gf_epoch_le_gj := core.semantics.state.gf_epoch_le_gj
  guf_epoch_le_gu := core.semantics.state.guf_epoch_le_gu
  gf_epoch_le_guf := core.semantics.state.gf_epoch_le_guf

theorem local_acceptedBlock (B : E.ObserverLocalFFG cfg ext obs) {r}
    (hr : B.state.domain r) : E.AcceptedBlockAt cfg ext r (B.state.blocks r) := by
  obtain ⟨store, hs, hk⟩ := (B.domain_local r).mp hr
  exact ⟨store, hs.causal, hk, (B.block_read hs r hk).symm⟩

/-- Domain closure and deterministic common selectors meet the union conditions. -/
def compatible (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    ObserverFFGContent.Compatible (sharedContent hobs core localInputs) B.state where
  blocks := fun hs hl =>
    (local_block_agree core localInputs B hl (shared_acceptedBlock (sharedBlock_at hs))).symm
  gj := fun hs hl => (selectors_agree core localInputs B hs hl).1.symm
  gu := fun hs hl => (selectors_agree core localInputs B hs hl).2.2.1.symm
  gf := fun hs hl => (selectors_agree core localInputs B hs hl).2.1.symm
  guf := fun hs hl => (selectors_agree core localInputs B hs hl).2.2.2.symm
  left_closed := fun hr hc hd => (shared_descends hobs core localInputs hr
    (local_acceptedBlock B hc).acceptedRoot hd).1
  right_closed := fun hr hc hd => local_descends hobs core localInputs B hr
    (shared_acceptedRoot hc) hd
  left_epoch_mono := fun hr hc hd => Nat.div_le_div_right
    (accepted_slot_le hobs core localInputs (shared_acceptedBlock (sharedBlock_at hr))
      (shared_acceptedBlock (sharedBlock_at hc)) hd)
  right_epoch_mono := fun hr hc hd => Nat.div_le_div_right
    (accepted_slot_le hobs core localInputs (local_acceptedBlock B hr)
      (local_acceptedBlock B hc) hd)

/-- One content object contains shared and observer-only certificates. -/
noncomputable def content (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    ObserverFFGContent cfg ext E E.genesis_store.justified_checkpoint :=
  (sharedContent hobs core localInputs).union B.state (compatible hobs core localInputs B)

/-- Its domain is exactly the actual execution's accepted roots. -/
theorem content_domain (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) (r) :
    (content hobs core localInputs B).domain r ↔ E.AcceptedRoot cfg ext r := by
  change ((E.withoutObserver obs).AcceptedRoot cfg ext r ∨ B.state.domain r) ↔ _
  constructor
  · intro hr
    exact hr.elim shared_acceptedRoot (fun h => (local_acceptedBlock B h).acceptedRoot)
  · intro hr
    exact (accepted_cases hr).imp_right (B.domain_local r).mpr

/-- The chosen block map agrees with every actual accepted carrier. -/
theorem content_block (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r b} (hb : E.AcceptedBlockAt cfg ext r b) :
    (content hobs core localInputs B).blocks r = b := by
  classical
  change (if (E.withoutObserver obs).AcceptedRoot cfg ext r then
    sharedBlock cfg ext E obs r else B.state.blocks r) = b
  split_ifs with hs
  · exact AcceptedBlockAt.unique cfg ext E
      (localInputs.wellFormed cfg ext core.base.wellFormed)
      (shared_acceptedBlock (sharedBlock_at hs)) hb
  · exact local_block_agree core localInputs B
      ((B.domain_local r).mpr ((accepted_cases hb.acceptedRoot).resolve_left hs)) hb

/-- Actual-run state, including all selector maximum and formed-entry laws. -/
noncomputable def state (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    TrustedCausalCarrierFFGState cfg ext E E.genesis_store.justified_checkpoint
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) where
  attestationValidity := ext.is_valid_indexed_attestation
  includedAttestations := relation hobs core localInputs B
  formed := (content hobs core localInputs B).formed
  C := (content hobs core localInputs B).C
  GJ := (content hobs core localInputs B).GJ
  GU := (content hobs core localInputs B).GU
  GF := (content hobs core localInputs B).GF
  GUF := (content hobs core localInputs B).GUF
  checkpoint_epoch := (content hobs core localInputs B).checkpoint_epoch
  formed_carrier_accepted := fun hf => (content_domain hobs core localInputs B _).mp
    ((content hobs core localInputs B).formed_domain hf)
  formed_evidence := fun hf => hf.elim (shared_formed_evidence core B)
    (local_formed_evidence core localInputs B)
  gj_mem := fun r hr => (content hobs core localInputs B).gj_mem r
    ((content_domain hobs core localInputs B r).mpr hr)
  gu_mem := fun r hr => (content hobs core localInputs B).gu_mem r
    ((content_domain hobs core localInputs B r).mpr hr)
  gf_mem := fun r hr => (content hobs core localInputs B).gf_mem r
    ((content_domain hobs core localInputs B r).mpr hr)
  guf_mem := fun r hr => (content hobs core localInputs B).guf_mem r
    ((content_domain hobs core localInputs B r).mpr hr)
  gj_anchor_or_before := by
    intro r b hb
    have h := (content hobs core localInputs B).gj_anchor_or_before r
      ((content_domain hobs core localInputs B r).mpr hb.acceptedRoot)
    rwa [content_block hobs core localInputs B hb] at h
  gj_max := by
    intro r b c hb hc he
    apply (content hobs core localInputs B).gj_max
      ((content_domain hobs core localInputs B r).mpr hb.acceptedRoot) hc
    rwa [content_block hobs core localInputs B hb]
  gu_max := fun hr hc => (content hobs core localInputs B).gu_max
    ((content_domain hobs core localInputs B _).mpr hr) hc
  au_epoch_le_block := by
    intro r b c hb hc
    have h := (content hobs core localInputs B).au_epoch_le_block
      ((content_domain hobs core localInputs B r).mpr hb.acceptedRoot) hc
    rwa [content_block hobs core localInputs B hb] at h
  gf_evidence := fun r hr => (content hobs core localInputs B).gf_evidence r
    ((content_domain hobs core localInputs B r).mpr hr)
  guf_evidence := fun r hr => (content hobs core localInputs B).guf_evidence r
    ((content_domain hobs core localInputs B r).mpr hr)
  gf_epoch_le_gj := fun r hr => (content hobs core localInputs B).gf_epoch_le_gj r
    ((content_domain hobs core localInputs B r).mpr hr)
  guf_epoch_le_gu := fun r hr => (content hobs core localInputs B).guf_epoch_le_gu r
    ((content_domain hobs core localInputs B r).mpr hr)
  gf_epoch_le_guf := fun r hr => (content hobs core localInputs B).gf_epoch_le_guf r
    ((content_domain hobs core localInputs B r).mpr hr)

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
