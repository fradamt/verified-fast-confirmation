module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunFFG

/-! Exact-endpoint inclusion preserves required certificates and controls mixed links. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- Keep body attestations whose endpoints are exact at their containing block.
No arrival or receipt condition is added. -/
def exactIncluded (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    (r : Root) (a : Attestation Root) : Prop :=
  included core B r a ∧ E.genesis_store.justified_checkpoint.epoch ≤ a.data.source.epoch ∧
    a.data.source = (state hobs core localInputs B).C r a.data.source.epoch ∧
    a.data.target = (state hobs core localInputs B).C r a.data.target.epoch

noncomputable def exactRelation (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    E.TrustedCarrierAttestationRelation cfg ext ext.is_valid_indexed_attestation
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) where
  Included := exactIncluded hobs core localInputs B
  evidence := fun h => (relation hobs core localInputs B).evidence h.1

private theorem attestation_bound (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r a source target} (ha : included core B r a)
    (_hs : a.data.source = source) (ht : a.data.target = target)
    (hlt : source.epoch < target.epoch) :
    ∃ b, E.AcceptedBlockAt cfg ext r b ∧
      compute_start_slot_at_epoch cfg source.epoch ≤ b.slot ∧
      compute_start_slot_at_epoch cfg target.epoch ≤ b.slot := by
  let ev := (relation hobs core localInputs B).evidence ha
  have htarget : compute_start_slot_at_epoch cfg target.epoch ≤ ev.carrier_message.slot := by
    rw [← ht, ev.target_epoch]
    exact (Nat.div_mul_le_self _ _).trans ev.slot_before_carrier.le
  exact ⟨ev.carrier_message, ev.carrier_accepted,
    (Nat.mul_le_mul_right cfg.slots_per_epoch hlt.le).trans htarget, htarget⟩

/-- Exactness at a certificate tip propagates back to each containing block. -/
theorem exactIncluded_of_tip (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip r a source target} (hr : E.AcceptedRoot cfg ext tip)
    (hd : E.RootDescends tip r) (ha : included core B r a)
    (hs : a.data.source = source) (ht : a.data.target = target)
    (hlt : source.epoch < target.epoch)
    (hanchor : E.genesis_store.justified_checkpoint.epoch ≤ source.epoch)
    (hex : source = (state hobs core localInputs B).C tip source.epoch ∧
      target = (state hobs core localInputs B).C tip target.epoch) :
    exactIncluded hobs core localInputs B r a := by
  obtain ⟨b, hb, hbs, hbt⟩ := attestation_bound hobs core localInputs B ha hs ht hlt
  refine ⟨ha, hs ▸ hanchor, ?_, ?_⟩
  · rw [hs]
    exact hex.1.trans (checkpoint_descends hobs core localInputs B hr hb hd hanchor hbs)
  · rw [ht]
    exact hex.2.trans (checkpoint_descends hobs core localInputs B hr hb hd
      (hanchor.trans hlt.le) hbt)

/-- A complete raw link with exact endpoints loses no signer under the filter. -/
def normalize_link (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip source target} (hr : E.AcceptedRoot cfg ext tip)
    (L : IncludedSupermajorityLink cfg E (included core B) tip source target)
    (hanchor : E.genesis_store.justified_checkpoint.epoch ≤ source.epoch)
    (hex : source = (state hobs core localInputs B).C tip source.epoch ∧
      target = (state hobs core localInputs B).C tip target.epoch) :
    IncludedSupermajorityLink cfg E (exactIncluded hobs core localInputs B) tip source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, ⟨r, hd, ha⟩, hia, hs, ht⟩ := L.signer_attestation i hi
    exact ⟨a, ⟨r, hd, exactIncluded_of_tip hobs core localInputs B hr hd ha hs ht
      L.source_before_target hanchor hex⟩, hia, hs, ht⟩
  supermajority := L.supermajority

/-- Every contributing shared link survives normalization. -/
def normalize_shared_link (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip source target} (hr : (E.withoutObserver obs).AcceptedRoot cfg ext tip)
    (L : IncludedSupermajorityLink cfg (E.withoutObserver obs)
      core.semantics.state.includedAttestations.Included tip source target)
    (hc : IncludedCertifiedJustified cfg (E.withoutObserver obs)
      core.semantics.state.includedAttestations.Included core.semantics.anchor tip source) :
    IncludedSupermajorityLink cfg E (exactIncluded hobs core localInputs B) tip source target := by
  have hex := core.exact_link_validity.endpoints_on_carrier L hc trivial
  have hepoch := IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hc
  have hvalues := (shared_values hobs core localInputs B hr).2.2.2.2
  apply normalize_link hobs core localInputs B (shared_acceptedRoot hr)
    (shared_link Or.inl L)
  · simpa only [core.anchor_eq] using hepoch
  · exact ⟨hex.1.trans (hvalues source.epoch).symm, hex.2.trans (hvalues target.epoch).symm⟩

/-- Every contributing local link survives normalization. -/
def normalize_local_link (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip source target} (hr : B.state.domain tip)
    (L : IncludedSupermajorityLink cfg E B.state.included tip source target)
    (hc : IncludedCertifiedJustified cfg E B.state.included
      E.genesis_store.justified_checkpoint tip source) :
    IncludedSupermajorityLink cfg E (exactIncluded hobs core localInputs B) tip source target := by
  have hex := B.exact_link_endpoints hr L hc
  have hvalues := (local_values hobs core localInputs B hr).2.2.2.2
  exact normalize_link hobs core localInputs B (local_acceptedBlock B hr).acceptedRoot
    (map_link Or.inr L) (IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) hc)
    ⟨hex.1.trans (hvalues source.epoch).symm, hex.2.trans (hvalues target.epoch).symm⟩

/-- Every shared justification certificate survives with its full signer sets. -/
theorem normalize_shared_certificate (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip c} (hr : (E.withoutObserver obs).AcceptedRoot cfg ext tip)
    (hc : IncludedCertifiedJustified cfg (E.withoutObserver obs)
      core.semantics.state.includedAttestations.Included core.semantics.anchor tip c) :
    IncludedCertifiedJustified cfg E (exactIncluded hobs core localInputs B)
      core.semantics.anchor tip c := by
  induction hc with
  | anchor => exact .anchor
  | link prev L ih => exact .link ih (normalize_shared_link hobs core localInputs B hr L prev)

/-- Every local justification certificate survives with its full signer sets. -/
theorem normalize_local_certificate (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip c} (hr : B.state.domain tip)
    (hc : IncludedCertifiedJustified cfg E B.state.included
      E.genesis_store.justified_checkpoint tip c) :
    IncludedCertifiedJustified cfg E (exactIncluded hobs core localInputs B)
      E.genesis_store.justified_checkpoint tip c := by
  induction hc with
  | anchor => exact .anchor
  | link prev L ih => exact .link ih (normalize_local_link hobs core localInputs B hr L prev)

/-- The filter preserves both justification and the finalizing link. -/
def normalize_shared_finalized (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip c} (hr : (E.withoutObserver obs).AcceptedRoot cfg ext tip)
    (F : IncludedCertifiedFinalized cfg (E.withoutObserver obs)
      core.semantics.state.includedAttestations.Included core.semantics.anchor tip c) :
    IncludedCertifiedFinalized cfg E (exactIncluded hobs core localInputs B)
      core.semantics.anchor tip c where
  justified := normalize_shared_certificate hobs core localInputs B hr F.justified
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := normalize_shared_link hobs core localInputs B hr F.finalizing_link F.justified

/-- Local finalized certificates also survive the filter. -/
def normalize_local_finalized (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip c} (hr : B.state.domain tip)
    (F : IncludedCertifiedFinalized cfg E B.state.included
      E.genesis_store.justified_checkpoint tip c) :
    IncludedCertifiedFinalized cfg E (exactIncluded hobs core localInputs B)
      E.genesis_store.justified_checkpoint tip c where
  justified := normalize_local_certificate hobs core localInputs B hr F.justified
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := normalize_local_link hobs core localInputs B hr F.finalizing_link F.justified

/-- Mixed links also have exact endpoints: each retained attestation is exact
at its containing block, and the target boundary precedes that block. -/
theorem mixed_link_endpoints (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {tip source target} (hr : E.AcceptedRoot cfg ext tip)
    (L : IncludedSupermajorityLink cfg E (exactIncluded hobs core localInputs B)
      tip source target) :
    source = (state hobs core localInputs B).C tip source.epoch ∧
      target = (state hobs core localInputs B).C tip target.epoch := by
  have hnonempty : L.signers.Nonempty := by
    by_contra hn
    have he : L.signers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hq := L.supermajority
    have hpos := E.total_active_pos cfg
    simp only [he, Execution.weight, Execution.weight_of, Finset.sum_empty, Nat.mul_zero] at hq
    exact (Nat.not_le_of_lt (Nat.mul_pos (by decide) hpos)) hq
  obtain ⟨i, hi⟩ := hnonempty
  obtain ⟨a, ⟨r, hd, ha⟩, _, hs, ht⟩ := L.signer_attestation i hi
  obtain ⟨b, hb, hbs, hbt⟩ := attestation_bound hobs core localInputs B ha.1 hs ht
    L.source_before_target
  have hanchor : E.genesis_store.justified_checkpoint.epoch ≤ source.epoch := hs ▸ ha.2.1
  have hex := ha.2.2
  rw [hs, ht] at hex
  exact ⟨hex.1.trans (checkpoint_descends hobs core localInputs B hr hb hd hanchor hbs).symm,
    hex.2.trans (checkpoint_descends hobs core localInputs B hr hb hd
      (hanchor.trans L.source_before_target.le) hbt).symm⟩

/-- Exactness for every mixed contributing link on the actual accepted domain. -/
def exactLinkValidity (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    ExactIncludedLinkValidity cfg E (exactIncluded hobs core localInputs B)
      E.genesis_store.justified_checkpoint (state hobs core localInputs B).C
      (E.AcceptedRoot cfg ext) (E.AcceptedRoot cfg ext) where
  carrier_accepted := fun _ _ hr => hr
  endpoints_on_carrier := fun L _ hr => mixed_link_endpoints hobs core localInputs B hr L

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
