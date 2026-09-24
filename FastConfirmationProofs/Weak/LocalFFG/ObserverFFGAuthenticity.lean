module
public import FastConfirmationInternal.Weak.ObserverIndependence
public import FastConfirmationProofs.FFG.Certificates.FFGCertificates
public import FastConfirmationProofs.Execution.Delivery.Registry

/-! Authentic signed origins for observer-local FFG body certificates. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}

/-- Local causal stores are causal stores of the actual run. -/
theorem ObserverCausalStore.causal {store : Store Root}
    (h : E.ObserverCausalStore cfg ext obs store) : E.CausalStore cfg ext store := by
  cases h with
  | genesis => exact .genesis
  | scheduledPrefix p _ => exact .scheduledPrefix p

/-- The boundary store belongs to the observer's exact causal domain. -/
theorem store_observerCausal (n : ℕ) :
    E.ObserverCausalStore cfg ext obs (E.store cfg ext obs n) := by
  cases n with
  | zero => exact .genesis
  | succ n =>
    let p : E.ScheduledEventPrefix := ⟨obs, n, (E.schedule obs (n + 1)).length, le_rfl⟩
    have h := ObserverCausalStore.scheduledPrefix (cfg := cfg) (ext := ext) p rfl
    simpa only [ScheduledEventPrefix.store, p, List.take_length, store] using h


/-- Generic received-attestation authenticity for a signer in H. The receiver
split uses only the original local input law at the observer. -/
theorem restricted_no_forgery
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs)
    (w : ValidatorIndex) (n : ℕ) (a : Attestation Root) (fb : Bool)
    (ha : Event.attestation a fb ∈ E.schedule w n)
    {i : ValidatorIndex} (hi : i ∈ E.honest.erase obs) (hia : i ∈ a.attesting_indices) :
    ∃ m a', m ≤ n ∧ (E.withoutObserver obs).vote i a.data.slot = some (m, a') ∧
      a.data = a'.data := by
  by_cases hw : w = obs
  · subst w
    exact localInputs.no_forgery n a fb ha i (Finset.mem_erase.mp hi).2 hia
  · exact core.base.honest_behavior.no_forgery w n a fb
      (by simpa only [withoutObserver, if_neg hw] using ha) i hi hia

namespace ObserverIncludedEvidence
/-- Prepared-state validity reduces to a keyed state of the observer. -/
theorem base_valid {r body a}
    (ev : ObserverIncludedEvidence cfg ext E obs r body a)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs) :
    ext.is_valid_indexed_attestation
      (ev.validation_store.block_states a.data.target.root) a = true := by
  have hk : E.ObserverValidationState cfg ext obs
      (ev.validation_store.block_states a.data.target.root) :=
    ⟨ev.validation_store, ev.validation_local, Or.inl ⟨_, ev.target_known, rfl⟩⟩
  have hv := ev.valid
  dsimp only at hv
  split_ifs at hv with hs
  · rw [localInputs.process_slots_validity _ _ a hk hs] at hv
    exact hv
  · exact hv

/-- Honest names in a local body certificate have signed origins. No gossip
or attestation event at any receiver is needed. -/
theorem honest_signed {r body a}
    (ev : ObserverIncludedEvidence cfg ext E obs r body a)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs)
    {i : ValidatorIndex} (hi : i ∈ E.honest.erase obs) (hia : i ∈ a.attesting_indices) :
    ∃ m a', (E.withoutObserver obs).vote i a.data.slot = some (m, a') ∧
      a.data = a'.data := by
  exact localInputs.validity.valid_attestation_honest _ a
    ⟨ev.validation_store, ev.validation_local, Or.inl ⟨_, ev.target_known, rfl⟩⟩
    (ev.base_valid localInputs) i (Finset.mem_erase.mp hi).2 hia

/-- Committee membership is derived from the same local validity law. -/
theorem committee {r body a}
    (ev : ObserverIncludedEvidence cfg ext E obs r body a)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs) :
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot :=
  localInputs.validity.valid_attestation_committee _ a
    ⟨ev.validation_store, ev.validation_local, Or.inl ⟨_, ev.target_known, rfl⟩⟩
    (ev.base_valid localInputs)
end ObserverIncludedEvidence

private theorem span_weight_le_total
    (base : SelectedMarginAssumptions cfg ext E)
    {lo hi : Slot} (hhi : E.SlotWithinHorizon cfg hi) :
    E.weight (E.span_committee lo hi) ≤ E.total_active cfg := by
  let U := (get_active_validator_indices E.anchor_state
    (get_current_epoch cfg E.anchor_state)).toFinset
  have hanchorSlot := E.anchor_state_slot_le cfg base.whole_seconds
    (by obtain ⟨st, b, hg, _⟩ := base.genesis; exact ⟨st, b, hg⟩)
  have hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hanchorSlot)
      base.static_validators.genesis_within_horizon.2.2
  have hsub : E.span_committee lo hi ⊆ U := by
    intro i hiSpan
    simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiSpan
    obtain ⟨s, hs, hiCommittee⟩ := hiSpan
    have hsH : E.SlotWithinHorizon cfg s :=
      ⟨le_trans hs.2 hhi.1, lt_of_le_of_lt (Nat.div_le_div_right hs.2) hhi.2⟩
    have hact := base.externals_coherence.committee_members_active i s hsH hiCommittee
    rw [base.static_validators.activity_constant i _ _ hsH.2 hanchorH] at hact
    have hir : i < E.registry.length := by
      by_contra hge
      rw [not_lt] at hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hact
      simp only [is_active_validator, decide_eq_true_eq] at hact
      exact Nat.not_lt_zero _ hact.2
    simpa only [U, List.mem_toFinset, get_active_validator_indices,
      List.mem_filter, List.mem_range, Execution.registry] using And.intro hir hact
  have hm : E.weight (E.span_committee lo hi) ≤ E.weight U := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  apply hm.trans
  simp only [U, Execution.weight, Execution.weight_of, Execution.total_active,
    get_total_active_balance, get_total_balance, Execution.registry]
  exact Nat.le_max_right _ _

namespace ObserverLocalFFG
/-- A content quorum has a signer in the restricted honest set. The carrier
need not be accepted anywhere in the restricted execution. -/
theorem link_honest_signer
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E B.state.included carrier source target) :
    ∃ i ∈ L.signers, i ∈ E.honest.erase obs := by
  let R := E.withoutObserver obs
  have hsub : L.signers ⊆ R.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := L.signers_in_epoch
  obtain ⟨i, hi, _, hh⟩ := two_quorums_intersect_honest R (R.total_active_pos cfg)
    hsub hsub (span_weight_le_total core.base L.target_span_within.2)
    (core.base.byzantine_bound.span_fraction _ _ L.target_span_within.1 L.target_span_within.2)
    cfg.confirmation_byzantine_threshold_le L.supermajority L.supermajority
  exact ⟨i, hi, hh⟩

/-- A local content quorum supplies an authentic non-observer vote and the
shared honest-vote deadline. There is no observer relay or receipt premise. -/
theorem link_signed_origin
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs)
    {carrier source target}
    (L : IncludedSupermajorityLink cfg E B.state.included carrier source target) :
    ∃ i ∈ E.honest.erase obs, ∃ containing a m a',
      E.RootDescends carrier containing ∧ B.state.included containing a ∧
      i ∈ a.attesting_indices ∧
      a.data.source = source ∧ a.data.target = target ∧
      (E.withoutObserver obs).vote i a.data.slot = some (m, a') ∧ a.data = a'.data ∧
      E.slot_start cfg a.data.slot ≤ m ∧
      m ≤ E.slot_start cfg a.data.slot + get_attestation_due_ms cfg / 1000 := by
  obtain ⟨i, hi, hh⟩ := B.link_honest_signer core L
  obtain ⟨a, ⟨containing, hdChain, ha⟩, hia, hs, ht⟩ := L.signer_attestation i hi
  obtain ⟨m, a', hv, hd⟩ := (B.included_evidence ha).honest_signed localInputs hh hia
  exact ⟨i, hh, containing, a, m, a', hdChain, ha, hia, hs, ht, hv, hd,
    core.base.honest_behavior.vote_deadline i hh _ _ _ hv⟩

/-- Non-anchor formed checkpoints yield a real restricted honest vote.
Certificate existence is the content refinement premise; this origin is derived. -/
theorem formed_signed_origin
    (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs)
    {r c} (hf : B.state.formed r c) (hne : c ≠ E.genesis_store.justified_checkpoint) :
    ∃ i ∈ E.honest.erase obs, ∃ s m a,
      (E.withoutObserver obs).vote i s = some (m, a) ∧ a.data.target = c := by
  cases hc : B.state.formed_certificate hf with
  | anchor => exact False.elim (hne rfl)
  | link prev L =>
    obtain ⟨i, hi, _, a, m, a', _, _, _, _, ht, hv, hd, _⟩ :=
      B.link_signed_origin core localInputs L
    exact ⟨i, hi, a.data.slot, m, a', hv, hd ▸ ht⟩
/-- A local content link and a shared scheduled link cannot certify different
roots at the same epoch. Only honest signed data is compared; no aggregate
body is required to occur as a received attestation in the shared run. -/
theorem link_root_eq_shared (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverInputAuthenticity cfg ext obs)
    {carrier s c s' c'}
    (L : IncludedSupermajorityLink cfg E B.state.included carrier s c)
    (L' : SupermajorityLink cfg (E.withoutObserver obs) s' c')
    (hepoch : c.epoch = c'.epoch) : c.root = c'.root := by
  let R := E.withoutObserver obs
  let U := R.span_committee (c.epoch * cfg.slots_per_epoch)
    (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  have hsub : L'.signers ⊆ U := by simpa only [U, hepoch] using L'.signers_in_epoch
  obtain ⟨i, hi, hi', hh⟩ := two_quorums_intersect_honest R (R.total_active_pos cfg)
    L.signers_in_epoch hsub (span_weight_le_total core.base L.target_span_within.2)
    (core.base.byzantine_bound.span_fraction _ _ L.target_span_within.1 L.target_span_within.2)
    cfg.confirmation_byzantine_threshold_le L.supermajority L'.supermajority
  obtain ⟨a, ⟨_, _, hin⟩, hia, _, hat⟩ := L.signer_attestation i hi
  obtain ⟨k, vote, hvote, hdata⟩ := (B.included_evidence hin).honest_signed localInputs hh hia
  obtain ⟨w', n', a', fb', hsched', hia', _, hat'⟩ := L'.signer_attestation i hi'
  obtain ⟨k', vote', _, hvote', hdata'⟩ :=
    core.base.honest_behavior.no_forgery w' n' a' fb' hsched' i hh hia'
  have ht : vote.data.target = c := by rw [← hdata]; exact hat
  have ht' : vote'.data.target = c' := by rw [← hdata']; exact hat'
  by_contra hroot
  have hne : vote.data ≠ vote'.data := by
    intro he
    have htarget := congrArg AttestationData.target he
    rw [ht, ht'] at htarget
    exact hroot (congrArg Checkpoint.root htarget)
  have hte : vote.data.target.epoch = vote'.data.target.epoch := by rw [ht, ht', hepoch]
  have hslash : is_slashable_attestation_data vote.data vote'.data = true := by
    simp [is_slashable_attestation_data, hne, hte]
  have hnot := core.base.honest_behavior.not_slashable i hh
    a.data.slot a'.data.slot k k' vote vote' hvote hvote'
  rw [hslash] at hnot
  contradiction

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
