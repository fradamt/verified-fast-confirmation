module
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFinalizedSafety

/-! Actual-run FFG evidence preserves the shared and observer input domains. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}

namespace ActualRunFFG

/-- A prefix at another node is unchanged by observer erasure. -/
def sharedPrefix (p : E.ScheduledEventPrefix) (h : p.node ≠ obs) :
    (E.withoutObserver obs).ScheduledEventPrefix where
  node := p.node
  previousSecond := p.previousSecond
  processedCount := p.processedCount
  count_le := by simpa only [withoutObserver, if_neg h] using p.count_le

theorem sharedPrefix_store (p : E.ScheduledEventPrefix) (h : p.node ≠ obs) :
    (sharedPrefix p h).store cfg ext = p.store cfg ext := by
  simp only [ScheduledEventPrefix.store, sharedPrefix]
  rw [withoutObserver_store cfg ext E obs p.node h p.previousSecond]
  simp only [withoutObserver, if_neg h, time_at]

/-- The shared honest validation domain embeds in the actual run. -/
theorem shared_honestStore {store : Store Root}
    (hs : (E.withoutObserver obs).HonestCausalStore cfg ext store) :
    E.HonestCausalStore cfg ext store := by
  cases hs with
  | genesis hh hn =>
    exact .genesis (hh.mono (Finset.erase_subset _ _)) hn
  | scheduledPrefix p hh hn =>
    have hne : p.node ≠ obs := (Finset.mem_erase.mp hh).1
    let q : E.ScheduledEventPrefix := {
      node := p.node
      previousSecond := p.previousSecond
      processedCount := p.processedCount
      count_le := by simpa only [withoutObserver, if_neg hne] using p.count_le }
    have heq : q.store cfg ext = p.store cfg ext := by
      simp only [ScheduledEventPrefix.store, q]
      rw [withoutObserver_store cfg ext E obs p.node hne p.previousSecond]
      simp only [withoutObserver, if_neg hne, time_at]
    rw [← heq]
    exact .scheduledPrefix q (Finset.mem_erase.mp hh).2 hn

theorem erased_blocks (n : ℕ) :
    ((E.withoutObserver obs).store cfg ext obs n).block_roots =
      E.genesis_store.block_roots ∧
    ((E.withoutObserver obs).store cfg ext obs n).blocks = E.genesis_store.blocks := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [store, withoutObserver, if_pos rfl, List.foldl_nil]
    exact ⟨(on_tick_sameBlocks cfg _ _).1.symm.trans ih.1,
      (on_tick_sameBlocks cfg _ _).2.1.symm.trans ih.2⟩

/-- Shared accepted carriers remain accepted, including roots at the erased node. -/
theorem shared_acceptedBlock {r b}
    (ha : (E.withoutObserver obs).AcceptedBlockAt cfg ext r b) :
    E.AcceptedBlockAt cfg ext r b := by
  obtain ⟨store, hs, hr, hb⟩ := ha
  cases hs with
  | genesis => exact ⟨_, .genesis, hr, hb⟩
  | scheduledPrefix p =>
    by_cases hp : p.node = obs
    · have heq : (p.store cfg ext).block_roots = E.genesis_store.block_roots ∧
          (p.store cfg ext).blocks = E.genesis_store.blocks := by
        simp only [ScheduledEventPrefix.store, hp, withoutObserver, ↓reduceIte,
          List.take_nil, List.foldl_nil]
        exact ⟨(on_tick_sameBlocks cfg _ _).1.symm.trans (erased_blocks p.previousSecond).1,
          (on_tick_sameBlocks cfg _ _).2.1.symm.trans (erased_blocks p.previousSecond).2⟩
      exact ⟨_, .genesis, heq.1 ▸ hr, by rw [← heq.2]; exact hb⟩
    · let q : E.ScheduledEventPrefix := {
        node := p.node
        previousSecond := p.previousSecond
        processedCount := p.processedCount
        count_le := by simpa only [withoutObserver, if_neg hp] using p.count_le }
      have heq : q.store cfg ext = p.store cfg ext := by
        simp only [ScheduledEventPrefix.store, q]
        rw [withoutObserver_store cfg ext E obs p.node hp p.previousSecond]
        simp only [withoutObserver, if_neg hp, time_at]
      exact ⟨q.store cfg ext, .scheduledPrefix q, heq.symm ▸ hr,
        by rw [heq]; exact hb⟩

theorem shared_acceptedRoot {r}
    (ha : (E.withoutObserver obs).AcceptedRoot cfg ext r) : E.AcceptedRoot cfg ext r := by
  obtain ⟨b, hb⟩ := ha.exists_blockAt
  exact (shared_acceptedBlock hb).acceptedRoot

/-- Every actual accepted root is covered by the shared or local domain. -/
theorem accepted_cases {r} (ha : E.AcceptedRoot cfg ext r) :
    (E.withoutObserver obs).AcceptedRoot cfg ext r ∨ E.ObserverAcceptedRoot cfg ext obs r := by
  obtain ⟨store, hs, hr⟩ := ha
  cases hs with
  | genesis => exact Or.inl ⟨_, .genesis, hr⟩
  | scheduledPrefix p =>
    by_cases hp : p.node = obs
    · exact Or.inr ⟨_, .scheduledPrefix p hp, hr⟩
    · exact Or.inl ⟨_, .scheduledPrefix (sharedPrefix p hp),
        (sharedPrefix_store p hp).symm ▸ hr⟩

/-- Shared body evidence retains its exact prepared state in the actual run. -/
def shared_evidence {validity r a}
    (ev : CausalCarrierAttestationEvidence cfg ext (E.withoutObserver obs) validity r a) :
    TrustedCarrierAttestationEvidence cfg ext E validity
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) r a where
  carrier_message := ev.carrier_message
  carrier_at := by
    rcases ev.carrier_at with hg | ⟨w, n, b, hb, hr, hm⟩
    · exact Or.inl hg
    · exact Or.inr ⟨w, n, b, withoutObserver_event hb, hr, hm⟩
  in_carrier_body := ev.in_carrier_body
  received_from_block := by
    obtain ⟨w, n, hn⟩ := ev.received_from_block
    exact ⟨w, n, withoutObserver_event hn⟩
  validation_state := ev.validation_state
  validation_registry := ev.validation_registry
  valid := ev.valid
  slot_within_horizon := ev.slot_within_horizon
  slot_before_carrier := ev.slot_before_carrier
  target_epoch := ev.target_epoch
  head_descends_target := withoutObserver_descends ev.head_descends_target
  target_on_chain := withoutObserver_descends ev.target_on_chain
  target_descends_source := withoutObserver_descends ev.target_descends_source
  attesters_in_committee := ev.attesters_in_committee
  attesters_in_registry := ev.attesters_in_registry
  carrier_accepted := shared_acceptedBlock ev.carrier_accepted
  validation_store := ev.validation_store
  validation_store_trusted := Or.inl (shared_honestStore ev.validation_store_honest)
  validation_target_known := ev.validation_target_known
  validation_state_from_target := ev.validation_state_from_target

/-- The inclusion union keeps the body evidence from either input. -/
def included (core : E.WeakObserverRestrictedCore cfg ext obs)
    (B : E.ObserverLocalFFG cfg ext obs) (r : Root) (a : Attestation Root) : Prop :=
  core.semantics.state.includedAttestations.Included r a ∨ B.state.included r a

/-- The full union has the required actual-run validation predicate. -/
noncomputable def relation (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs) :
    E.TrustedCarrierAttestationRelation cfg ext ext.is_valid_indexed_attestation
      (E.trustedObserverOrHonestStore (cfg := cfg) (ext := ext) obs) where
  Included := included core B
  evidence := fun h => Classical.choice (by
    rcases h with h | h
    · have ev := shared_evidence (core.semantics.state.includedAttestations.evidence h)
      rw [core.semantics.coherence.attestation_validity] at ev
      exact ⟨ev⟩
    · exact ⟨(B.trustedIncludedRelationActual hobs core localInputs).evidence h⟩)

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
