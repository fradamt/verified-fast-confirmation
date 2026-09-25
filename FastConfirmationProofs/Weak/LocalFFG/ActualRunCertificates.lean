module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunTransport

/-! Actual-run formed certificates retain genuine signed votes and body evidence. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- Inclusion enlargement preserves a complete link, including each signer. -/
def map_link {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {r source target}
    (L : IncludedSupermajorityLink cfg E I r source target) :
    IncludedSupermajorityLink cfg E J r source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, ⟨carrier, hd, ha⟩, hs⟩ := L.signer_attestation i hi
    exact ⟨a, ⟨carrier, hd, h ha⟩, hs⟩
  supermajority := L.supermajority

theorem map_justified {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {anchor r c}
    (hc : IncludedCertifiedJustified cfg E I anchor r c) :
    IncludedCertifiedJustified cfg E J anchor r c := by
  induction hc with
  | anchor => exact .anchor
  | link _ L ih => exact .link ih (map_link h L)

def map_finalized {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {anchor r c}
    (F : IncludedCertifiedFinalized cfg E I anchor r c) :
    IncludedCertifiedFinalized cfg E J anchor r c where
  justified := map_justified h F.justified
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := map_link h F.finalizing_link

/-- Shared links embed without a receipt at the observer. -/
def shared_link {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {r source target}
    (L : IncludedSupermajorityLink cfg (E.withoutObserver obs) I r source target) :
    IncludedSupermajorityLink cfg E J r source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := withoutObserver_descends L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, ⟨carrier, hd, ha⟩, hs⟩ := L.signer_attestation i hi
    exact ⟨a, ⟨carrier, withoutObserver_descends hd, h ha⟩, hs⟩
  supermajority := L.supermajority

theorem shared_justified {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {anchor r c}
    (hc : IncludedCertifiedJustified cfg (E.withoutObserver obs) I anchor r c) :
    IncludedCertifiedJustified cfg E J anchor r c := by
  induction hc with
  | anchor => exact .anchor
  | link _ L ih => exact .link ih (shared_link h L)

def shared_finalized {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {anchor r c}
    (F : IncludedCertifiedFinalized cfg (E.withoutObserver obs) I anchor r c) :
    IncludedCertifiedFinalized cfg E J anchor r c where
  justified := shared_justified h F.justified
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := shared_link h F.finalizing_link

/-- Shared formed entries retain the exact body and individual signed vote. -/
theorem shared_formed_evidence
    (core : E.WeakObserverRestrictedCore cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r c} (hc : core.semantics.state.formed r c) :
    IncludedVoteCheckpointCertificate cfg ext E (included core B)
      E.genesis_store.justified_checkpoint r c := by
  have ev := core.semantics.state.formed_evidence hc
  constructor
  · obtain ⟨hj⟩ := ev.certified
    have hj' := shared_justified (J := included core B) Or.inl hj
    exact ⟨by simpa only [core.anchor_eq] using hj'⟩
  · exact withoutObserver_descends ev.on_chain
  · rcases ev.causal with ha | ⟨b, hb, i, hi, s, k, a, hslot, hsH, hv, has, hat, body,
        ⟨carrier, hd, hin⟩, hib, heq⟩
    · exact Or.inl (ha.trans core.anchor_eq)
    · exact Or.inr ⟨b, shared_acceptedBlock hb, i, (Finset.mem_erase.mp hi).2,
        s, k, a, hslot, hsH, hv, has, hat, body,
        ⟨carrier, withoutObserver_descends hd, Or.inl hin⟩, hib, heq⟩

/-- A prefix extends to its node's completed second. -/
theorem prefix_le_boundary (p : E.ScheduledEventPrefix) :
    StoreLE (p.store cfg ext) (E.store cfg ext p.node (p.previousSecond + 1)) := by
  let events := E.schedule p.node (p.previousSecond + 1)
  let ticked := on_tick cfg (E.store cfg ext p.node p.previousSecond)
    (E.time_at (p.previousSecond + 1))
  change StoreLE ((events.take p.processedCount).foldl _ ticked) (events.foldl _ ticked)
  conv_rhs => rw [← List.take_append_drop p.processedCount events]
  rw [List.foldl_append]
  exact foldl_storeLE cfg ext _ _

/-- Local accepted roots have a completed observer-store witness. -/
theorem local_known {r} (h : E.ObserverAcceptedRoot cfg ext obs r) :
    ∃ n, r ∈ (E.store cfg ext obs n).block_roots := by
  obtain ⟨store, hs, hr⟩ := h
  cases hs with
  | genesis => exact ⟨0, hr⟩
  | scheduledPrefix p hp =>
    exact ⟨p.previousSecond + 1, hp ▸ (prefix_le_boundary p).1 hr⟩

/-- Local formation supplies the same causal vote certificate as shared formation. -/
theorem local_formed_evidence
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r c} (hc : B.state.formed r c) :
    IncludedVoteCheckpointCertificate cfg ext E (included core B)
      E.genesis_store.justified_checkpoint r c := by
  refine ⟨⟨map_justified Or.inr (B.state.formed_certificate hc)⟩,
    B.state.formed_on_chain hc, ?_⟩
  by_cases heq : c = E.genesis_store.justified_checkpoint
  · exact Or.inl heq
  right
  obtain ⟨n, hr⟩ := local_known (B.formed_local hc)
  have cert := B.state.formed_certificate hc
  cases cert with
  | anchor => exact False.elim (heq rfl)
  | link prev L =>
    obtain ⟨i, hi, carrier, a, k, own, hd, hin, hia, _, ht, hv, hdata, _⟩ :=
      B.link_signed_origin core localInputs.toObserverInputAuthenticity L
    have hev := B.included_evidence hin
    have hslot := B.included_slot_before_tip core localInputs n hr ⟨carrier, hd, hin⟩
    rw [B.block_read (store_observerCausal n) r hr] at hslot
    have hownslot : own.data.slot = a.data.slot :=
      (congrArg AttestationData.slot hdata).symm
    exact ⟨_, ⟨_, E.store_causal cfg ext obs n, hr, rfl⟩, i,
      (Finset.mem_erase.mp hi).2, a.data.slot, k, own, hslot,
      hev.slot_within_horizon, hv, hownslot, hdata ▸ ht, a,
      ⟨carrier, hd, Or.inr hin⟩, hia, hdata⟩

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
