module
public import FastConfirmationProofs.FFG.State.FFGCheckpointEpochOrder
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable {trusted : Store Root → Prop}

namespace CheckpointEpochOrder

theorem trustedAcceptedBlockTransition
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : CheckpointEpochOrder (t.atPrefix.store cfg ext)) :
    CheckpointEpochOrder t.postStore := by
  rcases Execution.AcceptedBlockTransition.on_block_inserted_state
      cfg ext t.accepted with
    (⟨_hknown, hpost⟩ | ⟨post, hst, hinserted⟩)
  · rw [hpost]
    exact h
  · have hstatePair : post.finalized_checkpoint.epoch ≤
        post.current_justified_checkpoint.epoch := by
      rw [← hinserted, hcoh.transition_gf t, hcoh.transition_gj t]
      exact S.gf_epoch_le_gj t.signedBlock.root t.root_accepted
    have hpulledPair :
        (ext.process_justification_and_finalization
          post).finalized_checkpoint.epoch ≤
        (ext.process_justification_and_finalization
          post).current_justified_checkpoint.epoch := by
      rw [← hinserted, hcoh.transition_guf t, hcoh.transition_gu t]
      exact S.guf_epoch_le_gu t.signedBlock.root t.root_accepted
    exact on_block_of_ordered_transition cfg ext hst hstatePair hpulledPair
      h t.accepted


end CheckpointEpochOrder

namespace Execution
variable {E : Execution Root}

private theorem trustedAcceptedCheckpointEpochOrder_take
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : CheckpointEpochOrder
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      CheckpointEpochOrder
        (((E.schedule w (n + 1)).take k).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) := by
  intro k hk
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      have hklt : k < (E.schedule w (n + 1)).length := by omega
      have hkle : k ≤ (E.schedule w (n + 1)).length := Nat.le_of_lt hklt
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := k
          count_le := hkle }
      have hp : CheckpointEpochOrder (p.store cfg ext) := ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change CheckpointEpochOrder ((p.successor hklt).store cfg ext)
      rw [hsucc]
      cases heq : apply_event cfg ext (p.store cfg ext) nextEvent with
      | none => simpa using hp
      | some store' =>
        simp only [Option.getD_some]
        cases hevent : nextEvent with
        | block sb =>
            let t : E.AcceptedBlockTransition cfg ext :=
              { atPrefix := p
                signedBlock := sb
                event_at := by
                  have hget :
                      (E.schedule w (n + 1))[k]? = some nextEvent := by
                    simp [nextEvent, List.getElem?_eq_getElem hklt]
                  rw [hget, hevent]
                postStore := store'
                accepted := by
                  simpa [apply_event, hevent] using heq }
            exact CheckpointEpochOrder.trustedAcceptedBlockTransition cfg ext hcoh t hp
        | attestation a fromBlock =>
            exact CheckpointEpochOrder.on_attestation cfg ext hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact CheckpointEpochOrder.on_attester_slashing ext hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope signed observation =>
            exact hp.of_payloadFrame (on_execution_payload_envelope_frame ext
              (by simpa [apply_event, hevent] using heq))
        | payload_attestation_message message fromBlock =>
            exact hp.of_payloadFrame (on_payload_attestation_message_frame cfg ext
              (by simpa [apply_event, hevent] using heq))

/-- Checkpoint epoch order at every ordinary execution boundary, derived only
from exact accepted block transitions. -/
theorem trustedAcceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (n : ℕ) :
    CheckpointEpochOrder (E.store cfg ext w n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq⟩ := hgen
      change CheckpointEpochOrder E.genesis_store
      rw [hgenEq]
      constructor <;> exact Nat.le_refl _
  | succ n ih =>
      change CheckpointEpochOrder
        ((E.schedule w (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.trustedAcceptedCheckpointEpochOrder_take cfg ext hcoh w n
          (CheckpointEpochOrder.on_tick cfg _ _ ih)
          (E.schedule w (n + 1)).length le_rfl

/-- Checkpoint epoch order at every exact in-second schedule prefix. -/
theorem ScheduledEventPrefix.trustedAcceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (p : E.ScheduledEventPrefix)
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    CheckpointEpochOrder (p.store cfg ext) := by
  apply E.trustedAcceptedCheckpointEpochOrder_take cfg ext hcoh
    p.node p.previousSecond
  · exact CheckpointEpochOrder.on_tick cfg _ _
      (E.trustedAcceptedCheckpointEpochOrder cfg ext hcoh hgen
        p.node p.previousSecond)
  · exact p.count_le

/-- Checkpoint epoch order throughout the exact causal-store domain. -/
theorem CausalStore.trustedAcceptedCheckpointEpochOrder
    {anchor : Checkpoint Root}
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk) :
    CheckpointEpochOrder store := by
  cases hstore with
  | genesis => exact E.trustedAcceptedCheckpointEpochOrder cfg ext hcoh hgen 0 0
  | scheduledPrefix p =>
      exact p.trustedAcceptedCheckpointEpochOrder cfg ext hcoh hgen

end Execution

/-- Accepted global selector/carrier provenance paired with the handler-derived
checkpoint epoch order at one exact causal store. -/
structure TrustedAcceptedFFGOrderedGlobalStoreProjection
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) : Prop where
  globalProjection : TrustedAcceptedFFGGlobalStoreProjection S store
  checkpointOrder : CheckpointEpochOrder store

namespace TrustedCausalPrefixFFGInterpretation

/-- One preselected accepted semantic state supplies block-local projection,
named global carriers, and checkpoint epoch order at the same causal store. -/
theorem trusted_causalStoreOrderedGlobalProjection
    {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    TrustedAcceptedFFGOrderedGlobalStoreProjection cfg ext B.state store := by
  obtain ⟨ast, ablk, hgenEq, hslot⟩ := hgen
  exact
    ⟨B.causalStoreGlobalProjection ⟨ast, ablk, hgenEq, hslot⟩
        hanchor hstore,
      hstore.trustedAcceptedCheckpointEpochOrder cfg ext
        B.coherence.toTrustedFFGSelectorsMatchBeaconStates
        ⟨ast, ablk, hgenEq⟩⟩

/-- Real accepted global consumer: finalized never exceeds justified at any
exact causal store, while the paired projection retains its named global
carrier evidence for downstream use. -/
theorem trusted_globalFinalizedEpoch_le_justified
    {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store) :
    store.finalized_checkpoint.epoch ≤
      store.justified_checkpoint.epoch :=
  (trusted_causalStoreOrderedGlobalProjection cfg ext B hgen hanchor hstore)
    |>.checkpointOrder
    |>.finalized_le_justified


end TrustedCausalPrefixFFGInterpretation

end FastConfirmation.Spec
end
