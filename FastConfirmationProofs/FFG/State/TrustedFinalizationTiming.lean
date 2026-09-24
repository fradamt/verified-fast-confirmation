module
public import FastConfirmationProofs.FFG.State.FinalizationTiming
public import FastConfirmationInternal.Weak.TrustedFFGInterpretation

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}

theorem trustedAcceptedPulledUpFinalized_succ_le_blockEpoch
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (t : E.AcceptedBlockTransition cfg ext) :
    let pulledFinalized :=
      (ext.process_justification_and_finalization
        (t.postStore.block_states t.signedBlock.root)).finalized_checkpoint
    pulledFinalized = B.anchor ∨
      pulledFinalized.epoch + 1 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot := by
  have hguf := B.coherence.transition_guf t
  rw [hguf]
  rcases B.state.guf_evidence t.signedBlock.root t.root_accepted with
    hanchor | hcertificate
  · exact Or.inl hanchor
  · right
    obtain ⟨F⟩ := hcertificate
    have hsigners : F.finalizing_link.signers.Nonempty := by
      by_contra hnone
      have hempty : F.finalizing_link.signers = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      have hzero : 2 * E.total_active cfg ≤ 0 := by
        simpa only [hempty, Execution.weight, Finset.sum_empty,
          Nat.mul_zero] using F.finalizing_link.supermajority
      exact (Nat.not_lt_of_ge hzero)
        (Nat.mul_pos (by omega) (E.total_active_pos cfg))
    obtain ⟨i, hi⟩ := hsigners
    obtain ⟨a, ⟨containing, htipContaining, hincluded⟩,
        _hiAttests, _haSource, haTarget⟩ :=
      F.finalizing_link.signer_attestation i hi
    have hevidence := B.state.includedAttestations.evidence hincluded
    obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
    have htipKnown : t.signedBlock.root ∈
        (E.store cfg ext t.atPrefix.node
          (t.atPrefix.previousSecond + 1)).block_roots :=
      t.root_known_at_second_end cfg ext
    have hcontainingRoot : E.ExecutionRoot containing :=
      ⟨hevidence.carrier_message, hevidence.carrier_at⟩
    have hreflection :=
      E.store_known_ancestor_of_rootDescends_for_storeReflection
        cfg ext hT.wellFormed hT.externals_coherence
        hgenEq hslot hparent htipKnown hcontainingRoot htipContaining
    have hcontainingKnown := hreflection.1
    have hancestor := hreflection.2
    let store := E.store cfg ext t.atPrefix.node
      (t.atPrefix.previousSecond + 1)
    have hparentSlots : ParentSlotLt store :=
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩
        hT.wellFormed.anchor_parent_unscheduled
        t.atPrefix.node (t.atPrefix.previousSecond + 1)
    have hwalkK : ∀ target ∈ store.block_roots,
        ∀ r ∈ store.block_roots,
          WalkKnown store (store.blocks target).slot r :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩
        t.atPrefix.node (t.atPrefix.previousSecond + 1)
    have hslotLe : (store.blocks containing).slot ≤
        (store.blocks t.signedBlock.root).slot :=
      ancestor_slot_le hparentSlots
        (hwalkK containing hcontainingKnown
          t.signedBlock.root htipKnown) hancestor
    have hstoreCausal : E.CausalStore cfg ext store :=
      E.store_causal cfg ext t.atPrefix.node
        (t.atPrefix.previousSecond + 1)
    have hcontainingBlock : store.blocks containing =
        hevidence.carrier_message :=
      (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
        hT.wellFormed hstoreCausal hcontainingKnown).mp
          hevidence.carrier_accepted
    have htipAt : E.AcceptedBlockAt cfg ext t.signedBlock.root
        t.signedBlock.message := by
      refine ⟨t.postStore, t.post_causal, t.root_known, ?_⟩
      by_cases hfresh : t.signedBlock.root ∉
          (t.atPrefix.store cfg ext).block_roots
      · exact t.inserted_message_fresh hfresh
      · have hknown : t.signedBlock.root ∈
            (t.atPrefix.store cfg ext).block_roots :=
          Classical.byContradiction hfresh
        have hpreStore : E.CausalStore cfg ext
            (t.atPrefix.store cfg ext) := .scheduledPrefix t.atPrefix
        have hprov := hpreStore.blockProvenance
          cfg ext E t.signedBlock.root hknown
        have hpreAt : E.BlockAt t.signedBlock.root
            ((t.atPrefix.store cfg ext).blocks t.signedBlock.root) := by
          rcases hprov with hgen | ⟨b, hsched, hroot, hmessage⟩
          · exact Or.inl ⟨hgen.1, hgen.2⟩
          · rcases hsched with ⟨w, n, hb⟩
            exact Or.inr ⟨w, n, b, hb, hroot, hmessage.symm⟩
        obtain ⟨hlt, hevent⟩ :=
          List.getElem?_eq_some_iff.mp t.event_at
        have hmemAt := List.getElem_mem hlt
        rw [hevent] at hmemAt
        have hsignedAt : E.BlockAt t.signedBlock.root
            t.signedBlock.message :=
          Or.inr ⟨t.atPrefix.node, t.atPrefix.previousSecond + 1,
            t.signedBlock, hmemAt, rfl, rfl⟩
        have hmessage := E.blockAt_unique
          hT.wellFormed hpreAt hsignedAt
        have hpost : t.postStore = t.atPrefix.store cfg ext := by
          exact (Option.some.inj (by
            simpa only [on_block, if_pos hknown] using t.accepted)).symm
        rw [hpost]
        exact hmessage
    have htipBlock : store.blocks t.signedBlock.root =
        t.signedBlock.message :=
      (Execution.CausalStore.acceptedBlockAt_iff_eq cfg ext E
        hT.wellFormed hstoreCausal htipKnown).mp htipAt
    have hattestationBeforeTip : a.data.slot <
        t.signedBlock.message.slot := by
      calc
        a.data.slot < hevidence.carrier_message.slot :=
          hevidence.slot_before_carrier
        _ = (store.blocks containing).slot :=
          (congrArg BeaconBlock.slot hcontainingBlock).symm
        _ ≤ (store.blocks t.signedBlock.root).slot := hslotLe
        _ = t.signedBlock.message.slot :=
          congrArg BeaconBlock.slot htipBlock
    have hchildEpoch : (B.state.GUF t.signedBlock.root).epoch + 1 =
        compute_epoch_at_slot cfg a.data.slot := by
      calc
        (B.state.GUF t.signedBlock.root).epoch + 1 = F.child.epoch :=
          F.child_epoch.symm
        _ = a.data.target.epoch :=
          congrArg Checkpoint.epoch haTarget.symm
        _ = compute_epoch_at_slot cfg a.data.slot := hevidence.target_epoch
    rw [hchildEpoch]
    exact ce_mono cfg (Nat.le_of_lt hattestationBeforeTip)


theorem AcceptedFinalizationLagAt.trustedAcceptedBlockTransition
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedFinalizationLagAt cfg B.anchor
      (t.atPrefix.store cfg ext)) :
    AcceptedFinalizationLagAt cfg B.anchor t.postStore := by
  by_cases hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots
  · obtain ⟨post, hst, hinserted⟩ :=
      Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
        cfg ext hfresh t.accepted
    apply AcceptedFinalizationLagAt.on_block_of_delays
      (cfg := cfg) (ext := ext) hst
    · simpa only [hinserted] using hDelay t
    · simpa only [hinserted] using
        E.trustedAcceptedPulledUpFinalized_succ_le_blockEpoch cfg ext B hT t
    · exact AcceptedBlockTransition.blockEpoch_le_current
        cfg ext E t hfresh
    · exact h
    · exact t.accepted
  · have hknown : t.signedBlock.root ∈
        (t.atPrefix.store cfg ext).block_roots :=
      Classical.byContradiction hfresh
    have hsame : t.postStore = t.atPrefix.store cfg ext := by
      exact (Option.some.inj (by
        simpa only [on_block, if_pos hknown] using t.accepted)).symm
    rw [hsame]
    exact h


def TrustedCausalRealizedFinalizationLag
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted) : Prop :=
  ∀ {store : Store Root}, E.CausalStore cfg ext store →
    store.finalized_checkpoint = B.anchor ∨
      store.finalized_checkpoint.epoch + 2 ≤
        get_current_store_epoch cfg store

/-! ## Exact-prefix generation of the causal invariant -/

private theorem trustedGenesisAcceptedFinalizationLagAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFinalizationLagAt cfg B.anchor E.genesis_store := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  rw [hgenEq] at hanchor ⊢
  constructor <;> apply Or.inl <;>
    simpa only [get_forkchoice_store] using hanchor.symm

private theorem trustedAcceptedFinalizationLagAt_take
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : AcceptedFinalizationLagAt cfg B.anchor
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedFinalizationLagAt cfg B.anchor
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
      have hp : AcceptedFinalizationLagAt cfg B.anchor (p.store cfg ext) :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFinalizationLagAt cfg B.anchor
        ((p.successor hklt).store cfg ext)
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
            exact AcceptedFinalizationLagAt.trustedAcceptedBlockTransition
              (cfg := cfg) (ext := ext) (E := E) B hT hDelay t hp
        | attestation a fromBlock =>
            exact AcceptedFinalizationLagAt.on_attestation
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact AcceptedFinalizationLagAt.on_attester_slashing
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_execution_payload_envelope_frame ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
        | payload_attestation_message message isFromBlock =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_payload_attestation_message_frame cfg ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint

/-- The paired finalization-lag invariant at every ordinary execution
boundary. -/
theorem trustedAcceptedFinalizationLagAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B)
    (w : ValidatorIndex) (n : ℕ) :
    AcceptedFinalizationLagAt cfg B.anchor (E.store cfg ext w n) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  induction n with
  | zero =>
      exact E.trustedGenesisAcceptedFinalizationLagAt cfg ext B hT hanchor
  | succ n ih =>
      change AcceptedFinalizationLagAt cfg B.anchor
        ((E.schedule w (n + 1)).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.trustedAcceptedFinalizationLagAt_take cfg ext B hT hDelay w n
          (E.finalizationLag_after_execution_tick cfg ext
            hT.whole_seconds hgenTime w n ih)
          (E.schedule w (n + 1)).length le_rfl

/-- The same invariant at an arbitrary exact in-second scheduled prefix. -/
theorem ScheduledEventPrefix.trustedAcceptedFinalizationLagAt
    (p : E.ScheduledEventPrefix)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B) :
    AcceptedFinalizationLagAt cfg B.anchor (p.store cfg ext) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  apply E.trustedAcceptedFinalizationLagAt_take cfg ext B hT hDelay
    p.node p.previousSecond
  · exact E.finalizationLag_after_execution_tick cfg ext
      hT.whole_seconds hgenTime p.node p.previousSecond
      (E.trustedAcceptedFinalizationLagAt cfg ext B hT hanchor
        hDelay p.node p.previousSecond)
  · exact p.count_le

/-- Paired lag at every exact causal store. -/
theorem CausalStore.trustedAcceptedFinalizationLagAt
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B) :
    AcceptedFinalizationLagAt cfg B.anchor store := by
  cases hstore with
  | genesis =>
      exact E.trustedGenesisAcceptedFinalizationLagAt cfg ext B hT hanchor
  | scheduledPrefix p =>
      exact p.trustedAcceptedFinalizationLagAt
        (cfg := cfg) (ext := ext) (E := E) B hT hanchor hDelay

/-- Main producer: exact accepted block delay generates the realized
two-epoch lag at every causal store.  The GUF half is derived from accepted
certificate inclusion; no second finalization timing premise is exposed. -/
theorem trustedCausalRealizedFinalizationLag_of_acceptedDelay
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.TrustedRealizedFinalizationDelay cfg ext B) :
    E.TrustedCausalRealizedFinalizationLag cfg ext B := by
  intro store hstore
  exact (hstore.trustedAcceptedFinalizationLagAt
    (cfg := cfg) (ext := ext) (E := E) B hT hanchor hDelay).realized

/-- The store-level lag gives the exact checkpoint-age statement without
truncated subtraction. -/
theorem trustedFinalizedCheckpoint_twoEpochLag_of_causalLag
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    (hLag : E.TrustedCausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hne : store.finalized_checkpoint ≠ B.anchor) :
    store.finalized_checkpoint.epoch + 2 ≤
      get_current_store_epoch cfg store := by
  rcases hLag hstore with hanchor | hlag
  · exact False.elim (hne hanchor)
  · exact hlag

/-- Together with existing reset realization, the same law makes the
finalized reset root fail the final selector's recency guard.  This is the
precise fact needed to eliminate the finalized-reset arm in the paper-L22
candidate-history step. -/
theorem trustedFinalizedResetRoot_stale_of_causalLag
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    (hLag : E.TrustedCausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hrealized : E.ResetCheckpointRealizedAt cfg B.anchor store
      store.finalized_checkpoint)
    (hne : store.finalized_checkpoint ≠ B.anchor) :
    get_block_epoch cfg store store.finalized_checkpoint.root + 1 <
      get_current_store_epoch cfg store := by
  have hscaled :
      get_block_epoch cfg store store.finalized_checkpoint.root *
          cfg.slots_per_epoch ≤
        store.finalized_checkpoint.epoch * cfg.slots_per_epoch := by
    simpa only [compute_start_slot_at_epoch] using
      (start_slot_at_block_epoch_le cfg store
        store.finalized_checkpoint.root).trans
          hrealized.root_slot_le_boundary
  have hrootLe :
      get_block_epoch cfg store store.finalized_checkpoint.root ≤
        store.finalized_checkpoint.epoch :=
    Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hfieldLag := E.trustedFinalizedCheckpoint_twoEpochLag_of_causalLag
    cfg ext hLag hstore hne
  have hcombined :
      get_block_epoch cfg store store.finalized_checkpoint.root + 2 ≤
        get_current_store_epoch cfg store :=
    (Nat.add_le_add_right hrootLe 2).trans hfieldLag
  apply Nat.lt_of_succ_le
  rw [show Nat.succ
      (get_block_epoch cfg store store.finalized_checkpoint.root + 1) =
        get_block_epoch cfg store store.finalized_checkpoint.root + 2 by
      omega]
  exact hcombined


end Execution
end FastConfirmation.Spec
end
