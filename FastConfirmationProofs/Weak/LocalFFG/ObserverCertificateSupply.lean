module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverSafetySupply
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGFinalization
public import FastConfirmationProofs.FFG.Certificates.EarlyFinalizingSigner
public import FastConfirmationProofs.Checkpoints.FinalizedBeforeVoteJustification

/-! Observer body certificates supply authentic global FFG certificates.

Validation uses the observer's own prepared state. The from-block event is
local handling of accepted content; no remote receipt or deadline is added.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

/-- Registry preservation also holds at prefixes of the observer's run. -/
theorem observerCertificate_causal_registry
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    {store : Store Root} (hs : E.CausalStore cfg ext store) :
    RegistryConstant E.registry store := by
  let hec := nonhonest_externals hobs core
  have hgen : ∃ (st : BeaconState Root) (b : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg st b := by
    obtain ⟨st, b, hg, _⟩ := core.genesis
    exact ⟨st, b, hg⟩
  cases hs with
  | genesis => exact E.genesis_registryConstant cfg hgen
  | scheduledPrefix p =>
    apply registryConstant_foldl
      (fun s e h => apply_event_getD_registryConstant cfg ext
        hec.state_transition_registry hec.process_slots_registry s e h)
    exact on_tick_registryConstant cfg _ _
      (E.registryConstant cfg ext hec hgen p.node p.previousSecond)

namespace ObserverLocalFFG

/-- Local body evidence projects to ordinary inclusion evidence. This does
not assert the old honest validation-store field. -/
def includedRelation (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    E.IncludedAttestationRelation cfg ext.is_valid_indexed_attestation where
  Included := B.state.included
  evidence := fun {r a} ha => by
    let ev := B.included_evidence ha
    let base := ev.validation_store.block_states a.data.target.root
    let start := compute_start_slot_at_epoch cfg a.data.target.epoch
    refine {
      carrier_message := B.state.blocks r
      carrier_at := (B.included_body ha).1
      in_carrier_body := ev.body_member
      received_from_block := ?_
      validation_state := if base.slot < start then ext.process_slots base start else base
      validation_registry := ?_
      valid := ev.valid
      slot_within_horizon := ev.slot_within_horizon
      slot_before_carrier := ev.slot_before_carrier
      target_epoch := ev.target_epoch
      head_descends_target := ev.head_descends_target
      target_on_chain := ev.target_on_chain
      target_descends_source := ev.target_descends_source
      attesters_in_committee := ev.committee localInputs.toObserverInputAuthenticity
      attesters_in_registry := ?_ }
    · obtain ⟨n, hn⟩ := ev.received_from_block
      exact ⟨obs, n, hn⟩
    · have hr := (observerCertificate_causal_registry hobs core ev.validation_local.causal).1
        a.data.target.root ev.target_known
      split_ifs
      · exact (nonhonest_externals hobs core).process_slots_registry _ _ |>.trans hr
      · exact hr
    · intro i hi
      have hc := ev.committee localInputs.toObserverInputAuthenticity i hi
      have hactive := (nonhonest_externals hobs core).committee_members_active
        i a.data.slot ev.slot_within_horizon hc
      by_contra hge
      rw [not_lt] at hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge,
        Option.getD_none] at hactive
      simp only [is_active_validator, decide_eq_true_eq] at hactive
      exact Nat.not_lt_zero _ hactive.2

/-- Every local AU entry has a scheduled certificate in the actual run.
The observer itself witnesses local body handling. -/
theorem au_certified (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {r c} (h : B.state.AU r c) :
    CertifiedJustified cfg E E.genesis_store.justified_checkpoint c := by
  obtain ⟨carrier, _, hc⟩ := (B.au_certificate h).1
  exact IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg)
    (B.includedRelation hobs core localInputs) hc

/-- The observer's finalized checkpoint has a global certificate, with the
trusted anchor as the only exception. -/
theorem finalized_certified (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {store : Store Root} (hs : E.ObserverCausalStore cfg ext obs store) :
    store.finalized_checkpoint = E.genesis_store.justified_checkpoint ∨
      Nonempty (CertifiedFinalized cfg E E.genesis_store.justified_checkpoint
        store.finalized_checkpoint) := by
  rcases B.finalized_certificate core hs with ha | ⟨r, _, ⟨hc⟩⟩
  · exact Or.inl ha
  · exact Or.inr ⟨IncludedCertifiedFinalized.toCertifiedFinalized (cfg := cfg)
      (B.includedRelation hobs core localInputs) hc⟩

set_option maxRecDepth 4096 in
/-- A local finalized certificate is no newer than an honest node's
justification in the same or a later slot. Its signer supplies the relay
source; no message is required at the observer. -/
theorem finalized_epoch_le_honest_justified
    (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {m n : ℕ}
    (hn : E.WithinHorizon cfg n)
    (hmn : E.slot_at cfg m ≤ E.slot_at cfg n) :
    (E.store cfg ext obs m).finalized_checkpoint.epoch ≤
      (E.store cfg ext v n).justified_checkpoint.epoch := by
  let R := E.withoutObserver obs
  let S := core.semantics
  let hT := ScheduledPrefixPremises.of_selectedMarginAssumptions
    cfg ext R core.base core.genesis
  have hh : R.honest = E.honest := withoutObserver_honest hobs
  have hvR : v ∈ R.honest := hh.symm ▸ hv
  have hvne : v ≠ obs := by intro heq; subst v; exact hobs hv
  have hstoreV := withoutObserver_store cfg ext E obs v hvne n
  rw [← hstoreV]
  have hanchorEq : S.anchor = E.genesis_store.justified_checkpoint := core.anchor_eq
  have hgenShort : ∃ (st : BeaconState Root) (b : SignedBeaconBlock Root),
      R.genesis_store = get_forkchoice_store cfg st b ∧ st.slot = b.message.slot := by
    obtain ⟨st, b, hg, hs, _⟩ := core.genesis
    exact ⟨st, b, hg, hs⟩
  have hanchorLe : E.genesis_store.justified_checkpoint.epoch ≤
      (R.store cfg ext v n).justified_checkpoint.epoch := by
    obtain ⟨cert⟩ := CausalPrefixFFGInterpretation.endpointJustified_certificate
      cfg ext S hgenShort core.anchor_eq (R.store_causal cfg ext v n)
    rw [← hanchorEq]
    exact CertifiedJustified.anchor_epoch_le (cfg := cfg) cert
  rcases B.finalized_certificate core (store_observerCausal m) with
      ha | ⟨carrier, hcarrier, ⟨cert⟩⟩
  · rw [ha]; exact hanchorLe
  obtain ⟨i, hi, containing, a, k, own, hdesc, hin, hia, hsource, htarget,
      hvote, hdata, _hdue⟩ :=
    B.link_signed_origin core localInputs.toObserverInputAuthenticity cert.finalizing_link
  have hslotBefore := B.included_slot_before_tip core localInputs m hcarrier
    (show AttestationIncludedOnChain E B.state.included carrier a from
      ⟨containing, hdesc, hin⟩)
  rw [B.block_read (store_observerCausal m) carrier hcarrier] at hslotBefore
  obtain ⟨ast, ablk, hgen, hgenSlot, hcommit, hparent⟩ := core.genesis
  have hblockLe := E.store_blocks_slot_le_current cfg ext core.base.whole_seconds
    ⟨ast, ablk, hgen, hgenSlot⟩ obs m carrier hcarrier
  rw [E.store_current_slot] at hblockLe
  have hslotLt : a.data.slot < R.slot_at cfg n :=
    hslotBefore.trans_le (hblockLe.trans hmn)
  have hcommittee := core.base.honest_behavior.votes_assigned i hi a.data.slot
    (by rw [hvote]; exact Option.some_ne_none _)
  have hanchorTarget : E.genesis_store.justified_checkpoint.epoch ≤ a.data.target.epoch := by
    rw [htarget, cert.child_epoch]
    exact (IncludedCertifiedJustified.anchor_epoch_le (cfg := cfg) cert.justified).trans
      (Nat.le_succ _)
  have hs0 : R.slot_at cfg 0 ≤ a.data.slot := by
    have hstart := R.initial_slot_le_anchor_boundary cfg ext hT
      core.anchor_eq core.anchor_boundary
    apply hstart.trans
    rw [hanchorEq]
    apply (Nat.mul_le_mul_right cfg.slots_per_epoch hanchorTarget).trans
    rw [(B.included_evidence hin).target_epoch]
    exact Nat.div_mul_le_self _ _
  obtain ⟨time, index, htimeH, htimeSlot, hown⟩ :=
    core.base.honest_behavior.votes_head i hi a.data.slot hcommittee
      (B.included_evidence hin).slot_within_horizon hs0
  have heq := hvote
  rw [hown] at heq
  have hownData : a.data = (honest_attestation cfg ext
      (R.store cfg ext i time) a.data.slot index i).data := by
    rw [(Prod.mk.inj (Option.some.inj heq)).2]
    exact hdata
  have hhead := R.headRootKnown_of_acceptedGlobalTrajectory cfg ext S hT
    core.anchor_eq core.anchor_boundary hi time htimeH
  have hselector := R.honest_attestation_source_selector cfg ext S hT
    core.completed_calls.phase0_source core.completed_calls.phase0_boundary_source
    (index := index) htimeSlot hhead
  have hsourceOwn : (honest_attestation cfg ext
      (R.store cfg ext i time) a.data.slot index i).data.source =
      (E.store cfg ext obs m).finalized_checkpoint := by
    rw [← hownData]; exact hsource
  rw [hsourceOwn] at hselector
  have hgenTime : R.genesis_store.genesis_time ≤ R.genesis_store.time := by
    change E.genesis_store.genesis_time ≤ E.genesis_store.time
    have hg : E.genesis_store = get_forkchoice_store cfg ast ablk := hgen
    rw [hg]; simp only [get_forkchoice_store]; omega
  have hnext : R.slot_start cfg (R.slot_at cfg time + 1) ≤ n := by
    rw [htimeSlot]
    exact (R.slot_start_mono cfg (Nat.succ_le_of_lt hslotLt)).trans
      (R.slot_start_le_of_slot_at cfg core.base.whole_seconds hgenTime rfl)
  have htimeLt : time < n := by
    have hlt : time < R.slot_start cfg (R.slot_at cfg n) :=
      (R.slot_at_lt_iff cfg core.base.whole_seconds hgenTime).mp
        (htimeSlot ▸ hslotLt)
    exact hlt.trans_le (R.slot_start_le_of_slot_at cfg core.base.whole_seconds hgenTime rfl)
  have hacc := CheckpointCertificateAccountability.of_assumptions cfg (anchor := S.anchor)
    (SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext R core.base)
  apply R.deadline_justified_epoch_le_of_carrier cfg ext S hT
    core.base.synchrony.deadline_block_relay core.anchor_eq core.anchor_boundary
    core.checkpoint_projection core.exact_link_validity hacc hi hvR htimeH hn hhead
    (by
      rw [show R.slot_at cfg time = a.data.slot from htimeSlot]
      exact (core.base.honest_behavior.vote_deadline i hi _ _ _ hown).2) hnext htimeLt
  rcases hselector with hgj | ⟨hgu, hold⟩
  · exact Or.inl hgj
  · exact Or.inr ⟨hgu, by
      simpa only [get_current_store_epoch, R.store_current_slot] using
        hold.trans_le (ce_mono cfg hslotLt.le)⟩

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
