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

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
