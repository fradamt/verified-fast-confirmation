module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverPremiseReduction
public import FastConfirmationProofs.Weak.Selection.WeakAncestryEndpoint
public import FastConfirmationProofs.FFG.CurrentTarget.HonestVoteTargetCache

/-! Honest endpoint delivery transfers from the observer-erased execution.

These adapters use head paths only at honest receivers. They do not require
the all-receiver head-path field for the actual observer's store.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

/-- A genuine honest vote persists at every honest receiver after its
delivery boundary, independently of the non-honest observer's schedule. -/
theorem nonhonest_vote_ubiquity
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots)
    (hwalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
      (get_head cfg (E.store cfg ext v n)).root)
    {m : ℕ} (hm : E.slot_start cfg (s + 1) ≤ m) (hHm : E.WithinHorizon cfg m) :
    ∃ msg, (E.store cfg ext w m).latest_messages v = some msg ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch ≤
        get_latest_message_epoch cfg msg := by
  let R := E.withoutObserver obs
  have hvne : v ≠ obs := by intro he; subst v; exact hobs hv
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hvR : v ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hv
  have hwR : w ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hw
  have hs := withoutObserver_store cfg ext E obs v hvne n
  rw [← hs] at hvote hhead hwalk ⊢
  rw [← withoutObserver_store cfg ext E obs w hwne m]
  exact R.vote_ubiquity cfg ext core.base.wellFormed core.base.honest_behavior
    core.base.synchrony core.base.domain.honest_head_paths core.base.externals_coherence
    core.base.whole_seconds core.base.genesis hvR hwR hn hHn hvote
    (by simpa only [honest_attestation_data_beacon_block_root] using hhead)
    (by simpa only [honest_attestation_data_beacon_block_root] using hwalk) hm hHm

/-- The delivered vote's target is known and cached at an honest receiver.
Both endpoint stores are unchanged by observer erasure. -/
theorem nonhonest_vote_target_received
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : ℕ} {index : CommitteeIndex} (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHdeliver : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots)
    (hwalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.epoch)
      (get_head cfg (E.store cfg ext v n)).root) :
    (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target.root ∈
        (E.store cfg ext w (E.slot_start cfg (s + 1))).block_roots ∧
      (honest_attestation cfg ext (E.store cfg ext v n) s index v).data.target ∈
        (E.store cfg ext w (E.slot_start cfg (s + 1))).checkpoint_state_keys := by
  let R := E.withoutObserver obs
  have hvne : v ≠ obs := by intro he; subst v; exact hobs hv
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hvR : v ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hv
  have hwR : w ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hw
  have hs := withoutObserver_store cfg ext E obs v hvne n
  rw [← hs] at hvote hhead hwalk ⊢
  rw [← withoutObserver_store cfg ext E obs w hwne (E.slot_start cfg (s + 1))]
  exact R.honestVoteTarget_received_at_delivery cfg ext core.base.wellFormed
    core.base.honest_behavior core.base.synchrony core.base.domain.honest_head_paths
    core.base.externals_coherence core.base.whole_seconds core.base.genesis hvR hwR
    hn hHn hHdeliver hvote
    (by simpa only [honest_attestation_data_beacon_block_root] using hhead)
    (by simpa only [honest_attestation_data_beacon_block_root] using hwalk)

/-- Relay a head ancestor between honest endpoints. This supplies both
the weak ancestry use and the whole-head special case of G4 transport. -/
theorem nonhonest_head_ancestor_known
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    {v w : ValidatorIndex} {n m : ℕ} {b : Root}
    (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) + get_attestation_due_ms cfg / 1000)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hanc : is_ancestor (E.store cfg ext v n)
      (get_node_for_root (get_head cfg (E.store cfg ext v n)).root)
      (get_node_for_root b) = true)
    (hslot : E.slot_at cfg n < E.slot_at cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  let R := E.withoutObserver obs
  have hvne : v ≠ obs := by intro he; subst v; exact hobs hv
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hvR : v ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hv
  have hwR : w ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hw
  rw [← withoutObserver_store cfg ext E obs v hvne n] at hb hanc
  rw [← withoutObserver_store cfg ext E obs w hwne m]
  exact R.honest_head_ancestor_known_at_endpoint_weak cfg ext core.base hvR hwR
    hHn hHm hdue hb hanc hslot

end Execution
end FastConfirmation.Spec
end
