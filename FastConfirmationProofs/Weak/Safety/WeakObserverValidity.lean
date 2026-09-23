module
public import FastConfirmationProofs.Discount.HonestWeight
public import FastConfirmationProofs.Execution.History.CausalQueryTraceAdapter

@[expose] public section

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

/-- Stores produced by the observer's own validated handler run. -/
inductive ObserverCausalStore (E : Execution Root) (obs : ValidatorIndex) :
    Store Root → Prop
  | genesis : ObserverCausalStore E obs E.genesis_store
  | scheduledPrefix (p : ScheduledEventPrefix E) : p.node = obs →
      ObserverCausalStore E obs (p.store cfg ext)

/-- Keyed states of the observer's handler run. -/
def ObserverValidationState (E : Execution Root) (obs : ValidatorIndex)
    (state : BeaconState Root) : Prop :=
  ∃ store, ObserverCausalStore cfg ext E obs store ∧
    ((∃ root ∈ store.block_roots, store.block_states root = state) ∨
      ∃ checkpoint ∈ store.checkpoint_state_keys,
        store.checkpoint_states checkpoint = state)

theorem ObserverCausalStore.blockState {E : Execution Root} {obs : ValidatorIndex}
    {store : Store Root} (h : ObserverCausalStore cfg ext E obs store)
    {root : Root} (hroot : root ∈ store.block_roots) :
    ObserverValidationState cfg ext E obs (store.block_states root) :=
  ⟨store, h, Or.inl ⟨root, hroot, rfl⟩⟩

theorem ObserverCausalStore.checkpointState {E : Execution Root} {obs : ValidatorIndex}
    {store : Store Root} (h : ObserverCausalStore cfg ext E obs store)
    {checkpoint : Checkpoint Root}
    (hcheckpoint : checkpoint ∈ store.checkpoint_state_keys) :
    ObserverValidationState cfg ext E obs (store.checkpoint_states checkpoint) :=
  ⟨store, h, Or.inr ⟨checkpoint, hcheckpoint, rfl⟩⟩

theorem observerCausalStore_prefix (E : Execution Root) (obs : ValidatorIndex)
    (n : ℕ) (pre rest : List (Event Root))
    (hl : E.schedule obs (n + 1) = pre ++ rest) :
    ObserverCausalStore cfg ext E obs
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext obs n) (E.time_at (n + 1)))) := by
  let p : ScheduledEventPrefix E :=
    { node := obs
      previousSecond := n
      processedCount := pre.length
      count_le := by rw [hl, List.length_append]; omega }
  have hp : p.store cfg ext =
      pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext obs n) (E.time_at (n + 1))) := by
    simp [p, ScheduledEventPrefix.store, hl]
  rw [← hp]
  exact .scheduledPrefix p rfl

theorem ScheduledEventPrefix.observerCausal_take {E : Execution Root}
    (p : E.ScheduledEventPrefix) (k : ℕ)
    (hk : k ≤ ((E.schedule p.node (p.previousSecond + 1)).take
      p.processedCount).length) :
    E.ObserverCausalStore cfg ext p.node
      ((((E.schedule p.node (p.previousSecond + 1)).take p.processedCount).take k).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext p.node p.previousSecond)
            (E.time_at (p.previousSecond + 1)))) := by
  have hkCount : k ≤ p.processedCount := by
    rw [List.length_take] at hk
    omega
  have hkSchedule : k ≤ (E.schedule p.node (p.previousSecond + 1)).length := by
    rw [List.length_take] at hk
    omega
  have hshort : E.ObserverCausalStore cfg ext p.node
      (({ p with processedCount := k, count_le := hkSchedule } :
        E.ScheduledEventPrefix).store cfg ext) :=
    .scheduledPrefix _ rfl
  simpa only [ScheduledEventPrefix.store, List.take_take,
    Nat.min_eq_left hkCount, Nat.min_eq_right hkCount] using hshort

/-- The three indexed-attestation laws on the observer's own keyed states. -/
structure ObserverValidity (E : Execution Root) (obs : ValidatorIndex) : Prop where
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot

private theorem on_attester_slashing_honest_not_added_of_observer
    {E : Execution Root} {obs : ValidatorIndex}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hvalid : E.ObserverValidity cfg ext obs)
    {store store' : Store Root} {asl : AttesterSlashing Root}
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (hcausal : E.ObserverCausalStore cfg ext obs store)
    (hunknown : UnknownBlockStatesDefault store)
    (hh : on_attester_slashing ext store asl = some store')
    (hprev : v ∉ store.equivocating_indices) :
    v ∉ store'.equivocating_indices := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh with hslash hv1 hv2
  cases hh
  simp only [Finset.mem_union, Finset.mem_inter, List.mem_toFinset, not_or, not_and]
  refine ⟨hprev, fun hv1' hv2' => ?_⟩
  have hs1 : ext.is_valid_indexed_attestation
      (store.block_states store.justified_checkpoint.root) asl.attestation_1 = true := by
    simpa using hv1
  have hs2 : ext.is_valid_indexed_attestation
      (store.block_states store.justified_checkpoint.root) asl.attestation_2 = true := by
    simpa using hv2
  have hknown : store.justified_checkpoint.root ∈ store.block_roots := by
    by_contra hnot
    rw [hunknown _ hnot, hec.valid_attestation_default] at hs1
    contradiction
  have hstate := hcausal.blockState cfg ext hknown
  obtain ⟨m1, c1, hvote1, hdata1⟩ :=
    hvalid.valid_attestation_honest _ asl.attestation_1 hstate hs1 v hv hv1'
  obtain ⟨m2, c2, hvote2, hdata2⟩ :=
    hvalid.valid_attestation_honest _ asl.attestation_2 hstate hs2 v hv hv2'
  have hns := hhb.not_slashable v hv asl.attestation_1.data.slot asl.attestation_2.data.slot
    m1 m2 c1 c2 hvote1 hvote2
  have hslash' : is_slashable_attestation_data asl.attestation_1.data asl.attestation_2.data
      = true := by simpa using hslash
  rw [hdata1, hdata2, hns] at hslash'
  simp at hslash'

private theorem apply_event_honest_not_equiv_of_observer
    {E : Execution Root} {obs : ValidatorIndex}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hvalid : E.ObserverValidity cfg ext obs)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    (store : Store Root) (e : Event Root) (hprev : v ∉ store.equivocating_indices)
    (hcausal : E.ObserverCausalStore cfg ext obs store)
    (hunknown : UnknownBlockStatesDefault store) :
    v ∉ ((apply_event cfg ext store e).getD store).equivocating_indices := by
  cases e with
  | block b =>
    simp only [apply_event]
    cases hb : on_block cfg ext store b with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]; rw [on_block_equiv cfg ext hb]; exact hprev
  | attestation a ifb =>
    simp only [apply_event]
    cases ha : on_attestation cfg ext store a ifb with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]; rw [on_attestation_equiv cfg ext ha]; exact hprev
  | attester_slashing asl =>
    simp only [apply_event]
    cases has : on_attester_slashing ext store asl with
    | none => simpa using hprev
    | some s' =>
      simp only [Option.getD_some]
      exact on_attester_slashing_honest_not_added_of_observer cfg ext hhb hec hvalid hv
        hcausal hunknown has hprev
  | execution_payload_envelope envelope observation =>
    simp only [apply_event]
    cases he : on_execution_payload_envelope ext store envelope observation with
    | none => exact hprev
    | some next =>
      simp only [Option.getD_some]
      rw [(on_execution_payload_envelope_frame ext he).equivocating_indices]
      exact hprev
  | payload_attestation_message message fromBlock =>
    simp only [apply_event]
    cases he : on_payload_attestation_message cfg ext store message fromBlock with
    | none => exact hprev
    | some next =>
      simp only [Option.getD_some]
      rw [(on_payload_attestation_message_frame cfg ext he).equivocating_indices]
      exact hprev

theorem honest_not_equiv_foldl_of_observer
    {E : Execution Root} {obs : ValidatorIndex}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hvalid : E.ObserverValidity cfg ext obs)
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ (l : List (Event Root)) (s : Store Root), v ∉ s.equivocating_indices →
      UnknownBlockStatesDefault s →
      (∀ k, k ≤ l.length → E.ObserverCausalStore cfg ext obs
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store) s)) →
      v ∉ (l.foldl (fun store e => (apply_event cfg ext store e).getD store)
        s).equivocating_indices := by
  intro l
  induction l with
  | nil => intro s hs _ _; exact hs
  | cons e l ih =>
    intro s hs hunknown hcausal
    rw [List.foldl_cons]
    refine ih _ ?_ (apply_event_unknownBlockStatesDefault cfg ext s e hunknown) ?_
    · exact apply_event_honest_not_equiv_of_observer cfg ext hhb hec hvalid hv s e hs
        (by simpa using hcausal 0 (Nat.zero_le _)) hunknown
    · intro k hk
      simpa only [List.take_succ_cons, List.foldl_cons] using
        hcausal (k + 1) (by simpa using Nat.succ_le_succ hk)

/-- Honest validators are never marked equivocating in this observer's run. -/
theorem honest_not_equivocating_of_observer_validity
    {E : Execution Root} {obs : ValidatorIndex}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hvalid : E.ObserverValidity cfg ext obs)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) (n : ℕ) :
    v ∉ (E.store cfg ext obs n).equivocating_indices := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg⟩ := hgen
    change v ∉ E.genesis_store.equivocating_indices
    rw [hg]
    simp [get_forkchoice_store]
  | succ n ih =>
    change v ∉ ((E.schedule obs (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext obs n) (E.time_at (n + 1)))).equivocating_indices
    refine honest_not_equiv_foldl_of_observer cfg ext hhb hec hvalid hv _ _ ?_ ?_ ?_
    · rw [on_tick_equiv]
      exact ih
    · exact on_tick_unknownBlockStatesDefault cfg _ _
        (E.unknownBlockStatesDefault_store cfg ext hgen obs n)
    · intro k hk
      exact E.observerCausalStore_prefix cfg ext obs n
        ((E.schedule obs (n + 1)).take k) ((E.schedule obs (n + 1)).drop k)
        (List.take_append_drop k _).symm

theorem ScheduledEventPrefix.honest_not_equivocating_of_observer_validity
    {E : Execution Root} (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (p : E.ScheduledEventPrefix)
    (hvalid : E.ObserverValidity cfg ext p.node) :
    ∀ i ∈ E.honest, i ∉ (p.store cfg ext).equivocating_indices := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  intro i hi
  rw [ScheduledEventPrefix.store]
  refine honest_not_equiv_foldl_of_observer cfg ext hT.honest_behavior
    hT.externals_coherence hvalid hi _ _ ?_ ?_ ?_
  · rw [on_tick_equiv]
    exact E.honest_not_equivocating_of_observer_validity cfg ext
      hT.honest_behavior hT.externals_coherence hvalid
      ⟨anchorState, anchorBlock, hgen⟩ hi p.previousSecond
  · exact on_tick_unknownBlockStatesDefault cfg _ _
      (E.unknownBlockStatesDefault_store cfg ext
        ⟨anchorState, anchorBlock, hgen⟩ p.node p.previousSecond)
  · exact p.observerCausal_take cfg ext

end Execution
end FastConfirmation.Spec
end
