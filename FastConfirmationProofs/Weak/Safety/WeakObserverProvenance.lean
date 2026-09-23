module
public import FastConfirmationProofs.Execution.Trajectory.LatestMessageProvenance
public import FastConfirmationProofs.Weak.Safety.WeakObserverValidity

@[expose] public section

/-!
An observer outside `Execution.honest` still has the structural part of
latest-message provenance. The attestation handler accepts a message only
when its block root is already known. This invariant uses no indexed
attestation validity law and therefore does not need an honest observer.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

def LatestMessageRootKnown (store : Store Root) : Prop :=
  ∀ i m, store.latest_messages i = some m → m.root ∈ store.block_roots

theorem latestMessageRootKnown_on_tick (store : Store Root) (time : Nat)
    (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown (on_tick cfg store time) := by
  intro i m hm
  rw [on_tick_latest cfg store time] at hm
  exact (on_tick_sameBlocks cfg store time).1 ▸ h i m hm

theorem latestMessageRootKnown_on_block {store store' : Store Root}
    {block : SignedBeaconBlock Root} (h : LatestMessageRootKnown store)
    (hsuccess : on_block cfg ext store block = some store') :
    LatestMessageRootKnown store' := by
  intro i m hm
  rw [on_block_latest cfg ext hsuccess] at hm
  exact (on_block_storeLE cfg ext hsuccess).1 (h i m hm)

theorem latestMessageRootKnown_on_attestation {store store' : Store Root}
    {a : Attestation Root} {fromBlock : Bool} (h : LatestMessageRootKnown store)
    (hsuccess : on_attestation cfg ext store a fromBlock = some store') :
    LatestMessageRootKnown store' := by
  have hsb := on_attestation_sameBlocks cfg ext hsuccess
  simp only [on_attestation] at hsuccess
  split_ifs at hsuccess with hv hvi
  cases hsuccess
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hroot⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨_, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact hsb.1 ▸ h i m hold
  · rw [hmeq]
    exact hsb.1 ▸ hroot

theorem latestMessageRootKnown_on_attester_slashing {store store' : Store Root}
    {slashing : AttesterSlashing Root} (h : LatestMessageRootKnown store)
    (hsuccess : on_attester_slashing ext store slashing = some store') :
    LatestMessageRootKnown store' := by
  intro i m hm
  rw [on_attester_slashing_latest ext hsuccess] at hm
  exact (on_attester_slashing_sameBlocks ext hsuccess).1 ▸ h i m hm

theorem latestMessageRootKnown_apply_event (store : Store Root) (event : Event Root)
    (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown ((apply_event cfg ext store event).getD store) := by
  cases event with
  | block block =>
    simp only [apply_event]
    cases hresult : on_block cfg ext store block with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_block cfg ext h hresult
  | attestation a fromBlock =>
    simp only [apply_event]
    cases hresult : on_attestation cfg ext store a fromBlock with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_attestation cfg ext h hresult
  | execution_payload_envelope envelope observation =>
    simp only [apply_event]
    cases he : on_execution_payload_envelope ext store envelope observation with
    | none => exact h
    | some next =>
      intro i m hm
      simp only [Option.getD_some] at hm ⊢
      have hf := on_execution_payload_envelope_frame ext he
      rw [hf.latest_messages] at hm
      rw [hf.block_roots]
      exact h i m hm
  | payload_attestation_message message fromBlock =>
    simp only [apply_event]
    cases he : on_payload_attestation_message cfg ext store message fromBlock with
    | none => exact h
    | some next =>
      intro i m hm
      simp only [Option.getD_some] at hm ⊢
      have hf := on_payload_attestation_message_frame cfg ext he
      rw [hf.latest_messages] at hm
      rw [hf.block_roots]
      exact h i m hm
  | attester_slashing slashing =>
    simp only [apply_event]
    cases hresult : on_attester_slashing ext store slashing with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_attester_slashing ext h hresult

theorem latestMessageRootKnown_foldl {α : Type*} (f : Store Root → α → Store Root)
    (hf : ∀ store event, LatestMessageRootKnown store →
      LatestMessageRootKnown (f store event))
    (events : List α) (store : Store Root) (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown (events.foldl f store) := by
  induction events generalizing store with
  | nil => exact h
  | cons event events ih => exact ih _ (hf store event h)

theorem Execution.latestMessageRootKnown {E : Execution Root}
    (hgen : ∃ state block, E.genesis_store = get_forkchoice_store cfg state block)
    (node : ValidatorIndex) (second : Nat) :
    LatestMessageRootKnown (E.store cfg ext node second) := by
  induction second with
  | zero =>
    obtain ⟨state, block, hgen⟩ := hgen
    change LatestMessageRootKnown E.genesis_store
    rw [hgen]
    intro i m hm
    simp [get_forkchoice_store] at hm
  | succ second ih =>
    exact latestMessageRootKnown_foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (latestMessageRootKnown_apply_event cfg ext) _ _
      (latestMessageRootKnown_on_tick cfg _ _ ih)

/-! ## Full provenance for an arbitrary observer under its validation contract -/

private theorem update_latest_messages_checkpointData
    (store : Store Root) (indices : List ValidatorIndex) (a : Attestation Root) :
    ((update_latest_messages store indices a).checkpoint_state_keys,
      (update_latest_messages store indices a).checkpoint_states) =
      (store.checkpoint_state_keys, store.checkpoint_states) := by
  simp only [update_latest_messages]
  generalize hindices :
    indices.filter (fun i => decide (i ∉ store.equivocating_indices)) = remaining
  clear hindices
  induction remaining generalizing store with
  | nil => rfl
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      split_ifs <;> rfl

theorem on_attestation_LMP_of_observer {E : Execution Root} {obs : ValidatorIndex} {sl : Slot}
    (hvalid : E.ObserverValidity cfg ext obs) {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool} (hcur : get_current_slot cfg store ≤ sl)
    (h : LatestMessageProvenance E cfg sl store)
    (hh : on_attestation cfg ext store a ifb = some store')
    (hpost : E.ObserverCausalStore cfg ext obs store') :
    LatestMessageProvenance E cfg sl store' := by
  have hsb := on_attestation_sameBlocks cfg ext hh
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  have hcache := update_latest_messages_checkpointData
    (store_target_checkpoint_state cfg ext store a.data.target) a.attesting_indices a
  have hkeys := congrArg Prod.fst hcache
  have hstates := congrArg Prod.snd hcache
  dsimp only at hkeys hstates
  have htarget : a.data.target ∈
      (store_target_checkpoint_state cfg ext store a.data.target).checkpoint_state_keys := by
    by_cases hcached : a.data.target ∈ store.checkpoint_state_keys
    · simp [store_target_checkpoint_state, hcached]
    · simp [store_target_checkpoint_state, hcached]
  have hreachable : E.ObserverValidationState cfg ext obs
      ((store_target_checkpoint_state cfg ext store a.data.target).checkpoint_states
        a.data.target) := by
    have hkey : a.data.target ∈
        (update_latest_messages
          (store_target_checkpoint_state cfg ext store a.data.target)
          a.attesting_indices a).checkpoint_state_keys := by
      rw [hkeys]
      exact htarget
    simpa only [hstates] using hpost.checkpointState cfg ext hkey
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hB⟩, _⟩, hD⟩, hE⟩, _⟩, _⟩, _⟩, _⟩, hG⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    obtain ⟨a', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i m hold
    exact ⟨a', h1, h2, h3, h4, h5, h6, hsb.1 ▸ h7, hsb.2.1 ▸ h8, h9⟩
  · exact ⟨a, hi, by rw [hmeq]; exact hB, by rw [hmeq], by rw [hmeq]; rfl,
      le_trans hG hcur, hvalid.valid_attestation_committee _ a hreachable hvi i hi,
      by rw [hmeq]; exact hsb.1 ▸ hD, by rw [hmeq]; exact hsb.2.1 ▸ hE,
      by rw [hmeq]⟩


theorem apply_event_LMP_of_observer {E : Execution Root} {obs : ValidatorIndex} {sl : Slot} (hwf : WellFormedExecution E)
    (hvalid : E.ObserverValidity cfg ext obs) {store store' : Store Root} {e : Event Root}
    (hsched : ∀ b, e = Event.block b → IsScheduledBlock E b)
    (hprov : BlockProvenance E store) (hcur : get_current_slot cfg store ≤ sl)
    (h : LatestMessageProvenance E cfg sl store)
    (he : apply_event cfg ext store e = some store')
    (hpost : E.ObserverCausalStore cfg ext obs store') :
    LatestMessageProvenance E cfg sl store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_LMP cfg ext hwf (hsched b rfl) hprov h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_LMP_of_observer cfg ext hvalid hcur h he hpost
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact h.of_sameBlocks (on_attester_slashing_sameBlocks ext he)
      (on_attester_slashing_latest ext he)
  | execution_payload_envelope envelope observation =>
    have hf := on_execution_payload_envelope_frame ext he
    exact h.of_transfer (by rw [hf.block_roots]; exact List.Subset.refl _)
      (fun _ _ hh => hf.latest_messages ▸ hh) (fun r _ => by rw [hf.blocks])
  | payload_attestation_message message fromBlock =>
    have hf := on_payload_attestation_message_frame cfg ext he
    exact h.of_transfer (by rw [hf.block_roots]; exact List.Subset.refl _)
      (fun _ _ hh => hf.latest_messages ▸ hh) (fun r _ => by rw [hf.blocks])


theorem LMP_foldl_of_observer {E : Execution Root} {obs : ValidatorIndex} {sl : Slot} (hwf : WellFormedExecution E)
    (hvalid : E.ObserverValidity cfg ext obs) :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ b, Event.block b ∈ l → IsScheduledBlock E b) →
      BlockProvenance E s → get_current_slot cfg s ≤ sl →
      LatestMessageProvenance E cfg sl s →
      (∀ k, k ≤ l.length → E.ObserverCausalStore cfg ext obs
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store) s)) →
      LatestMessageProvenance E cfg sl
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ _ _ h _; exact h
  | cons e l ih =>
    intro s hl hprov hcur h hcausal
    have htail : ∀ k, k ≤ l.length → E.ObserverCausalStore cfg ext obs
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ((apply_event cfg ext s e).getD s)) := by
      intro k hk
      simpa only [List.take_succ_cons, List.foldl_cons] using
        hcausal (k + 1) (by simpa using Nat.succ_le_succ hk)
    have hstep : E.ObserverCausalStore cfg ext obs
        ((apply_event cfg ext s e).getD s) := by
      simpa using htail 0 (Nat.zero_le _)
    rw [List.foldl_cons]
    have hbsched : ∀ b, e = Event.block b → IsScheduledBlock E b :=
      fun b hbe => hl b (by rw [← hbe]; exact List.mem_cons_self)
    cases he : apply_event cfg ext s e with
    | none =>
      simp only [Option.getD_none]
      exact ih _ (fun b hb => hl b (List.mem_cons_of_mem e hb)) hprov hcur h
        (by simpa only [he, Option.getD_none] using htail)
    | some s' =>
      simp only [Option.getD_some]
      refine ih _ (fun b hb => hl b (List.mem_cons_of_mem e hb)) ?_ ?_ ?_ ?_
      · exact apply_event_blockProvenance cfg ext hbsched hprov he
      · rw [apply_event_get_current_slot cfg ext he]; exact hcur
      · exact apply_event_LMP_of_observer cfg ext hwf hvalid hbsched hprov hcur h he
          (by simpa only [he, Option.getD_some] using hstep)
      · simpa only [he, Option.getD_some] using htail


theorem Execution.latestMessageProvenance_of_observer_validity {E : Execution Root}
    (hwf : WellFormedExecution E) (v : ValidatorIndex)
    (hvalid : E.ObserverValidity cfg ext v)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (n : ℕ) :
    LatestMessageProvenance E cfg (E.slot_at cfg n) (E.store cfg ext v n) := by
  induction n with
  | zero =>
    obtain ⟨ast, ablk, hg⟩ := hgen
    intro i m hm
    have hm' : E.genesis_store.latest_messages i = some m := hm
    rw [hg] at hm'
    simp [get_forkchoice_store] at hm'
  | succ n ih =>
    change LatestMessageProvenance E cfg (E.slot_at cfg (n + 1))
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have hontickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have hslot :
        get_current_slot cfg (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
          E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen,
        Execution.slot_at]
    refine LMP_foldl_of_observer cfg ext hwf hvalid _ _ (fun b hb => ⟨v, n + 1, hb⟩) ?_ ?_ ?_ ?_
    · exact on_tick_blockProvenance cfg _ _ (E.blockProvenance cfg ext v n)
    · rw [hslot]
    · exact on_tick_LMP cfg _ _
        (ih.mono_sl
          (E.slot_at_mono cfg (Nat.le_succ n)))
    · intro k hk
      exact .scheduledPrefix ⟨v, n, k, hk⟩ rfl


namespace Execution

variable {E : Execution Root}

theorem ScheduledEventPrefix.latestMessageProvenance_of_observer_validity
    (hT : E.ScheduledPrefixPremises cfg ext)
    (p : E.ScheduledEventPrefix)
    (hvalid : E.ObserverValidity cfg ext p.node)
    (hn : E.WithinHorizon cfg (p.previousSecond + 1)) :
    LatestMessageProvenance E cfg (get_current_slot cfg (p.store cfg ext))
      (p.store cfg ext) := by
  obtain ⟨anchorState, anchorBlock, hgen, _hslot, _hparent⟩ := hT.genesis_structure
  have hcur : get_current_slot cfg
      (on_tick cfg (E.store cfg ext p.node p.previousSecond)
        (E.time_at (p.previousSecond + 1))) =
      E.slot_at cfg (p.previousSecond + 1) := by
    have hp := p.current_slot cfg ext
    rwa [ScheduledEventPrefix.store, foldl_get_current_slot] at hp
  have hresult : LatestMessageProvenance E cfg
      (E.slot_at cfg (p.previousSecond + 1)) (p.store cfg ext) := by
    rw [ScheduledEventPrefix.store]
    refine LMP_foldl_of_observer cfg ext hT.wellFormed hvalid _ _ ?_ ?_ ?_ ?_ ?_
    · intro block hmem
      exact ⟨p.node, p.previousSecond + 1, List.mem_of_mem_take hmem⟩
    · exact on_tick_blockProvenance cfg _ _
        (E.blockProvenance cfg ext p.node p.previousSecond)
    · exact le_of_eq hcur
    · exact on_tick_LMP cfg _ _
        ((E.latestMessageProvenance_of_observer_validity cfg ext hT.wellFormed
            p.node hvalid ⟨anchorState, anchorBlock, hgen⟩ p.previousSecond).mono_sl
          (E.slot_at_mono cfg (Nat.le_succ p.previousSecond)))
    · exact p.observerCausal_take cfg ext
  rwa [p.current_slot cfg ext]

end Execution

end FastConfirmation.Spec

end
