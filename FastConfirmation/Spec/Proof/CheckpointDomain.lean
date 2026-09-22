module
public import FastConfirmation.Spec.Proof.Registry

@[expose] public section

/-!
# Spec / Proof / CheckpointDomain: exactness of the totalized checkpoint map

The executable store represents Python's partial `checkpoint_states` dictionary
by a total function together with the finite set `checkpoint_state_keys`.  The
trajectory starts with `default` outside the singleton key set, and the only
handler that writes the function (`store_target_checkpoint_state`) inserts the
same key at the same time.  Consequently every reachable store still returns
`default` outside its advertised domain.

This is a trajectory invariant, not an assumption.  In particular it prevents
an unkeyed checkpoint from supplying arbitrary validator balances through the
totalized function.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [Inhabited Root]

/-- The totalized checkpoint-state map is `default` outside its explicit key
set.  This is the faithful finite-map invariant for `checkpoint_states`. -/
def CheckpointStatesExact (store : Store Root) : Prop :=
  ∀ c : Checkpoint Root, c ∉ store.checkpoint_state_keys →
    store.checkpoint_states c = default

namespace CheckpointStatesExact

/-- Transfer exactness across an update that preserves the key set and map. -/
theorem of_eq {store store' : Store Root} (h : CheckpointStatesExact store)
    (hkeys : store'.checkpoint_state_keys = store.checkpoint_state_keys)
    (hstates : store'.checkpoint_states = store.checkpoint_states) :
    CheckpointStatesExact store' := by
  unfold CheckpointStatesExact at h ⊢
  intro c hc
  rw [hkeys] at hc
  rw [hstates]
  exact h c hc

end CheckpointStatesExact

variable [LinearOrder Root]
variable (cfg : Config) (ext : Externals Root)

/-- Caching a checkpoint preserves exactness: the map update and key insertion
have the same target. -/
theorem store_target_checkpoint_state_exact {store : Store Root}
    (target : Checkpoint Root) (h : CheckpointStatesExact store) :
    CheckpointStatesExact (store_target_checkpoint_state cfg ext store target) := by
  simp only [store_target_checkpoint_state]
  split_ifs with hnew hslot
  all_goals
    first
    | exact h
    | · unfold CheckpointStatesExact at h ⊢
        intro c hc
        have hct : c ≠ target := by
          intro heq
          subst heq
          exact hc (Finset.mem_insert_self _ _)
        have hcold : c ∉ store.checkpoint_state_keys := by
          intro hmem
          exact hc (Finset.mem_insert_of_mem hmem)
        simp only [Function.update_apply]
        split_ifs with heq
        · exact absurd heq hct
        · exact h c hcold

omit [LinearOrder Root] in
/-- Updating latest messages does not touch the checkpoint dictionary. -/
theorem update_latest_messages_exact {store : Store Root}
    (indices : List ValidatorIndex) (a : Attestation Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (update_latest_messages store indices a) := by
  simp only [update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;> exact h.of_eq rfl rfl

omit [LinearOrder Root] in
/-- The checkpoint-only helpers preserve the checkpoint-map domain exactly. -/
theorem update_checkpoints_exact {store : Store Root} (jc fc : Checkpoint Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (update_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp)

omit [LinearOrder Root] in
theorem update_unrealized_checkpoints_exact {store : Store Root}
    (jc fc : Checkpoint Root) (h : CheckpointStatesExact store) :
    CheckpointStatesExact (update_unrealized_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp)

theorem record_block_timeliness_exact {store : Store Root} (r : Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (record_block_timeliness cfg store r) :=
  h.of_eq rfl rfl

theorem update_proposer_boost_root_exact {store : Store Root} (head r : Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (update_proposer_boost_root cfg store head r) := by
  refine h.of_eq ?_ ?_ <;>
    (simp only [update_proposer_boost_root]; split_ifs <;> rfl)

theorem compute_pulled_up_tip_exact {store : Store Root} (r : Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (compute_pulled_up_tip cfg ext store r) := by
  refine h.of_eq ?_ ?_ <;>
    (simp only [compute_pulled_up_tip]; split_ifs <;> simp)

/-- A successful attestation handler preserves checkpoint-map exactness. -/
theorem on_attestation_exact {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    (h : CheckpointStatesExact store)
    (hh : on_attestation cfg ext store a is_from_block = some store') :
    CheckpointStatesExact store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvalid
  cases hh
  exact update_latest_messages_exact _ _
    (store_target_checkpoint_state_exact cfg ext a.data.target h)

/-- A successful block handler preserves checkpoint-map exactness. -/
theorem on_block_exact {store store' : Store Root} {b : SignedBeaconBlock Root}
    (h : CheckpointStatesExact store)
    (hh : on_block cfg ext store b = some store') :
    CheckpointStatesExact store' := by
  by_cases hknown : b.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states b.message.parent_root) b with
    | none => rw [hst] at hh; cases hh
    | some state =>
        rw [hst] at hh
        cases hh
        apply compute_pulled_up_tip_exact cfg ext
        apply update_checkpoints_exact
        apply update_proposer_boost_root_exact
        apply record_block_timeliness_exact
        exact h.of_eq rfl rfl

/-- A successful slashing handler preserves checkpoint-map exactness. -/
theorem on_attester_slashing_exact {store store' : Store Root}
    {sl : AttesterSlashing Root} (h : CheckpointStatesExact store)
    (hh : on_attester_slashing ext store sl = some store') :
    CheckpointStatesExact store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl

omit [LinearOrder Root] in
/-- Slot ticking preserves checkpoint-map exactness. -/
theorem on_tick_per_slot_exact (store : Store Root) (time : ℕ)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (on_tick_per_slot cfg store time) := by
  simp only [on_tick_per_slot]
  split_ifs <;>
    first
    | exact h.of_eq rfl rfl
    | exact update_checkpoints_exact _ _ (h.of_eq rfl rfl)

omit [LinearOrder Root] in
theorem on_tick_aux_exact (tick_slot fuel : ℕ) :
    ∀ store : Store Root, CheckpointStatesExact store →
      CheckpointStatesExact (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro store h; exact h
  | succ fuel ih =>
      intro store h
      rw [on_tick_aux]
      split_ifs
      · exact ih _ (on_tick_per_slot_exact cfg _ _ h)
      · exact h

omit [LinearOrder Root] in
theorem on_tick_exact (store : Store Root) (time : ℕ)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_exact cfg _ _
    (on_tick_aux_exact cfg _ _ _ h)

/-- One event, with rejection interpreted as no state change, preserves
checkpoint-map exactness. -/
theorem apply_event_getD_exact (store : Store Root) (event : Event Root)
    (h : CheckpointStatesExact store) :
    CheckpointStatesExact ((apply_event cfg ext store event).getD store) := by
  cases heq : apply_event cfg ext store event with
  | none => simpa using h
  | some store' =>
      simp only [Option.getD_some]
      cases event with
      | block b => exact on_block_exact cfg ext h heq
      | attestation a ifb => exact on_attestation_exact cfg ext h heq
      | attester_slashing sl => exact on_attester_slashing_exact ext h heq

/-- The trusted-anchor initialization has an exact singleton checkpoint map. -/
theorem get_forkchoice_store_checkpointStatesExact
    (ast : BeaconState Root) (ablk : SignedBeaconBlock Root) :
    CheckpointStatesExact (get_forkchoice_store cfg ast ablk) := by
  unfold CheckpointStatesExact
  intro c hc
  simp only [get_forkchoice_store, Finset.mem_singleton] at hc ⊢
  simp [hc]

namespace Execution

omit [LinearOrder Root] in
/-- Folding exactness-preserving store updates preserves exactness. -/
private theorem exact_foldl {Alpha : Type*} {f : Store Root → Alpha → Store Root}
    (hf : ∀ store a, CheckpointStatesExact store → CheckpointStatesExact (f store a)) :
    ∀ (l : List Alpha) (store : Store Root), CheckpointStatesExact store →
      CheckpointStatesExact (l.foldl f store) := by
  intro l
  induction l with
  | nil => intro store h; exact h
  | cons a rest ih =>
      intro store h
      rw [List.foldl_cons]
      exact ih _ (hf store a h)

/-- Every reachable execution store has an exact checkpoint-state map. -/
theorem checkpointStatesExact (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    CheckpointStatesExact (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgeq⟩ := hgen
  induction n with
  | zero =>
      change CheckpointStatesExact E.genesis_store
      rw [hgeq]
      exact get_forkchoice_store_checkpointStatesExact cfg ast ablk
  | succ n ih =>
      change CheckpointStatesExact
        ((E.schedule v (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
      apply exact_foldl
        (fun store event hs => apply_event_getD_exact cfg ext store event hs)
      exact on_tick_exact cfg _ _ ih

/-- An unkeyed checkpoint state is the default state, whose validator list is
empty and whose attestation score is therefore zero. -/
theorem get_attestation_score_unkeyed_eq_zero (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (c : Checkpoint Root)
    (hc : c ∉ (E.store cfg ext v n).checkpoint_state_keys)
    (node : ForkChoiceNode Root) :
    get_attestation_score cfg (E.store cfg ext v n) node
        ((E.store cfg ext v n).checkpoint_states c) = 0 := by
  rw [E.checkpointStatesExact cfg ext hgen v n c hc]
  have hvalidators : (default : BeaconState Root).validators = [] := rfl
  have hactive : get_active_validator_indices (default : BeaconState Root)
      (get_current_epoch cfg (default : BeaconState Root)) = [] := by
    unfold get_active_validator_indices
    rw [hvalidators]
    rfl
  simp only [get_attestation_score]
  rw [hactive]
  rfl

/-- Any checkpoint state that witnesses a successful `is_one_confirmed` call
must be in the executable store's checkpoint-state dictionary.  Otherwise its
score is zero, contradicting the strict confirmation inequality. -/
theorem checkpoint_state_key_of_one_confirmed (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (c : Checkpoint Root) (b : Root)
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n)
      ((E.store cfg ext v n).checkpoint_states c) b = true) :
    c ∈ (E.store cfg ext v n).checkpoint_state_keys := by
  by_contra hc
  simp only [is_one_confirmed, gt_iff_lt, decide_eq_true_eq] at hconf
  rw [E.get_attestation_score_unkeyed_eq_zero cfg ext hgen v n c hc] at hconf
  exact (Nat.not_lt_zero _ hconf).elim

end Execution

end FastConfirmation.Spec

end
