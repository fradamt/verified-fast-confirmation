module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Model.Execution
public import FastConfirmation.Spec.Model.PayloadEffects

@[expose] public section

/-!
# Spec / Model / AcceptedExecution

Exact, handler-derived reachability for one execution second's scheduled
event list.

This is intentionally narrower than a delayed-inbox or global-action replay:
`ScheduledEventPrefix` starts from the actual preceding `Execution.store`
boundary, ticks to the next second, and folds an exact left prefix of that
second's concrete schedule.  It cannot reorder, fabricate, or import events
from another node or second.  Rejected events leave the store unchanged, as
they do in `Execution.store`.

`AcceptedBlockTransition` contains only the exact next scheduled block event
and the successful handler result.  Its causal successor and root knownness
are theorems derived below from the fold and `on_block`; they are not public
semantic assumptions.  No freshness premise is imposed, so a successfully
processed duplicate root is an accepted transition too.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

/-! ## Exact per-second schedule prefixes -/

/-- An exact prefix of the events scheduled for `node` at relative second
`previousSecond + 1`. -/
structure ScheduledEventPrefix (E : Execution Root) where
  node : ValidatorIndex
  previousSecond : ℕ
  processedCount : ℕ
  count_le : processedCount ≤
    (E.schedule node (previousSecond + 1)).length

namespace ScheduledEventPrefix

variable {E : Execution Root}

/-- The concrete fork-choice store after an exact in-second event prefix. -/
def store (p : ScheduledEventPrefix E) : Store Root :=
  ((E.schedule p.node (p.previousSecond + 1)).take p.processedCount).foldl
    (fun store event => (apply_event cfg ext store event).getD store)
    (on_tick cfg (E.store cfg ext p.node p.previousSecond)
      (E.time_at (p.previousSecond + 1)))

/-- Two local prefixes are compatible when they observe the same node and
the same scheduled second.  Their natural-number prefix lengths are then
linearly ordered. -/
def Compatible (p q : ScheduledEventPrefix E) : Prop :=
  p.node = q.node ∧ p.previousSecond = q.previousSecond

/-- Extend an exact prefix by its concrete next scheduled event. -/
def successor (p : ScheduledEventPrefix E)
    (hnext : p.processedCount <
      (E.schedule p.node (p.previousSecond + 1)).length) :
    ScheduledEventPrefix E where
  node := p.node
  previousSecond := p.previousSecond
  processedCount := p.processedCount + 1
  count_le := hnext

/-- The successor prefix performs exactly one additional handler dispatch. -/
theorem successor_store (p : ScheduledEventPrefix E)
    (hnext : p.processedCount <
      (E.schedule p.node (p.previousSecond + 1)).length) :
    (p.successor hnext).store cfg ext =
      (apply_event cfg ext (p.store cfg ext)
        (E.schedule p.node (p.previousSecond + 1))[p.processedCount]
      ).getD (p.store cfg ext) := by
  rw [store, store]
  change
    List.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext p.node p.previousSecond)
          (E.time_at (p.previousSecond + 1)))
        (List.take (p.processedCount + 1)
          (E.schedule p.node (p.previousSecond + 1))) = _
  rw [← List.take_append_getElem hnext, List.foldl_append]
  rfl

end ScheduledEventPrefix

/-! ## Causal stores and accepted carriers -/

/-- A store in the exact per-second-prefix domain: either the trusted initial
store or a prefix whose predecessor is the actual execution boundary. -/
inductive CausalStore (E : Execution Root) : Store Root → Prop
  | genesis : CausalStore E E.genesis_store
  | scheduledPrefix (p : ScheduledEventPrefix E) :
      CausalStore E (p.store cfg ext)

/-- The causal stores at honest nodes inside the verification horizon. -/
inductive HonestCausalStore (E : Execution Root) : Store Root → Prop
  | genesis : E.honest.Nonempty → E.WithinHorizon cfg 0 →
      HonestCausalStore E E.genesis_store
  | scheduledPrefix (p : ScheduledEventPrefix E) :
      p.node ∈ E.honest → E.WithinHorizon cfg (p.previousSecond + 1) →
      HonestCausalStore E (p.store cfg ext)

theorem HonestCausalStore.causal {E : Execution Root} {store : Store Root}
    (h : HonestCausalStore cfg ext E store) : CausalStore cfg ext E store := by
  cases h with
  | genesis _ _ => exact .genesis
  | scheduledPrefix p _ _ => exact .scheduledPrefix p

/-- Only keyed block and checkpoint states of honest, in-horizon causal
stores enter the indexed-attestation coherence laws. Prepared states produced
by `process_slots` are related to this domain by a separate preservation law. -/
def ReachableValidationState (E : Execution Root) (state : BeaconState Root) : Prop :=
  ∃ store, HonestCausalStore cfg ext E store ∧
    ((∃ root ∈ store.block_roots, store.block_states root = state) ∨
      ∃ checkpoint ∈ store.checkpoint_state_keys,
        store.checkpoint_states checkpoint = state)

theorem HonestCausalStore.blockState {E : Execution Root} {store : Store Root}
    (h : HonestCausalStore cfg ext E store) {root : Root}
    (hroot : root ∈ store.block_roots) :
    ReachableValidationState cfg ext E (store.block_states root) :=
  ⟨store, h, Or.inl ⟨root, hroot, rfl⟩⟩

theorem HonestCausalStore.checkpointState {E : Execution Root} {store : Store Root}
    (h : HonestCausalStore cfg ext E store) {checkpoint : Checkpoint Root}
    (hcheckpoint : checkpoint ∈ store.checkpoint_state_keys) :
    ReachableValidationState cfg ext E (store.checkpoint_states checkpoint) :=
  ⟨store, h, Or.inr ⟨checkpoint, hcheckpoint, rfl⟩⟩

theorem honestCausalStore_store (E : Execution Root) (v : ValidatorIndex) (n : ℕ)
    (hv : v ∈ E.honest) (hn : E.WithinHorizon cfg n) :
    HonestCausalStore cfg ext E (E.store cfg ext v n) := by
  cases n with
  | zero => exact .genesis ⟨v, hv⟩ hn
  | succ n =>
    let p : ScheduledEventPrefix E :=
      { node := v
        previousSecond := n
        processedCount := (E.schedule v (n + 1)).length
        count_le := le_rfl }
    have hp : p.store cfg ext = E.store cfg ext v (n + 1) := by
      simp [p, ScheduledEventPrefix.store, Execution.store]
    rw [← hp]
    exact .scheduledPrefix p hv hn

/-- An exact left part of an honest node's in-horizon schedule is in the
validation domain, including the empty prefix after the tick. -/
theorem honestCausalStore_prefix (E : Execution Root) (v : ValidatorIndex)
    (hv : v ∈ E.honest) (n : ℕ) (hn : E.WithinHorizon cfg (n + 1))
    (pre rest : List (Event Root)) (hl : E.schedule v (n + 1) = pre ++ rest) :
    HonestCausalStore cfg ext E
      (pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1)))) := by
  let p : ScheduledEventPrefix E :=
    { node := v
      previousSecond := n
      processedCount := pre.length
      count_le := by rw [hl, List.length_append]; omega }
  have hp : p.store cfg ext =
      pre.foldl (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) := by
    simp [p, ScheduledEventPrefix.store, hl]
  rw [← hp]
  exact .scheduledPrefix p hv hn

/-- Every ordinary execution boundary is represented by the exact-prefix
causal domain. -/
theorem store_causal (E : Execution Root) (v : ValidatorIndex) (n : ℕ) :
    CausalStore cfg ext E (E.store cfg ext v n) := by
  cases n with
  | zero => exact .genesis
  | succ n =>
      let p : ScheduledEventPrefix E :=
        { node := v
          previousSecond := n
          processedCount := (E.schedule v (n + 1)).length
          count_le := le_rfl }
      have hp : p.store cfg ext = E.store cfg ext v (n + 1) := by
        simp [p, ScheduledEventPrefix.store, Execution.store]
      rw [← hp]
      exact .scheduledPrefix p

/-- A root is accepted exactly when it is known in a causal prefix store.
Schedule membership alone is insufficient. -/
def AcceptedRoot (E : Execution Root) (r : Root) : Prop :=
  ∃ store : Store Root, CausalStore cfg ext E store ∧
    r ∈ store.block_roots

/-- The concrete block message carried by an accepted root in a causal
prefix. -/
def AcceptedBlockAt (E : Execution Root) (r : Root)
    (b : BeaconBlock Root) : Prop :=
  ∃ store : Store Root, CausalStore cfg ext E store ∧
    r ∈ store.block_roots ∧ store.blocks r = b

theorem acceptedRoot_of_causal_known {E : Execution Root}
    {store : Store Root} (hstore : CausalStore cfg ext E store)
    {r : Root} (hr : r ∈ store.block_roots) :
    AcceptedRoot cfg ext E r :=
  ⟨store, hstore, hr⟩

theorem acceptedBlockAt_of_causal_known {E : Execution Root}
    {store : Store Root} (hstore : CausalStore cfg ext E store)
    {r : Root} (hr : r ∈ store.block_roots) :
    AcceptedBlockAt cfg ext E r (store.blocks r) :=
  ⟨store, hstore, hr, rfl⟩

theorem acceptedRoot_of_store_known (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) {r : Root}
    (hr : r ∈ (E.store cfg ext v n).block_roots) :
    AcceptedRoot cfg ext E r :=
  acceptedRoot_of_causal_known cfg ext (E.store_causal cfg ext v n) hr

theorem acceptedBlockAt_of_store_known (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) {r : Root}
    (hr : r ∈ (E.store cfg ext v n).block_roots) :
    AcceptedBlockAt cfg ext E r ((E.store cfg ext v n).blocks r) :=
  acceptedBlockAt_of_causal_known cfg ext (E.store_causal cfg ext v n) hr

/-! ## Accepted block-handler transitions -/

/-- One successful `on_block` call at the exact next position of a causal
schedule prefix.  Causality and root knownness are deliberately absent from
the fields and derived below. -/
structure AcceptedBlockTransition (E : Execution Root) where
  atPrefix : ScheduledEventPrefix E
  signedBlock : SignedBeaconBlock Root
  event_at :
    (E.schedule atPrefix.node
      (atPrefix.previousSecond + 1))[atPrefix.processedCount]? =
      some (.block signedBlock)
  postStore : Store Root
  accepted :
    on_block cfg ext (atPrefix.store cfg ext) signedBlock = some postStore

namespace AcceptedBlockTransition

variable {E : Execution Root}

/-- The exact next-event equation implies that the prefix has a successor. -/
theorem processedCount_lt (t : AcceptedBlockTransition cfg ext E) :
    t.atPrefix.processedCount <
      (E.schedule t.atPrefix.node
        (t.atPrefix.previousSecond + 1)).length := by
  exact (List.getElem?_eq_some_iff.mp t.event_at).choose

/-- The concrete exact prefix immediately after the accepted block event. -/
def successorPrefix (t : AcceptedBlockTransition cfg ext E) :
    ScheduledEventPrefix E :=
  t.atPrefix.successor t.processedCount_lt

/-- The successful handler result is definitionally the successor-prefix
fold result. -/
theorem successorPrefix_store (t : AcceptedBlockTransition cfg ext E) :
    t.successorPrefix.store cfg ext = t.postStore := by
  rw [successorPrefix, ScheduledEventPrefix.successor_store]
  have hevent :
      (E.schedule t.atPrefix.node
        (t.atPrefix.previousSecond + 1))[t.atPrefix.processedCount]'
          t.processedCount_lt =
        .block t.signedBlock :=
    (List.getElem?_eq_some_iff.mp t.event_at).choose_spec
  rw [hevent]
  simp [apply_event, t.accepted]

/-- The block domain and state map needed by accepted-transition inversion. -/
private def retainedBlockFields (store : Store Root) :=
  (store.block_roots, store.block_states)

private theorem update_checkpoints_retainedBlockFields (store : Store Root)
    (justified finalized : Checkpoint Root) :
    retainedBlockFields (update_checkpoints store justified finalized) =
      retainedBlockFields store := by
  simp only [update_checkpoints]
  split_ifs <;> rfl

private theorem update_unrealized_checkpoints_retainedBlockFields (store : Store Root)
    (justified finalized : Checkpoint Root) :
    retainedBlockFields (update_unrealized_checkpoints store justified finalized) =
      retainedBlockFields store := by
  simp only [update_unrealized_checkpoints]
  split_ifs <;> rfl

private theorem update_proposer_boost_root_retainedBlockFields (store : Store Root)
    (head root : Root) :
    retainedBlockFields (update_proposer_boost_root cfg store head root) =
      retainedBlockFields store := by
  simp only [update_proposer_boost_root]
  split_ifs <;> rfl

private theorem compute_pulled_up_tip_retainedBlockFields (store : Store Root)
    (root : Root) :
    retainedBlockFields (compute_pulled_up_tip cfg ext store root) =
      retainedBlockFields store := by
  simp only [compute_pulled_up_tip]
  split_ifs
  · rw [update_checkpoints_retainedBlockFields,
      update_unrealized_checkpoints_retainedBlockFields] <;> rfl
  · rw [update_unrealized_checkpoints_retainedBlockFields] <;> rfl

/-- Inversion of the Gloas fresh-block path. PTC processing preserves the
block domain and the installed state before checkpoint updates. -/
private theorem on_block_fresh_effects
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots)
    (hh : on_block cfg ext store sb = some store') :
    sb.root ∈ store'.block_roots ∧
      ∃ post : BeaconState Root,
        ext.state_transition (store.block_states sb.message.parent_root) sb = some post ∧
        store'.block_states sb.root = post := by
  simp only [on_block, hfresh] at hh
  split_ifs at hh <;> try contradiction
  cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
  | none => rw [hst] at hh; cases hh
  | some post =>
    rw [hst] at hh
    let added : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => none
      | some notified => some (compute_pulled_up_tip cfg ext
          (update_checkpoints
            (update_proposer_boost_root cfg
              (record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
        some store' at hh
    cases hn : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      let finished := compute_pulled_up_tip cfg ext
        (update_checkpoints
          (update_proposer_boost_root cfg
            (record_block_timeliness cfg notified sb.root)
            (get_head cfg store).root sb.root)
          post.current_justified_checkpoint post.finalized_checkpoint) sb.root
      have heq : finished = store' := Option.some.inj hh
      have hframe := notify_ptc_messages_frame cfg ext hn
      have hroots : sb.root ∈ notified.block_roots := by
        rw [hframe.block_roots]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hstate : notified.block_states sb.root = post := by
        rw [hframe.block_states]
        exact Function.update_self _ _ _
      have hfields : retainedBlockFields finished = retainedBlockFields notified := by
        dsimp only [finished]
        rw [compute_pulled_up_tip_retainedBlockFields,
          update_checkpoints_retainedBlockFields,
          update_proposer_boost_root_retainedBlockFields] <;> rfl
      have hfinalRoots : finished.block_roots = notified.block_roots :=
        congrArg (a₁ := retainedBlockFields finished)
          (a₂ := retainedBlockFields notified) Prod.fst hfields
      have hfinalStates : finished.block_states = notified.block_states :=
        congrArg (a₁ := retainedBlockFields finished)
          (a₂ := retainedBlockFields notified) Prod.snd hfields
      constructor
      · have hfinished : sb.root ∈ finished.block_roots := by
          rw [hfinalRoots]
          exact hroots
        exact heq ▸ hfinished
      · refine ⟨post, rfl, ?_⟩
        have hfinished : finished.block_states sb.root = post :=
          (congrFun hfinalStates sb.root).trans hstate
        exact heq ▸ hfinished

/-- A successful Gloas block call leaves its root in the finite block domain.
A duplicate root is a no-op; a fresh root is installed before PTC processing. -/
theorem on_block_root_known
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store') :
    sb.root ∈ store'.block_roots := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact hknown
  · exact (on_block_fresh_effects cfg ext hknown hh).1

/-- A successful fresh Gloas block call installs the opaque transition state. -/
theorem on_block_inserted_state_fresh
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots)
    (hh : on_block cfg ext store sb = some store') :
    ∃ post : BeaconState Root,
      ext.state_transition (store.block_states sb.message.parent_root) sb =
          some post ∧
        store'.block_states sb.root = post :=
  (on_block_fresh_effects cfg ext hfresh hh).2

/-- Mechanical handler inversion: either a known root is a no-op, or a fresh
root installs exactly the opaque transition result. -/
theorem on_block_inserted_state
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store') :
    (sb.root ∈ store.block_roots ∧ store' = store) ∨
      ∃ post : BeaconState Root,
        ext.state_transition (store.block_states sb.message.parent_root) sb =
            some post ∧
          store'.block_states sb.root = post := by
  by_cases hknown : sb.root ∈ store.block_roots
  · left
    simp [on_block, hknown] at hh
    exact ⟨hknown, hh.symm⟩
  · exact Or.inr (on_block_inserted_state_fresh cfg ext hknown hh)

/-- The accepted result is a causal exact successor prefix. -/
theorem post_causal (t : AcceptedBlockTransition cfg ext E) :
    CausalStore cfg ext E t.postStore := by
  rw [← t.successorPrefix_store]
  exact .scheduledPrefix t.successorPrefix

/-- Root knownness is derived from the successful handler, not supplied by
the accepted-transition constructor. -/
theorem root_known (t : AcceptedBlockTransition cfg ext E) :
    t.signedBlock.root ∈ t.postStore.block_roots :=
  on_block_root_known cfg ext t.accepted

/-- Every accepted block transition contributes an accepted root. -/
theorem root_accepted (t : AcceptedBlockTransition cfg ext E) :
    AcceptedRoot cfg ext E t.signedBlock.root :=
  ⟨t.postStore, t.post_causal, t.root_known⟩

end AcceptedBlockTransition

end Execution

end FastConfirmation.Spec

end
