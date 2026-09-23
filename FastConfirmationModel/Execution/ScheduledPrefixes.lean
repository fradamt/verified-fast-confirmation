module
public import Mathlib.Tactic
public import FastConfirmationModel.Execution.Run
public import FastConfirmationModel.Execution.PayloadFrame

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


/-- Extend an exact prefix by its concrete next scheduled event. -/
def successor (p : ScheduledEventPrefix E)
    (hnext : p.processedCount <
      (E.schedule p.node (p.previousSecond + 1)).length) :
    ScheduledEventPrefix E where
  node := p.node
  previousSecond := p.previousSecond
  processedCount := p.processedCount + 1
  count_le := hnext

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

/-- Only keyed block and checkpoint states of honest, in-horizon causal
stores enter the indexed-attestation coherence laws. Prepared states produced
by `process_slots` are related to this domain by a separate preservation law. -/
def ReachableValidationState (E : Execution Root) (state : BeaconState Root) : Prop :=
  ∃ store, HonestCausalStore cfg ext E store ∧
    ((∃ root ∈ store.block_roots, store.block_states root = state) ∨
      ∃ checkpoint ∈ store.checkpoint_state_keys,
        store.checkpoint_states checkpoint = state)

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

end AcceptedBlockTransition

end Execution

end FastConfirmation.Spec

end
