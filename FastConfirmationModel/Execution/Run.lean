module
public import FastConfirmationModel.Spec.Validator.Attesting
public import FastConfirmationModel.Spec.FastConfirmation.Rule

@[expose] public section

/-!
# Spec / Model / Execution

Defines each node's scheduled store run and its once-per-slot FCR update. Python: `specs/gloas/fork-choice.md`, Handlers; `specs/gloas/fast-confirmation.md`, `on_fast_confirmation`.

Store evolution over time. Time is discrete seconds (the spec's own
`store.time` granularity), counted relative to the genesis store's initial
time; nodes are identified with validators (as in the paper model). A
`Schedule` says which wire messages each node processes at each second; the
per-node store trajectory is *defined* by folding the fork-choice handlers
(`on_tick`, then the second's events, a rejected event leaving the store
unchanged), and the FCR trajectory applies `on_fast_confirmation` at the first
second of each slot — inside the handler's mandated once-per-slot window,
after that second's (past-slot, under synchrony) attestations. See
`docs/MODELING_CHOICES.md`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Sources: `specs/gloas/fork-choice.md:1020`, `:1089`, and `:1115`;
`specs/phase0/fork-choice.md:1000` and `:1027`.
A wire message a node can process: a block (`on_block`), an attestation
(`on_attestation`, with its `is_from_block` flag), or an attester slashing
(`on_attester_slashing`), an execution envelope with its local observation, or
an individual PTC message with its block-origin flag. -/
inductive Event (Root : Type*) where
  | block (signed_block : SignedBeaconBlock Root)
  | attestation (attestation : Attestation Root) (is_from_block : Bool)
  | attester_slashing (attester_slashing : AttesterSlashing Root)
  | execution_payload_envelope (signed_envelope : SignedExecutionPayloadEnvelope Root)
      (observation : EnvelopeObservation Root)
  | payload_attestation_message (ptc_message : PayloadAttestationMessage Root)
      (is_from_block : Bool)

/-- Sources: `specs/gloas/fork-choice.md:1020`, `:1089`, and `:1115`;
`specs/phase0/fork-choice.md:1000` and `:1027`.
Dispatch one wire message to its handler (`none` = the handler rejected
it — a python assert failed / `state_transition` raised). -/
def apply_event (store : Store Root) : Event Root → Option (Store Root)
  | .block signed_block => on_block cfg ext store signed_block
  | .attestation attestation is_from_block =>
      on_attestation cfg ext store attestation is_from_block
  | .attester_slashing attester_slashing =>
      on_attester_slashing ext store attester_slashing
  | .execution_payload_envelope signed_envelope observation =>
      on_execution_payload_envelope ext store signed_envelope observation
  | .payload_attestation_message ptc_message is_from_block =>
      on_payload_attestation_message cfg ext store ptc_message is_from_block

/-- An execution of the protocol: the shared trusted starting store, the
per-node message schedule, the honest-node set, the ground-truth committee
assignment (state-independent within the spec's own `MAX_SEED_LOOKAHEAD`
consistency window — see `Assumptions.lean`), and the record of the
attestation each validator casts for its per-slot assignment (`vote v s =
some (n, a)`: validator `v` cast `a` at second `n` for slot `s`; what honest
validators' votes look like is `HonestBehavior`'s business, when they arrive
is `Synchrony`'s). -/
structure Execution (Root : Type*) where
  /-- Exclusive epoch bound of the concrete execution segment being verified.
  The source specification uses `uint64` time and `FAR_FUTURE_EPOCH`; the Lean
  execution clock is `ℕ`, so the meaningful finite segment is recorded
  explicitly rather than postulating that an unbounded clock never reaches a
  finite sentinel. Public guarantees are stated only at endpoints below this
  horizon. -/
  verification_horizon : Epoch
  genesis_store : Store Root
  schedule : ValidatorIndex → ℕ → List (Event Root)
  honest : Finset ValidatorIndex
  committee : Slot → Finset ValidatorIndex
  vote : ValidatorIndex → Slot → Option (ℕ × Attestation Root)

namespace Execution

variable (E : Execution Root)

/-- Absolute wall-clock time (seconds) at relative second `n`. -/
def time_at (n : ℕ) : ℕ :=
  E.genesis_store.time + n

/-- The slot the wall clock is in at relative second `n` (the
`get_current_slot` arithmetic applied to `time_at`). -/
def slot_at (n : ℕ) : Slot :=
  GENESIS_SLOT + (E.time_at n - E.genesis_store.genesis_time) * 1000 / cfg.slot_duration_ms

/-- A relative second belongs to the finite execution segment whose validator
set and protocol assumptions are being verified. -/
def WithinHorizon (n : ℕ) : Prop :=
  E.time_at n ≤ UINT64_MAX ∧
    E.slot_at cfg n ≤ UINT64_MAX ∧
    compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon

/-- Slot-level form of `WithinHorizon`, used by committee and vote premises. -/
def SlotWithinHorizon (s : Slot) : Prop :=
  s ≤ UINT64_MAX ∧ compute_epoch_at_slot cfg s < E.verification_horizon

/-- The relative second at which slot `s` starts (exact when
`1000 ∣ slot_duration_ms` — mainnet 12000ms; an execution well-formedness
assumption). Truncates to `0` for slots before the genesis store's time. -/
def slot_start (s : Slot) : ℕ :=
  E.genesis_store.genesis_time + s * cfg.slot_duration_ms / 1000 - E.genesis_store.time

/-- Node `v`'s store at relative second `n`: tick to the current time, then
process the second's scheduled events left-to-right, a rejected event
(`none`) leaving the store unchanged (the spec's "delay consideration" —
under synchrony, honest messages are scheduled where they apply). -/
def store (v : ValidatorIndex) : ℕ → Store Root
  | 0 => E.genesis_store
  | n + 1 =>
    let ticked := on_tick cfg (store v n) (E.time_at (n + 1))
    (E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store) ticked

/-- Node `v`'s fast-confirmation store at relative second `n`: the read-only
`store` snapshot tracks `E.store v n`, and `on_fast_confirmation` runs at the
first second of each slot (detected as the slot advancing), after that
second's events — the handler's mandated call discipline (once per slot, in
the first part of the slot, after past-slot attestations have been applied). -/
def fcr (v : ValidatorIndex) : ℕ → FastConfirmationStore Root
  | 0 => get_fast_confirmation_store (E.store cfg ext v 0)
  | n + 1 =>
    let fcr_store := { fcr v n with store := E.store cfg ext v (n + 1) }
    if get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) then
      on_fast_confirmation cfg ext fcr_store
    else fcr_store

/-- Node `v`'s confirmed block root at relative second `n`. -/
def confirmed (v : ValidatorIndex) (n : ℕ) : Root :=
  (E.fcr cfg ext v n).confirmed_root

end Execution

/-- Core structural invariants of a fork-choice store. The trusted-anchor
store satisfies them and the handlers preserve them. They delimit the domain
on which totalized maps and fuel-bounded traversals represent the Python
specification. -/
structure WellFormedStore (store : Store Root) : Prop where
  /-- python dict keys are pairwise distinct. -/
  block_roots_nodup : store.block_roots.Nodup
  /-- the store clock never precedes genesis. -/
  time_ge_genesis : store.genesis_time ≤ store.time
  /-- parent pointers strictly decrease slots (within the store). -/
  parent_slot_lt : ∀ r ∈ store.block_roots,
    (store.blocks r).parent_root ∈ store.block_roots →
      (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot
  /-- block states sit at their block's slot (`on_block` stores the
      transition's post-state; `state_transition_slot` keeps them aligned). -/
  block_state_slot_eq : ∀ r ∈ store.block_roots,
    (store.block_states r).slot = (store.blocks r).slot
  /-- the justified checkpoint's block is known. -/
  justified_known : store.justified_checkpoint.root ∈ store.block_roots
  /-- the finalized checkpoint's block is known. -/
  finalized_known : store.finalized_checkpoint.root ∈ store.block_roots
  /-- the finalized block is on the justified block's chain (true of
      `get_forkchoice_store`'s output, where both are the anchor). NOT a raw
      handler invariant — `update_checkpoints`' two guards are independent —
      so along trajectories the general fact is the *FFG export*
      `JustificationInterface.finalized_justified_ancestry`; this field is
      consumed only at the genesis store (the `n = 0` base of safety). -/
  finalized_ancestor_of_justified :
    is_ancestor store (ForkChoiceNode.mk store.justified_checkpoint.root .pending)
      (ForkChoiceNode.mk store.finalized_checkpoint.root .pending) = true

end FastConfirmation.Spec

end
