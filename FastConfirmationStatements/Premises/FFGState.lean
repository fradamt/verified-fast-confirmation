module
public import FastConfirmationStatements.Premises.FFGCertificates
public import FastConfirmationModel.Execution.ScheduledPrefixes

@[expose] public section

/-!
Defines paper Assumption 3.2 over a checkpoint inclusion view. A view names
the carrier blocks, the attestations in each block body, the formed
checkpoints of each block, the checkpoint selector `C(b, e)`, and the
realized and unrealized justified checkpoints. `AvailableCheckpoint` names
the checkpoints with formed evidence at a tip: a checkpoint is available at a
tip when a carrier block on the tip's chain has formed it.

`EventualCheckpointInclusion` is the paper's separate liveness assumption.
Its antecedent is the paper's link-specific support condition in every honest
view throughout epoch `e+1`. Its conclusion is available-checkpoint inclusion
in a concrete descendant: of `C(b, e)` itself, or of a later checkpoint that
extends it (`AvailableCheckpointOrExtension`). This is stronger than the
epoch-only consequence read by `get_voting_source`.

None of these declarations assumes that a block is canonical, safe, retained
by the filter, or selected by the FCR. Canonicality appears only as an
antecedent of Assumption 3.2.

Paper references use arXiv:2405.00549v4 (https://arxiv.org/abs/2405.00549v4).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- Canonicity throughout one execution epoch.  This is used only as an
antecedent of the paper's Assumption 3.2. -/
def CanonicalThroughoutEpoch (b : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    compute_epoch_at_slot cfg (E.slot_at cfg m) = e →
    b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true

end Execution

/-- An attestation occurs in a block on `tip`'s concrete execution chain. -/
def AttestationIncludedOnChain (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (tip : Root) (a : Attestation Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ included carrier a

/-- A wire attestation has reached validator `w`'s execution view by second
`m`.  The schedule is the model's received-message history; validity and
link identity are recorded by the support certificate below. -/
def Execution.AttestationReceivedBy
    (E : Execution Root) (w : ValidatorIndex) (m : ℕ)
    (a : Attestation Root) : Prop :=
  ∃ k ≤ m, ∃ fromBlock : Bool,
    Event.attestation a fromBlock ∈ E.schedule w k

/-- The positive state ingredients used by paper Assumption 3.2.

`Included carrier a` states that the attestation `a` is in the body of the
block `carrier`. It defines `D_b`, the block-local slashing set. AU is derived
below from the relation `formed`. The view is stated for one configuration
`cfg`. -/
structure CheckpointInclusionView (cfg : Config) (E : Execution Root) where
  /-- Carrier domain for the block whose canonicality triggers A.3.2. -/
  BlockAt : Root → BeaconBlock Root → Prop
  Included : Root → Attestation Root → Prop
  formed : Root → Checkpoint Root → Prop
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (C r e).epoch = e

namespace CheckpointInclusionView

variable {E : Execution Root}

/-- AU ("available or unrealized") membership inherited from a formed carrier
on the tip's chain. -/
def AvailableCheckpoint (V : CheckpointInclusionView cfg E)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ V.formed carrier c

/-- The conclusion of Assumption 3.2 at one descendant `tip`: the checkpoint
`c` is in AU at `tip`, or a checkpoint `J` of a later epoch is in AU at `tip`
and the block of `J` descends from (or equals) the block of `c`.

The second case covers one Python justification pass that justifies the
epochs `e` and `e+1` together. The state then carries only the epoch-`e+1`
checkpoint, and no carried selector holds `C(b, e)`. A later checkpoint that
extends `C(b, e)` gives the same epoch bound for `get_voting_source`. -/
def AvailableCheckpointOrExtension (V : CheckpointInclusionView cfg E)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  V.AvailableCheckpoint cfg tip c ∨
    ∃ J : Checkpoint Root, c.epoch < J.epoch ∧ E.RootDescends J.root c.root ∧
      V.AvailableCheckpoint cfg tip J

/-- The concrete block-body equivocation predicate underlying `D_b`. -/
def HasSlashablePairOnChain (V : CheckpointInclusionView cfg E)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    AttestationIncludedOnChain E V.Included tip a₁ ∧
    AttestationIncludedOnChain E V.Included tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

/-- `D_b`, computed from actual included attestation payloads. -/
noncomputable def slashableOnChain (V : CheckpointInclusionView cfg E)
    (tip : Root) : Finset ValidatorIndex := by
  classical
  exact (Finset.range E.registry.length).filter
    (V.HasSlashablePairOnChain cfg tip)

/-- The paper's source selector `vs(b,e)`, expressed through the block-local
AU selectors and a reachable store's exact block epoch.

Definition 7 only defines this selector when the block epoch is at most `e`.
Callers representing paper statements therefore carry that domain fact
explicitly; this executable helper remains total for internal phase0 lemmas
which already establish the same/current-or-earlier dichotomy. -/
def voting_source_at (V : CheckpointInclusionView cfg E) (store : Store Root)
    (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then V.GJ b else V.GU b

end CheckpointInclusionView

/-- The exact link-specific support term in Assumption 3.2 at one honest
view/time/descendant.

`signers` are validators whose received valid FFG attestations name precisely
`source → target`, after removing the block-local slashable set `D_b'`.
The static-validator-set premise used by the public theorem identifies the
paper's `W_t^{b'}` with `E.total_active`; this record deliberately does not
replace a source-specific link by target-only LMD support. -/
structure SourceTargetLinkSupportAt
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (w : ValidatorIndex) (m : ℕ) (b' : Root)
    (source target : Checkpoint Root) : Type where
  view_within_horizon : E.WithinHorizon cfg m
  source_before_target : source.epoch < target.epoch
  target_epoch_within : target.epoch < E.verification_horizon
  target_known : target.root ∈ (E.store cfg ext w m).block_roots
  target_state_keyed :
    target ∈ (E.store cfg ext w m).checkpoint_state_keys
  signers : Finset ValidatorIndex
  signers_not_slashable : ∀ i ∈ signers,
    i ∉ V.slashableOnChain cfg b'
  signers_in_registry : signers ⊆ Finset.range E.registry.length
  signer_attestation : ∀ i ∈ signers,
    ∃ a : Attestation Root,
      E.AttestationReceivedBy w m a ∧
      i ∈ a.attesting_indices ∧
      ext.is_valid_indexed_attestation
        ((E.store cfg ext w m).checkpoint_states target) a = true ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      a.data.slot ≤ E.slot_at cfg m ∧
      compute_epoch_at_slot cfg a.data.slot = target.epoch ∧
      i ∈ E.committee a.data.slot ∧
      CheckpointReadsAs a.data.source source ∧
      a.data.target = target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers

/-- Assumption 3.2's support premise throughout epoch `e+1`: every honest
view, for every known block `b' ⪰ C(b,e)`, has a two-thirds link from the
fixed paper voting source `vs(b,e)` to the exact target `C(b,e)`, after
excluding `D_b'`.

The quantified descendant indexes the paper's block-local slashable set and
active weight; it does not replace the fixed source by `vs(b',e)`.  The base
block's knownness and `epoch(b) ≤ e` are recorded at each concrete view so
that Definition 7 is never silently read on its undefined future-block
branch.

The paper also asks `st(e+1) ≥ GST`.  The spec execution begins inside the
globally synchronous segment, so that temporal guard is represented by the
ambient `Synchrony`/horizon premises rather than a second clock constant. -/
def SourceTargetSupportThroughoutEpoch
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (b : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    compute_epoch_at_slot cfg (E.slot_at cfg m) = e + 1 →
    b ∈ (E.store cfg ext w m).block_roots ∧
      get_block_epoch cfg (E.store cfg ext w m) b ≤ e ∧
      ∀ b' ∈ (E.store cfg ext w m).block_roots,
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root (V.C b e).root) = true →
        Nonempty (SourceTargetLinkSupportAt cfg ext V w m b'
          (V.voting_source_at cfg (E.store cfg ext w m) b e) (V.C b e))

/-- Paper Assumption 3.2, separated from state-transition coherence.

This is the paper's quantifier shape: if `b` is canonical and the exact fixed
`vs(b,e)`-to-`C(b,e)` support condition holds in every honest view throughout
epoch `e+1`, then by `st(e+2)` each honest view contains a pre-boundary
descendant that carries in AU either `C(b,e)` or a checkpoint of a later
epoch whose block descends from the block of `C(b,e)`.  Target-only support
or a free `A32IncludedAtTip` consequence is intentionally insufficient.

The second alternative is necessary for the fixed bridge view, in which AU
holds the four carried selectors of the blocks on the chain. One Python
justification pass can justify `C(b,e)` and a checkpoint of epoch `e+1`
together; the state then carries only the later checkpoint
(`regression.a32_exact_carried_superseded` in
`scripts/conformance/contracts/test_realized_gap.py`).

The descendant must be in an epoch above `GENESIS_EPOCH + 1` unless
`e = GENESIS_EPOCH`.  Python `process_justification_and_finalization`
returns early at epochs up to `GENESIS_EPOCH + 1`, so it never computes the
unrealized justification of epoch 1 in a block of epoch 1: the epoch-1 votes
must be included in a block of epoch 2 or later.  Without this bound the
premise admits a run in which the Python FCR confirms a block and then loses
it (`regression.fcr_confirmed_block_reorged_epoch_one` in
`scripts/conformance/contracts/test_realized_gap.py`). -/
structure EventualCheckpointInclusion
    {E : Execution Root} (V : CheckpointInclusionView cfg E) : Prop where
  included : ∀ {b : Root} {bb : BeaconBlock Root} {e : Epoch},
    V.BlockAt b bb →
    compute_epoch_at_slot cfg bb.slot ≤ e →
    E.CanonicalThroughoutEpoch cfg ext b (e + 1) →
    SourceTargetSupportThroughoutEpoch cfg ext V b e →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      compute_start_slot_at_epoch cfg (e + 2) ≤ E.slot_at cfg m →
      ∃ b' ∈ (E.store cfg ext w m).block_roots,
        b ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root b) = true ∧
        get_block_epoch cfg (E.store cfg ext w m) b' < e + 2 ∧
        (e ≤ GENESIS_EPOCH ∨ GENESIS_EPOCH + 1 < get_block_epoch cfg (E.store cfg ext w m) b') ∧
        V.AvailableCheckpointOrExtension cfg b' (V.C b e)

end FastConfirmation.Spec

end
