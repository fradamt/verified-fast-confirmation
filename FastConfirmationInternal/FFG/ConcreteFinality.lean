module
public import FastConfirmationInternal.FFG.ConcreteJustification

@[expose] public section

/-! Defines concrete FFG finalization certificates, the justification-bit
invariant of the four Python finalization rules, and slashable evidence among
included, target-matching body votes. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

/-- The checkpoint of an accepted chain at an epoch: the root of the latest
block at or before the epoch start slot. -/
def chainCheckpoint (S : FFGSetup Root) (blocks : List (FFGWireBlock Root))
    (epoch : Epoch) : Checkpoint Root :=
  ⟨epoch, chainRootAt S.genesisRoot blocks (compute_start_slot_at_epoch S.cfg epoch)⟩

/-- A finalizing link from a justified `finalized` checkpoint to a chain
checkpoint `target` one or two epochs later. In the two-epoch case the chain
checkpoint between them is justified (Gasper `k = 2`). This is the certificate
that each of the four Python finalization rules produces. -/
structure FinalizationLink [BEq Root] (S : FFGSetup Root)
    (blocks : List (FFGWireBlock Root)) (votes : List (IncludedVote Root))
    (finalized target : Checkpoint Root) : Prop where
  justified : Justified S votes finalized
  link : Nonempty (SupermajorityLink S votes finalized target)
  target_on_chain : target = chainCheckpoint S blocks target.epoch
  target_epoch : target.epoch = finalized.epoch + 1 ∨ target.epoch = finalized.epoch + 2
  middle_justified : target.epoch = finalized.epoch + 2 →
    Justified S votes (chainCheckpoint S blocks (finalized.epoch + 1))

/-- A checkpoint with a finalizing link. -/
def FinalizationCertified [BEq Root] (S : FFGSetup Root)
    (blocks : List (FFGWireBlock Root)) (votes : List (IncludedVote Root))
    (c : Checkpoint Root) : Prop :=
  ∃ target, FinalizationLink S blocks votes c target

/-- The justification bits and the finalized checkpoint of a state whose next
PJF pass is the pass of `epoch`. Bit `i` records the justification of the
chain checkpoint of epoch `epoch - 1 - i`. Bit 0 also records the link from
the previous justified checkpoint, which the current-epoch test used. -/
structure FinalityInvariant [BEq Root] (S : FFGSetup Root)
    (blocks : List (FFGWireBlock Root)) (votes : List (IncludedVote Root))
    (epoch : Epoch) (state : FFGBeaconState Root) : Prop where
  bits_length : state.justification_bits.length = 4
  bit_epoch : ∀ i, state.justification_bits.getD i false = true → i + 2 ≤ epoch
  bit_link : state.justification_bits.getD 0 false = true →
    Nonempty (SupermajorityLink S votes state.previous_justified_checkpoint
      (chainCheckpoint S blocks (epoch - 1)))
  bit_justified : ∀ i, state.justification_bits.getD i false = true →
    Justified S votes (chainCheckpoint S blocks (epoch - 1 - i))
  finalized_certified : state.finalized_checkpoint = S.stub ∨
    ∃ target, FinalizationLink S blocks votes state.finalized_checkpoint target ∧
      target.epoch < epoch

/-- A validator that signed two included, target-matching body votes whose
data is slashable (a double vote or a surround vote). -/
def SlashableSigner [DecidableEq Root] (S : FFGSetup Root)
    (votes : List (IncludedVote Root)) (i : ValidatorIndex) : Prop :=
  ∃ r r', TargetIncluded S votes r ∧ TargetIncluded S votes r' ∧
    i ∈ r.attesters S ∧ i ∈ r'.attesters S ∧
    is_slashable_attestation_data r.vote.data r'.vote.data = true

/-- Slashable signers with at least one third of the fixed total active
balance. -/
def SlashableQuorum [DecidableEq Root] (S : FFGSetup Root)
    (votes : List (IncludedVote Root)) : Prop :=
  ∃ signers : Finset ValidatorIndex, S.scope.activeBalance ≤ 3 * S.scope.weight signers ∧
    ∀ i ∈ signers, SlashableSigner S votes i

/-- The two certificate laws that the exact finalized-prefix argument uses,
in the fixed horizon. This is the concrete counterpart of
`CheckpointCertificateAccountability`. -/
structure ConcreteCertificateAccountability [BEq Root] (S : FFGSetup Root)
    (votes : List (IncludedVote Root)) : Prop where
  justified_unique : ∀ {x y : Checkpoint Root}, Justified S votes x → Justified S votes y →
    x.epoch ≤ S.scope.last_epoch → x.epoch = y.epoch → x.root = y.root
  links_not_surround : ∀ {s t s' t' : Checkpoint Root},
    SupermajorityLink S votes s t → SupermajorityLink S votes s' t' →
    t.epoch ≤ S.scope.last_epoch → ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch)

/-- The block roots of accepted blocks commit to the block slot and parent,
and no accepted block has the genesis block root. This is the collision
resistance of the root commitment, stated over a finite block set. -/
structure RootsCommit (S : FFGSetup Root) (blocks : List (FFGWireBlock Root)) : Prop where
  not_genesis : ∀ b ∈ blocks, b.root ≠ S.genesisRoot
  commit : ∀ a ∈ blocks, ∀ b ∈ blocks, a.root = b.root →
    a.slot = b.slot ∧ a.parent_root = b.parent_root

end FastConfirmation.Spec.ConcreteFFG

end
