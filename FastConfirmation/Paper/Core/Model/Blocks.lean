module
public import FastConfirmation.Paper.Core.Model.Validators

@[expose] public section

/-!
# Core / Model / Blocks

Raw parent-pointer block trees, ancestry, and a chain-validity witness.
Adapted from the `decoupled-consensus` block model. Blocks carry their slot and,
for the HFC/FFG layer, may also carry a finite set of simplified on-chain FFG
vote records. The legacy `Block.mk` constructor remains vote-free for
backward-compatible §3.1/LMD-GHOST code; use `Block.mkWithVotes` when modeling a
block with included FFG votes.
-/

namespace FastConfirmation

/-- Opaque block identifiers (model block hashes). -/
abbrev BlockId := ℕ

/-- A simplified FFG vote record included in a block.

The record identifies the signer, the slot at which the vote was cast, and the
source/target epochs for a vote targeting the including block's chain. The source
and target blocks are intentionally not stored here: the HFC layer interprets
the epochs as checkpoint blocks computed from the including block's chain, and
known-vote inclusion is scoped to messages that already target those chain
checkpoints. This is the minimal AU(b)-style model surface needed for §4
Algorithm 1. It does not model the execution spec's one-recorded-vote
participation flag; downstream predicates may drop equivocating validators per
epoch when reading a chain's on-chain votes. -/
structure ContainedFFGVote (n : ℕ) where
  validator : Validator n
  slot : Slot
  sourceEpoch : Epoch
  targetEpoch : Epoch
  deriving DecidableEq

/-- A block: an id, a parent, a slot, and optionally included FFG votes. -/
inductive Block (n : ℕ) : Type
  | genesis : Block n
  | mk (id : BlockId) (parent : Block n) (slot : Slot) : Block n
  | mkWithVotes (id : BlockId) (parent : Block n) (slot : Slot)
      (ffgVotes : Finset (ContainedFFGVote n)) : Block n
  deriving DecidableEq

namespace Block

variable {n : ℕ}

/-- Slot of a block. Genesis has slot `0`. -/
def slot : Block n → Slot
  | genesis => 0
  | mk _ _ s => s
  | mkWithVotes _ _ s _ => s

/-- Parent of a non-genesis block. -/
def parent? : Block n → Option (Block n)
  | genesis => none
  | mk _ p _ => some p
  | mkWithVotes _ p _ _ => some p

/-- Slot of the parent (genesis ↦ `0`). Used for the `psPlus1` lower endpoint. -/
def parentSlot : Block n → Slot
  | genesis => 0
  | mk _ p _ => p.slot
  | mkWithVotes _ p _ _ => p.slot

/-- The FFG vote records included directly in this block. Legacy `mk` blocks
    contain none; `mkWithVotes` carries an arbitrary finite set. -/
def containedFFGVotes : Block n → Finset (ContainedFFGVote n)
  | genesis => ∅
  | mk _ _ _ => ∅
  | mkWithVotes _ _ _ votes => votes

/-- `psPlus1 b = slot(parent b) + 1`, the lower endpoint of the committee range
    in the weights `S`/`W`. Genesis is never load-bearing (the genesis disjunct
    in `isLMDGHOSTSafe` fires first). -/
def psPlus1 (b : Block n) : Slot := b.parentSlot + 1

/-- Well-formedness: slots strictly increase along parent links. -/
def WellFormed : Block n → Prop
  | genesis => True
  | mk _ p s => p.slot < s ∧ WellFormed p
  | mkWithVotes _ p s _ => p.slot < s ∧ WellFormed p

/-- Parent-pointer ancestry. `B ≼ C` means `B` is reached from `C` by following
    parent pointers, or `B = C`. -/
inductive Ancestor : Block n → Block n → Prop
  | refl (B : Block n) : Ancestor B B
  | step {B C : Block n} {bid : BlockId} {s : Slot}
      (h : Ancestor B C) : Ancestor B (mk bid C s)
  | stepWithVotes {B C : Block n} {bid : BlockId} {s : Slot}
      {votes : Finset (ContainedFFGVote n)}
      (h : Ancestor B C) : Ancestor B (mkWithVotes bid C s votes)

@[inherit_doc] scoped infix:50 " ≼ " => Block.Ancestor

/-- Executable ancestry test. -/
def isAncestorOf (B : Block n) : Block n → Bool
  | genesis => decide (B = genesis)
  | mk bid parent s => decide (B = mk bid parent s) || isAncestorOf B parent
  | mkWithVotes bid parent s votes =>
      decide (B = mkWithVotes bid parent s votes) || isAncestorOf B parent

/-- Two blocks are compatible if one is an ancestor of the other. -/
def Compatible (B C : Block n) : Prop := B ≼ C ∨ C ≼ B

@[inherit_doc] scoped infix:50 " ~ " => Block.Compatible

end Block

end FastConfirmation

end
