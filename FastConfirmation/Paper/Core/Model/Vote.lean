module
public import FastConfirmation.Paper.Core.Model.Blocks
public import FastConfirmation.Paper.Core.Model.Validators

@[expose] public section

/-!
# Core / Model / Vote

GHOST votes and the payload-generic message envelope. A `GhostVote` names the
block it supports directly (the idealization that "a vote names a block hash";
block-hash collisions are idealized away — distinct blocks are distinct values).

The `Message` envelope keeps a `Payload` slot so that the §4 FFG layer can ride
its checkpoint vote in `extra` without touching any §3.1 definition. Some HFC
block-contained AU payloads are FFG-only carriers rather than live LMD votes; the
`countsForLMD` flag keeps those payloads visible to FFG justification without
letting them affect fork choice.
-/

namespace FastConfirmation

/-- A GHOST (block-level) vote: who, when, and which block. -/
structure GhostVote (n : ℕ) where
  validator : Validator n
  slot : Slot
  block : Block n
  deriving DecidableEq

/-- A received message: a GHOST vote plus a payload. §3.1 uses `Payload := Unit`.
    `countsForLMD = false` marks a payload-only carrier that should not enter LMD
    GHOST latest-vote/support calculations. -/
structure Message (n : ℕ) (Payload : Type) where
  ghost : GhostVote n
  countsForLMD : Bool := true
  extra : Payload
  deriving DecidableEq

end FastConfirmation

end
