import FastConfirmation.Paper.Core.Model

/-!
# HFC / Model / Checkpoint

The FFG-Casper checkpoint — the object §4's anchor and `ffgFilter` read. A
checkpoint is a block together with the epoch at which it is checkpointed
(arXiv:2405.00549 §2.2.1; explainer p.1 "Checkpoints"). The `block` field is the
actual `Block n`, so checkpoint/block compatibility reuses Core's ancestry `≼`
directly (`C.block ≼ b` / `b ≼ C.block` at the use sites).

Nothing here touches `Core` or `LMDGhost`; this is the additive §4 layer.

`deriving DecidableEq` is **load-bearing**: it propagates to `FFGVote` and thence
to `Message n (FFGVote n)` / `View n (FFGVote n)`'s `Finset` machinery (Core
derives `DecidableEq` on `Message`).
-/

namespace FastConfirmation.HFC

open FastConfirmation

/-- A checkpoint `C = (block(C), epoch(C))`: a block together with the epoch at
    which it is checkpointed (arXiv §2.2.1; explainer p.1). -/
structure Checkpoint (n : ℕ) where
  block : Block n
  epoch : Epoch
  deriving DecidableEq

end FastConfirmation.HFC
