import FastConfirmation.Paper.HFC.Model.Checkpoint

/-!
# HFC / Model / FFGVote

The FFG-Casper vote — the `Payload` instantiation of §4. An FFG vote is a
source→target checkpoint link `a = ⟨C_s, C_t⟩` (arXiv §2.2.1; explainer p.2
"FFG vote: checkpoint-level vote").

The signer and slot ride in the enclosing `Message.ghost` (a `GhostVote n` carries
`validator`/`slot`/`block`), so the payload is *just* the link. Setting
`Payload := FFGVote n` makes `Message n (FFGVote n)` carry both a GHOST envelope
(`ghost`) and the FFG vote (`extra`). The envelope's `countsForLMD` flag decides
whether the GHOST component participates in LMD fork choice; block-contained AU carriers
set it to `false`.

`deriving DecidableEq` is required for the `Message`/`View` `Finset` derivations.
-/

namespace FastConfirmation.HFC

/-- An FFG-Casper vote: a source→target checkpoint link (arXiv §2.2.1; explainer
    p.2). This is the §4 `Payload`: `Message n (FFGVote n)`. -/
structure FFGVote (n : ℕ) where
  source : Checkpoint n
  target : Checkpoint n
  deriving DecidableEq

end FastConfirmation.HFC
