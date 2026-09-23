module
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.List.MinMax
public import FastConfirmationPaper.Core.Model.GhostVote

@[expose] public section

/-!
# Core / Model / View

A validator's time-indexed view (the messages and blocks it has received), the
LMD "latest message" filter, and the axiomatized `Synchrony` bundle — exactly
the timing facts the §3 safety proofs consume (monotone views; honest votes
cast in a slot are delivered to every honest view by the next slot boundary,
post-GST). Committees are modeled as a single global object, so committee
view-independence past `gst` holds by construction (a deliberate strengthening
of the paper's GST-gated committee consistency; §5 would relax it).
-/

namespace FastConfirmation

open scoped Block

/-- A view: the blocks and messages received so far. -/
structure View (n : ℕ) (P : Type) where
  blocks : Finset (Block n)
  msgs : Finset (Message n P)

namespace View

variable {n : ℕ} {P : Type}

/-- The LMD-relevant GHOST votes in a view. Payload-only carrier messages remain in
    `V.msgs` for higher-layer protocols but do not enter fork-choice vote support. -/
def ghostVotes (V : View n P) : Finset (GhostVote n) :=
  (V.msgs.filter (fun m => m.countsForLMD)).image Message.ghost

/-- The GHOST votes in `V` cast by validator `i`. -/
def votesOf (V : View n P) (i : Validator n) : Finset (GhostVote n) :=
  V.ghostVotes.filter (fun gv => gv.validator = i)

/-- LMD filter with a slot cutoff (`FIL_cur ∘ FIL_lmd`): validator `i`'s
    highest-slot GHOST vote in `V` among votes of slot `≤ upTo`, if any.
    Noncomputable (via `Finset.toList`); this layer is for statements, not execution. -/
noncomputable def latestVote (V : View n P) (i : Validator n) (upTo : Slot) :
    Option (GhostVote n) :=
  ((V.votesOf i).filter (fun gv => gv.slot ≤ upTo)).toList.argmax (·.slot)

/-- `i` equivocates in `V`: two distinct GHOST votes at the same slot. Such a
    validator's votes are dropped by the fork choice (the paper's `FIL_eq`). -/
def equivocator (V : View n P) (i : Validator n) : Prop :=
  ∃ gv₁ ∈ V.votesOf i, ∃ gv₂ ∈ V.votesOf i, gv₁ ≠ gv₂ ∧ gv₁.slot = gv₂.slot

open Classical in
/-- The LMD vote actually counted for `i` up to slot `upTo`: its latest such vote,
    unless it equivocates (`FIL_eq` then `FIL_cur ∘ FIL_lmd`). -/
noncomputable def effectiveVote (V : View n P) (i : Validator n) (upTo : Slot) :
    Option (GhostVote n) :=
  if V.equivocator i then none else V.latestVote i upTo

/-- Does `i`'s effective (latest non-equivocating, slot `≤ upTo`) vote support `b`? -/
noncomputable def supportsLMD (V : View n P) (b : Block n) (i : Validator n) (upTo : Slot) : Bool :=
  match V.effectiveVote i upTo with
  | some gv => b.isAncestorOf gv.block
  | none => false

end View

/-- A time-indexed family of views, one per validator: `𝒱_v(t)`. -/
abbrev ViewFamily (n : ℕ) (P : Type) := Validator n → Time → View n P

/-- Views only grow with time (no message is ever removed). The family-level
    predicate (named `ViewsMonotone`, paralleling `ViewsValid`, to avoid shadowing
    mathlib's order-theoretic `Monotone`). -/
def ViewsMonotone {n : ℕ} {P : Type} (𝒱 : ViewFamily n P) : Prop :=
  ∀ v t t', t ≤ t' → (𝒱 v t).msgs ⊆ (𝒱 v t').msgs ∧ (𝒱 v t).blocks ⊆ (𝒱 v t').blocks

/-- An honest validator has "cast" message `m` if `m` is its own vote present in
    its own view at the slot it acts. -/
def HonestCast {n : ℕ} {P : Type} (fm : FaultModel n) (𝒱 : ViewFamily n P)
    (τ : Timing) (m : Message n P) : Prop :=
  m.ghost.validator ∈ fm.honest ∧ m ∈ (𝒱 m.ghost.validator (τ.st m.ghost.slot)).msgs

/-- The synchrony facts the §3 safety proofs consume. -/
structure Synchrony (n : ℕ) (P : Type) (τ : Timing) (fm : FaultModel n)
    (𝒱 : ViewFamily n P) : Prop where
  /-- Views grow monotonically. -/
  monotone : ViewsMonotone 𝒱
  /-- An honest vote cast in a slot `≤ s'` is in every honest view by `st(s'+1)`,
      once **slot `s'` itself** is past `gst` — the vote has then circulated through a
      full post-`gst` slot, so the `Δ ≤ slot` delivery bound has flushed it to every
      honest view by the next boundary `st(s'+1)`. Gating instead on `st(s'+1) ≥ gst`
      would be unsound: a vote circulating during a `gst`-straddling slot `s'`
      (`st s' < gst ≤ st(s'+1)`) need not reach everyone by `st(s'+1)`. -/
  honestVoteUbiq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest →
    ∀ {m : Message n P} {s' : Slot}, HonestCast fm 𝒱 τ m → m.ghost.slot ≤ s' →
      τ.AfterGST (τ.st s') → m ∈ (𝒱 w (τ.st (s' + 1))).msgs
  /-- Views are vote-closed on blocks: a vote present in a view carries its block,
      so vote delivery (gossip) also propagates the voted-for block (Lemma 5). -/
  votesCarryBlocks : ∀ ⦃v : Validator n⦄ ⦃t : Time⦄ ⦃m : Message n P⦄,
    m ∈ (𝒱 v t).msgs → m.ghost.block ∈ (𝒱 v t).blocks
  /-- Views are ancestor-closed on blocks: having a block means having its whole
      prefix. With `votesCarryBlocks` this delivers the safe block itself (Lemma 5). -/
  blocksAncestorClosed : ∀ ⦃v : Validator n⦄ ⦃t : Time⦄ ⦃b b' : Block n⦄,
    b ∈ (𝒱 v t).blocks → b' ≼ b → b' ∈ (𝒱 v t).blocks
  /-- **Block gossip:** once a block appears in any honest view, every honest view has it by the
      next slot boundary after a full post-GST slot. This is the block-level surface used by the
      HFC on-chain-vote model: FFG votes included in a block's ancestry travel with the block. -/
  blockRelay : ∀ ⦃v w : Validator n⦄, v ∈ fm.honest → w ∈ fm.honest →
    ∀ ⦃t : Time⦄ ⦃b : Block n⦄ ⦃s' : Slot⦄, b ∈ (𝒱 v t).blocks → τ.slotOf t ≤ s' →
      τ.AfterGST (τ.st s') → b ∈ (𝒱 w (τ.st (s' + 1))).blocks
  /-- **Causality: no future messages.** A message in a view at time `t` was cast in a slot
      `≤ slotOf t` (a validator only receives, by `t`, what was sent by `t`). This is the network
      property used by the HFC selector bridge: view-visible FFG votes are all slot-`≤ slotOf t`,
      so the proof-facing epoch-cut helpers can agree with the paper-facing AU
      `GJ(V,t) = max{vs(b,t) : slot(b) ≤ slot(t)}` / `GF(V,t)` selectors under the explicit
      block-contained-vote visibility assumptions. -/
  noFutureMessages : ∀ ⦃v : Validator n⦄ ⦃t : Time⦄ ⦃m : Message n P⦄,
    m ∈ (𝒱 v t).msgs → m.ghost.slot ≤ τ.slotOf t
  /-- **Gossip relay: what one honest validator sees, all honest validators see by the next
      boundary.** Any message present in *some* honest view at time `t` (slot `slotOf t ≤ s'`, with
      `s'` past `gst`) is, by `st(s'+1)`, present in *every* honest view — honest validators
      re-broadcast
      every message they receive, so a single post-`gst` slot's Δ-flush propagates it to all. (Same
      `s'`-parameterized shape as `honestVoteUbiq`, so a vote received by an early-epoch slot still
      delivers by the epoch-end boundary `st(lslot e + 1)` once the *last* slot is post-`gst`.) This
      is the message-level generalization of `honestVoteUbiq` (which moves only `HonestCast`
      messages):
      here
      even an *adversary-authored* message becomes common knowledge once any honest node has seen it
      (the relay does not depend on the author being honest, only on the *receiver* being honest and
      re-gossiping). `honestVoteUbiq` is the special case where the seen message is the caster's own
      vote in its own view.

      This is the message-level gossip surface used by certificate arguments over observed view
      messages. The HFC AU model is block-contained: its inclusion/visibility bridge uses block
      payloads plus `blockRelay`, while this field remains the generic relay fact for messages
      already present in an honest view. It uses the same Δ ≤ slot, gate-on-`AfterGST(st(slotOf t))`
      discipline as `honestVoteUbiq` (gating on `st(slotOf t + 1) ≥ gst` would be unsound for a
      `gst`-straddling slot). -/
  messageRelay : ∀ ⦃v w : Validator n⦄, v ∈ fm.honest → w ∈ fm.honest →
    ∀ ⦃t : Time⦄ ⦃m : Message n P⦄ ⦃s' : Slot⦄, m ∈ (𝒱 v t).msgs → τ.slotOf t ≤ s' →
      τ.AfterGST (τ.st s') → m ∈ (𝒱 w (τ.st (s' + 1))).msgs

/-- A view is valid (`FIL_¬valid` for votes): every message envelope is from a committee member of
    its slot, supports a block of not-greater slot, and that block is well-formed. LMD fork choice
    only consumes messages with `countsForLMD = true`, but payload-only FFG carriers still need a
    valid attestation envelope for committee and no-future reasoning. -/
def ViewValid {n : ℕ} {P : Type} (cm : Committees n) (V : View n P) : Prop :=
  ∀ m ∈ V.msgs,
    m.ghost.validator ∈ cm.member m.ghost.slot ∧
      m.ghost.block.slot ≤ m.ghost.slot ∧ m.ghost.block.WellFormed

/-- Every view in the family is valid. -/
def ViewsValid {n : ℕ} {P : Type} (cm : Committees n) (𝒱 : ViewFamily n P) : Prop :=
  ∀ v t, ViewValid cm (𝒱 v t)

/-- **No forgery of honest votes** (a faithful well-formedness/honesty hypothesis).
    Every GHOST vote attributed to an *honest* validator that appears in *any* honest
    view was genuinely cast by that validator (it is a `HonestCast`). This is exactly
    the unforgeability guarantee a signature scheme provides for honest signers: an
    attacker cannot fabricate a vote in an honest validator's name. It lets the proofs
    feed honest-attributed votes observed in one honest view into `honestVoteUbiq`
    (vote delivery) to transfer them to every other honest view. -/
def HonestNoForgery {n : ℕ} {P : Type} (fm : FaultModel n) (τ : Timing)
    (𝒱 : ViewFamily n P) : Prop :=
  ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t : Time⦄ ⦃m : Message n P⦄,
    m ∈ (𝒱 w t).msgs → m.ghost.validator ∈ fm.honest → HonestCast fm 𝒱 τ m

end FastConfirmation

end
