# Model annotation — paper ↔ Lean correspondence

A side-by-side map from Ethereum's **Fast Confirmation Rule** paper (arXiv:2405.00549,
Asgaonkar–D'Amato–Saltini–Zanolini–Zhang; §3.1 LMD-GHOST + §4 HFC/FFG-Casper) and its
explainer to this Lean 4 / mathlib formalization. Each row pairs the paper-side object
(definition, assumption, or theorem) with the Lean object that models it.

The paper `.tex` is **not** in this repo; the *Paper* column is reconstructed from the
Lean docstrings, which cite the paper labels (e.g. *Def 8*, *Algorithm 1 l.2344*, *Lemma 13*,
*Assumption 5.3*) and usually quote the formulas. Where a docstring only paraphrases, the
Paper column paraphrases — it does not invent formulas. The *Lean* column gives the constant
name, its `file:line`, and a trimmed signature (long premise lists abbreviated as
`… (explicit interface premises) …`; long proof terms elided to the conclusion).

**Faithfulness legend** (the *Faithfulness* note under each pair):
- *faithful* — models the paper object as-is.
- *documented deviation* — a deliberate, disclosed simplification (e.g. **constant balances**;
  the **clean Definition 8** predicate rather than the deployed Definition 10). See
  `docs/paper-model-design.md` and `docs/algorithm1-gate-discharge.md`.
- *gate eliminated* — used for an Algorithm-1 result that removes the semantic
  confirmation gate `WillNoConflictingChkpBeJustified`.

> The primary §4 results are `HFC_Safety_Alg1` / `HFC_Monotonicity_Alg1` (over the HFC
> Algorithm-1 wrapper `isConfirmedAlg1`, whose selector ranges over the paper-shaped
> `isConfirmedNoCaching` rule). Algorithm 1 and `ffgFilterAt` consume AU selectors:
> `ruleVotingSource`, `ruleGJBlock`, `ruleRealizedGJ`, and `ruleRealizedGF`; the
> `votingSource` / `greatestRealizedJustified` names are proof-facing view-realized helpers. The
> gate-based `HFC_Safety` / `HFC_Monotonicity` provide a separate semantic-gate formulation.

## Contents

- [Core vocabulary](#core-vocabulary)
- [§3.1 LMD-GHOST layer (defs + statements)](#31-lmd-ghost-layer-defs--statements)
- [§4 HFC model (defs)](#4-hfc-model-defs)
- [§4 HFC statements (TheoremStatements.lean + ProvenTheorems.lean)](#4-hfc-statements-theoremstatementslean--proventheoremslean)

## Core vocabulary

#### Base types (Slot/Epoch/Time/Validator/Weight) + modeling decisions

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2 (time/validator/weight model)</i><br><br>Time is a single linearly-ordered quantity; slots and epochs are projections of it. Validators are an (idealized finite) set; weights/balances are exact reals. The safety proofs consume no metric on time beyond the slot lattice and gst comparisons.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Slot / Epoch / Time / Validator / Weight</code><br><sub>FastConfirmation/Paper/Core/Model/Time.lean:15; FastConfirmation/Paper/Core/Model/Validators.lean:18 · <i>structure</i></sub><pre>abbrev Slot := ℕ ; abbrev Epoch := ℕ ; abbrev Time := ℕ ; abbrev Validator (n : ℕ) := Fin n ; abbrev Weight := ℚ</pre>

</td>
</tr>
</table>

> **Faithfulness:** Modeling decisions: Time := ℕ (no metric, only slot lattice + gst); Validator := Fin n (paper allows infinite set; finite per-slot committees suffice for §3.1 weights); Weight := ℚ (exact rationals).

#### Timing (slotsPerEpoch/slotDur/gst) + slotOf/st/epochOf/fslot/lslot/AfterGST

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2 (slots, epochs, GST)</i><br><br>Protocol timing parameters: slots-per-epoch, slot duration, and the network global stabilization time gst. slotOf(t)=t/slotDur is the slot containing instant t; st(s)=s·slotDur its start; epochOf(s)=s/slotsPerEpoch; fslot(e)=e·slotsPerEpoch first slot of epoch e; lslot(e)=e·slotsPerEpoch+(slotsPerEpoch−1) last slot; AfterGST(t) iff gst ≤ t.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Timing (+ slotOf, st, epochOf, fslot, lslot, AfterGST)</code><br><sub>FastConfirmation/Paper/Core/Model/Time.lean:23 · <i>def</i></sub><pre>structure Timing where slotsPerEpoch slotDur : ℕ; gst : Time; hSlotsPerEpoch : 0 &lt; slotsPerEpoch; hSlot : 0 &lt; slotDur
  slotOf t := t / slotDur ; st s := s * slotDur ; epochOf s := s / slotsPerEpoch
  fslot e := e * slotsPerEpoch ; lslot e := e * slotsPerEpoch + (slotsPerEpoch - 1) ; AfterGST t := gst ≤ t</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Block (parent-pointer tree, optional FFG votes) + slot/parentSlot/psPlus1

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2 (block tree / chains), §2.2.1 AU(b)</i><br><br>A block is an id, a parent pointer, and a slot. For §4, blocks may include FFG votes, and AU(b) is computed from votes in b's ancestry. psPlus1(b)=slot(parent(b))+1 is the lower endpoint of the committee range in the weights S/W.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>ContainedFFGVote / Block (+ slot, parentSlot, psPlus1)</code><br><sub>FastConfirmation/Paper/Core/Model/Blocks.lean:30 · <i>structure</i></sub><pre>structure ContainedFFGVote (n : ℕ) where
  validator : Validator n
  slot : Slot
  sourceEpoch : Epoch
  targetEpoch : Epoch

inductive Block (n : ℕ)
  | genesis
  | mk (id : BlockId) (parent : Block n) (slot : Slot)
  | mkWithVotes (id : BlockId) (parent : Block n) (slot : Slot)
      (ffgVotes : Finset (ContainedFFGVote n))
  psPlus1 b := b.parentSlot + 1</pre>

</td>
</tr>
</table>

> **Faithfulness:** Parent-pointer ancestry and slot arithmetic are faithful. `Block.mk` constructs vote-free blocks for the LMD-GHOST model; `Block.mkWithVotes` carries simplified chain-targeted FFG vote records for the §4 AU model, including the vote slot so previous-epoch votes can be included in a current-epoch block. Source/target blocks are interpreted as checkpoints on the including block's chain, and known-vote inclusion is scoped to messages already targeting those checkpoints. The simplified AU model has no capacity cap and does not encode execution-spec participation flags; on-chain readers ignore a validator for an epoch if that validator equivocates for that epoch.

#### Ancestor (≼), Compatible (~), WellFormed

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2 (ancestry / chain validity)</i><br><br>B ≼ C means B is reached from C by following parent pointers, or B = C (parent-pointer ancestry). Two blocks are compatible (B ~ C) iff one is an ancestor of the other. WellFormed: slots strictly increase along parent links.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Block.Ancestor (≼) / Block.Compatible (~) / Block.WellFormed</code><br><sub>FastConfirmation/Paper/Core/Model/Blocks.lean:87 · <i>def</i></sub><pre>inductive Ancestor : Block n → Block n → Prop | refl (B) : Ancestor B B | step (h : Ancestor B C) : Ancestor B (mk bid C s)
  Compatible B C := B ≼ C ∨ C ≼ B
  WellFormed : genesis ↦ True | mk _ p s ↦ p.slot &lt; s ∧ WellFormed p</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Stakes / Anchor + totalWeight

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (balance assignment anchored at checkpoint C)</i><br><br>A balance source is an effective-balance assignment bal : Validator → Weight with all balances positive. In the paper this is the balance assignment anchored at a checkpoint C; §3.1 uses it only as such. totalWeight(A,X) = Σ_{i∈X} A.bal i.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Stakes / Anchor / totalWeight</code><br><sub>FastConfirmation/Paper/Core/Model/Validators.lean:25 · <i>structure</i></sub><pre>structure Stakes (n) where bal : Validator n → Weight ; hpos : ∀ i, 0 &lt; bal i
  abbrev Anchor (n) := Stakes n ; def totalWeight (A : Anchor n) (X : Finset (Validator n)) : Weight := ∑ i ∈ X, A.bal i</pre>

</td>
</tr>
</table>

> **Faithfulness:** Anchor is abstract in the §3.1 layer; the HFC layer supplies its checkpoint and justification structure.

#### Committees (per-slot committee assignment)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2 (per-slot committees)</i><br><br>Per-slot committee assignment: member : Slot → Finset of validators. Finite per-slot committees model the paper's (possibly infinite) validator set as far as the §3.1 weights read it.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Committees</code><br><sub>FastConfirmation/Paper/Core/Model/Validators.lean:38 · <i>structure</i></sub><pre>structure Committees (n : ℕ) where member : Slot → Finset (Validator n)</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### FaultModel (β &lt; 1/3)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2/§3.1 (adversarial weight bound β; Assumption 2)</i><br><br>The fault model carries the honest validator set and the adversarial-weight bound β &lt; 1/3 (with β ≥ 0). It deliberately does NOT carry the adversary's identity (adversary = complement univ \ honest) nor an anchor-relative weight bound (that depends on the balance anchor C and so is supplied as a premise).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FaultModel</code><br><sub>FastConfirmation/Paper/Core/Model/Validators.lean:56 · <i>structure</i></sub><pre>structure FaultModel (n) where honest : Finset (Validator n) ; β : Weight ; hβ0 : 0 ≤ β ; hβ : β &lt; 1 / 3</pre>

</td>
</tr>
</table>

> **Faithfulness:** β is only the bare bound; it constrains the adversary only through premises (CommitteeHonestMajority / GlobalByzantineBound). Monotonicity needs the extra Assumption 4 β &lt; (1−pb)/4 elsewhere.

#### GlobalByzantineBound (anchor-relative adversary bound)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4 (adversary controls &lt; β of stake)</i><br><br>The total weight of non-honest validators is at most β of the total, measured at anchor C: totalWeight C (univ \ honest) ≤ β · totalWeight C univ. The §4 statement of 'the adversary controls less than β of stake'; lives as a premise (not a FaultModel field) because it depends on the balance anchor C.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>GlobalByzantineBound</code><br><sub>FastConfirmation/Paper/Core/Model/Validators.lean:66 · <i>def</i></sub><pre>def GlobalByzantineBound (C : Anchor n) (fm : FaultModel n) : Prop :=
  totalWeight C (univ.filter (· ∉ fm.honest)) ≤ fm.β * totalWeight C univ</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### GhostVote + Message (payload-generic envelope)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (GHOST/block-level votes); §4 (FFG checkpoint vote payload)</i><br><br>A GHOST (block-level) vote names who, when (slot), and which block it supports directly (idealization: a vote names a block hash; block-hash collisions idealized away). A received message is a GHOST vote plus a Payload (§3.1 uses Payload := Unit; the §4 FFG layer rides its checkpoint vote in `extra`). The model marks whether the ghost component participates in LMD fork choice.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>GhostVote / Message</code><br><sub>FastConfirmation/Paper/Core/Model/Vote.lean:21 · <i>structure</i></sub><pre>structure GhostVote (n) where validator : Validator n ; slot : Slot ; block : Block n
  structure Message (n) (Payload : Type) where
    ghost : GhostVote n
    countsForLMD : Bool := true
    extra : Payload</pre>

</td>
</tr>
</table>

> **Faithfulness:** Payload slot keeps §4 additive: FFG vote rides in `extra` without touching §3.1 defs. `countsForLMD` separates ordinary LMD attestations from payload-only FFG carriers used for block-contained AU votes.

#### View + ghostVotes/votesOf/latestVote/effectiveVote/supportsLMD/equivocator

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (validator views; LMD latest-message filter FIL_lmd, FIL_cur, FIL_eq)</i><br><br>A view is the blocks and messages a validator has received. latestVote(V,i,upTo) is i's highest-slot GHOST vote among votes of slot ≤ upTo (FIL_cur ∘ FIL_lmd). equivocator: two distinct GHOST votes at the same slot (FIL_eq drops such a validator). effectiveVote = latestVote unless equivocating. supportsLMD(V,b,i,upTo): does i's effective vote support a descendant of b (b ≼ gv.block).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>View (+ ghostVotes, votesOf, latestVote, effectiveVote, supportsLMD, equivocator)</code><br><sub>FastConfirmation/Paper/Core/Model/View.lean:22 · <i>structure</i></sub><pre>structure View (n) (P) where blocks : Finset (Block n) ; msgs : Finset (Message n P)
  ghostVotes V := (V.msgs.filter (fun m => m.countsForLMD)).image Message.ghost
  latestVote V i upTo := ((votesOf i).filter (·.slot ≤ upTo)).toList.argmax (·.slot)
  equivocator V i := ∃ gv₁ gv₂ ∈ votesOf i, gv₁ ≠ gv₂ ∧ gv₁.slot = gv₂.slot
  effectiveVote V i upTo := if equivocator i then none else latestVote i upTo
  supportsLMD V b i upTo := match effectiveVote i upTo | some gv =&gt; b.isAncestorOf gv.block | none =&gt; false</pre>

</td>
</tr>
</table>

> **Faithfulness:** latestVote/effectiveVote/supportsLMD noncomputable (via toList.argmax); this layer is for statements not execution. Payload-only FFG carriers remain in `msgs` but are filtered out of LMD fork choice by `ghostVotes`.

#### ViewFamily / ViewsMonotone / ViewValid / ViewsValid

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (view family 𝒱_v(t); monotone views; FIL_¬valid)</i><br><br>A time-indexed family 𝒱_v(t), one view per validator per time. ViewsMonotone: views only grow with time (no message ever removed). ViewValid (FIL_¬valid for votes): every message envelope is from a committee member of its slot, supports a block of not-greater slot, and that block is well-formed — forcing every LMD supporter into the block's committee range while keeping payload-only FFG carriers well formed.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>ViewFamily / ViewsMonotone / ViewValid / ViewsValid</code><br><sub>FastConfirmation/Paper/Core/Model/View.lean:67 · <i>def</i></sub><pre>abbrev ViewFamily (n) (P) := Validator n → Time → View n P
  ViewsMonotone 𝒱 := ∀ v t t', t ≤ t' → (𝒱 v t).msgs ⊆ (𝒱 v t').msgs ∧ (𝒱 v t).blocks ⊆ (𝒱 v t').blocks
  ViewValid cm V := ∀ m ∈ V.msgs,
    m.ghost.validator ∈ cm.member m.ghost.slot ∧
    m.ghost.block.slot ≤ m.ghost.slot ∧ m.ghost.block.WellFormed</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### HonestCast (honest validator cast a message)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (honest validator's own vote at acting slot)</i><br><br>An honest validator has 'cast' message m iff m is its own vote present in its own view at the slot start st(slot) where it acts: m.ghost.validator ∈ honest ∧ m ∈ 𝒱_{validator}(st(slot)).msgs.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>HonestCast</code><br><sub>FastConfirmation/Paper/Core/Model/View.lean:77 · <i>def</i></sub><pre>def HonestCast (fm) (𝒱) (τ) (m) : Prop :=
  m.ghost.validator ∈ fm.honest ∧ m ∈ (𝒱 m.ghost.validator (τ.st m.ghost.slot)).msgs</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Synchrony (axiomatized timing/gossip bundle)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3 (synchrony / GST + gossip; Lemma 5; Def 3 l.311/l.325; Assumption 5.3)</i><br><br>The synchrony facts the §3 safety proofs consume: (monotone) views grow; (honestVoteUbiq) an honest vote cast in slot ≤ s' reaches every honest view by st(s'+1) once slot s' itself is past gst; (votesCarryBlocks + blocksAncestorClosed) views are vote-closed and ancestor-closed on blocks, so gossip delivers the safe block (Lemma 5); (blockRelay) any block in some honest view reaches every honest view by st(s'+1), carrying included FFG votes with it; (noFutureMessages) a message in a view at t was cast in slot ≤ slotOf t (causality, making realized GJ/GF faithful to Def 3); (messageRelay) any message in some honest view (slot ≤ s', s' past gst) is in every honest view by st(s'+1).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>Synchrony</code><br><sub>FastConfirmation/Paper/Core/Model/View.lean:82 · <i>assumption</i></sub><pre>structure Synchrony (n) (P) (τ) (fm) (𝒱) : Prop where
  monotone : ViewsMonotone 𝒱
  honestVoteUbiq : w ∈ honest → HonestCast m → m.ghost.slot ≤ s' → AfterGST (st s') → m ∈ (𝒱 w (st (s'+1))).msgs
  votesCarryBlocks : m ∈ (𝒱 v t).msgs → m.ghost.block ∈ (𝒱 v t).blocks
  blocksAncestorClosed : b ∈ (𝒱 v t).blocks → b' ≼ b → b' ∈ (𝒱 v t).blocks
  blockRelay : v,w ∈ honest → b ∈ (𝒱 v t).blocks → slotOf t ≤ s' → AfterGST (st s') → b ∈ (𝒱 w (st (s'+1))).blocks
  noFutureMessages : m ∈ (𝒱 v t).msgs → m.ghost.slot ≤ τ.slotOf t
  messageRelay : v,w ∈ honest → m ∈ (𝒱 v t).msgs → slotOf t ≤ s' → AfterGST (st s') → m ∈ (𝒱 w (st (s'+1))).msgs</pre>

</td>
</tr>
</table>

> **Faithfulness:** Axiomatized bundle (paper's own approach: no network/clock metric). Gate is AfterGST(st s') not st(s'+1)≥gst (gating on next boundary unsound for gst-straddling slot). `blockRelay` is the AU-style block propagation surface; `messageRelay` is the message-level gossip primitive.

#### HonestNoForgery (unforgeability of honest votes)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (signature unforgeability for honest signers)</i><br><br>Every GHOST vote attributed to an honest validator that appears in any honest view was genuinely cast by that validator (it is a HonestCast). Exactly the unforgeability a signature scheme provides for honest signers: an attacker cannot fabricate a vote in an honest validator's name.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>HonestNoForgery</code><br><sub>FastConfirmation/Paper/Core/Model/View.lean:162 · <i>assumption</i></sub><pre>def HonestNoForgery (fm) (τ) (𝒱) : Prop :=
  ∀ w ∈ fm.honest, ∀ t m, m ∈ (𝒱 w t).msgs → m.ghost.validator ∈ fm.honest → HonestCast fm 𝒱 τ m</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### BlockFilter / trivialFilter (eligibility seam)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (plain LMD-GHOST) / §4 (HFC FFG filter)</i><br><br>A block-eligibility filter as seen in a view at a time: View → Time → Block → Prop. Plain LMD-GHOST uses trivialFilter (everything eligible); the §4 HFC layer instantiates the same seam with its FFG checkpoint filter, so the §3.1 weight machinery is filter-agnostic.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>BlockFilter / trivialFilter</code><br><sub>FastConfirmation/Paper/Core/Model/Filter.lean:14 · <i>def</i></sub><pre>abbrev BlockFilter (n) (P) := View n P → Time → Block n → Prop
  def trivialFilter : BlockFilter n P := fun _ _ _ =&gt; True</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### ProposerBoost / forkChoiceHead (LMD-GHOST head + proposer boost)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2/§3.1 (LMD-GHOST fork choice; proposer boost l.527)</i><br><br>ProposerBoost names the optional current-slot block receiving the boost W_p. forkChoiceHead: from genesis, repeatedly move to the heaviest filter-eligible child of slot ≤ slot(t), where a child's weight = anchor-weight of validators whose effective vote (slot ≤ slot(t)−1) supports its subtree, plus the proposer boost pb·total if the boosted block lies in that subtree. Fuel-bounded (slot(t)+1 fuel exhausts any path since slots strictly increase). WellFormedBoost: boosted block, when present, is a well-formed block in the view proposed in the current slot (timely current proposal), so the boost adds at most W_p to one branch.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>forkChoiceHead (+ ProposerBoost, latestSupportWeight, boostWeight, childWeight, eligibleChildren, ghostStep, ghostAux, WellFormedBoost)</code><br><sub>FastConfirmation/Paper/Core/Model/ForkChoice.lean:72 · <i>def</i></sub><pre>structure ProposerBoost (n) (P) where proposalAt : View n P → Time → Option (Block n)
  latestSupportWeight A V upTo c := totalWeight A (univ.filter (V.supportsLMD c · upTo))
  boostWeight A boost pb V t c := match boost.proposalAt V t | some bp =&gt; if c.isAncestorOf bp then pb * totalWeight A univ else 0 | none =&gt; 0
  childWeight := latestSupportWeight + boostWeight
  eligibleChildren τ flt V t b := V.blocks.filter (·.parent? = some b ∧ ·.WellFormed ∧ ·.slot ≤ slotOf t ∧ flt V t ·)
  ghostStep := (eligibleChildren …).toList.argmax (childWeight … (slotOf t - 1))
  forkChoiceHead τ A boost pb flt V t := ghostAux … (slotOf t + 1) Block.genesis</pre>

</td>
</tr>
</table>

> **Faithfulness:** noncomputable (rests on latestVote). Ties broken by argmax order; Def 8 strict inequality ensures the safe path never relies on tie-breaking. WellFormedBoost conjuncts tighten the model to the paper but the safety proof bounds the boost structurally (boostWeight_le_Wp) without consuming them.

#### HonestBehavior (definitional honest voting protocol)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (honest validator votes for own LMD-GHOST head, no equivocation; engine of Lemmas 1–2)</i><br><br>Definitional honest behavior (not an environmental assumption): an honest committee member of slot s casts exactly one GHOST vote, in its own view at st(s), for its own filtered LMD-GHOST fork-choice head at st(s) (votesHead); honest validators vote only in slots whose committee they belong to (votesInCommittee); honest validators never equivocate in any honest view (noEquivocation). gj is the abstract greatest-justified anchor provider parameter.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>HonestBehavior</code><br><sub>FastConfirmation/Paper/Core/Model/Honest.lean:22 · <i>structure</i></sub><pre>structure HonestBehavior (τ) (fm) (cm) (gj) (boost) (pb) (flt) (𝒱) : Prop where
  votesHead : v ∈ honest → v ∈ cm.member s → ∃ gv ∈ (𝒱 v (st s)).votesOf v, gv.slot = s ∧ gv.block = forkChoiceHead τ (gj 𝒱 v (st s)) boost pb flt (𝒱 v (st s)) (st s)
  votesInCommittee : v ∈ honest → gv ∈ (𝒱 w t).votesOf v → v ∈ cm.member gv.slot
  noEquivocation : v ∈ honest → ¬ (𝒱 w t).equivocator v</pre>

</td>
</tr>
</table>

> **Faithfulness:** Definitional (what it means to be honest running the protocol), deliberately separate from Synchrony (network) and economic Assumptions (β-bound, static balances). `gj` is an explicit abstract parameter.

## §3.1 LMD-GHOST layer (defs + statements)

#### committeeUnion — union of committees over a slot range

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1, the W̄ committee-union (Def 5-7 support)</i><br><br>The union of per-slot committees over slots [lo, hi], so each validator (counted once) forms the support set W̄ over the relevant slot range [psPlus1 b, s] used for W_b/S_b.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.committeeUnion</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:30 · <i>def</i></sub><pre>def committeeUnion (cm : Committees n) (lo hi : Slot) : Finset (Validator n) := (Finset.Icc lo hi).biUnion cm.member</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Definition 5 — W_b (committee-union weight)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 5, §3.1</i><br><br>W_b: the total weight of the committee union over slots [psPlus1 b, s], evaluated at anchor A (the paper's checkpoint C balances).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.W</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:34 · <i>def</i></sub><pre>def W (A : Anchor n) (cm : Committees n) (b : Block n) (s : Slot) : Weight := totalWeight A (committeeUnion cm b.psPlus1 s)</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; anchored at arbitrary A so §4 reuses verbatim

#### Definition 6 — S_b (supporting weight)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 6, §3.1</i><br><br>S_b: the anchor-weight of those committee-union validators whose effective (LMD) vote up to slot s supports block b.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.S</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:39 · <i>def</i></sub><pre>noncomputable def S (A) (cm) (V : View n P) (b : Block n) (s : Slot) : Weight := totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i =&gt; V.supportsLMD b i s = true))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Definition 6 — Q_b = S_b / W_b (support fraction)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 6, §3.1</i><br><br>Q_b = S_b / W_b, the fraction of committee-union weight supporting block b.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.Q</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:44 · <i>def</i></sub><pre>noncomputable def Q (A) (cm) (V : View n P) (b : Block n) (s : Slot) : Weight := S A cm V b s / W A cm b s</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### J_b — honest part of W_b

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (Def 7 support)</i><br><br>J_b: the honest part of W_b — the anchor-weight of honest validators in the committee union over [psPlus1 b, s].

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.J</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:49 · <i>def</i></sub><pre>def J (A) (cm) (fm : FaultModel n) (b : Block n) (s : Slot) : Weight := totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i =&gt; i ∈ fm.honest))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### H_b — honest part of S_b

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (Def 7 support)</i><br><br>H_b: the honest part of S_b — the anchor-weight of honest validators in the committee union whose effective vote up to s supports b.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.H</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:53 · <i>def</i></sub><pre>noncomputable def H (A) (cm) (fm) (V) (b) (s) : Weight := totalWeight A ((committeeUnion cm b.psPlus1 s).filter (fun i =&gt; i ∈ fm.honest ∧ V.supportsLMD b i s = true))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Definition 7 — P_b = H_b / J_b (honest LMD-GHOST safety indicator)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 7, §3.1</i><br><br>P_b = H_b / J_b, the honest LMD-GHOST safety indicator (honest supporters of b as a fraction of honest committee-union weight). This is the recurrence-robust quantity maintained by the engine proof.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.Phon</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:60 · <i>def</i></sub><pre>noncomputable def Phon (A) (cm) (fm) (V) (b) (s) : Weight := H A cm fm V b s / J A cm fm b s</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; named Phon to avoid clash with payload type variable P

#### W_p — proposer boost weight

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (proposer boost W_p)</i><br><br>W_p^C = pb · W_t^C: proposer boost as a fraction pb of the total validator-set weight at anchor A.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.Wp</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:65 · <i>def</i></sub><pre>def Wp (A : Anchor n) (pb : Weight) : Weight := pb * totalWeight A Finset.univ</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Definition 8 — single-block safety threshold ½(1 + W_p/W_b) + β

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 8, §3.1 (right-hand side); cf. Def 10 / consensus-specs PR #4747</i><br><br>The Definition 8 single-block threshold right-hand side: ½(1 + W_p/W_b) + β. A block is one-confirmed when Q_b exceeds this.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.safetyThreshold</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Weights.lean:68 · <i>def</i></sub><pre>def safetyThreshold (A) (cm) (fm : FaultModel n) (pb : Weight) (b : Block n) (s : Slot) : Weight := (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β</pre>

</td>
</tr>
</table>

> **Faithfulness:** clean Def 8; factored into a named def so the deployed Def 10 / PR #4747 refined predicate (support_discount, adversarial_weight, ρ/π/ϵ balance terms) is a model-level localized swap. Caveat (docstring): localization is at the DEFINITION layer only—the proofs unfold this exact Def-8 shape, so adding Def-10 terms is NOT a proof-free swap.

#### Definition 8 — isOneConfirmed (single-block check)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 8, §3.1</i><br><br>The Definition 8 single-block check: Q_b &gt; safetyThreshold, evaluated at slot(t)-1.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.isOneConfirmed</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Confirm.lean:20 · <i>def</i></sub><pre>def isOneConfirmed (τ) (fm) (cm) (pb) (A) (V) (b : Block n) (t : Time) : Prop := Q A cm V b (τ.slotOf t - 1) &gt; safetyThreshold A cm fm pb b (τ.slotOf t - 1)</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; evaluated at slot(t)-1

#### Definition 8 — isLMDGHOSTSafe (ancestor lift)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 8, §3.1</i><br><br>Definition 8: block b is LMD-GHOST-safe when every ancestor b' ≼ b is either genesis or one-confirmed. Filter-agnostic (the eligibility filter enters only the fork choice).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.isLMDGHOSTSafe</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Confirm.lean:25 · <i>def</i></sub><pre>def isLMDGHOSTSafe (τ) (fm) (cm) (pb) (A) (V) (b : Block n) (t : Time) : Prop := ∀ ⦃b' : Block n⦄, b' ≼ b → b' = Block.genesis ∨ isOneConfirmed τ fm cm pb A V b' t</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; filter-agnostic

#### Algorithm 4 — highestConfirmedSinceEpoch

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 Algorithm 4</i><br><br>Algorithm 4: the highest-slot block that is LMD-GHOST-safe in v's view at the start of some slot in [fslot e + 1, slot(t)] (each block evaluated at its slot's start, anchored at gj there), defaulting to genesis. Search starts at the SECOND slot of epoch e (fslot e + 1).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.highestConfirmedSinceEpoch</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Rule.lean:23 · <i>def</i></sub><pre>noncomputable def highestConfirmedSinceEpoch (τ) (fm) (cm) (pb) (gj) (𝒱) (v) (e : Epoch) (t : Time) : Block n := let cand := (Finset.Icc (τ.fslot e + 1) (τ.slotOf t)).biUnion (fun s' =&gt; (𝒱 v (τ.st s')).blocks.filter (fun b' =&gt; isLMDGHOSTSafe τ fm cm pb (gj 𝒱 v (τ.st s')) (𝒱 v (τ.st s')) b' (τ.st s'))); match cand.toList.argmax (·.slot) with | some b =&gt; b | none =&gt; Block.genesis</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; `gj` is an abstract balance-anchor parameter whose checkpoint realization is supplied by the HFC layer.

#### Algorithm 4 — isConfirmed

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 Algorithm 4</i><br><br>Algorithm 4: b is confirmed iff it is an ancestor of the highest confirmed block of the previous epoch (epochOf(slotOf t) - 1).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.isConfirmed</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Rule.lean:36 · <i>def</i></sub><pre>def isConfirmed (τ) (fm) (cm) (pb) (gj) (𝒱) (v) (b : Block n) (t : Time) : Prop := b ≼ highestConfirmedSinceEpoch τ fm cm pb gj 𝒱 v (τ.epochOf (τ.slotOf t) - 1) t</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; previous-epoch (epoch t-1) anchoring

#### Security guard sg(b,t) (Theorem 1 guard)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 Theorem 1 (guard)</i><br><br>Security guard sg(b,t): b's epoch is recent (epochOf(slotOf t) ≤ epochOf(b.slot) + 1) and gst precedes the first slot of the previous epoch (AfterGST at st(fslot(epochOf(slotOf t) - 1))).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.sg</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Rule.lean:43 · <i>def</i></sub><pre>def sg (τ : Timing) (b : Block n) (t : Time) : Prop := τ.epochOf (τ.slotOf t) ≤ τ.epochOf b.slot + 1 ∧ τ.AfterGST (τ.st (τ.fslot (τ.epochOf (τ.slotOf t) - 1)))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Assumption 2 — CommitteeHonestMajority

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3 Assumption 2 (bridge for Lemmas 3-4)</i><br><br>Assumption 2: over every committee union (at anchor A), honest weight is at least (1 - β) of the total — the bridge from the all-voter Q-threshold (Def 8) to an honest majority (Lemmas 3-4); β &lt; 1/3 alone is not enough.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.CommitteeHonestMajority</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Assumptions.lean:21 · <i>assumption</i></sub><pre>def CommitteeHonestMajority (fm) (cm) (A : Anchor n) : Prop := ∀ lo hi : Slot, (1 - fm.β) * totalWeight A (committeeUnion cm lo hi) ≤ totalWeight A ((committeeUnion cm lo hi).filter (fun i =&gt; i ∈ fm.honest))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Assumption 1 — StaticBalances

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3 Assumption 1 (static balances; Lemma 6 GJ-weight non-increase)</i><br><br>Assumption 1 (static balances): every anchor produced by gj assigns the same balance to each validator — the validator set and balances are static (except slashing). Implies the GJ-weight-non-increase condition of Lemma 6.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.StaticBalances</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Assumptions.lean:46 · <i>assumption</i></sub><pre>def StaticBalances (gj) (𝒱) : Prop := ∀ (v) (t) (v') (t') (i : Validator n), (gj 𝒱 v t).bal i = (gj 𝒱 v' t').bal i</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### Assumption 1 corollary — CommitteeCoversEpoch (full-epoch coverage)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Lemma 8 (lem:canonical-for-an-epoch-implies-q-satisfied); Assumption-1 corollary</i><br><br>Assumption-1 corollary: over a full epoch e (slots [fslot e, lslot e]) the committees together cover the whole validator set (committee union = univ). Used verbatim in Lemma 8: delivers (i) W_{b'}^{slot(t')-1} = totalWeight univ so Wp/W_{b'} = pb, and (ii) every honest validator votes at some slot of epoch e (so H = J). Parameterized by the single operative epoch e, matching the paper.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.CommitteeCoversEpoch</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Assumptions.lean:62 · <i>assumption</i></sub><pre>def CommitteeCoversEpoch (τ) (cm) (e : Epoch) : Prop := committeeUnion cm (τ.fslot e) (τ.lslot e) = Finset.univ</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; epoch taken as a parameter rather than ∀ e, matching the paper's monotonicity step

#### AnchorsCoincide (§3.1 specialization of Lemma 6 hyp (4))

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Lemma 6, hypothesis (4) — §3.1 specialization</i><br><br>Anchor-coincidence premise: every honest validator's greatest-justified anchor (read at any slot's start view) coincides with the engine anchor C. Strictly implied by StaticBalances with C := gj 𝒱 v t. Pins honest voters' fork-choice anchor to C, so an honest vote for its own gj-head is a vote for the C-head the induction reasons about.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.AnchorsCoincide</code><br><sub>FastConfirmation/Paper/LMDGhost/Model/Assumptions.lean:72 · <i>assumption</i></sub><pre>def AnchorsCoincide (gj) (𝒱) (fm) (τ) (C : Anchor n) : Prop := ∀ ⦃j : Validator n⦄, j ∈ fm.honest → ∀ (kk : Slot), gj 𝒱 j (τ.st kk) = C</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful

#### NeverFiltered (eligibility-stability statement)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 (eligibility/never-filter premise; trivial for plain LMD-GHOST)</i><br><br>Every ancestor of b stays eligible (unfiltered) in every honest view from st(slot(t)) onward. Trivial for trivialFilter (plain LMD-GHOST).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.NeverFiltered</code><br><sub>FastConfirmation/Paper/LMDGhost/TheoremStatements.lean:35 · <i>statement</i></sub><pre>def NeverFiltered (τ) (fm) (flt : BlockFilter n P) (𝒱) (b : Block n) (t : Time) : Prop := ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' : Block n⦄, b' ≼ b → flt (𝒱 w t') t' b'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; the public §3.1 theorems use trivialFilter

#### NeverFilteredFromHead (functional/joint-induction never-filter)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §3.1 / §4 (functional never-filter form; HeadFutureAgreement's hNFilOfHead antecedent)</i><br><br>NeverFiltered in joint-induction functional form: filter-eligibility of every b' ≼ b at the cutoff slot k is granted GIVEN head safety for b at all earlier honest views at slot boundaries j &lt; k. NeverFiltered(k) is a function of head-safety(&lt;k), never head-safety(k), so no circularity. A static NeverFiltered is a special case (the head-safety antecedent is ignored). The §4 proof builds the genuinely functional form.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.NeverFilteredFromHead</code><br><sub>FastConfirmation/Paper/LMDGhost/TheoremStatements.lean:50 · <i>statement</i></sub><pre>def NeverFilteredFromHead (τ) (fm) (gj) (boost) (pb) (flt) (𝒱) (b) (t) : Prop := ∀ ⦃k : Slot⦄, τ.slotOf t ≤ k → (∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j &lt; k → ∀ ⦃i' ∈ fm.honest⦄, b ≼ forkChoiceHead τ (gj 𝒱 i' (τ.st j)) boost pb flt (𝒱 i' (τ.st j)) (τ.st j)) → ∀ ⦃w ∈ fm.honest⦄ ⦃t' : Time⦄, τ.slotOf t' = k → τ.st (τ.slotOf t) ≤ t' → ∀ ⦃b' ≼ b⦄, flt (𝒱 w t') t' b'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; the §4-reuse functional form, no circularity (NeverFiltered(k) depends on head-safety(&lt;k))

#### HeadFutureAgreement — reusable engine (≈ Lemma 6)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 ≈ Lemma 6, §3.1 (filter-generic, arbitrary-anchor engine)</i><br><br>Reusable engine (≈ Lemma 6): filter-generic, arbitrary-anchor head safety and future agreement — a block safe in some honest view at t is, from st(slot(t)) on, on every honest validator's filtered LMD-GHOST head. AfterGST(st(slot(t)-1)) places gst before the slot BEFORE the safe slot (base supporters voted by slot(t)-1). P = H/J (Def 7) is the maintained quantity; CommitteeHonestMajority (Assumption 2) is the only honest-fraction hypothesis. §4 HFC reuses this at flt := ffgFilter.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.HeadFutureAgreement</code><br><sub>FastConfirmation/Paper/LMDGhost/TheoremStatements.lean:88 · <i>statement</i></sub><pre>def HeadFutureAgreement (τ) (flt : BlockFilter n P) : Prop := ∀ {fm cm pb gj boost 𝒱} (C : Anchor n), Synchrony … → HonestNoForgery … → HonestBehavior … → ViewsValid … → CommitteeHonestMajority fm cm C → 0 ≤ pb → AnchorsCoincide gj 𝒱 fm τ C → ∀ {v b t}, v ∈ fm.honest → b.WellFormed → b.slot ≤ τ.slotOf t → 1 ≤ τ.slotOf t → τ.AfterGST (τ.st (τ.slotOf t - 1)) → isLMDGHOSTSafe τ fm cm pb C (𝒱 v t) b t → NeverFiltered τ fm flt 𝒱 b t → ∀ ⦃w ∈ fm.honest⦄ ⦃t'⦄, τ.st (τ.slotOf t) ≤ t' → b ≼ forkChoiceHead τ C boost pb flt (𝒱 w t') t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; filter-generic + arbitrary anchor C so §4 reuses verbatim. Extra premises (HonestNoForgery, ViewsValid, AnchorsCoincide, well-formedness) are faithful well-formedness/honesty premises mapping to Lemma 6

#### Theorem 1, Safety half (Definition 4)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Theorem 1 (safety), Definition 4, §3.1</i><br><br>Theorem 1, Safety half (Definition 4) for plain LMD-GHOST: a confirmed block (isConfirmed under guard sg) is, from some time t0 on, on every honest validator's LMD-GHOST head. Uses trivialFilter.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.Theorem1_Safety</code><br><sub>FastConfirmation/Paper/LMDGhost/TheoremStatements.lean:109 · <i>statement</i></sub><pre>def Theorem1_Safety (τ) (gj) : Prop := ∀ {fm cm pb boost 𝒱}, Synchrony … → HonestNoForgery … → HonestBehavior … trivialFilter 𝒱 → ViewsValid … → (∀ ⦃w t⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) → WellFormedBoost τ boost → 0 ≤ pb → StaticBalances gj 𝒱 → ∀ {v b t}, v ∈ fm.honest → sg τ b t → isConfirmed τ fm cm pb gj 𝒱 v b t → ∃ t0 : Time, ∀ ⦃w ∈ fm.honest⦄ ⦃t'⦄, t0 ≤ t' → b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb trivialFilter (𝒱 w t') t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; instantiates the engine at trivialFilter; CommitteeHonestMajority supplied per (gj 𝒱 w t) anchor

#### Theorem 1, Monotonicity half (Definition 4)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Theorem 1 (monotonicity), Definition 4, Assumption 4 (assum:beta-lmd-monotonicity), Lemma 8</i><br><br>Theorem 1, Monotonicity half (Definition 4): once confirmed, always confirmed. Needs the tighter Assumption 4, β &lt; ¼(1 - pb) (paper β &lt; ¼(1 - p/E)), plus CommitteeCoversEpoch (Assumption-1 corollary) which pins the later-epoch threshold to ½(1 + pb) + β, dominated by Assumption 4 (Lemma 8).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.LMDGhost.Theorem1_Monotonicity</code><br><sub>FastConfirmation/Paper/LMDGhost/TheoremStatements.lean:138 · <i>statement</i></sub><pre>def Theorem1_Monotonicity (τ) (gj) : Prop := ∀ {fm cm pb boost 𝒱}, Synchrony … → HonestNoForgery … → HonestBehavior … trivialFilter 𝒱 → ViewsValid … → (∀ ⦃w t⦄, CommitteeHonestMajority fm cm (gj 𝒱 w t)) → WellFormedBoost τ boost → 0 ≤ pb → StaticBalances gj 𝒱 → fm.β &lt; (1 - pb) / 4 → ∀ {v b t t'}, v ∈ fm.honest → sg τ b t → t ≤ t' → CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) → isConfirmed τ fm cm pb gj 𝒱 v b t → isConfirmed τ fm cm pb gj 𝒱 v b t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; β &lt; (1 - pb)/4 is Assumption 4. The denominator 4 is required by `1 - 2β &gt; ½(1 + pb)`; a denominator of 2 would admit β &gt; 1/3.

## §4 HFC model (defs)

#### Checkpoint — FFG-Casper checkpoint (block, epoch)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1; explainer p.1 "Checkpoints"</i><br><br>A checkpoint C = (block(C), epoch(C)): a block together with the epoch at which it is checkpointed. Checkpoints are "blocks positioned at the onset of an epoch."

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.Checkpoint</code><br><sub>FastConfirmation/Paper/HFC/Model/Checkpoint.lean:25 · <i>structure</i></sub><pre>structure Checkpoint (n : ℕ) where
  block : Block n
  epoch : Epoch
  deriving DecidableEq</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful. `block` is the actual `Block n` so checkpoint/block compatibility reuses Core ancestry `≼` directly. `deriving DecidableEq` is load-bearing (propagates to FFGVote / Message / View Finset machinery).

#### FFGVote — source→target checkpoint link (the §4 Payload)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1; explainer p.2 "FFG vote: checkpoint-level vote"</i><br><br>An FFG-Casper vote a = ⟨C_s, C_t⟩: a source→target checkpoint link.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.FFGVote</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGVote.lean:24 · <i>structure</i></sub><pre>structure FFGVote (n : ℕ) where
  source : Checkpoint n
  target : Checkpoint n
  deriving DecidableEq</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful. Signer/slot ride in the enclosing Message.ghost (GhostVote); the payload is just the link. Setting Payload := FFGVote n makes Message n (FFGVote n) carry both the GHOST envelope and the FFG vote payload. Block-contained AU carriers set `countsForLMD := false`, so they count for FFG links without entering LMD latest-vote support.

#### genesisCheckpoint — (genesis, 0) base/default

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (genesis checkpoint)</i><br><br>The genesis checkpoint (genesis, 0); the base of the Justified induction and the default greatest-justified / greatest-finalized value.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.genesisCheckpoint</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:62 · <i>def</i></sub><pre>def genesisCheckpoint : Checkpoint n := ⟨Block.genesis, 0⟩</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful.

#### View.ffgVotes — FFG votes carried in a view

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (FFG votes in a view)</i><br><br>The FFG votes carried in a view, read off the extra payloads of the view's messages.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.View.ffgVotes</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:79 · <i>def</i></sub><pre>def View.ffgVotes (V : View n (FFGVote n)) : Finset (FFGVote n) :=
  V.msgs.image Message.extra</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful. Declared in FastConfirmation.View namespace so V.ffgVotes dot-notation resolves.

#### linkWeight — total signer balance of a Cs→Ct link

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (supermajority links)</i><br><br>Source→target link weight at anchor A: total balance of signers whose FFG vote in V is exactly src → tgt (the link analogue of latestSupportWeight).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.linkWeight</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:259 · <i>def</i></sub><pre>noncomputable def linkWeight (A : Anchor n) (V) (src tgt : Checkpoint n) : Weight :=
  totalWeight A (univ.filter (fun i =&gt; ∃ m ∈ V.msgs,
    m.ghost.validator = i ∧ m.extra.source = src ∧ m.extra.target = tgt))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful, weight-only. Pure balance sum at anchor A; no β.

#### Justified — inductive ≥2/3 supermajority-link justification

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (FFG justification)</i><br><br>C is justified in V (inductive): a genesis-epoch checkpoint (base), or the target of a ≥ 2/3 weighted supermajority link from an already-justified source: 3·linkWeight(Cs,Ct) ≥ 2·W.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.Justified</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:267 · <i>def</i></sub><pre>inductive Justified (A) (V) : Checkpoint n → Prop
  | base : Justified A V genesisCheckpoint
  | link {Cs Ct} (hs : Justified A V Cs)
      (hsup : 3 * linkWeight A V Cs Ct ≥ 2 * totalWeight A univ) :
      Justified A V Ct</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful, pure weight predicate (no β). Minimal §4 slice: no full Casper slashing/link-graph machinery.

#### Finalized — justified with justified next-epoch successor

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (FFG finalization)</i><br><br>C is finalized in V: justified, with its immediate next-epoch successor (a descendant checkpoint one epoch later) also justified.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.Finalized</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:276 · <i>def</i></sub><pre>def Finalized (A) (V) (C) : Prop :=
  Justified A V C ∧ ∃ C', C'.epoch = C.epoch + 1 ∧ C.block ≼ C'.block ∧ Justified A V C'</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful, weight-only (1-finality, immediate-successor form).

#### mentionedCheckpoints — candidate set for greatest* selectors

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (checkpoints appearing in a view)</i><br><br>The candidate checkpoints the greatest* selectors range over: every source and target appearing in V's FFG votes, together with the genesis checkpoint. GJ/GF are realized only against checkpoints actually mentioned in the view.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.mentionedCheckpoints</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:284 · <i>def</i></sub><pre>noncomputable def mentionedCheckpoints (V) : Finset (Checkpoint n) :=
  insert genesisCheckpoint (V.ffgVotes.image FFGVote.source ∪ V.ffgVotes.image FFGVote.target)</pre>

</td>
</tr>
</table>

> **Faithfulness:** Lean-internal finiteness device making the max-by-epoch argmax selectors total; faithful as the realized candidate set.

#### greatestJustified — global max-by-epoch justified (GU, any epoch)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (no direct paper counterpart — see note)</i><br><br>Max-by-epoch over the justified mentioned checkpoints; default genesis if none. The global, view-wide, any-epoch greatest justified checkpoint.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.greatestJustified</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:295 · <i>def</i></sub><pre>noncomputable def greatestJustified (A) (V) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter (Justified A V ·)).toList.argmax (·.epoch) with
  | some C =&gt; C | none =&gt; genesisCheckpoint</pre>

</td>
</tr>
</table>

> **Faithfulness:** Lean-internal helper per its own docstring: NO direct paper counterpart (GU(b) is chain-relative; public realized GJ(V,t) is `ruleRealizedGJ`). Used only to epoch-dominate the view-realized proof selectors.

#### greatestFinalized — global max-by-epoch finalized (GF)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (greatest finalized checkpoint GF)</i><br><br>The greatest finalized checkpoint GF: max-by-epoch over the finalized mentioned checkpoints; default genesis if none.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.greatestFinalized</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:303 · <i>def</i></sub><pre>noncomputable def greatestFinalized (A) (V) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter (Finalized A V ·)).toList.argmax (·.epoch) with
  | some C =&gt; C | none =&gt; genesisCheckpoint</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful (the GF the ffgFilter reads).

#### greatestJustifiedOfChain — view-realized analogue of GU(b)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 / Def 1 (GU(b) = "greatest justified checkpoint in the chain of b")</i><br><br>GU(b): the greatest justified checkpoint in the chain of b, computed from AU(b). Max-by-epoch over justified mentioned checkpoints whose block is an ancestor of b (C.block ≼ b); default genesis.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.greatestJustifiedOfChain</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:315 · <i>def</i></sub><pre>noncomputable def greatestJustifiedOfChain (A) (V) (b : Block n) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter
      (fun C =&gt; Justified A V C ∧ C.block ≼ b)).toList.argmax (·.epoch) with
  | some C =&gt; C | none =&gt; genesisCheckpoint</pre>

</td>
</tr>
</table>

> **Faithfulness:** view-realized analogue, not the AU `GU(b)` itself. The paper-facing AU selector is `GU A τ blockVotes b`; this helper ranges over checkpoints justified in a view and supports the never-filter proofs. It is chain-relative: its epoch can precede that of global `greatestJustified`, which is how the proof-facing `votingSource` ages when chain(b) stops being re-justified. No epoch cut (distinct from `gjblock`).

#### greatestRealizedJustified — view-realized proof helper for GJ(V,t)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1, Def 3</i><br><br>The realized greatest justified checkpoint GJ(𝒱,t) = max{vs(b,t) : slot(b) ≤ slot(t)}, where `vs` is AU/source-target based on `chain(b)`.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.greatestRealizedJustified</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:339 · <i>def</i></sub><pre>noncomputable def greatestRealizedJustified (A) (τ : Timing) (V) (t : Time) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter
      (fun C =&gt; Justified A V C ∧ C.epoch &lt; τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | some C =&gt; C | none =&gt; genesisCheckpoint</pre>

</td>
</tr>
</table>

> **Faithfulness:** proof-facing view-realized collapse, not the public paper selector. The AU filter selector is `ruleRealizedGJ`, which takes the literal max over `ruleVotingSource` for known non-future blocks. `FilterSelectorAgreementAt` is the explicit bridge between this helper and the AU selector.

#### votingSource — view-realized analogue of vs(b,t)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1, Def 2</i><br><br>The voting source vs(b,e): gjblock(b) (Def 1 — the greatest justified checkpoint in chain(b) of epoch strictly below epoch(b)) if epoch(b) = e, otherwise gujblock(b) = GU(b) (the greatest justified checkpoint in chain(b), no epoch cut). [vs(b,t) := vs(b, epoch(t)).] Both branches are chain-relative and computed from AU(b), so the function is determined by b's chain, not by a validator's current view.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.votingSource</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:377 · <i>def</i></sub><pre>noncomputable def votingSource (A) (τ) (V) (b : Block n) (t : Time) : Checkpoint n :=
  if τ.epochOf b.slot = τ.epochOf (τ.slotOf t) then gjblock A τ V b
  else greatestJustifiedOfChain A V b</pre>

</td>
</tr>
</table>

> **Faithfulness:** This Lean helper is the view-realized analogue of Def 2, not the paper-literal AU function. Its two branches are chain-relative inside the view, but they route through view-level `Justified A V`. The AU-side Def-2 selector is `onChainVotingSource A τ blockVotes b t`, with same-epoch branch `onChainGJBlock` and else branch `GU`. The same totalization caveat applies: `epoch(b)>epoch(t)` is assigned the else branch, but is unreachable for causal in-view blocks.

#### FinalizedPrefixOfJustified — GF ⪯ GJ prefix property (named premise)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (finalized chain is a prefix of the justified chain)</i><br><br>The greatest finalized checkpoint's block is an ancestor of every justified checkpoint of weakly-greater epoch: ∀ Cf Cj, Finalized Cf → Justified Cj → Cf.epoch ≤ Cj.epoch → Cf.block ≼ Cj.block.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.FinalizedPrefixOfJustified</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:391 · <i>assumption</i></sub><pre>def FinalizedPrefixOfJustified (A) (V) : Prop :=
  ∀ ⦃Cf Cj⦄, Finalized A V Cf → Justified A V Cj → Cf.epoch ≤ Cj.epoch → Cf.block ≼ Cj.block</pre>

</td>
</tr>
</table>

> **Faithfulness:** Carried as a named structural premise: NOT derivable in the minimal §4 slice (Justified/Finalized are pure weight predicates with no chain linkage between distinct justified checkpoints). Its faithful proof is the Casper slashing / 2/3-link-intersection argument behind FFG_AccountableSafety (out of scope).

#### gjFFG — Def-3 gj realization as constant Stakes (Assumption 1)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 3 / explainer footnote 2; Assumption 1 (static balances)</i><br><br>The §3.1 abstract gj : ViewFamily → Validator → Time → Anchor realized by FFG. The §3.1 engine consumes gj/C only as a Stakes balance source; under Assumption 1 (static validator set/balances modulo slashing) the FFG anchor's balances are the static deployment balances bal₀ regardless of which checkpoint is GJ, so the faithful minimal realization is a constant Stakes.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.gjFFG</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:405 · <i>def</i></sub><pre>noncomputable def gjFFG (bal₀ : Stakes n) :
    ViewFamily n (FFGVote n) → Validator n → Time → Anchor n :=
  fun _ _ _ =&gt; bal₀</pre>

</td>
</tr>
</table>

> **Faithfulness:** Constant-balances realization (Assumption 1). Checkpoint structure is read by ffgFilter (which inspects GJ(V,t)), not by this balance anchor; the §3.1 AnchorsCoincide / StaticBalances premises then discharge exactly as §3.1.

#### boundaryBlock — epoch-boundary block of a chain at a slot bound

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (boundary block of a chain)</i><br><br>The epoch-boundary block of a chain at bound: the highest-slot ancestor of b whose slot is ≤ bound (structural recursion down the parent chain).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.boundaryBlock</code><br><sub>FastConfirmation/Paper/HFC/Model/Rule.lean:24 · <i>def</i></sub><pre>def boundaryBlock (bound : Slot) : Block n → Block n
  | Block.genesis =&gt; Block.genesis
  | Block.mk bid p s =&gt; if s ≤ bound then Block.mk bid p s else boundaryBlock bound p</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful. With bound := fslot e (via checkpointOf) gives the epoch-e onset boundary block.

#### checkpointOf — chkp / C(b,e), epoch-e onset boundary checkpoint

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 (Def of chkp)</i><br><br>C(b,e): the checkpoint of b at epoch e — the epoch-e onset (start) boundary block of chain(b), tagged with e: the highest-slot ancestor of b with slot ≤ fslot e (the first slot of epoch e). Checkpoints are "blocks positioned at the onset of an epoch."

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.checkpointOf</code><br><sub>FastConfirmation/Paper/HFC/Model/Rule.lean:43 · <i>def</i></sub><pre>def checkpointOf (τ : Timing) (b : Block n) (e : Epoch) : Checkpoint n :=
  ⟨boundaryBlock (τ.fslot e) b, e⟩</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful, onset convention (`fslot e`). For a same-epoch head this is a settled ancestor of `b` (not `b` itself), so two honest validators whose heads descend from a canonical `b` compute the same `C(b,e)`—load-bearing for the §4.1 certificate because prefix agreement `b ⪯ head` suffices without head convergence. An `lslot e` epoch-end convention would instead require head equality.

#### gjblock — view-realized analogue of gjblock(b)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Def 1, l.289-294</i><br><br>gjblock(b): the greatest justified checkpoint in AU(b) whose block is in the chain of b and whose epoch is strictly below epoch(b). Max-by-epoch over justified mentioned checkpoints C with C.block ≼ b and C.epoch &lt; epoch(b); default genesis. Both the previous-epoch anchor the confirmation rule re-roots at (Algorithm 1 l.2351-2352) AND Def 2's same-epoch voting source vs(b,t) (epoch(b)=epoch(t)).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.gjblock</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean:352 · <i>def</i></sub><pre>noncomputable def gjblock (A) (τ) (V) (b : Block n) : Checkpoint n :=
  match ((mentionedCheckpoints V).filter (fun C =&gt;
      Justified A V C ∧ C.block ≼ b ∧ C.epoch &lt; τ.epochOf b.slot)).toList.argmax (·.epoch) with
  | some C =&gt; C | none =&gt; genesisCheckpoint</pre>

</td>
</tr>
</table>

> **Faithfulness:** view-realized analogue. Distinct from `greatestJustifiedOfChain` (no epoch cut) and from `greatestRealizedJustified = GJ(V,t)`: `gjblock` has both the chain restriction and the epoch &lt; epoch(b) cut, but it ranges over view-level `Justified`. The AU-side Def-1 selector is `onChainGJBlock`.

#### linkWeightUpTo — ffgvalsettoslot[to=s] committee-slot-restricted link weight

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 l.2527 (ffgvalsettoslot)</i><br><br>The ffgvalsettoslot[source=src, target=tgt, to=upTo] weight: the balance of validators in the committee of slots [firstslot(epoch tgt), upTo] whose FFG vote in V is exactly src → tgt. The committee-slot-restricted analogue of linkWeight.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.linkWeightUpTo</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGRule.lean:46 · <i>def</i></sub><pre>noncomputable def linkWeightUpTo (A) (cm : Committees n) (τ) (V) (src tgt : Checkpoint n) (upTo : Slot) : Weight :=
  totalWeight A ((committeeUnion cm (τ.fslot tgt.epoch) upTo).filter (fun i =&gt;
    ∃ m ∈ V.msgs, m.ghost.validator = i ∧ m.extra.source = src ∧ m.extra.target = tgt))</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful. Committee union runs from fslot(epoch tgt) to upTo.

#### willChkpBeJustified — Algorithm 1 l.2334-2343 local FFG-weight reservation

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Algorithm 1, l.2334-2343</i><br><br>willChkpBeJustified_v(b,e,t): the FFG votes for the link vs(b,t) → C(b,e) received so far (committee up to slot(t)-1) plus the honest (1-β) fraction of the remaining epoch-e committee [slot(t), lastslot(e)] reach 2/3·W net of the slashable bound min(W_e, β·W). Formula: linkWeightUpTo(vs(b,t), C(b,e), slot(t)-1) + (1-β)·W([slot(t), lslot e]) ≥ (2/3)·W + min(we, β·W).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.willChkpBeJustified</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGRule.lean:59 · <i>def</i></sub><pre>def willChkpBeJustified (bal₀) (cm) (fm) (we : Weight) (τ) (𝒱) (v) (b) (e : Epoch) (t : Time) : Prop :=
  linkWeightUpTo bal₀ cm τ (𝒱 v t) (ruleVotingSource bal₀ τ b t) (checkpointOf τ b e) (τ.slotOf t - 1)
    + (1 - fm.β) * totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e))
    ≥ (2 / 3) * totalWeight bal₀ Finset.univ + min we (fm.β * totalWeight bal₀ Finset.univ)</pre>

</td>
</tr>
</table>

> **Faithfulness:** Formula shape matches Algorithm 1, with source `vs(b,t)` represented by the AU-based `ruleVotingSource` over block-contained votes on `chain(b)`. Constant balances (bal₀): per-anchor weight_{C(b,e)} is totalWeight bal₀ (Assumption 1). we = W_e the max-slashable parameter (ffgEquivWeight, Assumption 5.2). Note the 2/3·W + min(we, βW) inequality form.

#### isConfirmedNoCaching — Algorithm 1 l.2344-2361, both branches

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 v3 Algorithm `alg:ffg`, l.2344-2361</i><br><br>isConfirmedNoCaching(b,t): per-block per-slot FFG confirmation. Current epoch (epoch(b)=epoch(t)): willChkpBeJustified(b, epoch(t), t), the GU-anchor precondition epoch(gjblock(b)) = epoch(t)-1, and isLMDGHOSTSafe(b, gjblock(b), t). Previous epoch (else): it is the epoch's first slot (slot(t)=firstslot(epoch(t))), willChkpBeJustified(b, epoch(t)-1, t), and ∃ witness b' ⪰ b in the view at st(slot(t)-1) of epoch &lt; epoch(t) whose voting source is recent (epoch(vs(b',t)) ≥ epoch(t)-2, lower bound only, l.2360), and isLMDGHOSTSafe(b, vs(b',t), t).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.isConfirmedNoCaching</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGRule.lean:108 · <i>def</i></sub><pre>noncomputable def isConfirmedNoCaching (bal₀) (fm) (cm) (pb we : Weight) (τ) (𝒱) (v) (b) (t) : Prop :=
  if τ.epochOf b.slot = τ.epochOf (τ.slotOf t) then
    willChkpBeJustified … b (τ.epochOf (τ.slotOf t)) t ∧
      (gjblock … b).epoch = τ.epochOf (τ.slotOf t) - 1 ∧
      isLMDGHOSTSafe … b t
  else
    τ.slotOf t = τ.fslot (τ.epochOf (τ.slotOf t)) ∧
      willChkpBeJustified … b (τ.epochOf (τ.slotOf t) - 1) t ∧
      ∃ b', b' ∈ (𝒱 v (τ.st (τ.slotOf t - 1))).blocks ∧ b ≼ b' ∧
        τ.epochOf b'.slot &lt; τ.epochOf (τ.slotOf t) ∧
        (ruleVotingSource … b' t).epoch ≥ τ.epochOf (τ.slotOf t) - 2 ∧
        isLMDGHOSTSafe … b t</pre>

</td>
</tr>
</table>

> **Faithfulness:** Paper branch structure and conjunct set, with no added rule conjuncts. The `vs` calls use the AU-based `ruleVotingSource` / `ruleGJBlock` selectors over block-contained votes on `chain(b)`. The previous-epoch branch carries only the paper's lower-bound recency epoch(vs(b',t)) ≥ epoch(t)−2; it has NO upper bound epoch(vs) ≤ epoch(t)−1 and NO vs(b',t).block ≼ b ancestor conjunct.

#### ffgFilterAt — FIL_hfc keep-predicate (§4 justification filter)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4 (FIL_hfc), confirmed vs arXiv HTML</i><br><br>FIL_hfc(𝒱,t) keeps block b iff: b ⪯ GJ(𝒱,t) (b ancestor of the greatest-justified block); OR b ⪰ block(GJ) and there is a leaf b' ⪰ b that descends from the greatest-finalized block, is no later than the current epoch, has no children in the view, and whose voting source is either GJ(𝒱,t) itself or no older than epoch(t)−2. Removes any block conflicting with GJ or descending from it but whose subtree has no leaf with a recent-enough voting source.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.ffgFilterAt</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGFilter.lean:52 · <i>def</i></sub><pre>def ffgFilterAt (A) (τ) (V) (t) (b : Block n) : Prop :=
  let gjC := ruleRealizedGJ A τ V t
  let gfC := ruleRealizedGF A τ V t
  b ≼ gjC.block ∨
    ( gjC.block ≼ b ∧ ∃ b' ∈ V.blocks, b ≼ b' ∧ gfC.block ≼ b' ∧
        τ.epochOf b'.slot ≤ τ.epochOf (τ.slotOf t) ∧
        eligibleChildren τ trivialFilter V t b' = ∅ ∧
        ( ruleVotingSource A τ b' t = gjC ∨
          (ruleVotingSource A τ b' t).epoch + 2 ≥ τ.epochOf (τ.slotOf t) ) )</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful filter shape. `GJ(V,t)` is `ruleRealizedGJ`, the literal max over AU `ruleVotingSource(b,t)` for known non-future blocks; `GF(V,t)` is `ruleRealizedGF`; the leaf source is AU `ruleVotingSource`. The proof layer uses `FilterSelectorAgreementAt` to reuse view-realized lemmas.

#### ffgFilter — FIL_hfc as the Core BlockFilter seam

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4 (LMD-GHOST-HFC = LMD-GHOST ∘ FIL_hfc)</i><br><br>The FIL_hfc filter realized as the Core BlockFilter seam at P := FFGVote n (the slot where trivialFilter sits in plain LMD-GHOST). The anchor it reads is the §4 GJ-anchor C.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.ffgFilter</code><br><sub>FastConfirmation/Paper/HFC/Model/FFGFilter.lean:67 · <i>def</i></sub><pre>def ffgFilter (A : Anchor n) (τ : Timing) : BlockFilter n (FFGVote n) :=
  ffgFilterAt A τ</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful seam swap (plain LMD-GHOST uses trivialFilter; §4 swaps in ffgFilter), leaving the §3.1 weight machinery filter-agnostic. §4 statements partially apply at the GJ-anchor C.

#### HonestFFGNoEquivocation — definitional honest FFG one-vote-per-slot discipline

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4 (honest FFG-Casper voting); FFG mirror of HonestBehavior.noEquivocation (FastConfirmation/Paper/Core/Model/Honest.lean)</i><br><br>Honest FFG non-equivocation (definitional): an honest committee member casts at most one FFG link vote per slot — its prescribed head-vote — whose source is the voting source vs(head, epoch(t)) (Def 2) of its own view and whose target is the checkpoint (at the slot's epoch) of its own LMD-GHOST-HFC fork-choice head. Any honest-attributed HonestCast FFG message is that prescribed cast.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HonestFFGNoEquivocation</code><br><sub>FastConfirmation/Paper/HFC/Model/HonestFFG.lean:46 · <i>assumption</i></sub><pre>def HonestFFGNoEquivocation (τ) (fm) (_cm) (bal₀) (boost) (pb) (𝒱) : Prop :=
  ∀ ⦃m⦄, HonestCast fm 𝒱 τ m →
    m.extra.target = checkpointOf τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 m.ghost.validator (τ.st m.ghost.slot)) boost pb (ffgFilter bal₀ τ) (𝒱 m.ghost.validator (τ.st m.ghost.slot)) (τ.st m.ghost.slot)) (τ.epochOf m.ghost.slot) ∧
    m.extra.source = ruleVotingSource bal₀ τ (forkChoiceHead τ …) (τ.st m.ghost.slot)</pre>

</td>
</tr>
</table>

> **Faithfulness:** Definitional honest behavior (not an additional economic assumption): the FFG mirror of GHOST noEquivocation. Source is the AU chain-relative source of the head (`ruleVotingSource(head,·)`), NOT the global greatest-justified. Pairs with HonestNoForgery (delivers HonestCast) to pin every honest FFG message to the prescribed head-checkpoint cast — consumed by the cross-epoch never-filter argument. Balances constant (bal₀ via gjFFG).

## §4 HFC statements (TheoremStatements.lean + ProvenTheorems.lean)

#### Assumption3 — alternative per-message FFG inclusion surface

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Assumption 5.3 (explainer p.2 "Assumption 3")</i><br><br>This is the per-message inclusion formulation: an honest committee member's FFG vote (riding in `extra`) cast in a slot ≤ s' is, by the next boundary st(s'+1), present in every honest view once slot s' itself is past gst. The Algorithm-1 theorem instead uses block-contained AU votes and `OnChainAnchorInterface`; see the AU sections below. Numbering caveat: arXiv "Assumption 3" is unrelated (no validator slashed); the Lean name follows the explainer.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.Assumption3</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:72 · <i>assumption</i></sub><pre>def Assumption3 (τ : Timing) (fm : FaultModel n) (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  ∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃m⦄ ⦃s'⦄, HonestCast fm 𝒱 τ m → m.ghost.slot ≤ s' →
    τ.AfterGST (τ.st s') → m ∈ (𝒱 w (τ.st (s' + 1))).msgs</pre>

</td>
</tr>
</table>

> **Faithfulness:** alternative surface, used only by `checkpoint_justified_of_canonical`. The Algorithm-1 facades use `OnChainAnchorInterface` over block-contained AU votes.

#### FFG accountable safety

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1, l.2522/2536/2538 (prop:gasper-basic:*)</i><br><br>The three accountable-safety consequences used by §4 are standard Gasper/Casper results: (1) no two conflicting checkpoints are both finalized; (2) two justified checkpoints in the same epoch have the same block (l.2536); and (3) the greatest finalized checkpoint's block is an ancestor of every justified checkpoint of weakly greater epoch (l.2538). All three follow from the same ≥2/3-supermajority-link and β&lt;1/3 no-double-vote argument. The Lean weight model does not encode slashing evidence, so it exposes these consequences as the explicit <code>FFG_AccountableSafety</code> premise.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.FFG_AccountableSafety</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:262 · <i>assumption</i></sub><pre>def FFG_AccountableSafety (A : Anchor n) (fm : FaultModel n) (𝒱 : ViewFamily n (FFGVote n)) : Prop :=
  (∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t C₁ C₂⦄, Finalized A (𝒱 w t) C₁ → Finalized A (𝒱 w t) C₂ → (C₁.block ~ C₂.block)) ∧
  (∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t C₁ C₂⦄, Justified A (𝒱 w t) C₁ → Justified A (𝒱 w t) C₂ → C₁.epoch = C₂.epoch → C₁.block = C₂.block) ∧
  (∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t⦄, FinalizedPrefixOfJustified A (𝒱 w t))</pre>

</td>
</tr>
</table>

> **Faithfulness:** scoped to honest views of the active view family, matching the Gasper/Casper safety consequences used by the proofs rather than asserting uniqueness for arbitrary syntactic views. `FFG_AccountableSafety` is an explicit premise of `ConfirmedNotFFGFiltered`, `HFC_Safety`, `HFC_Monotonicity`, and their `_Alg1` counterparts.

#### WillNoConflictingChkpBeJustified — the semantic FFG confirmation gate

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 / explainer Algorithm 1 l.15-16 (willNoConflictingChkpBeJustified)</i><br><br>The FFG confirmation gate: no checkpoint conflicting with the block's latest checkpoint will ever be justified in any honest view from st(slot(t)) on. Modeled at anchor C: for every honest w and every t' ≥ st(slotOf t), every checkpoint Cc justified in w's view at t' with epoch ≥ epoch(b) has its block compatible (~) with b — i.e. no conflicting checkpoint becomes justified.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.WillNoConflictingChkpBeJustified</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:156 · <i>def</i></sub><pre>def WillNoConflictingChkpBeJustified (C fm τ 𝒱 b t) : Prop :=
  ∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t'⦄, τ.st (τ.slotOf t) ≤ t' →
    ∀ ⦃Cc⦄, Justified C (𝒱 w t') Cc → τ.epochOf b.slot ≤ Cc.epoch → (b ~ Cc.block)</pre>

</td>
</tr>
</table>

> **Faithfulness:** the semantic gate; used by the gate-based `HFC_Safety` / `HFC_Monotonicity` formulation and derived rather than assumed by the `_Alg1` pair.

#### AU / GU / OnChainJustifiedAtTransition — block-contained on-chain FFG votes

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1, l.277-285</i><br><br>AU(b) is computed from FFG votes included in the blocks of chain(b). A checkpoint is justified on chain at an epoch transition when an epoch-N block on the chain carries enough included source→target votes from an already justified source to the chain checkpoint; later descendants inherit that AU fact.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>BlockFFGVotes / chainIncludedFFGVotes / OnChainJustifiedAtTransition / AU / GU / onChainGJBlock / onChainVotingSource / GF</code><br><sub>FastConfirmation/Paper/HFC/Model/Justification.lean · <i>defs</i></sub><pre>abbrev BlockFFGVotes (n) := Block n → Finset (Message n (FFGVote n))
def BlockFFGVotes.WellFormedOnChain (τ blockVotes tip) : Prop := …
def chainIncludedFFGVotes (blockVotes) : Block n → Finset (Message n (FFGVote n))
inductive OnChainJustified (A τ blockVotes) : Block n → Checkpoint n → Prop
def OnChainJustifiedAtTransition (A τ blockVotes b N C) : Prop
noncomputable def AU (A τ blockVotes b) : Finset (Checkpoint n)
noncomputable def GU (A τ blockVotes b) : Checkpoint n
noncomputable def onChainGJBlock (A τ blockVotes b) : Checkpoint n
noncomputable def onChainVotingSource (A τ blockVotes b t) : Checkpoint n</pre>

</td>
</tr>
</table>

> **Faithfulness:** simplified AU-style model. Blocks can contain any number of current/previous-epoch chain-targeted FFG votes; no capacity cap or execution participation flags are modeled. Reified block-contained messages are payload-only (`countsForLMD := false`) to avoid synthetic LMD support. Per-validator/per-epoch equivocations are ignored by the effective on-chain vote selectors. `OnChainJustifiedAtTransition` uses a witness epoch-N block in the chain, so AU facts persist to later chain tips. `onChainGJBlock` and `onChainVotingSource` are the AU-based Def-1/Def-2 selectors; `ruleRealizedGJ`/`ruleRealizedGF` are the paper-facing filter selectors. The `gjblock`/`votingSource` helpers are view-realized analogues for proofs. `OnChainAnchorInterface` includes `WellFormedOnChain`, scoped to the selected/rule-witness chain rather than every syntactic block.

#### OnChainAnchorInterface — AU realization and visibility bridge

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 l.280-281; §4 Algorithm 1 GU anchor</i><br><br>The paper assumes FFG votes available to an honest proposer can be included on the canonical chain, and that AU(b) facts computed from chain-carried votes are available to honest validators. In the simplified no-cap model, a block can include all known previous/current-epoch votes that target its chain checkpoints and filters known equivocators.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.OnChainAnchorInterface</code><br><sub>FastConfirmation/Paper/HFC/Model/Rule.lean · <i>defs</i></sub><pre>def OnChainAnchorWellFormed (A τ b) : Prop := …
def HonestProposerIncludesKnownVotes (fm τ 𝒱 tip) : Prop := …
def OnChainAnchorBlockAvailable (fm 𝒱 b t) : Prop := …
theorem OnChainAnchorBlockAvailable.of_blockRelay : …
def ViewReadsChainFFGVotes (τ 𝒱) : Prop :=
  … → BlockFFGVotes.WellFormedOnChain τ (blockContainedFFGVotes τ) b →
  … → m ∈ (𝒱 v t).msgs
def OnChainAnchorRealization (A fm τ 𝒱 b t) : Prop := …
def OnChainAnchorVisibility (A fm τ 𝒱 b t) : Prop := …
theorem OnChainAnchorVisibility.of_block_available : …
def OnChainAnchorInterface (A fm τ 𝒱 b t) : Prop :=
  OnChainAnchorWellFormed A τ b ∧
  HonestProposerIncludesKnownVotes fm τ 𝒱 b ∧
  OnChainAnchorBlockAvailable fm 𝒱 b (τ.st (τ.slotOf t)) ∧
  ViewReadsChainFFGVotes τ 𝒱 ∧
  OnChainAnchorRealization A fm τ 𝒱 b t
theorem OnChainAnchorInterface.justified : …
def OnChainAnchorInterfacesForRule (A fm τ 𝒱 b t) : Prop := …</pre>

</td>
</tr>
</table>

> **Faithfulness:** active AU bridge. It formalizes chain-scoped AU payload well-formedness, the simplified honest-proposer inclusion assumption, block availability at the interface boundary, and the rule-to-AU realization direction. `OnChainAnchorBlockAvailable.of_blockRelay` discharges block availability from `Synchrony.blockRelay`; `ViewReadsChainFFGVotes` records the local invariant that a known block's well-formed ancestry payloads are readable as view FFG messages. AU and view justification are both source→target-link based, so `OnChainAnchorVisibility.of_block_available` derives AU-to-view `Justified` visibility from well-formedness, block availability, and readability. `OnChainAnchorInterfacesForRule` scopes this to the selected Algorithm-1 block and previous-slot witness blocks, not arbitrary forks. Block caps and execution participation flags are intentionally omitted.

#### GreatestJustifiedAnchorPrecondition — the rule's GU-anchor local check

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Algorithm 1 l.21-22 / ln:ffg:gjblock-from-previous-epoch, l.2349</i><br><br>The confirmation rule's GU-anchor precondition: for b to be confirmed, the greatest justified checkpoint on chain(b) is at epoch exactly epoch(b)−1, justified in an honest view at t. A local check the rule performs (part of what "confirmed" means), not an environmental assumption.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.GreatestJustifiedAnchorPrecondition</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:167 · <i>def</i></sub><pre>def GreatestJustifiedAnchorPrecondition (C fm τ 𝒱 b t) : Prop :=
  ∃ GUc : Checkpoint n, GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b ∧
    ∃ v, v ∈ fm.honest ∧ Justified C (𝒱 v t) GUc</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful local check (Alg 1 l.21-22)

#### GreatestJustifiedAnchorInputs — §4 honest-view GU-anchor inputs at b

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Algorithm 1 l.21-22 (re-root at previous-epoch greatest unrealized justified GU_conf)</i><br><br>This interface records the anchor facts used when Algorithm 1 re-roots at the previous epoch's greatest unrealized justified checkpoint. In every honest view at every t' ≥ st(slot(t)), it provides: (1) a justified checkpoint GUc at epoch exactly epoch(b)−1 with GUc.block ≼ b; (2) epoch(greatestFinalized) &lt; epochOf(slotOf t'), expressing that the greatest finalized checkpoint precedes the current epoch; and (3) <code>FilterSelectorAgreementAt</code>, identifying the proof-facing realized selectors with Algorithm 1's selectors. A separate GU-root slot bound is unnecessary because the comparability split covers both ancestry directions; the interface does not assert block(GJ) ≼ b directly.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.GreatestJustifiedAnchorInputs</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:141 · <i>def</i></sub><pre>def GreatestJustifiedAnchorInputs (C fm τ 𝒱 b t) : Prop :=
  ∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t'⦄, τ.st (τ.slotOf t) ≤ t' →
    (∃ GUc, Justified C (𝒱 w t') GUc ∧ GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b) ∧
      (greatestFinalized C (𝒱 w t')).epoch &lt; τ.epochOf (τ.slotOf t') ∧
      FilterSelectorAgreementAt C τ (𝒱 w t') t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** explicit anchor and selector interface used by the gate-based `ConfirmedNotFFGFiltered` theorem. A GU-root slot bound is unnecessary because the comparability split covers both ancestry directions.

#### SafeGreatestJustifiedAnchorInputs — §4-monotonicity per-safe-block bundle (gate-based)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4 (decomposed replacement for SafeNeverFilteredInputs)</i><br><br>Every block X that is isLMDGHOSTSafe in an honest view at t' satisfies the gate-based confirmation-soundness conditions: the conflict-exclusion gate WillNoConflictingChkpBeJustified … X t', chain-scoped AU payload well-formedness, and the GU-anchor inputs. The Algorithm-1 theorem uses the block-vote bundle below instead.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.SafeGreatestJustifiedAnchorInputs</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:194 · <i>def</i></sub><pre>def SafeGreatestJustifiedAnchorInputs (τ fm cm pb C 𝒱) : Prop :=
  ∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t'⦄ ⦃X⦄, isLMDGHOSTSafe τ fm cm pb C (𝒱 w t') X t' →
    WillNoConflictingChkpBeJustified C fm τ 𝒱 X t' ∧
    OnChainAnchorWellFormed C τ X ∧
    GreatestJustifiedAnchorInputs C fm τ 𝒱 X t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** gate-based bundle; carries the semantic gate per safe block for `HFC_Monotonicity` (the `_Alg1` analogue is `SafeConfirmedAlg1Inputs`).

#### ConfirmedNotFFGFiltered — the §4 never-filter obligation

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.1 (FFG-confirmed ⇒ NeverFiltered at ffgFilter)</i><br><br>The §4 safety argument proves that FFG confirmation implies <code>NeverFiltered</code> at <code>ffgFilter</code> by induction across epochs. It uses <code>FFG_AccountableSafety</code>, <code>HonestFFGNoEquivocation</code>, the global Byzantine bound, and, for each safe descendant B at time st s, the confirmation gate and GU-anchor inputs. Its conclusion is the joint-induction form <code>NeverFilteredFromHead</code>. R3 splits on epoch(GJ_real) versus epochOf(slot s): the descendant case uses the cross-epoch ladder, while the lower-or-equal-epoch case uses the gate's compatibility and a comparability split without a slot bound. The GST guard is AfterGST(st(s−1)).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.ConfirmedNotFFGFiltered</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:329 · <i>statement</i></sub><pre>def ConfirmedNotFFGFiltered (τ fm cm pb boost C 𝒱 v b) : Prop :=
  FFG_AccountableSafety (n:=n) → HonestFFGNoEquivocation … →
  GlobalByzantineBound C fm →
  ∀ ⦃s⦄ ⦃B⦄, 1 ≤ s → τ.AfterGST (τ.st (s - 1)) → b ≼ B →
    isLMDGHOSTSafe τ fm cm pb C (𝒱 v (τ.st s)) B (τ.st s) →
    WillNoConflictingChkpBeJustified C fm τ 𝒱 B (τ.st s) → GreatestJustifiedAnchorInputs C fm τ 𝒱 B (τ.st s) →
    NeverFilteredFromHead τ fm (gjFFG C) boost pb (ffgFilter C τ) 𝒱 B (τ.st s)</pre>

</td>
</tr>
</table>

> **Faithfulness:** faithful; the §4 obligation is proved by `confirmedNotFFGFiltered_proved`. Gate-based form consuming `WillNoConflictingChkpBeJustified`.

#### isHFCConfirmed — the HFC confirmation predicate (Definition 4)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 Definition 4 (HFC confirmation rule)</i><br><br>The paper's HFC confirmation rule as a single object (Def 4): b is HFC-confirmed by honest v at t when it is LMD-GHOST-confirmed (Algorithm 4, isConfirmed) AND the FFG gate holds (no checkpoint conflicting with b will ever be justified in an honest view). The gate is the semantic invariant WillNoConflictingChkpBeJustified, not the validator's local weight reservation at Alg 1 line 16; the Algorithm-1 theorem derives the invariant from FFG accountable safety. Taken semantically so the never-filter consumes the honest-view invariant directly.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.isHFCConfirmed</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:216 · <i>def</i></sub><pre>def isHFCConfirmed (τ fm cm pb gj C 𝒱 v b t) : Prop :=
  isConfirmed τ fm cm pb gj 𝒱 v b t ∧ WillNoConflictingChkpBeJustified C fm τ 𝒱 b t</pre>

</td>
</tr>
</table>

> **Faithfulness:** Def 4 modeled with the semantic gate (not the local 2/3 weight reservation); the gate-based pair is built on this, while the `_Alg1` pair uses `isConfirmedNoCaching` and derives the gate.

#### HFC_Safety — §4 confirmation-rule safety (gate-based)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.1/§4.3 (analogue of Theorem 1 safety)</i><br><br>An honest validator FFG-confirming b at t ⇒ from some time on, b is on every honest validator's LMD-GHOST-HFC head. Same shape as Theorem1_Safety with flt := ffgFilter C τ, gj := gjFFG bal₀, C := bal₀, plus FFG_AccountableSafety, HonestFFGNoEquivocation, GlobalByzantineBound, SafeGreatestJustifiedAnchorInputs, and the per-block FFG gate (carried in isHFCConfirmed). The D2 leaf existential is derived structurally (no EpochLeafWitness premise).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Safety</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:353 · <i>statement</i></sub><pre>def HFC_Safety (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm cm pb boost 𝒱}, let gj := gjFFG bal₀; let C := bal₀;
    … (Synchrony, HonestNoForgery, HonestBehavior, ViewsValid, CommitteeHonestMajority, WellFormedBoost, 0≤pb, StaticBalances, FFG_AccountableSafety, HonestFFGNoEquivocation, GlobalByzantineBound, SafeGreatestJustifiedAnchorInputs) … →
    ∀ {v b t}, v ∈ fm.honest → sg τ b t → isHFCConfirmed τ fm cm pb gj C 𝒱 v b t →
      ∃ t0, ∀ ⦃w⦄ ⦃t'⦄, w ∈ fm.honest → t0 ≤ t' →
        b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb (ffgFilter C τ) (𝒱 w t') t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** This gate-based form is implied by the stronger `HFC_Safety_Alg1`, which derives the semantic gate from the Algorithm 1 assumptions.

#### HFC_Monotonicity — §4 confirmation-rule monotonicity (gate-based)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.2 (analogue of Theorem 1 monotonicity); β-bound = Assumption 6.2</i><br><br>Once HFC-confirmed, always HFC-confirmed. Same shape as Theorem1_Monotonicity at flt := ffgFilter, gj := gjFFG bal₀, C := bal₀; the semantic FFG gate persists because it is already a future-closed invariant. β-bound carries β &lt; min(1/6, (1−pb)/4): the 1/6 is Assumption 6.2's FFG-closure bound (honFFGratio(β) = (2/3+β)/(1−β) ≤ 1, matched verbatim); (1−pb)/4 (Assumption 4, the LMD-GHOST monotonicity bound ¼(1−p/E)) stands in for the paper's 1/3−d (safety decay d abstracted).

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Monotonicity</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:403 · <i>statement</i></sub><pre>def HFC_Monotonicity (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm cm pb boost 𝒱}, let gj := gjFFG bal₀; let C := bal₀;
    … (explicit interface premises) … fm.β &lt; min (1 / 6) ((1 - pb) / 4) → FFG_AccountableSafety → HonestFFGNoEquivocation → GlobalByzantineBound → SafeGreatestJustifiedAnchorInputs … →
    ∀ {v b t t'}, v ∈ fm.honest → sg τ b t → t ≤ t' → CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) →
      isHFCConfirmed τ fm cm pb gj C 𝒱 v b t → isHFCConfirmed τ fm cm pb gj C 𝒱 v b t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** Gate-based form; `HFC_Monotonicity_Alg1` derives the semantic gate. The β-bound 1/6⊓(1−pb)/4 matches Assumption 6.2's FFG-closure; (1−pb)/4 abstracts safety decay d.

#### Alg1SafetyInterface — explicit per-confirmation interface for the Alg-1 safety theorem

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §2.2.1 l.280-281; Gasper ldm-vote-for-b-is-ffg-vote-for-cb l.2544</i><br><br>The paper-cited Gasper/protocol facts the gate-free never-filter consumes for a single confirmation of b at st s. The interface starts from the rule-targeted `OnChainAnchorInterfacesForRule` assumption, which includes well-formed block-contained AU vote contents, block availability, payload readability, and AU realization. It then carries greatest-finalized realization, committee partition, and P-link common source. Justification of the anchor source is derived from the AU interface.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.Alg1SafetyInterface</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean · <i>def</i></sub><pre>def Alg1SafetyInterface (τ fm cm pb boost bal₀ 𝒱 v b s) : Prop :=
  OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 b (τ.st s) ∧
  (∀ ⦃w⦄, w ∈ fm.honest → ∀ ⦃t'⦄, τ.st (τ.slotOf (τ.st s)) ≤ t' → (greatestFinalized bal₀ (𝒱 w t')).epoch &lt; τ.epochOf (τ.slotOf t')) ∧
  Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf (τ.st s) - 1)) (committeeUnion cm (τ.slotOf (τ.st s)) (τ.lslot (τ.epochOf b.slot))) ∧
  (∀ ⦃i⦄, i ∈ fm.honest → … ruleVotingSource(head of i) = ruleVotingSource bal₀ τ b (τ.st s))</pre>

</td>
</tr>
</table>

> **Faithfulness:** Uses the explicit AU block-vote surface through the active `OnChainAnchorInterface`. The selector's local `isConfirmedNoCaching` witness is carried separately by `Alg1SelectorSafetyInterface`; execution participation flags and block capacity limits are omitted.

#### HFC_Safety_Alg1 — primary §4 safety theorem for the paper's Algorithm 1 (gate eliminated)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.1/§4.3, Algorithm 1 (current + previous-epoch branches)</i><br><br>The §4 safety statement with the semantic gate eliminated: an honest validator whose HFC Algorithm-1 wrapper `isConfirmedAlg1` holds for b at the slot boundary st s ⇒ from some time on, b is on every honest validator's LMD-GHOST-HFC head. The wrapper confirms ancestors of the highest block satisfying `isConfirmedNoCaching`.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Safety_Alg1</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:498 · <i>statement</i></sub><pre>def HFC_Safety_Alg1 (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm cm pb boost 𝒱}, let gj := gjFFG bal₀; let C := bal₀;
    … (Synchrony, HonestNoForgery, HonestBehavior, ViewsValid, CommitteeHonestMajority, 0≤pb, FFG_AccountableSafety, HonestFFGNoEquivocation, GlobalByzantineBound, SlotCommitteeMinority) … →
    ∀ {v b s we}, v ∈ fm.honest → 1 ≤ s → τ.AfterGST (τ.st (s - 1)) → b.WellFormed → b.slot ≤ s → 0 ≤ we →
      isConfirmedAlg1 C fm cm pb we τ 𝒱 v b (τ.st s) →
      Alg1SelectorSafetyInterface τ fm cm pb we boost C 𝒱 v B (epochOf(slotOf(st s))-1) (τ.st s) →
        ∃ t0, ∀ ⦃w⦄ ⦃t'⦄, w ∈ fm.honest → t0 ≤ t' →
          b ≼ forkChoiceHead τ (gj 𝒱 w t') boost pb (ffgFilter C τ) (𝒱 w t') t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** Algorithm-1 form of `HFC_Safety`; the semantic gate `WillNoConflictingChkpBeJustified` is eliminated in favor of the `isConfirmedAlg1` wrapper plus the selector-scoped Algorithm-1 safety interfaces.

#### SafeConfirmedAlg1Inputs — Algorithm-1 monotonicity input bundle (gate-free)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.2, Algorithm 1 (analogue of SafeGreatestJustifiedAnchorInputs)</i><br><br>For every honest v and safe block X at st s (isLMDGHOSTSafe), X is confirmed via `isConfirmedNoCaching` together with the explicit `Alg1SafetyInterface`, represented with chain-scoped block-contained AU vote payloads read by `blockContainedFFGVotes τ` plus `OnChainAnchorInterfacesForRule`.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.SafeConfirmedAlg1Inputs</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:541 · <i>def</i></sub><pre>def SafeConfirmedAlg1Inputs (τ fm cm pb we boost bal₀ 𝒱) : Prop :=
  ∀ ⦃v⦄, v ∈ fm.honest → ∀ ⦃s⦄ ⦃X⦄, isLMDGHOSTSafe τ fm cm pb bal₀ (𝒱 v (τ.st s)) X (τ.st s) →
    isConfirmedNoCaching bal₀ fm cm pb we τ 𝒱 v X (τ.st s) ∧
    OnChainAnchorInterfacesForRule bal₀ fm τ 𝒱 X (τ.st s) ∧
    (greatestFinalized realization ∧ FilterSelectorAgreementAt …) ∧
    Disjoint (committeeUnion …) (committeeUnion …) ∧
    (P-link common source)</pre>

</td>
</tr>
</table>

> **Faithfulness:** Uses the explicit AU block-vote surface and active AU interface, but packages paper Assumption 6's conditional eventual FFG-closure as a stronger per-safe-block premise: every honest-view-safe `X` must already satisfy `isConfirmedNoCaching` plus the AU/visibility interfaces needed by the monotonicity proof. This is stronger and more direct than Assumption 6 itself; it is the Algorithm-1 analogue of the gate-based per-safe-block bundle.

#### HFC_Monotonicity_Alg1 — primary §4 monotonicity theorem for Algorithm 1 (gate eliminated)

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.2, Algorithm 1; β-bound = Assumption 6.2</i><br><br>The §4 monotonicity statement with the semantic gate eliminated: once b is Algorithm-1-confirmed at t via `isConfirmedAlg1`, it stays Algorithm-1-confirmed at every t' ≥ t. The FFG soundness keeping each Algorithm-1 highest-confirmed block canonical comes from the rule plus the explicit `SafeConfirmedAlg1Inputs` bundle, not `WillNoConflictingChkpBeJustified`.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Monotonicity_Alg1</code><br><sub>FastConfirmation/Paper/HFC/TheoremStatements.lean:568 · <i>statement</i></sub><pre>def HFC_Monotonicity_Alg1 (τ : Timing) (bal₀ : Stakes n) : Prop :=
  ∀ {fm cm pb we boost 𝒱}, let gj := gjFFG bal₀; let C := bal₀;
    … (explicit interface premises) … fm.β &lt; min (1 / 6) ((1 - pb) / 4) → FFG_AccountableSafety → HonestFFGNoEquivocation → GlobalByzantineBound → SlotCommitteeMinority → 0 ≤ we → SafeConfirmedAlg1Inputs τ fm cm pb we boost C 𝒱 →
    ∀ {v b t t'}, v ∈ fm.honest → sg τ b t → t ≤ t' → CommitteeCoversEpoch τ cm (τ.epochOf (τ.slotOf t') - 1) →
      isConfirmedAlg1 C fm cm pb we τ 𝒱 v b t → isConfirmedAlg1 C fm cm pb we τ 𝒱 v b t'</pre>

</td>
</tr>
</table>

> **Faithfulness:** Algorithm-1 form of `HFC_Monotonicity`; the semantic gate is eliminated and the proof is driven by `isConfirmedAlg1` via `SafeConfirmedAlg1Inputs`.

#### HFC_Safety_proved — proved facade for gate-based safety

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.1/§4.3 (facade discharging HFC_Safety)</i><br><br>Theorem constant discharging the public HFC_Safety statement by composing the filter-generic §3.1 engine (hfc_safety_of_notFiltered) with the §4 never-filter (confirmedNotFFGFiltered_proved), threading the gate out of isHFCConfirmed.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Safety_proved</code><br><sub>FastConfirmation/Paper/HFC/ProvenTheorems.lean:44 · <i>statement</i></sub><pre>theorem HFC_Safety_proved (τ : Timing) (bal₀ : Stakes n) : HFC_Safety τ bal₀ := by
  intro … ; obtain ⟨hconf, _hgate⟩ := hHFCconf
  exact hfc_safety_of_notFiltered bal₀ … hconf (confirmedNotFFGFiltered_proved bal₀ …)</pre>

</td>
</tr>
</table>

> **Faithfulness:** proved facade for the gate-based formulation.

#### HFC_Monotonicity_proved — proved facade for gate-based monotonicity

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.2 (facade discharging HFC_Monotonicity)</i><br><br>Theorem constant discharging the public HFC_Monotonicity statement via hfc_monotonicity_proved.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Monotonicity_proved</code><br><sub>FastConfirmation/Paper/HFC/ProvenTheorems.lean:54 · <i>statement</i></sub><pre>theorem HFC_Monotonicity_proved (τ : Timing) (bal₀ : Stakes n) : HFC_Monotonicity τ bal₀ :=
  hfc_monotonicity_proved bal₀</pre>

</td>
</tr>
</table>

> **Faithfulness:** proved facade for the gate-based formulation.

#### HFC_Safety_Alg1_proved — proved facade for Algorithm-1 safety

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.1/§4.3 (facade discharging HFC_Safety_Alg1)</i><br><br>Theorem constant discharging the public HFC_Safety_Alg1 statement. The public confirmation hypothesis is `isConfirmedAlg1`; the proof extracts the selected highest `isConfirmedNoCaching` block and its actual witness slot, runs the current/previous-epoch Algorithm-1 safety fold there, and then transfers canonicity back to the requested ancestor. `Alg1SelectorSafetyInterface` supplies the witness-slot GST guard plus the `Alg1SafetyInterface` AU/P-link/partition/realization facts.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Safety_Alg1_proved</code><br><sub>FastConfirmation/Paper/HFC/ProvenTheorems.lean · <i>statement</i></sub><pre>theorem HFC_Safety_Alg1_proved (τ : Timing) (bal₀ : Stakes n) : HFC_Safety_Alg1 τ bal₀ := by
  exact hfc_safety_alg1_public τ bal₀</pre>

</td>
</tr>
</table>

> **Faithfulness:** facade for gate-free safety; case-splits current vs previous epoch

#### HFC_Monotonicity_Alg1_proved — proved facade for Algorithm-1 monotonicity

<table>
<tr>
<td width="50%" valign="top">

<b>Paper</b> — <i>arXiv:2405.00549 §4.2</i><br><br>The proved public facade is over the HFC Algorithm-1 wrapper `isConfirmedAlg1`: once `b` is Algorithm-1-confirmed at `t`, it remains Algorithm-1-confirmed at later `t'`. The proof uses Algorithm-1 selector membership/dominance lemmas for `highestConfirmedSinceEpochAlg1`, then drives the selected blocks canonical through `isConfirmedNoCaching` and `SafeConfirmedAlg1Inputs`.

</td>
<td width="50%" valign="top">

<b>Lean</b> — <code>FastConfirmation.HFC.HFC_Monotonicity_Alg1_proved</code><br><sub>FastConfirmation/Paper/HFC/ProvenTheorems.lean · <i>theorem</i></sub><pre>theorem HFC_Monotonicity_Alg1_proved (τ : Timing) (bal₀ : Stakes n) :
    HFC_Monotonicity_Alg1 τ bal₀ := by
  … exact hfc_monotonicity_alg1 bal₀ … hconf</pre>

</td>
</tr>
</table>

> **Faithfulness:** proved wrapper-level monotonicity. The proof uses the HFC Algorithm-1 selector, not the imported LMD selector.
