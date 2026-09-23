module
public import FastConfirmationPaper.HFC.Claims
public import FastConfirmationPaper.LMDGhost.Proof.PositiveWeights
public import FastConfirmationPaper.LMDGhost.Proof.BlockAncestry

@[expose] public section

/-!
# HFC / Proof / Justification

Proves monotonicity and chain transport for FFG link weights and on-chain justification.

This module contains `linkWeight_mono`, `onChainLinkWeight_le_linkWeight_of_view_reads_chain`, `onChainJustified_to_view_justified_of_view_reads_chain` and related declarations.
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **I.1 — `linkWeight` is monotone in the view's messages.** When `V.msgs ⊆ V'.msgs`
    the signer set targeting the link `src → tgt` only grows, so its total weight grows. -/
theorem linkWeight_mono (A : Anchor n) {V V' : View n (FFGVote n)} (hsub : V.msgs ⊆ V'.msgs)
    (src tgt : Checkpoint n) : linkWeight A V src tgt ≤ linkWeight A V' src tgt := by
  classical
  unfold linkWeight
  apply totalWeight_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨m, hm, hmv, hsrc, htgt⟩ := hi
  exact ⟨m, hsub hm, hmv, hsrc, htgt⟩

/-- If a view reads the FFG payloads of a known block, the source-to-target link weight computed
    from the block-contained chain votes is bounded by the ordinary view-level FFG link weight. This
    is the proof-side payload bridge that block gossip can feed once the block is available. -/
theorem onChainLinkWeight_le_linkWeight_of_view_reads_chain {A : Anchor n} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} (hread : ViewReadsChainFFGVotes (n := n) τ 𝒱)
    {v : Validator n} {t : Time} {tip b : Block n} (htip : tip ∈ (𝒱 v t).blocks)
    (hbtip : b ≼ tip)
    (hWF : BlockFFGVotes.WellFormedOnChain (n := n) τ (blockContainedFFGVotes (n := n) τ) b)
    (Cs Ct : Checkpoint n) :
    onChainLinkWeight A (blockContainedFFGVotes (n := n) τ) b Cs Ct ≤
      linkWeight A (𝒱 v t) Cs Ct := by
  classical
  unfold onChainLinkWeight linkWeight
  apply totalWeight_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨m, hm, hval, hsrc, htgt⟩ := hi
  have hmChain : m ∈ chainIncludedFFGVotes (blockContainedFFGVotes (n := n) τ) b := by
    suffices h :
        m ∈ chainIncludedFFGVotes (blockContainedFFGVotes (n := n) τ) b ∧
          (m.extra.target.epoch = Ct.epoch ∧
            ¬ OnChainFFGEquivocator
              (chainIncludedFFGVotes (blockContainedFFGVotes (n := n) τ) b)
              m.ghost.validator Ct.epoch) from h.1
    simpa [onChainFFGVotesForEpoch] using hm
  exact ⟨m, hread htip hbtip hWF hmChain, hval, hsrc, htgt⟩

/-- A source→target AU fact carried by a known chain tip is visible as ordinary view-level
    `Justified`, provided the view reads block-contained FFG payloads from that tip's ancestry. -/
theorem onChainJustified_to_view_justified_of_view_reads_chain {A : Anchor n} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} (hread : ViewReadsChainFFGVotes (n := n) τ 𝒱)
    {v : Validator n} {t : Time} {tip b : Block n} {C : Checkpoint n}
    (htip : tip ∈ (𝒱 v t).blocks) (hbtip : b ≼ tip)
    (hWF : BlockFFGVotes.WellFormedOnChain (n := n) τ (blockContainedFFGVotes (n := n) τ) b)
    (h : OnChainJustified A τ (blockContainedFFGVotes (n := n) τ) b C) :
    Justified A (𝒱 v t) C := by
  induction h generalizing tip with
  | base => exact Justified.base
  | @link b N B Cs Ct hchainBlock _hblockEpoch hsource _htargetEpoch _hchainTarget hsup ih =>
    have hBtip : B ≼ tip := Block.Ancestor.trans hchainBlock hbtip
    have hWFB : BlockFFGVotes.WellFormedOnChain (n := n) τ
        (blockContainedFFGVotes (n := n) τ) B := by
      intro c hc m hm
      exact hWF (Block.Ancestor.trans hc hchainBlock) hm
    have hsrc : Justified A (𝒱 v t) Cs := ih htip hBtip hWFB
    refine Justified.link hsrc ?_
    have hle := onChainLinkWeight_le_linkWeight_of_view_reads_chain (A := A)
      hread htip hBtip hWFB Cs Ct
    linarith

/-- The AU visibility bridge is a gossip/readability consequence once the carrying block is
    available in honest views. -/
theorem OnChainAnchorVisibility.of_block_available {A : Anchor n} {fm : FaultModel n}
    {τ : Timing} {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (hread : ViewReadsChainFFGVotes (n := n) τ 𝒱)
    (havail : OnChainAnchorBlockAvailable fm 𝒱 b (τ.st (τ.slotOf t))) :
    OnChainAnchorVisibility A fm τ 𝒱 b t := by
  intro _hprop hWF _havail Cc _hchain hjust w hw t' ht'
  exact onChainJustified_to_view_justified_of_view_reads_chain (A := A) hread
    (havail.2 hw ht') (Block.Ancestor.refl b) hWF hjust

/-- The view-level consequence consumed by the never-filter proof, derived from the active AU
    interface rather than assumed directly: realization gives an AU fact, and block
    availability/readability make that AU fact visible as ordinary view-level `Justified`. -/
theorem OnChainAnchorInterface.justified {A : Anchor n} {fm : FaultModel n} {τ : Timing}
    {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (h : OnChainAnchorInterface A fm τ 𝒱 b t)
    {Cc : Checkpoint n} (hchain : Cc.block ≼ b)
    (hlocal : ∃ v : Validator n, v ∈ fm.honest ∧ Justified A (𝒱 v t) Cc)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time} (ht' : τ.st (τ.slotOf t) ≤ t') :
    Justified A (𝒱 w t') Cc :=
  (OnChainAnchorVisibility.of_block_available h.2.2.2.1 h.2.2.1) h.2.1 h.1 h.2.2.1 hchain
    (h.2.2.2.2 h.2.1 hchain hlocal) hw ht'

/-- A checkpoint already known to be AU-justified on `chain(b)` is visible as view-level
    `Justified` from the block-availability boundary onward. This is the direct AU→view bridge
    used by the paper-facing selectors (`ruleGJBlock`, `ruleVotingSource`); it avoids routing those
    selectors through the older view-dependent `gjblock` / `votingSource` helpers. -/
theorem OnChainAnchorInterface.onChainJustified_visible {A : Anchor n} {fm : FaultModel n}
    {τ : Timing} {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (h : OnChainAnchorInterface A fm τ 𝒱 b t)
    {Cc : Checkpoint n} (hchain : Cc.block ≼ b)
    (hjust : OnChainJustified A τ (blockContainedFFGVotes (n := n) τ) b Cc)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time} (ht' : τ.st (τ.slotOf t) ≤ t') :
    Justified A (𝒱 w t') Cc :=
  (OnChainAnchorVisibility.of_block_available h.2.2.2.1 h.2.2.1) h.2.1 h.1 h.2.2.1 hchain
    hjust hw ht'

/-- `GU(b)` is AU-justified. -/
theorem GU_onChainJustified (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : OnChainJustified A τ blockVotes b (GU A τ blockVotes b) := by
  classical
  unfold GU
  cases harg : ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧ C.block ≼ b)).toList.argmax
      (·.epoch) with
  | none => exact OnChainJustified.base
  | some C =>
      have hmem := List.argmax_mem harg
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact hmem.2.1

/-- `GU(b)` is on `chain(b)`. -/
theorem GU_block_le (A : Anchor n) (τ : Timing) (blockVotes : BlockFFGVotes n)
    (b : Block n) : (GU A τ blockVotes b).block ≼ b := by
  classical
  unfold GU
  cases harg : ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧ C.block ≼ b)).toList.argmax
      (·.epoch) with
  | none => exact genesis_ancestor _
  | some C =>
      have hmem := List.argmax_mem harg
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact hmem.2.2

/-- AU Def-1 `gjblock(b)` is AU-justified. -/
theorem onChainGJBlock_onChainJustified (A : Anchor n) (τ : Timing)
    (blockVotes : BlockFFGVotes n) (b : Block n) :
    OnChainJustified A τ blockVotes b (onChainGJBlock A τ blockVotes b) := by
  classical
  unfold onChainGJBlock
  cases harg : ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧
        C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax (·.epoch) with
  | none => exact OnChainJustified.base
  | some C =>
      have hmem := List.argmax_mem harg
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact hmem.2.1

/-- AU Def-1 `gjblock(b)` is on `chain(b)`. -/
theorem onChainGJBlock_block_le (A : Anchor n) (τ : Timing)
    (blockVotes : BlockFFGVotes n) (b : Block n) :
    (onChainGJBlock A τ blockVotes b).block ≼ b := by
  classical
  unfold onChainGJBlock
  cases harg : ((onChainMentionedCheckpoints blockVotes b).filter
      (fun C => OnChainJustified A τ blockVotes b C ∧
        C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax (·.epoch) with
  | none => exact genesis_ancestor _
  | some C =>
      have hmem := List.argmax_mem harg
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact hmem.2.2.1

/-- AU Def-2 `vs(b,t)` is AU-justified. -/
theorem onChainVotingSource_onChainJustified (A : Anchor n) (τ : Timing)
    (blockVotes : BlockFFGVotes n) (b : Block n) (t : Time) :
    OnChainJustified A τ blockVotes b (onChainVotingSource A τ blockVotes b t) := by
  unfold onChainVotingSource
  split
  · exact onChainGJBlock_onChainJustified A τ blockVotes b
  · exact GU_onChainJustified A τ blockVotes b

/-- AU Def-2 `vs(b,t)` is on `chain(b)`. -/
theorem onChainVotingSource_block_le (A : Anchor n) (τ : Timing)
    (blockVotes : BlockFFGVotes n) (b : Block n) (t : Time) :
    (onChainVotingSource A τ blockVotes b t).block ≼ b := by
  unfold onChainVotingSource
  split
  · exact onChainGJBlock_block_le A τ blockVotes b
  · exact GU_block_le A τ blockVotes b

/-- The rule's AU Def-1 selector is AU-justified. -/
theorem ruleGJBlock_onChainJustified (A : Anchor n) (τ : Timing) (b : Block n) :
    OnChainJustified A τ (blockContainedFFGVotes (n := n) τ) b (ruleGJBlock A τ b) := by
  unfold ruleGJBlock
  exact onChainGJBlock_onChainJustified A τ (blockContainedFFGVotes (n := n) τ) b

/-- The rule's AU Def-1 selector is on `chain(b)`. -/
theorem ruleGJBlock_block_le (A : Anchor n) (τ : Timing) (b : Block n) :
    (ruleGJBlock A τ b).block ≼ b := by
  unfold ruleGJBlock
  exact onChainGJBlock_block_le A τ (blockContainedFFGVotes (n := n) τ) b

/-- The rule's AU Def-2 source selector is AU-justified. -/
theorem ruleVotingSource_onChainJustified (A : Anchor n) (τ : Timing) (b : Block n) (t : Time) :
    OnChainJustified A τ (blockContainedFFGVotes (n := n) τ) b
      (ruleVotingSource A τ b t) := by
  unfold ruleVotingSource
  exact onChainVotingSource_onChainJustified A τ (blockContainedFFGVotes (n := n) τ) b t

/-- The rule's AU Def-2 source selector is on `chain(b)`. -/
theorem ruleVotingSource_block_le (A : Anchor n) (τ : Timing) (b : Block n) (t : Time) :
    (ruleVotingSource A τ b t).block ≼ b := by
  unfold ruleVotingSource
  exact onChainVotingSource_block_le A τ (blockContainedFFGVotes (n := n) τ) b t

/-- The rule's AU Def-1 selector is visible as view-level `Justified`. -/
theorem OnChainAnchorInterface.ruleGJBlock_justified {A : Anchor n} {fm : FaultModel n}
    {τ : Timing} {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (h : OnChainAnchorInterface A fm τ 𝒱 b t)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time} (ht' : τ.st (τ.slotOf t) ≤ t') :
    Justified A (𝒱 w t') (ruleGJBlock A τ b) :=
  h.onChainJustified_visible (ruleGJBlock_block_le A τ b)
    (ruleGJBlock_onChainJustified A τ b) hw ht'

/-- The rule's AU Def-2 source selector is visible as view-level `Justified`. -/
theorem OnChainAnchorInterface.ruleVotingSource_justified {A : Anchor n} {fm : FaultModel n}
    {τ : Timing} {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (h : OnChainAnchorInterface A fm τ 𝒱 b t)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time} (ht' : τ.st (τ.slotOf t) ≤ t') :
    Justified A (𝒱 w t') (ruleVotingSource A τ b t) :=
  h.onChainJustified_visible (ruleVotingSource_block_le A τ b t)
    (ruleVotingSource_onChainJustified A τ b t) hw ht'

/-- **I.2 — `Justified` is monotone in the view's messages.** Induction on the
    justification derivation; `base ↦ base`, and a supermajority link survives because
    `linkWeight` only grows (I.1) while `totalWeight A univ` is view-independent. -/
theorem Justified_mono (A : Anchor n) {V V' : View n (FFGVote n)} (hsub : V.msgs ⊆ V'.msgs)
    {C : Checkpoint n} (h : Justified A V C) : Justified A V' C := by
  induction h with
  | base => exact Justified.base
  | @link Cs Ct _hs hsup ih =>
    refine Justified.link ih ?_
    exact le_trans hsup (by
      have hlw : linkWeight A V Cs Ct ≤ linkWeight A V' Cs Ct := linkWeight_mono A hsub Cs Ct
      linarith)

/-- **I.3 — `Justified` persists forward in time** (under monotone views). The time
    specialization of I.2 actually consumed by the never-filtered argument. -/
theorem Justified_mono_time (A : Anchor n) {𝒱 : ViewFamily n (FFGVote n)}
    (hMono : ViewsMonotone 𝒱) {w : Validator n} {t t' : Time} (hle : t ≤ t')
    {C : Checkpoint n} (h : Justified A (𝒱 w t) C) : Justified A (𝒱 w t') C :=
  Justified_mono A (hMono w t t' hle).1 h

/-- **I.3r — justification is stable under gossip relay.** A checkpoint `Justified` in *some*
    honest view `𝒱 v t` is `Justified` in *every* honest view `𝒱 w (st(s'+1))` one slot after a
    post-`gst` slot `s' ≥ slotOf t` — the message-level generalization of `Justified_mono_time`
    across *different* validators' views. Proof: the gossip relay (`hRelay`) moves the *entire*
    justifying message set of `𝒱 v t` into `𝒱 w (st(s'+1))` in one step (it relays *any* message,
    adversary-authored included), so the conclusion is just `Justified_mono` along that
    relay-supplied `msgs ⊆ msgs`. `Justified = base | link(Justified src)(3·linkWeight ≥ 2·W)` and
    `linkWeight` only grows when the signer set grows, so every link survives. This is the keystone
    for the **previous-epoch** no-conflicting argument: it carries a realized-`GJ`'s justification
    into a common future view where the (observed-only) `C(b, epoch(b))` certificate also holds, so
    per-epoch uniqueness applies *in that view* — sidestepping the one-slot relay delay at the epoch
    boundary without re-deriving accountable safety. -/
theorem justified_relays (A : Anchor n) {τ : Timing} {fm : FaultModel n}
    {𝒱 : ViewFamily n (FFGVote n)}
    (hRelay : ∀ ⦃v w : Validator n⦄, v ∈ fm.honest → w ∈ fm.honest →
      ∀ ⦃t : Time⦄ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄, m ∈ (𝒱 v t).msgs → τ.slotOf t ≤ s' →
        τ.AfterGST (τ.st s') → m ∈ (𝒱 w (τ.st (s' + 1))).msgs)
    {v w : Validator n} (hv : v ∈ fm.honest) (hw : w ∈ fm.honest)
    {t : Time} {s' : Slot} (hs' : τ.slotOf t ≤ s') (hgst : τ.AfterGST (τ.st s'))
    {C : Checkpoint n} (hJ : Justified A (𝒱 v t) C) :
    Justified A (𝒱 w (τ.st (s' + 1))) C :=
  Justified_mono A (fun _m hm => hRelay hv hw hm hs' hgst) hJ

/-- The genesis checkpoint is always a mentioned checkpoint (it is `insert`ed). -/
theorem genesisCheckpoint_mem_mentioned (V : View n (FFGVote n)) :
    genesisCheckpoint ∈ mentionedCheckpoints V := by
  unfold mentionedCheckpoints
  exact Finset.mem_insert_self _ _



/-- A link-justified target whose link weight is positive is a *mentioned* checkpoint:
    a positive `linkWeight` means some FFG vote in `V` targets `Ct`, so `Ct` appears in
    `V.ffgVotes.image FFGVote.target ⊆ mentionedCheckpoints V`. -/
theorem mem_mentioned_of_linkWeight_pos (A : Anchor n) (V : View n (FFGVote n))
    {Cs Ct : Checkpoint n} (hpos : 0 < linkWeight A V Cs Ct) :
    Ct ∈ mentionedCheckpoints V := by
  classical
  -- positive weight ⇒ the signer filter set is nonempty ⇒ some message targets `Ct`.
  unfold linkWeight at hpos
  have hne : (Finset.univ.filter (fun i =>
      ∃ m ∈ V.msgs, m.ghost.validator = i ∧ m.extra.source = Cs ∧ m.extra.target = Ct)).Nonempty
      := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hpos
    simp [totalWeight] at hpos
  obtain ⟨i, hi⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨m, hm, _hmv, _hsrc, htgt⟩ := hi
  -- `Ct` is the target of `m.extra ∈ V.ffgVotes`, hence in the target image.
  unfold mentionedCheckpoints
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  refine ⟨m.extra, ?_, htgt⟩
  rw [View.ffgVotes, Finset.mem_image]
  exact ⟨m, hm, rfl⟩

/-- Every **justified** checkpoint is a *mentioned* checkpoint (given a witness validator
    so the total stake is positive). `base` is genesis (always mentioned); a `link` target
    has `3·linkWeight ≥ 2·totalWeight univ > 0`, so `linkWeight > 0` and the target is
    mentioned by `mem_mentioned_of_linkWeight_pos`. This is the membership side-condition
    `greatestJustified_max` needs at the J1 call site (`checkpointOf τ b e` justified ⇒
    its epoch dominated by `greatestJustified.epoch`). -/
theorem justified_mem_mentioned (A : Anchor n) (V : View n (FFGVote n))
    (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    {C : Checkpoint n} (hJ : Justified A V C) : C ∈ mentionedCheckpoints V := by
  cases hJ with
  | base => exact genesisCheckpoint_mem_mentioned V
  | @link Cs _hs hsup =>
    have hWpos : 0 < totalWeight A (Finset.univ : Finset (Validator n)) :=
      totalWeight_pos A hwit
    have hlwpos : 0 < linkWeight A V Cs C := by linarith
    exact mem_mentioned_of_linkWeight_pos A V hlwpos

/-- **I.6 — `votingSource` on its same-epoch branch is the view-realized `gjblock(b)`.**
    For the proof-facing Def-2 analogue, when `epoch(b) = epoch(t)` the voting source is
    `gjblock A τ V b`
    (Def 1, the greatest justified checkpoint in `chain(b)` of epoch strictly below `epoch(b)`), by
    `rfl` on that branch. (The complementary `else` branch is the view-realized chain selector
    `greatestJustifiedOfChain`, which can age — see `greatestJustifiedOfChain_*`
    below.) This is the proof-facing same-epoch identity (the earlier global
    `greatestRealizedJustified` divergence is gone); the never-filter's voting-source disjunct then
    closes the same-epoch case by further identifying `gjblock(b'') = gjC` (the realized `GJ`) via
    realized-max + accountable-safety uniqueness (`votingSource_disjunct`). -/
theorem votingSource_eq_gjblock (A : Anchor n) (τ : Timing) (V : View n (FFGVote n))
    (b : Block n) (t : Time) (hep : τ.epochOf b.slot = τ.epochOf (τ.slotOf t)) :
    votingSource A τ V b t = gjblock A τ V b := by
  unfold votingSource; rw [if_pos hep]

/-- **`greatestJustifiedOfChain` is itself justified.** `argmax` over the justified
    in-chain mentioned checkpoints: its `some` branch is a member of the filtered set
    (hence justified); the `none` branch defaults to genesis, justified by
    `Justified.base`. Mirrors `greatestJustified_justified`. -/
theorem greatestJustifiedOfChain_justified (A : Anchor n) (V : View n (FFGVote n))
    (b : Block n) : Justified A V (greatestJustifiedOfChain A V b) := by
  classical
  unfold greatestJustifiedOfChain
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.block ≼ b)).toList.argmax (·.epoch) with
  | none => exact Justified.base
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.1


/-- **`greatestJustifiedOfChain` dominates (by epoch) every justified *in-chain* mentioned
    checkpoint.** The chain-relative argmax mirror of `greatestJustified_max`: any checkpoint
    `C` that is mentioned, justified, and on the chain of `b` (`C.block ≼ b`) has epoch
    `≤ (greatestJustifiedOfChain A V b).epoch`, by `List.le_of_mem_argmax` over the in-chain
    filtered set (the `none` branch contradicts the membership). -/
theorem greatestJustifiedOfChain_max (A : Anchor n) (V : View n (FFGVote n)) (b : Block n)
    {C : Checkpoint n} (hC : C ∈ mentionedCheckpoints V) (hJ : Justified A V C)
    (hle : C.block ≼ b) :
    C.epoch ≤ (greatestJustifiedOfChain A V b).epoch := by
  classical
  have hCmem : C ∈ (mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b) :=
    Finset.mem_filter.mpr ⟨hC, hJ, hle⟩
  unfold greatestJustifiedOfChain
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.block ≼ b)).toList.argmax (·.epoch) with
  | none =>
    -- argmax = none ⇒ the list is empty ⇒ the filtered set is empty, contradicting `hCmem`.
    rw [List.argmax_eq_none, Finset.toList_eq_nil] at harg
    rw [harg] at hCmem
    simp at hCmem
  | some D =>
    exact List.le_of_mem_argmax (Finset.mem_toList.mpr hCmem) harg


/-- **`greatestJustifiedOfChain` dominates the epoch of any justified, in-chain
    mentioned checkpoint** (the general form behind `greatestJustifiedOfChain_ge_gJ`).
    If `C` is justified, mentioned, and `C.block ≼ x`, then `C` sits in the in-chain
    argmax set for `x`, so `greatestJustifiedOfChain A V x` dominates its epoch. The
    `_ge_gJ` lemma is the special case `C := greatestJustified A V`; the realized-GJ
    recency discharge is the case `C := greatestRealizedJustified A τ V t`. -/
theorem greatestJustifiedOfChain_ge_of_justified (A : Anchor n) (V : View n (FFGVote n))
    (x : Block n) (hwit : (Finset.univ : Finset (Validator n)).Nonempty)
    {C : Checkpoint n} (hJ : Justified A V C) (h : C.block ≼ x) :
    C.epoch ≤ (greatestJustifiedOfChain A V x).epoch :=
  greatestJustifiedOfChain_max A V x (justified_mem_mentioned A V hwit hJ) hJ h

/-- **`greatestRealizedJustified` is itself justified** (Def-3 selector). `argmax`
    over the justified, epoch-cut mentioned checkpoints: its `some` branch is a member
    of the filtered set (hence justified); the `none` branch defaults to genesis,
    justified by `Justified.base`. Mirrors `greatestJustified_justified`. -/
theorem greatestRealizedJustified_justified (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) :
    Justified A V (greatestRealizedJustified A τ V t) := by
  classical
  unfold greatestRealizedJustified
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | none => exact Justified.base
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.1

/-- `gjblock A τ V b` is `Justified` (its `some` branch lies in the justified-filtered set; the
    `none` branch is the genesis checkpoint, `Justified.base`). Moved here from `Proof/FFGRule.lean`
    so the same-epoch `votingSource` proofs can use it. -/
theorem gjblock_justified (A : Anchor n) (τ : Timing) (V : View n (FFGVote n)) (b : Block n) :
    Justified A V (gjblock A τ V b) := by
  classical
  unfold gjblock
  cases harg : ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax
      (·.epoch) with
  | none => exact Justified.base
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.1


/-- **`gjblock` is realized** — its epoch is strictly below `b`'s own epoch `epoch(b.slot)`, given
    `epoch(b.slot) ≥ 1` (`hpos`). On the `some` branch the filter predicate carries
    `C.epoch < epochOf b.slot` directly; on the `none` branch the default is genesis (epoch `0`),
    and `0 < epoch(b.slot)` holds by `hpos`. The Def-1 epoch cut in realization form — the mirror of
    `greatestRealizedJustified_realized`, keyed on `b`'s epoch rather than the running epoch. -/
theorem gjblock_realized (A : Anchor n) (τ : Timing) (V : View n (FFGVote n)) (b : Block n)
    (hpos : 1 ≤ τ.epochOf b.slot) : (gjblock A τ V b).epoch < τ.epochOf b.slot := by
  classical
  unfold gjblock
  cases harg : ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax
      (·.epoch) with
  | none =>
    change genesisCheckpoint.epoch < τ.epochOf b.slot
    simpa [genesisCheckpoint] using hpos
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.2.2

/-- **`gjblock` dominates (by epoch) every justified, in-chain, epoch-cut mentioned checkpoint.**
    The Def-1 argmax mirror of `greatestJustifiedOfChain_max` with the extra epoch-cut conjunct: any
    `C` that is mentioned, justified, on `chain(b)` (`C.block ≼ b`) and of epoch `< epoch(b.slot)`
    has epoch `≤ (gjblock A τ V b).epoch`, by `List.le_of_mem_argmax` over the filtered set (the
    `none` branch contradicts the membership). -/
theorem gjblock_max (A : Anchor n) (τ : Timing) (V : View n (FFGVote n)) (b : Block n)
    {C : Checkpoint n} (hC : C ∈ mentionedCheckpoints V) (hJ : Justified A V C)
    (hle : C.block ≼ b) (hlt : C.epoch < τ.epochOf b.slot) :
    C.epoch ≤ (gjblock A τ V b).epoch := by
  classical
  have hCmem : C ∈ (mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b ∧ C.epoch < τ.epochOf b.slot) :=
    Finset.mem_filter.mpr ⟨hC, hJ, hle, hlt⟩
  unfold gjblock
  cases harg : ((mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.block ≼ b ∧ C.epoch < τ.epochOf b.slot)).toList.argmax
      (·.epoch) with
  | none =>
    rw [List.argmax_eq_none, Finset.toList_eq_nil] at harg
    rw [harg] at hCmem
    simp at hCmem
  | some D =>
    exact List.le_of_mem_argmax (Finset.mem_toList.mpr hCmem) harg


/-- **`greatestRealizedJustified` is realized** — its epoch is strictly below the
    current epoch `epochOf(slotOf t)`, given the current epoch is `≥ 1` (`hpos`). On
    the `some` branch the filter predicate carries `C.epoch < epochOf(slotOf t)`
    directly; on the `none` branch the default is genesis (epoch `0`), and `0 < current`
    holds by `hpos`. This is the Def-3 realization property: `GJ(𝒱,t)` only ever reports
    a checkpoint of epoch strictly below the running epoch. -/
theorem greatestRealizedJustified_realized (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) (hpos : 1 ≤ τ.epochOf (τ.slotOf t)) :
    (greatestRealizedJustified A τ V t).epoch < τ.epochOf (τ.slotOf t) := by
  classical
  unfold greatestRealizedJustified
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | none =>
    -- genesis default: epoch 0 < current epoch by `hpos`.
    change genesisCheckpoint.epoch < τ.epochOf (τ.slotOf t)
    simpa [genesisCheckpoint] using hpos
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.2

/-- **`greatestRealizedJustified` is realized whenever its epoch is positive** — no
    `1 ≤ epochOf(slotOf t)` side-condition needed. If `(greatestRealizedJustified A τ V
    t).epoch > 0`, the selector cannot be on the `none` (genesis, epoch `0`) branch, so it
    is the `some` branch, whose filter predicate carries `C.epoch < epochOf(slotOf t)`
    directly. This is the form the §4 RECENCY *descendant* case consumes: there the realized
    `GJ`'s epoch is `> epochOf s ≥ 0`, hence positive, so its realization
    (`epoch < epochOf(slotOf t)`) is free. -/
theorem greatestRealizedJustified_realized_of_pos (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) (hp : 0 < (greatestRealizedJustified A τ V t).epoch) :
    (greatestRealizedJustified A τ V t).epoch < τ.epochOf (τ.slotOf t) := by
  classical
  revert hp
  unfold greatestRealizedJustified
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | none =>
    -- genesis default has epoch `0`, contradicting `0 < epoch`.
    intro hp; exact absurd hp (by simp only [genesisCheckpoint]; exact Nat.not_lt_zero _)
  | some C =>
    intro _hp
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.2

/-- **`greatestRealizedJustified` dominates (by epoch) every justified, *realized*
    mentioned checkpoint.** The Def-3 argmax mirror of `greatestJustified_max` with the
    extra epoch-cut conjunct: any checkpoint `C` that is mentioned, justified, and
    realized (`C.epoch < epochOf(slotOf t)`) has epoch `≤ (greatestRealizedJustified
    A τ V t).epoch`, by `List.le_of_mem_argmax` over the epoch-cut filtered set (the
    `none` branch contradicts the membership). -/
theorem greatestRealizedJustified_max (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) {C : Checkpoint n}
    (hC : C ∈ mentionedCheckpoints V) (hJ : Justified A V C)
    (hlt : C.epoch < τ.epochOf (τ.slotOf t)) :
    C.epoch ≤ (greatestRealizedJustified A τ V t).epoch := by
  classical
  have hCmem : C ∈ (mentionedCheckpoints V).filter
      (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t)) :=
    Finset.mem_filter.mpr ⟨hC, hJ, hlt⟩
  unfold greatestRealizedJustified
  cases harg :
      ((mentionedCheckpoints V).filter
        (fun C => Justified A V C ∧ C.epoch < τ.epochOf (τ.slotOf t))).toList.argmax (·.epoch) with
  | none =>
    -- argmax = none ⇒ the list is empty ⇒ the filtered set is empty, contradicting `hCmem`.
    rw [List.argmax_eq_none, Finset.toList_eq_nil] at harg
    rw [harg] at hCmem
    simp at hCmem
  | some D =>
    exact List.le_of_mem_argmax (Finset.mem_toList.mpr hCmem) harg


/-- The greatest finalized checkpoint is a mentioned checkpoint. -/
theorem greatestFinalized_mem_mentioned (A : Anchor n) (V : View n (FFGVote n)) :
    (greatestFinalized A V) ∈ mentionedCheckpoints V := by
  classical
  unfold greatestFinalized
  cases harg :
      ((mentionedCheckpoints V).filter (fun C => Finalized A V C)).toList.argmax (·.epoch) with
  | none => exact genesisCheckpoint_mem_mentioned V
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.1

/-- **I.5a — `greatestFinalized` is itself justified.** Its `some` branch is finalized,
    hence justified (`Finalized.1`); the `none` branch defaults to genesis. -/
theorem greatestFinalized_justified (A : Anchor n) (V : View n (FFGVote n)) :
    Justified A V (greatestFinalized A V) := by
  classical
  unfold greatestFinalized
  cases harg :
      ((mentionedCheckpoints V).filter (fun C => Finalized A V C)).toList.argmax (·.epoch) with
  | none => exact Justified.base
  | some C =>
    have hmem := List.argmax_mem harg
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2.1

/-! ### The proper §4 anchor argument (derive `block(GJ) ≼ b` on `chain(b)`)

The lemmas below *derive* — rather than assume — the two halves of the never-filter's
GJ-rootedness fact (`gfC.block ≼ gjC.block` and the `block(GJ) ~ b` comparability) from the FFG
justification dynamics, following the paper's actual GU-recency argument (no honest head agreement
above `b`). Naming: **D1** (`greatestFinalized_block_ancestor_greatestRealizedJustified`),
**J2/D3** (`greatestRealizedJustified_on_chain`, the paper's GU-recency +
justified-uniqueness-per-epoch route, in its slot-bound-free comparability form).
-/


/-- **The realized D1 — `greatestFinalized.block ≼ (greatestRealizedJustified).block`.** The
    realized analogue of D1: `block(GF) ≼ block(GJ_real)` for the *realized* greatest justified
    (Def 3). Given the greatest *finalized* checkpoint is **realized**
    (`hGFreal : (greatestFinalized A V).epoch < τ.epochOf (τ.slotOf t)` — carried as a faithful
    realization invariant, since the greatest finalized always lags the running epoch): if there is
    no finalized mentioned checkpoint, `greatestFinalized` defaults to `genesisCheckpoint`, ancestor
    of everything (`genesis_ancestor`); otherwise `greatestFinalized` is genuinely finalized, and
    being justified + mentioned + realized, `greatestRealizedJustified_max` dominates it in epoch
    (`gfC.epoch ≤ (GJ_real).epoch`), so the FFG prefix property (`FinalizedPrefixOfJustified`)
    supplies the block-ancestry `gfC.block ≼ (GJ_real).block`. This is what makes the never-filter's
    D2 leaf condition (`gfC.block ≼ b''`) hold against the realized `GJ` block — the filter's `gjC`
    is now the realized `GJ`. -/
theorem greatestFinalized_block_ancestor_greatestRealizedJustified (A : Anchor n) (τ : Timing)
    (V : View n (FFGVote n)) (t : Time) (hpre : FinalizedPrefixOfJustified A V)
    (hGFreal : (greatestFinalized A V).epoch < τ.epochOf (τ.slotOf t)) :
    (greatestFinalized A V).block ≼ (greatestRealizedJustified A τ V t).block := by
  classical
  -- Case on whether some finalized mentioned checkpoint exists; mirror the global D1, but with the
  -- realized-GJ argmax dominating the (now realized) greatest finalized in epoch.
  -- The greatest finalized is justified and mentioned; with `hGFreal` it is realized.
  have hGFJust : Justified A V (greatestFinalized A V) := greatestFinalized_justified A V
  have hGFMem : (greatestFinalized A V) ∈ mentionedCheckpoints V :=
    greatestFinalized_mem_mentioned A V
  -- realized-GJ epoch domination of the realized greatest finalized.
  have hepoch : (greatestFinalized A V).epoch ≤ (greatestRealizedJustified A τ V t).epoch :=
    greatestRealizedJustified_max A τ V t hGFMem hGFJust hGFreal
  -- the realized GJ is justified; the FFG prefix property gives the block-ancestry direction.
  have hGFFin' : Finalized A V (greatestFinalized A V) ∨
      (greatestFinalized A V) = genesisCheckpoint := by
    -- finalized-or-genesis: re-derive the `some/none` case of `greatestFinalized`.
    unfold greatestFinalized
    cases harg :
        ((mentionedCheckpoints V).filter (fun C => Finalized A V C)).toList.argmax (·.epoch) with
    | none => exact Or.inr rfl
    | some Cf =>
      have hmem := List.argmax_mem harg
      rw [Finset.mem_toList, Finset.mem_filter] at hmem
      exact Or.inl hmem.2
  rcases hGFFin' with hFin | hGen
  · exact hpre hFin (greatestRealizedJustified_justified A τ V t) hepoch
  · rw [hGen]; exact genesis_ancestor _

/-! #### J2 / D3 — the realized `greatestJustified` stays on `chain(b)` -/

/-- **J2 / D3 — `greatestRealizedJustified` stays on `chain(b)`, comparability form — NO slot
    bound.**
    Concludes `block(GJ) ~ b` (`block(GJ) ≼ b ∨ b ≼ block(GJ)`) for the *realized*
    greatest-justified `GJ = greatestRealizedJustified bal₀ τ (𝒱 w t') t'` (epoch strictly below
    `epochOf(slotOf t')`, by `greatestRealizedJustified_realized`). The GU-root **slot bound is no
    longer needed** — the never-filter consumes the bare comparability and case-splits on its
    direction (the `b ≼ block(GJ)` branch closes the never-filter directly; see
    `confirmedNotFFGFiltered_proved`). Both cases of the proof deliver one of the two directions:

    * **Case A (`epoch(b) ≤ GJ.epoch`)** — the realized GJ is `Justified`
      (`greatestRealizedJustified_justified`), so the gate `WillNoConflictingChkpBeJustified`
      yields compatibility `b ~ GJ.block` **directly**, which is exactly the comparability
      `GJ.block ≼ b ∨ b ≼ GJ.block` (after symmetrizing the `~`). No slot bound is used to pick a
      direction — both directions are kept for the caller.
    * **Case B (`GJ.epoch < epoch(b)`)** — the GU-recency / justified-uniqueness argument. `hGU`
      supplies a justified `GUc` of epoch `epoch(b) − 1` with `GUc.block ≼ b`. In this case
      `epoch(b) > GJ.epoch ≥ 0`, so `epoch(b) ≥ 1`, and `GUc` is *realized*
      (`GUc.epoch = epoch(b) − 1 < epoch(b) ≤ epochOf(slotOf t')`, from `hbt'`), so
      `greatestRealizedJustified_max` dominates it: `epoch(b) − 1 ≤ GJ.epoch`. With the case bound
      `GJ.epoch ≤ epoch(b) − 1` this is equality, and `huniq` (justified-uniqueness-per-epoch)
      forces `GJ.block = GUc.block ≼ b` — the `GJ.block ≼ b` direction. (The `epoch(b) = 0`
      sub-case never reaches Case B.)

    The realization (`hbt'`) is what makes the GU anchor *realized* so the realized argmax
    `greatestRealizedJustified` sees it. `hgjwf` (GJ-block well-formedness) is no longer needed
    either: it was used only by the dropped slot-bound antisymmetry step. -/
theorem greatestRealizedJustified_on_chain {bal₀ : Stakes n} {τ : Timing} {fm : FaultModel n}
    {𝒱 : ViewFamily n (FFGVote n)} {b : Block n} {t : Time}
    (hgate : WillNoConflictingChkpBeJustified bal₀ fm τ 𝒱 b t)
    (huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t') C₁ → Justified bal₀ (𝒱 w t') C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time} (ht' : τ.st (τ.slotOf t) ≤ t')
    (hbt' : τ.epochOf b.slot ≤ τ.epochOf (τ.slotOf t'))
    (hGU : ∃ GUc : Checkpoint n, Justified bal₀ (𝒱 w t') GUc ∧
      GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b) :
    (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b
      ∨ b ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block := by
  classical
  rcases Nat.lt_or_ge (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch (τ.epochOf b.slot)
    with hlt | hge
  · -- Case B: GJ.epoch < epoch(b). Pin GJ to the GU anchor via realized-domination + uniqueness.
    refine Or.inl ?_
    obtain ⟨GUc, hGUc, hGUcep, hGUcle⟩ := hGU
    have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
    have hGUcMem : GUc ∈ mentionedCheckpoints (𝒱 w t') :=
      justified_mem_mentioned bal₀ (𝒱 w t') hwit hGUc
    -- In Case B, `epoch(b) > GJ.epoch ≥ 0`, so `epoch(b) ≥ 1`; GUc is realized:
    -- epoch(b) − 1 < epoch(b) ≤ epochOf(slotOf t').
    have hbpos : 0 < τ.epochOf b.slot := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hGUcReal : GUc.epoch < τ.epochOf (τ.slotOf t') := by
      rw [hGUcep]
      exact lt_of_lt_of_le (Nat.sub_lt hbpos Nat.one_pos) hbt'
    have hdom : GUc.epoch ≤ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch :=
      greatestRealizedJustified_max bal₀ τ (𝒱 w t') t' hGUcMem hGUc hGUcReal
    -- GJ.epoch = GUc.epoch (= epoch(b) − 1), from `hlt`, `hdom`, `hGUcep`.
    have hle : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ GUc.epoch := by
      rw [hGUcep]; exact Nat.le_sub_one_of_lt hlt
    have hepeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch = GUc.epoch :=
      Nat.le_antisymm hle hdom
    have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block = GUc.block :=
      huniq hw (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') hGUc hepeq
    rw [hblockeq]; exact hGUcle
  · -- Case A: epoch(b) ≤ GJ.epoch. The gate gives compatibility `b ~ GJ.block` directly — that IS
    -- the comparability (no slot bound to pick a direction; both directions handed to the caller).
    have hcompat : b ~ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block :=
      hgate hw ht' (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') hge
    exact (Or.symm hcompat)

end FastConfirmation.HFC

end
