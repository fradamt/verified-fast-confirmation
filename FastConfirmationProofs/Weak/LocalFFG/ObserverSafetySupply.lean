module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverPremiseReduction
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadMembership

/-! Observer-local knownness and AU ancestry for the weak safety path. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

namespace ObserverLocalFFG

/-- The observer's fork-choice head is in its own block map. -/
theorem head_known (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n : ℕ) :
    (get_head cfg (E.store cfg ext obs n)).root ∈
      (E.store cfg ext obs n).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext obs n) with hm | heq
  · exact hm
  · rw [heq]
    exact B.justified_root_known core localInputs n

/-- A local AU tip's walk reaches its checkpoint epoch boundary. -/
theorem auTip_walkKnown (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU tip c) :
    WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip := by
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  obtain ⟨ast, ablk, hgenEq, hslot, _, hparent⟩ := hT.genesis
  have hanchorRoot : E.genesis_store.justified_checkpoint.root = ablk.root := by
    rw [hgenEq]
    rfl
  have hanchorMem0 : E.genesis_store.justified_checkpoint.root ∈
      E.genesis_store.block_roots := by
    rw [hanchorRoot, hgenEq]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : E.genesis_store.justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks E.genesis_store.justified_checkpoint.root =
        ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg E.genesis_store.justified_checkpoint.epoch := by
    have hb := core.anchor_boundary
    rw [core.anchor_eq] at hb
    simpa only [TrustedAnchorBoundaryAligned, withoutObserver, hgenEq,
      get_forkchoice_store, Function.update_self] using hb
  have hanchorEpochLe : E.genesis_store.justified_checkpoint.epoch ≤ c.epoch :=
    (B.au_certificate hAU).2
  have hstartLe :
      compute_start_slot_at_epoch cfg E.genesis_store.justified_checkpoint.epoch ≤
        compute_start_slot_at_epoch cfg c.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks E.genesis_store.justified_checkpoint.root).slot
      tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
      E.genesis_store.justified_checkpoint.root hanchorMem tip htip
  apply hwalkAnchor.mono
  rw [hanchorBlock]
  exact hboundary.trans hstartLe

/-- An observer-local AU checkpoint is known and lies below its known tip. -/
theorem auCheckpoint_known_and_below_tip
    (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (n : ℕ) {tip : Root} {c : Checkpoint Root}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hAU : B.state.AU tip c) :
    c.root ∈ (E.store cfg ext obs n).block_roots ∧
      is_ancestor (E.store cfg ext obs n) (get_node_for_root tip)
        (get_node_for_root c.root) = true := by
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  obtain ⟨ast, ablk, hgenEq, hslot, _, hparent⟩ := hT.genesis
  have hstore : E.ObserverCausalStore cfg ext obs
      (E.store cfg ext obs n) := store_observerCausal n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  have hwalk : WalkKnown (E.store cfg ext obs n)
      (compute_start_slot_at_epoch cfg c.epoch) tip :=
    B.auTip_walkKnown hobs core localInputs n htip hAU
  have hcheckpoint := B.au_checkpoint_of_known hstore tip htip c hAU
  have hroot : c.root = (get_ancestor (E.store cfg ext obs n)
      (ForkChoiceNode.mk tip .pending)
      (compute_start_slot_at_epoch cfg c.epoch)).root := by
    have hr := congrArg Checkpoint.root hcheckpoint
    simpa only [get_checkpoint_for_block, get_checkpoint_block] using hr
  obtain ⟨hknown, hslotLe⟩ := get_ancestor_spec hparentSlots hwalk
  have hcKnown : c.root ∈ (E.store cfg ext obs n).block_roots := by
    rw [hroot]
    exact hknown
  have hcSlot : ((E.store cfg ext obs n).blocks c.root).slot ≤
      compute_start_slot_at_epoch cfg c.epoch := by
    rw [hroot]
    exact hslotLe
  have hback : WalkKnown (E.store cfg ext obs n)
      ((E.store cfg ext obs n).blocks c.root).slot tip :=
    E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n c.root hcKnown tip htip
  have hcomp := get_ancestor_comp_root hparentSlots hcSlot hback
  rw [← hroot, get_ancestor_stop (le_refl _)] at hcomp
  refine ⟨hcKnown, ?_⟩
  simp only [is_ancestor_get_node_for_root, decide_eq_true_eq]
  exact hcomp.symm

/-- A known block's local unrealized justification is known and lies below
that block. -/
theorem blockUnrealizedJustification_known_and_below
    (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (n : ℕ) (supplier : Root)
    (hsupplier : supplier ∈ (E.store cfg ext obs n).block_roots) :
    ((E.store cfg ext obs n).unrealized_justifications supplier).root ∈
      (E.store cfg ext obs n).block_roots ∧
    is_ancestor (E.store cfg ext obs n)
      (get_node_for_root supplier)
      (get_node_for_root
        ((E.store cfg ext obs n).unrealized_justifications supplier).root) = true := by
  have hs : E.ObserverCausalStore cfg ext obs
      (E.store cfg ext obs n) := store_observerCausal n
  have hgu := (B.store_projection hs).unrealized_justification supplier hsupplier
  have hAU : B.state.AU supplier
      ((E.store cfg ext obs n).unrealized_justifications supplier) := by
    rw [hgu]
    exact (B.selectors_AU hs hsupplier).2.1
  exact B.auCheckpoint_known_and_below_tip hobs core localInputs n hsupplier hAU

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
