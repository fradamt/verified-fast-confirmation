module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedBlockTransitionProvenance
public import FastConfirmation.Spec.Proof.FFGSourceCoherence
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Guarded realization of accepted same-epoch ancestry segments

This module lifts the concrete `KnownSameEpochAncestrySegment` of one exact
causal store into `AcceptedProjectedSameEpochSegment`.  Every nontrivial edge
uses the last accepted writer supplied by
`AcceptedBlockTransitionProvenance`; a bare scheduled block or reconstructed
history is never accepted as an edge.

Two guards are essential under duplicate-root overwrites:

* `WellFormedExecution` makes the transition-prefix parent message agree with
  the later ancestry store's parent message.
* well-formed core evidence at every causal prefix identifies the
  transition-prefix parent-state slot with that agreed block-message slot.

Thus the same-epoch premise passed to
`AcceptedProjectedSameEpochTransition.of_transition` remains an
insertion-time statement.  A same-epoch claim about only the later store is
never substituted for it.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}

/-! ## Well-formed core at exact prefixes -/

namespace Execution

/-- The handler-local core at every store in the exact causal domain. -/
def ExactCausalStoreWellFormedCore
    (cfg : Config) (ext : Externals Root) (E : Execution Root) : Prop :=
  ∀ {store : Store Root}, E.CausalStore cfg ext store →
    WellFormedStoreCore store

/-- A rejected event leaves the store unchanged; a successful event preserves
the handler-local core by the executable handler theorem. -/
private theorem apply_event_getD_wellFormedStoreCore_forPrefix
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (store : Store Root) (event : Event Root)
    (hcore : WellFormedStoreCore store) :
    WellFormedStoreCore ((apply_event cfg ext store event).getD store) := by
  cases hevent : apply_event cfg ext store event with
  | none => rw [Option.getD_none]; exact hcore
  | some store' =>
      rw [Option.getD_some]
      exact apply_event_wellFormedStoreCore cfg ext hst_slot hcore hevent

/-- Folding an exact list prefix preserves the handler-local core. -/
private theorem foldl_wellFormedStoreCore_forPrefix
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot) :
    ∀ (events : List (Event Root)) (store : Store Root),
      WellFormedStoreCore store →
      WellFormedStoreCore
        (events.foldl
          (fun s event => (apply_event cfg ext s event).getD s) store) := by
  intro events
  induction events with
  | nil => intro store hcore; exact hcore
  | cons event events ih =>
      intro store hcore
      rw [List.foldl_cons]
      exact ih _
        (apply_event_getD_wellFormedStoreCore_forPrefix
          hst_slot store event hcore)

/-- Every exact scheduled prefix has the handler-local core when the genesis
store has it and valid state transitions land on their block slots. -/
theorem ScheduledEventPrefix.wellFormedStoreCore
    {E : Execution Root} (p : E.ScheduledEventPrefix)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hbase : WellFormedStoreCore E.genesis_store) :
    WellFormedStoreCore (p.store cfg ext) := by
  rw [ScheduledEventPrefix.store]
  apply foldl_wellFormedStoreCore_forPrefix hst_slot
  exact on_tick_wellFormedStoreCore cfg _ _
    (E.store_wellFormedStoreCore cfg ext hst_slot hbase
      p.node p.previousSecond)

/-- Mechanical producer for core evidence over the full exact causal domain. -/
theorem exactCausalStoreWellFormedCore
    (E : Execution Root)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hbase : WellFormedStoreCore E.genesis_store) :
    ExactCausalStoreWellFormedCore cfg ext E := by
  intro store hstore
  cases hstore with
  | genesis => exact hbase
  | scheduledPrefix p => exact p.wellFormedStoreCore hst_slot hbase

/-! ## One last-writer edge -/

namespace AcceptedBlockTransition

variable {E : Execution Root}

/-- A fresh successful handler's parent guard exposes parent knownness at the
transition's exact pre-prefix. -/
theorem parent_known (t : E.AcceptedBlockTransition cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots) :
    t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots := by
  have haccepted := t.accepted
  simp only [on_block, if_neg hfresh] at haccepted
  split_ifs at haccepted with hparent <;> try cases haccepted
  all_goals simpa only [not_not] using hparent

end AcceptedBlockTransition

/-- A known non-genesis parent-child edge in a later causal store is realized
by the child's actual last accepted writer.  `hsame` is transported back to
the transition prefix through message uniqueness and the prefix core before
being supplied to the accepted edge constructor. -/
theorem acceptedProjectedSameEpochTransition_of_known_parent
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hwf : WellFormedExecution E)
    (hcore : ExactCausalStoreWellFormedCore cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {parent child : Root}
    (hparentKnown : parent ∈ store.block_roots)
    (hchildKnown : child ∈ store.block_roots)
    (hchildNonGenesis : child ∉ E.genesis_store.block_roots)
    (hparent : (store.blocks child).parent_root = parent)
    (hsame : compute_epoch_at_slot cfg (store.blocks parent).slot =
      compute_epoch_at_slot cfg (store.blocks child).slot) :
    AcceptedProjectedSameEpochTransition cfg ext E S parent child := by
  obtain ⟨writer⟩ :=
    hstore.acceptedBlockLastWriterProvenance child hchildKnown
      hchildNonGenesis
  let t := writer.transition
  have htRoot : t.signedBlock.root = child := writer.root_eq
  have htMessage : t.signedBlock.message = store.blocks child :=
    writer.message_eq
  have htParent : t.signedBlock.message.parent_root = parent :=
    (congrArg BeaconBlock.parent_root htMessage).trans hparent
  have htParentKnown : t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots :=
    t.parent_known writer.fresh
  have hprefixParentKnown : parent ∈
      (t.atPrefix.store cfg ext).block_roots := by
    rw [← htParent]
    exact htParentKnown
  have hprefixParentAt : E.AcceptedBlockAt cfg ext parent
      ((t.atPrefix.store cfg ext).blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hprefixParentKnown
  have hstoreParentAt : E.AcceptedBlockAt cfg ext parent
      (store.blocks parent) :=
    E.acceptedBlockAt_of_causal_known cfg ext hstore hparentKnown
  have hparentMessage :
      (t.atPrefix.store cfg ext).blocks parent = store.blocks parent :=
    hprefixParentAt.unique cfg ext E hwf hstoreParentAt
  have hprefixCore : WellFormedStoreCore
      (t.atPrefix.store cfg ext) :=
    hcore (.scheduledPrefix t.atPrefix)
  have hinsertionSameEpoch :
      compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root).slot =
        compute_epoch_at_slot cfg t.signedBlock.message.slot := by
    calc
      compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).block_states
            t.signedBlock.message.parent_root).slot =
          compute_epoch_at_slot cfg
            ((t.atPrefix.store cfg ext).block_states parent).slot := by
        rw [htParent]
      _ = compute_epoch_at_slot cfg
          ((t.atPrefix.store cfg ext).blocks parent).slot :=
        congrArg (compute_epoch_at_slot cfg)
          (hprefixCore.2 parent hprefixParentKnown)
      _ = compute_epoch_at_slot cfg (store.blocks parent).slot :=
        congrArg (fun b => compute_epoch_at_slot cfg b.slot)
          hparentMessage
      _ = compute_epoch_at_slot cfg (store.blocks child).slot := hsame
      _ = compute_epoch_at_slot cfg t.signedBlock.message.slot :=
        (congrArg (fun b => compute_epoch_at_slot cfg b.slot)
          htMessage).symm
  have hedge := AcceptedProjectedSameEpochTransition.of_transition
    (S := S) t writer.fresh htParentKnown hinsertionSameEpoch
  rw [htParent, htRoot] at hedge
  exact hedge

/-! ## Segment lift -/

/-- Every concrete known same-epoch ancestry segment in an exact causal store
lifts to accepted edges.  The reflexive constructor is the explicit genesis
base case; each nontrivial child is non-genesis by the source relation and is
therefore realized through last-writer provenance. -/
theorem knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hwf : WellFormedExecution E)
    (hcore : ExactCausalStoreWellFormedCore cfg ext E)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {first last : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots store first last) :
    AcceptedProjectedSameEpochSegment cfg ext E S first last := by
  induction hsegment with
  | refl known =>
      exact .refl first (store.blocks first)
        (E.acceptedBlockAt_of_causal_known cfg ext hstore known)
  | @tail parent child hprefix hchild hnonGenesis hparent hsame ih =>
      exact .tail ih
        (acceptedProjectedSameEpochTransition_of_known_parent
          hwf hcore hstore hprefix.last_known hchild hnonGenesis
          hparent hsame)

/-- Mechanical specialization using the standard state-transition slot law
and a genesis core witness. -/
theorem knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment_of_core
    {E : Execution Root} {anchor : Checkpoint Root}
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hwf : WellFormedExecution E)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hbase : WellFormedStoreCore E.genesis_store)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {first last : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots store first last) :
    AcceptedProjectedSameEpochSegment cfg ext E S first last :=
  knownSameEpochAncestrySegment_toAcceptedProjectedSameEpochSegment
    hwf (E.exactCausalStoreWellFormedCore hst_slot hbase) hstore hsegment

end Execution

end FastConfirmation.Spec

end
