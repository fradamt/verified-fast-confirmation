module
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationModel.Execution.PayloadFrame

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / BlockAgreement

Cross-store block agreement (`BlockAgreement`). Three layers, each built on the
previous:

* **Provenance (per-node trajectory invariant).** Every root an honest or
  Byzantine node's store carries is either the genesis anchor (with its block
  unchanged) or the root of a scheduled block event whose message equals the
  store's recorded block. Proved by induction over `Execution.store` with
  `on_block` inversion — the only handler that writes `blocks` / `block_roots`.
  No behavioral assumption enters: block roots provably come only from the
  node's own `schedule`.
* **Cross-store agreement.** Under `WellFormedExecution` (roots are genuine
  commitments), any two stores agree on `blocks r` for every commonly-known
  root `r` — genesis roots via `genesis_blocks_agree`, scheduled roots via
  `blocks_root_injective`.
* **`is_ancestor` transport.** `get_ancestor` reads only `blocks` along the
  walk, so on the `WalkKnown` domain it — and hence `is_ancestor` — is
  invariant under any store that agrees on the known blocks. Specialized to one
  node across time via `StoreLE` (block sets grow) + provenance.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## Provenance predicate -/

/-- `b` is a block scheduled to some node at some second — the wire objects
`WellFormedExecution` ranges over. -/
def IsScheduledBlock (E : Execution Root) (b : SignedBeaconBlock Root) : Prop :=
  ∃ w m, Event.block b ∈ E.schedule w m

/-- Provenance of a store relative to an execution: every known root either is
a genesis-anchor root carrying its genesis block, or is the root of a scheduled
block event whose message is the store's recorded block. Depends only on the
`block_roots` / `blocks` fields, so it transfers across stores agreeing on
those (`of_eq`). -/
def BlockProvenance (E : Execution Root) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots,
    (r ∈ E.genesis_store.block_roots ∧ store.blocks r = E.genesis_store.blocks r) ∨
    (∃ b : SignedBeaconBlock Root,
      IsScheduledBlock E b ∧ b.root = r ∧ store.blocks r = b.message)

namespace BlockProvenance

/-- `BlockProvenance` reads only `block_roots` and `blocks`; transfer it across
any store agreeing on those two fields. -/
theorem of_eq {E : Execution Root} {store store' : Store Root}
    (h : BlockProvenance E store)
    (hbr : store'.block_roots = store.block_roots)
    (hb : store'.blocks = store.blocks) : BlockProvenance E store' := by
  intro r hr
  rw [hbr] at hr
  rw [hb]
  exact h r hr

/-- Payload handlers leave the block provenance fields equal. -/
theorem of_payloadFrame {E : Execution Root} {store store' : Store Root}
    (h : BlockProvenance E store) (hf : PayloadFrame store store') :
    BlockProvenance E store' := h.of_eq hf.block_roots hf.blocks

end BlockProvenance

/-! ## Provenance preservation by the block-set-preserving helpers

Every handler helper except `on_block` leaves `block_roots` and `blocks`
untouched, so it preserves `BlockProvenance` via `of_eq`. -/

/-- Folding a `block_roots`-preserving step preserves `block_roots`. -/
private theorem foldl_block_roots {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, (f s a).block_roots = s.block_roots) (l : List α) (s : Store Root) :
    (l.foldl f s).block_roots = s.block_roots := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf]

/-- Folding a `blocks`-preserving step preserves `blocks`. -/
private theorem foldl_blocks {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, (f s a).blocks = s.blocks) (l : List α) (s : Store Root) :
    (l.foldl f s).blocks = s.blocks := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hf]

theorem update_checkpoints_blockProvenance {E : Execution Root} (store : Store Root)
    (jc fc : Checkpoint Root) (h : BlockProvenance E store) :
    BlockProvenance E (update_checkpoints store jc fc) :=
  h.of_eq (by simp) (by simp only [update_checkpoints]; split_ifs <;> rfl)


theorem update_latest_messages_blockProvenance {E : Execution Root} (store : Store Root)
    (attesting_indices : List ValidatorIndex) (attestation : Attestation Root)
    (h : BlockProvenance E store) :
    BlockProvenance E (update_latest_messages store attesting_indices attestation) := by
  refine h.of_eq ?_ ?_
  · simp only [update_latest_messages]
    refine foldl_block_roots (fun s i => ?_) _ _
    dsimp only
    rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> rfl
  · simp only [update_latest_messages]
    refine foldl_blocks (fun s i => ?_) _ _
    dsimp only
    rcases hmi : s.latest_messages i with _ | lm <;> split_ifs <;> rfl

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
theorem record_block_timeliness_blockProvenance {E : Execution Root} (store : Store Root)
    (root : Root) (h : BlockProvenance E store) :
    BlockProvenance E (record_block_timeliness cfg store root) :=
  h.of_eq rfl rfl

theorem update_proposer_boost_root_blockProvenance {E : Execution Root} (store : Store Root)
    (head root : Root) (h : BlockProvenance E store) :
    BlockProvenance E (update_proposer_boost_root cfg store head root) :=
  h.of_eq (by simp only [update_proposer_boost_root]; split_ifs <;> rfl)
    (by simp only [update_proposer_boost_root]; split_ifs <;> rfl)

omit [Inhabited Root] in
theorem store_target_checkpoint_state_blockProvenance {E : Execution Root} (store : Store Root)
    (target : Checkpoint Root) (h : BlockProvenance E store) :
    BlockProvenance E (store_target_checkpoint_state cfg ext store target) :=
  h.of_eq (by simp only [store_target_checkpoint_state]; split_ifs <;> rfl)
    (by simp only [store_target_checkpoint_state]; split_ifs <;> rfl)

omit [Inhabited Root] in
theorem compute_pulled_up_tip_blockProvenance {E : Execution Root} (store : Store Root)
    (block_root : Root) (h : BlockProvenance E store) :
    BlockProvenance E (compute_pulled_up_tip cfg ext store block_root) :=
  h.of_eq
    (by simp only [compute_pulled_up_tip, update_checkpoints, update_unrealized_checkpoints]
        split_ifs <;> rfl)
    (by simp only [compute_pulled_up_tip, update_checkpoints, update_unrealized_checkpoints]
        split_ifs <;> rfl)

/-! ## Provenance preservation by `on_tick`

`on_tick` only ticks the clock and pulls up checkpoints; it never writes the
block set. -/

omit [LinearOrder Root] in
theorem on_tick_per_slot_blockProvenance {E : Execution Root} (store : Store Root)
    (time : ℕ) (h : BlockProvenance E store) :
    BlockProvenance E (on_tick_per_slot cfg store time) :=
  h.of_eq (by simp only [on_tick_per_slot, update_checkpoints]; split_ifs <;> rfl)
    (by simp only [on_tick_per_slot, update_checkpoints]; split_ifs <;> rfl)

omit [LinearOrder Root] in
theorem on_tick_aux_blockProvenance {E : Execution Root} (tick_slot fuel : ℕ) :
    ∀ store : Store Root, BlockProvenance E store →
      BlockProvenance E (on_tick_aux cfg tick_slot fuel store) := by
  induction fuel with
  | zero => intro s h; exact h
  | succ f ih =>
    intro s h
    rw [on_tick_aux]
    split_ifs
    · exact ih _ (on_tick_per_slot_blockProvenance cfg _ _ h)
    · exact h

omit [LinearOrder Root] in
theorem on_tick_blockProvenance {E : Execution Root} (store : Store Root) (time : ℕ)
    (h : BlockProvenance E store) :
    BlockProvenance E (on_tick cfg store time) := by
  simp only [on_tick]
  exact on_tick_per_slot_blockProvenance cfg _ _ (on_tick_aux_blockProvenance cfg _ _ _ h)

/-! ## Provenance preservation by `on_block`

The one handler that writes the block set. The added root is the applied
block's own `root`, its recorded block the block's `message`, and the applied
block is a scheduled event — so provenance's scheduled clause is discharged by
`hsched`; every pre-existing root keeps its recorded block (the `Function.update`
misses it). -/

omit [Inhabited Root] in
/-- Provenance survives adding one scheduled block to the store (the store shape
`on_block` produces after its four post-helpers are peeled off). The block-root
list is left abstract with a membership bound so both branches of `on_block`'s
append-if-absent are covered uniformly. -/
theorem blockProvenance_add {E : Execution Root} {store : Store Root}
    (sb : SignedBeaconBlock Root) (hsched : IsScheduledBlock E sb)
    (state : BeaconState Root) (br : List Root)
    (hbr : ∀ r ∈ br, r = sb.root ∨ r ∈ store.block_roots)
    (h : BlockProvenance E store) :
    BlockProvenance E
      { store with
        block_roots := br
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root state } := by
  intro r hr
  dsimp only at hr ⊢
  by_cases hrb : r = sb.root
  · subst hrb
    right
    exact ⟨sb, hsched, rfl, by rw [Function.update_self]⟩
  · rw [Function.update_of_ne hrb]
    exact h r ((hbr r hr).resolve_left hrb)

theorem notify_ptc_messages_blockProvenance {E : Execution Root} {store store' : Store Root}
    {state : BeaconState Root} {attestations : List (IndexedPayloadAttestation Root)}
    (h : BlockProvenance E store)
    (hh : notify_ptc_messages cfg ext store state attestations = some store') :
    BlockProvenance E store' := h.of_payloadFrame (notify_ptc_messages_frame cfg ext hh)

theorem on_block_blockProvenance {E : Execution Root} {store store' : Store Root}
    {sb : SignedBeaconBlock Root} (hsched : IsScheduledBlock E sb)
    (h : BlockProvenance E store) (hh : on_block cfg ext store sb = some store') :
    BlockProvenance E store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact h
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      dsimp only at hh
      split at hh
      · cases hh
      · rename_i after_ptc hptc
        cases hh
        apply compute_pulled_up_tip_blockProvenance
        apply update_checkpoints_blockProvenance
        apply update_proposer_boost_root_blockProvenance
        apply record_block_timeliness_blockProvenance
        refine notify_ptc_messages_blockProvenance cfg ext ?_ hptc
        refine blockProvenance_add sb hsched state _ ?_ h
        intro r hr
        rw [List.mem_append, List.mem_singleton] at hr
        exact hr.symm

/-! ## Provenance preservation by the attestation handlers -/

omit [Inhabited Root] in
theorem on_attestation_blockProvenance {E : Execution Root} {store store' : Store Root}
    {attestation : Attestation Root} {is_from_block : Bool} (h : BlockProvenance E store)
    (hh : on_attestation cfg ext store attestation is_from_block = some store') :
    BlockProvenance E store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  exact update_latest_messages_blockProvenance _ _ _
    (store_target_checkpoint_state_blockProvenance cfg ext store _ h)

omit [Inhabited Root] in
theorem on_attester_slashing_blockProvenance {E : Execution Root} {store store' : Store Root}
    {attester_slashing : AttesterSlashing Root} (h : BlockProvenance E store)
    (hh : on_attester_slashing ext store attester_slashing = some store') :
    BlockProvenance E store' := by
  simp only [on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact h.of_eq rfl rfl

omit [Inhabited Root] in
theorem on_payload_attestation_message_blockProvenance {E : Execution Root}
    {store store' : Store Root} {message : PayloadAttestationMessage Root}
    {is_from_block : Bool} (h : BlockProvenance E store)
    (hh : on_payload_attestation_message cfg ext store message is_from_block = some store') :
    BlockProvenance E store' :=
  h.of_payloadFrame (on_payload_attestation_message_frame cfg ext hh)

omit [Inhabited Root] in
theorem on_execution_payload_envelope_blockProvenance {E : Execution Root}
    {store store' : Store Root} {envelope : SignedExecutionPayloadEnvelope Root}
    {observation : EnvelopeObservation Root} (h : BlockProvenance E store)
    (hh : on_execution_payload_envelope ext store envelope observation = some store') :
    BlockProvenance E store' :=
  h.of_payloadFrame (on_execution_payload_envelope_frame ext hh)

/-! ## Event dispatch, the event fold, and the trajectory invariant -/

/-- One dispatched event preserves provenance; block events additionally require
the applied block to be scheduled (`hsched`), which the trajectory supplies from
the node's own `schedule`. -/
theorem apply_event_blockProvenance {E : Execution Root} {s s' : Store Root}
    {e : Event Root} (hsched : ∀ b, e = Event.block b → IsScheduledBlock E b)
    (h : BlockProvenance E s) (he : apply_event cfg ext s e = some s') :
    BlockProvenance E s' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_blockProvenance cfg ext (hsched b rfl) h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_blockProvenance cfg ext h he
  | attester_slashing sl =>
    simp only [apply_event] at he
    exact on_attester_slashing_blockProvenance ext h he
  | execution_payload_envelope envelope observation =>
    exact on_execution_payload_envelope_blockProvenance ext h he
  | payload_attestation_message message is_from_block =>
    exact on_payload_attestation_message_blockProvenance cfg ext h he

/-- Folding the second's scheduled events preserves provenance: every block
event in the list is scheduled, so each `apply_event` step keeps the invariant. -/
theorem blockProvenance_foldl {E : Execution Root} :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ b, Event.block b ∈ l → IsScheduledBlock E b) → BlockProvenance E s →
      BlockProvenance E
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ h; exact h
  | cons e l ih =>
    intro s hl h
    rw [List.foldl_cons]
    apply ih
    · intro b hb; exact hl b (List.mem_cons_of_mem e hb)
    · cases he : apply_event cfg ext s e with
      | none => simpa [he] using h
      | some s' =>
        simp only [Option.getD_some]
        refine apply_event_blockProvenance cfg ext (fun b hbeq => hl b ?_) h he
        rw [← hbeq]; exact List.mem_cons_self

/-- Provenance holds at every node and second (no honesty needed — block roots
provably come only from the node's own scheduled events / the genesis anchor). -/
theorem Execution.blockProvenance (E : Execution Root) (v : ValidatorIndex) (n : ℕ) :
    BlockProvenance E (E.store cfg ext v n) := by
  induction n with
  | zero => intro r hr; exact Or.inl ⟨hr, rfl⟩
  | succ n ih =>
    change BlockProvenance E ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    exact blockProvenance_foldl cfg ext _ _ (fun b hb => ⟨v, n + 1, hb⟩)
      (on_tick_blockProvenance cfg _ _ ih)

/-! ## Cross-store block agreement

Under `WellFormedExecution`, two provenance-respecting stores agree on the block
recorded at any commonly-known root: genesis roots via `genesis_blocks_agree`,
scheduled roots via `blocks_root_injective` (equal roots ⇒ equal messages). -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Any two stores respecting provenance agree on `blocks r` for every root `r`
known to both. -/
theorem WellFormedExecution.blocks_agree {E : Execution Root} (hwf : WellFormedExecution E)
    {s t : Store Root} (hps : BlockProvenance E s) (hpt : BlockProvenance E t)
    {r : Root} (hrs : r ∈ s.block_roots) (hrt : r ∈ t.block_roots) :
    s.blocks r = t.blocks r := by
  rcases hps r hrs with ⟨hg, hbs⟩ | ⟨b, ⟨w, m, hmem⟩, hbr, hbb⟩ <;>
    rcases hpt r hrt with ⟨hg', hbt⟩ | ⟨b', ⟨w', m', hmem'⟩, hbr', hbb'⟩
  · rw [hbs, hbt]
  · rw [hbs, hbb']
    have hgb := hwf.genesis_blocks_agree w' m' b' hmem' (by rw [hbr']; exact hg)
    rw [hbr'] at hgb
    exact hgb.symm
  · rw [hbb, hbt]
    have hgb := hwf.genesis_blocks_agree w m b hmem (by rw [hbr]; exact hg')
    rw [hbr] at hgb
    exact hgb
  · rw [hbb, hbb']
    exact hwf.blocks_root_injective w m b hmem w' m' b' hmem' (hbr.trans hbr'.symm)

/-! ## `is_ancestor` transport

`get_ancestor` reads only `blocks` along the parent walk, so on the `WalkKnown`
domain it is invariant under any store agreeing on the known blocks; hence so is
`is_ancestor`. -/

omit [Inhabited Root] in
/-- Every parent step reads the child's bid and its known parent's bid. Stores
that agree on known blocks therefore agree on the complete node, for any
starting status and fuel. -/
theorem get_ancestor_aux_congr_status {s t : Store Root}
    (hagree : ∀ x ∈ s.block_roots, s.blocks x = t.blocks x)
    {slot : Slot} {r : Root} (hw : WalkKnown s slot r) :
    ∀ (status : PayloadStatus) (fuel : ℕ),
      get_ancestor_aux s slot fuel (ForkChoiceNode.mk r status) =
        get_ancestor_aux t slot fuel (ForkChoiceNode.mk r status) := by
  induction hw with
  | @stop r hr hle =>
    intro status fuel
    cases fuel with
    | zero => rfl
    | succ f =>
      simp only [get_ancestor_aux]
      rw [if_neg (by simpa using hle),
        if_neg (by rw [← hagree r hr]; simpa using hle)]
  | @step r hr hgt hp ih =>
    intro status fuel
    cases fuel with
    | zero => rfl
    | succ f =>
      simp only [get_ancestor_aux]
      rw [if_pos (by simpa using hgt),
        if_pos (by rw [← hagree r hr]; simpa using hgt), ← hagree r hr]
      have hstatus : get_parent_payload_status s (s.blocks r) =
          get_parent_payload_status t (s.blocks r) := by
        simp only [get_parent_payload_status, ← hagree _ hp.root_mem]
      rw [← hstatus]
      exact ih _ f


omit [Inhabited Root] in
/-- Complete ancestor transport for an arbitrary starting node. -/
theorem get_ancestor_congr_status {s t : Store Root}
    (hagree : ∀ x ∈ s.block_roots, s.blocks x = t.blocks x)
    {slot : Slot} {node : ForkChoiceNode Root} (hr : node.root ∈ s.block_roots)
    (hw : WalkKnown s slot node.root) :
    get_ancestor s node slot = get_ancestor t node slot := by
  cases node with
  | mk r status =>
    simp only [get_ancestor]
    rw [hagree r hr]
    exact get_ancestor_aux_congr_status hagree hw status _

omit [Inhabited Root] in
/-- An ancestor walk needs agreement only on its own roots. A receiver that
knows the head has its parent walk locally; other source-store forks need not
be present at the receiver. -/
theorem get_ancestor_aux_congr_common_walk {s t : Store Root}
    (hagree : ∀ x, x ∈ s.block_roots → x ∈ t.block_roots →
      s.blocks x = t.blocks x)
    {slot : Slot} {r : Root}
    (hs : WalkKnown s slot r) (ht : WalkKnown t slot r) :
    ∀ (status : PayloadStatus) (fuel : ℕ),
      get_ancestor_aux s slot fuel (ForkChoiceNode.mk r status) =
        get_ancestor_aux t slot fuel (ForkChoiceNode.mk r status) := by
  induction hs generalizing t with
  | @stop r hr hle =>
    intro status fuel
    have hblock := hagree r hr ht.root_mem
    cases fuel with
    | zero => rfl
    | succ f =>
      simp only [get_ancestor_aux]
      rw [if_neg (by simpa using hle), if_neg (by rw [← hblock]; simpa using hle)]
  | @step r hr hgt hp ih =>
    intro status fuel
    have hblock := hagree r hr ht.root_mem
    cases ht with
    | stop hrt hle =>
      rw [← hblock] at hle
      exact False.elim ((Nat.not_lt_of_ge hle) hgt)
    | step hrt hgtT hpT =>
      cases fuel with
      | zero => rfl
      | succ f =>
        simp only [get_ancestor_aux]
        rw [if_pos (by simpa using hgt),
          if_pos (by rw [← hblock]; simpa using hgt), ← hblock]
        have hparentBlock :
            s.blocks (s.blocks r).parent_root =
              t.blocks (s.blocks r).parent_root := by
          apply hagree _ hp.root_mem
          rw [hblock]
          exact hpT.root_mem
        have hstatus : get_parent_payload_status s (s.blocks r) =
            get_parent_payload_status t (s.blocks r) := by
          simp only [get_parent_payload_status, hparentBlock]
        rw [← hstatus]
        have hpT' : WalkKnown t slot (s.blocks r).parent_root := by
          rw [hblock]
          exact hpT
        exact ih hagree hpT' _ f

omit [Inhabited Root] in
/-- Complete ancestor transport along a head known in both stores. -/
theorem get_ancestor_congr_common_walk {s t : Store Root}
    (hagree : ∀ x, x ∈ s.block_roots → x ∈ t.block_roots →
      s.blocks x = t.blocks x)
    {slot : Slot} {r : Root}
    (hs : WalkKnown s slot r) (ht : WalkKnown t slot r) :
    get_ancestor s (ForkChoiceNode.mk r .pending) slot =
      get_ancestor t (ForkChoiceNode.mk r .pending) slot := by
  simp only [get_ancestor]
  rw [hagree r hs.root_mem ht.root_mem]
  exact get_ancestor_aux_congr_common_walk hagree hs ht .pending _

omit [Inhabited Root] in
/-- Pending-root ancestry transports when only the compared walk is common
to the two stores. -/
theorem is_ancestor_congr_common_walk {s t : Store Root}
    (hagree : ∀ x, x ∈ s.block_roots → x ∈ t.block_roots →
      s.blocks x = t.blocks x)
    {node ancestor : Root}
    (hancS : ancestor ∈ s.block_roots)
    (hancT : ancestor ∈ t.block_roots)
    (hs : WalkKnown s (s.blocks ancestor).slot node)
    (ht : WalkKnown t (s.blocks ancestor).slot node) :
    is_ancestor s (get_node_for_root node) (get_node_for_root ancestor) =
      is_ancestor t (get_node_for_root node) (get_node_for_root ancestor) := by
  simp only [get_node_for_root, is_ancestor_pending]
  rw [← hagree ancestor hancS hancT]
  rw [get_ancestor_congr_common_walk hagree hs ht]

omit [Inhabited Root] in
/-- Pending-node wrapper for stores that agree on every known block. -/
theorem get_ancestor_congr {s t : Store Root}
    (hagree : ∀ x ∈ s.block_roots, s.blocks x = t.blocks x)
    {slot : Slot} {r : Root} (hr : r ∈ s.block_roots) (hw : WalkKnown s slot r) :
    get_ancestor s (ForkChoiceNode.mk r .pending) slot = get_ancestor t (ForkChoiceNode.mk r .pending) slot :=
  get_ancestor_congr_status hagree hr hw

omit [Inhabited Root] in
/-- The Gloas ancestry test transports both its root and status comparison. -/
theorem is_ancestor_congr {s t : Store Root}
    (hagree : ∀ x ∈ s.block_roots, s.blocks x = t.blocks x)
    {node ancestor : ForkChoiceNode Root}
    (hnode : node.root ∈ s.block_roots) (hanc : ancestor.root ∈ s.block_roots)
    (hw : WalkKnown s (s.blocks ancestor.root).slot node.root) :
    is_ancestor s node ancestor = is_ancestor t node ancestor := by
  simp only [is_ancestor, ← hagree ancestor.root hanc,
    get_ancestor_congr_status hagree hnode hw]

/-! ## Transport along one node's trajectory

The store's block set only grows in time (`StoreLE`), and provenance +
`WellFormedExecution` pin the recorded block at every commonly-known root, so an
`is_ancestor` fact on a walk known at second `n` is invariant through second
`m ≥ n` — the same node's later store answers `is_ancestor` identically. -/


end FastConfirmation.Spec

end
