module
public import FastConfirmation.Spec.Proof.BlockAgreement
public import FastConfirmation.Spec.Proof.Preservation

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Spec / Proof / WFTrajectory

This module proves the two provenance premises of
`Preservation.on_block_parentSlotLt` (`hfresh` / `hno_child`) along execution
trajectories, deriving the fourth `WellFormedStore` field —
`ParentSlotLt` — at the trajectory level, and bundling it with the
already-delivered `WellFormedStoreCore` and `time_ge_genesis`.

## The two provenance premises

`on_block`'s block insertion preserves the parent-slot order only under two
facts that are **not** handler-local:

* `hfresh` — the wire root is not yet known. This is **not** invariant (a block
  can be re-delivered), so the trajectory step splits on it: the *fresh* branch
  uses `on_block_parentSlotLt`; the *already-present* branch observes that the
  `blocks` write is a **no-op** — cross-store block agreement
  (`WellFormedExecution` + `BlockProvenance`) pins the recorded block, so
  `Function.update store.blocks r r.message = store.blocks` and the order rides
  across unchanged.
* `hno_child` — no known block names the fresh root as its parent. Derived from
  a companion trajectory invariant `ParentInRootsOr P`: every known block's
  parent pointer is itself a known root **or** the genesis anchor's single
  dangling parent `P`. A fresh root differs from every known root, so the only
  way a known block could name it is via the anchor's dangling `P` — excluded
  by the guarded hypothesis below.

## The anchor-parent guard

`hno_child` for the genesis anchor's edge needs the anchor's dangling parent
`P` to differ from the fresh wire root. `WellFormedExecution` does **not**
carry this (`genesis_blocks_agree` / `blocks_root_injective` tie *known* roots,
not the anchor's dangling parent), and it is not derivable from the other
assumptions: an abstract wire block could be scheduled with root `= P` and
pass `on_block`'s guards (the model has no root-acyclicity assumption). So the
trajectory theorems take an explicit **guarded hypothesis** `hanchor`:
*no scheduled block's root equals the genesis anchor's parent pointer* — a
`WellFormedExecution`-shaped fact.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## The parent-known companion invariant -/

/-- Every known block's parent pointer is itself a known root, or the fixed
root `P` (instantiated at the genesis anchor's single dangling parent). This is
the trajectory invariant that discharges `on_block_parentSlotLt`'s `hno_child`:
a fresh root differs from every known root, so a known block can only name it
via `P`. -/
def ParentInRootsOr (P : Root) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots,
    (store.blocks r).parent_root ∈ store.block_roots ∨ (store.blocks r).parent_root = P

/-- `SameBlocks` carries the parent-known invariant across: it reads only
`block_roots` and `blocks`. -/
theorem SameBlocks.parentInRootsOr {s t : Store Root} (h : SameBlocks s t)
    (P : Root) (hs : ParentInRootsOr P s) : ParentInRootsOr P t := by
  obtain ⟨hbr, hb, _⟩ := h
  simp only [ParentInRootsOr, ← hbr, ← hb]
  exact hs

/-! ## Same-store block identification

Under `WellFormedExecution` + `BlockProvenance`, a scheduled block whose root is
already known carries exactly the store's recorded block — genesis roots via
`genesis_blocks_agree`, scheduled roots via `blocks_root_injective`. This is the
no-op witness for the already-present branch of the `on_block` step. -/


variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
/-- Block insertion preserves the parent-known invariant. The new block's parent
was checked known by `on_block`'s first guard (`hpar_in`), so it stays a known
root; every older block keeps its parent classification (`store.block_roots ⊆ br`
via `hsub`, so an old known parent is still known). The key list `br` is left
abstract with two membership bounds so both append-if branches are covered. -/
theorem parentInRootsOr_insert (P : Root) (store : Store Root) (block_root : Root)
    (block : BeaconBlock Root) (state : BeaconState Root) (br : List Root)
    (hsub : ∀ r ∈ store.block_roots, r ∈ br)
    (hbr : ∀ r ∈ br, r = block_root ∨ r ∈ store.block_roots)
    (hQ : ParentInRootsOr P store)
    (hpar_in : block.parent_root ∈ store.block_roots) :
    ParentInRootsOr P { store with
      block_roots := br
      blocks := Function.update store.blocks block_root block
      block_states := Function.update store.block_states block_root state } := by
  intro r hr
  dsimp only at hr ⊢
  by_cases hrb : r = block_root
  · subst hrb
    rw [Function.update_self]
    exact Or.inl (hsub _ hpar_in)
  · rw [Function.update_of_ne hrb]
    have hrin : r ∈ store.block_roots := (hbr r hr).resolve_left hrb
    rcases hQ r hrin with hin | hP
    · exact Or.inl (hsub _ hin)
    · exact Or.inr hP



/-- `on_block` preserves `ParentSlotLt` under the trajectory-supplied facts:
`WellFormedExecution` + `BlockProvenance` (block identification / no-op),
`ParentInRootsOr P` + `hP : sb.root ≠ P` (the fresh `hno_child`), and the
sanctioned `state_transition_pre_slot_lt`. -/
theorem on_block_parentSlotLt_traj (P : Root) {E : Execution Root}
    (hwf : WellFormedExecution E)
    (hst_pre_lt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st.slot < b.message.slot)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hsched : IsScheduledBlock E sb) (hP : sb.root ≠ P)
    (hprov : BlockProvenance E store) (hcore : WellFormedStoreCore store)
    (hpar : ParentSlotLt store) (hQ : ParentInRootsOr P store)
    (hh : on_block cfg ext store sb = some store') :
    ParentSlotLt store' := by
  by_cases hfresh : sb.root ∈ store.block_roots
  · -- already present: the `blocks` write is a no-op
    simp [on_block, hfresh] at hh
    cases hh
    exact hpar
  · -- fresh: derive `hno_child` from `ParentInRootsOr P` and `hP`
    have hno_child : ∀ r ∈ store.block_roots, (store.blocks r).parent_root ≠ sb.root := by
      intro r hr
      rcases hQ r hr with hin | heq
      · exact fun hc => hfresh (hc ▸ hin)
      · rw [heq]; exact fun hc => hP hc.symm
    exact on_block_parentSlotLt cfg ext hst_pre_lt hcore hpar hfresh hno_child hh

/-- `on_block` preserves the parent-known invariant: the block insertion's only
new edge is guard-checked (`parentInRootsOr_insert`), and the post-insertion tail
is block-identity-preserving. -/
theorem on_block_parentInRootsOr (P : Root) {store store' : Store Root}
    {sb : SignedBeaconBlock Root} (hQ : ParentInRootsOr P store)
    (hh : on_block cfg ext store sb = some store') :
    ParentInRootsOr P store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at hh
    cases hh
    exact hQ
  · simp only [on_block, if_neg hknown] at hh
    split_ifs at hh with hp hpayload hslot hfin hfc
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some state =>
      rw [hst] at hh
      let added : Store Root :=
        { store with
          block_roots := store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root state
          payload_timeliness_vote := Function.update store.payload_timeliness_vote
            sb.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update store.payload_data_availability_vote
            sb.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added state sb.message.payload_attestations with
        | none => none
        | some notified => some (compute_pulled_up_tip cfg ext
            (update_checkpoints
              (update_proposer_boost_root cfg
                (record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              state.current_justified_checkpoint state.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added state sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        refine (compute_pulled_up_tip_sameBlocks cfg ext _ _).parentInRootsOr P ?_
        refine (update_checkpoints_sameBlocks _ _ _).parentInRootsOr P ?_
        refine (update_proposer_boost_root_sameBlocks cfg _ _ _).parentInRootsOr P ?_
        refine (record_block_timeliness_sameBlocks cfg _ _).parentInRootsOr P ?_
        refine (notify_ptc_messages_sameBlocks cfg ext hn).parentInRootsOr P ?_
        refine parentInRootsOr_insert P store sb.root sb.message state
          (store.block_roots ++ [sb.root]) ?_ ?_ hQ hp
        · intro r hr
          exact List.mem_append_left _ hr
        · intro r hr
          rw [List.mem_append, List.mem_singleton] at hr
          exact hr.symm

/-! ## The combined trajectory invariant

`ParentSlotLt` cannot be carried alone through the event fold: its `on_block`
step needs the handler-local core (`WellFormedStoreCore`), the parent-known
companion (`ParentInRootsOr P`) and block provenance (`BlockProvenance`) of the
*intermediate* fold state. So all four are bundled and preserved together. The
core and provenance halves ride on the already-delivered lemmas; the two new
halves are the `on_block` steps above. -/

/-- The four store facts carried together along a trajectory: the handler-local
core, the parent-slot order, the parent-known companion, and block provenance. -/
def WFPlus (P : Root) (E : Execution Root) (store : Store Root) : Prop :=
  WellFormedStoreCore store ∧ ParentSlotLt store ∧
    ParentInRootsOr P store ∧ BlockProvenance E store

omit [LinearOrder Root] in
/-- `on_tick` preserves the combined invariant: it is block-identity-preserving
(so all four halves ride across via `SameBlocks` / the delivered lemmas). -/
theorem on_tick_WFPlus (P : Root) {E : Execution Root} (store : Store Root) (time : ℕ)
    (h : WFPlus P E store) : WFPlus P E (on_tick cfg store time) := by
  obtain ⟨hc, hp, hq, hpr⟩ := h
  exact ⟨on_tick_wellFormedStoreCore cfg store time hc,
    (on_tick_sameBlocks cfg store time).parentSlotLt hp,
    (on_tick_sameBlocks cfg store time).parentInRootsOr P hq,
    on_tick_blockProvenance cfg store time hpr⟩

/-- One dispatched event preserves the combined invariant. The block case chains
the four `on_block` lemmas (needing `WellFormedExecution`, the two sanctioned
`state_transition` facts, and the guarded `hanchor` for the fresh `hno_child`);
the attestation / slashing cases ride on `SameBlocks`. -/
theorem apply_event_WFPlus (P : Root) {E : Execution Root}
    (hwf : WellFormedExecution E)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hst_pre_lt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st.slot < b.message.slot)
    (hanchor : ∀ w n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n → b.root ≠ P)
    {store store' : Store Root} {event : Event Root}
    (hsched : ∀ b, event = Event.block b → IsScheduledBlock E b)
    (h : WFPlus P E store) (he : apply_event cfg ext store event = some store') :
    WFPlus P E store' := by
  obtain ⟨hc, hp, hq, hpr⟩ := h
  cases event with
  | block b =>
    simp only [apply_event] at he
    obtain ⟨w, n, hmem⟩ := hsched b rfl
    exact ⟨on_block_wellFormedStoreCore cfg ext hst_slot hc he,
      on_block_parentSlotLt_traj cfg ext P hwf hst_pre_lt ⟨w, n, hmem⟩
        (hanchor w n b hmem) hpr hc hp hq he,
      on_block_parentInRootsOr cfg ext P hq he,
      on_block_blockProvenance cfg ext ⟨w, n, hmem⟩ hpr he⟩
  | attestation a ifb =>
    simp only [apply_event] at he
    exact ⟨(on_attestation_sameBlocks cfg ext he).wellFormedStoreCore hc,
      (on_attestation_sameBlocks cfg ext he).parentSlotLt hp,
      (on_attestation_sameBlocks cfg ext he).parentInRootsOr P hq,
      on_attestation_blockProvenance cfg ext hpr he⟩
  | attester_slashing sl =>
    simp only [apply_event] at he
    exact ⟨(on_attester_slashing_sameBlocks ext he).wellFormedStoreCore hc,
      (on_attester_slashing_sameBlocks ext he).parentSlotLt hp,
      (on_attester_slashing_sameBlocks ext he).parentInRootsOr P hq,
      on_attester_slashing_blockProvenance ext hpr he⟩
  | execution_payload_envelope envelope observation =>
    have hf := on_execution_payload_envelope_frame ext he
    exact ⟨hf.sameBlocks.wellFormedStoreCore hc,
      hf.sameBlocks.parentSlotLt hp, hf.sameBlocks.parentInRootsOr P hq,
      hpr.of_payloadFrame hf⟩
  | payload_attestation_message message ifb =>
    have hf := on_payload_attestation_message_frame cfg ext he
    exact ⟨hf.sameBlocks.wellFormedStoreCore hc,
      hf.sameBlocks.parentSlotLt hp, hf.sameBlocks.parentInRootsOr P hq,
      hpr.of_payloadFrame hf⟩

/-- Folding a second's scheduled events preserves the combined invariant: every
block event is scheduled, so each `apply_event` step keeps it. -/
theorem WFPlus_foldl (P : Root) {E : Execution Root}
    (hwf : WellFormedExecution E)
    (hst_slot : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st'.slot = b.message.slot)
    (hst_pre_lt : ∀ (st : BeaconState Root) (b : SignedBeaconBlock Root)
        (st' : BeaconState Root),
      ext.state_transition st b = some st' → st.slot < b.message.slot)
    (hanchor : ∀ w n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n → b.root ≠ P) :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ b, Event.block b ∈ l → IsScheduledBlock E b) → WFPlus P E s →
      WFPlus P E
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
        refine apply_event_WFPlus cfg ext P hwf hst_slot hst_pre_lt hanchor
          (fun b hbeq => hl b ?_) h he
        rw [← hbeq]; exact List.mem_cons_self

/-! ## The trajectory-level results

`ParentSlotLt` at every node and second, from the `get_forkchoice_store` base,
via the combined-invariant induction. The guarded hypothesis `hanchor` — *no
scheduled block's root is a genesis block's parent pointer* — is the explicit
anchor-parent coherence premise. At the genesis store this is exactly "no scheduled
block is the anchor's dangling parent". -/

/-- The parent-slot order holds at every node and second of a trajectory whose
genesis store is a `get_forkchoice_store`, under the guarded `hanchor`. -/
theorem Execution.store_parentSlotLt (E : Execution Root)
    (hwf : WellFormedExecution E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hanchor : ∀ r ∈ E.genesis_store.block_roots, ∀ w n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n → b.root ≠ (E.genesis_store.blocks r).parent_root)
    (v : ValidatorIndex) (n : ℕ) :
    ParentSlotLt (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]; exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
  -- specialize the guarded hypothesis to the anchor's parent
  have hanchorP : ∀ w m (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w m → b.root ≠ ablk.message.parent_root := by
    intro w m b hb
    have hmem : ablk.root ∈ E.genesis_store.block_roots := by
      rw [hgeq]; simp [get_forkchoice_store]
    have hpeq : (E.genesis_store.blocks ablk.root).parent_root = ablk.message.parent_root := by
      rw [hgeq]; simp [get_forkchoice_store]
    rw [← hpeq]; exact hanchor ablk.root hmem w m b hb
  suffices key : ∀ k, WFPlus ablk.message.parent_root E (E.store cfg ext v k) from
    (key n).2.1
  intro k
  induction k with
  | zero =>
    refine ⟨hgws.core, hgws.parentSlotLt, ?_, E.blockProvenance cfg ext v 0⟩
    change ParentInRootsOr ablk.message.parent_root E.genesis_store
    rw [hgeq]
    intro r hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    subst hr
    right
    simp [get_forkchoice_store]
  | succ k ih =>
    change WFPlus ablk.message.parent_root E
      ((E.schedule v (k + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v k) (E.time_at (k + 1))))
    refine WFPlus_foldl cfg ext ablk.message.parent_root hwf
      hec.state_transition_slot hec.state_transition_pre_slot_lt hanchorP
      _ _ (fun b hb => ⟨v, k + 1, hb⟩) ?_
    exact on_tick_WFPlus cfg ablk.message.parent_root _ _ ih


end FastConfirmation.Spec

end
