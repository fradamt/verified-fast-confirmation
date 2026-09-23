module
public import FastConfirmation.Spec.Proof.PayloadPersistence
public import FastConfirmation.Spec.Proof.Preservation
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Spec / Proof / FullParentAvailability

`on_block` rejects a fresh block whose parent status is FULL when the parent
payload is not verified in the local store. Block identity fields never change
for a known root, and verified payloads persist. Thus every non-anchor block in
an execution store has its FULL parent payload verified in that same store.

This is the availability half of the pending-parent status contest: a child
with a FULL parent status is known only when the FULL node of its parent is a
fork-choice child of the pending parent at the same store.

The proof is an induction over the executable handlers. No honest behavior or
delivery assumption is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- Every non-anchor known block has a known parent. If its parent status is
FULL, the parent payload is verified in the same store. -/
def FullParentVerified (G store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots, r ∈ G.block_roots ∨
    ((store.blocks r).parent_root ∈ store.block_roots ∧
      (get_parent_payload_status store (store.blocks r) = .full →
        is_payload_verified store (store.blocks r).parent_root = true))

namespace FullParentVerified

/-- The invariant reads only the block identity fields and verified payloads. -/
theorem of_sameBlocks {G s t : Store Root} (h : FullParentVerified G s)
    (hsb : SameBlocks s t) (hpl : PayloadLE s t) : FullParentVerified G t := by
  obtain ⟨hbr, hb, _⟩ := hsb
  have hstatus : ∀ x : BeaconBlock Root,
      get_parent_payload_status t x = get_parent_payload_status s x := by
    intro x
    simp only [get_parent_payload_status, hb]
  unfold FullParentVerified at h ⊢
  intro r hr
  rw [← hbr] at hr
  rcases h r hr with hg | ⟨hp, hfull⟩
  · exact Or.inl hg
  · right
    refine ⟨by rw [← hbr, ← hb]; exact hp, fun hst => ?_⟩
    rw [hstatus, ← hb] at hst
    rw [← hb]
    exact hpl _ (hfull hst)

end FullParentVerified

variable (cfg : Config) (ext : Externals Root)

/-- Shape of a fresh successful block insertion: the parent was known, the
FULL parent was verified, and the tail handlers keep the inserted block
identity fields. -/
private theorem on_block_fresh_shape {store store' : Store Root}
    {sb : SignedBeaconBlock Root}
    (hknown : sb.root ∉ store.block_roots)
    (hh : on_block cfg ext store sb = some store') :
    sb.message.parent_root ∈ store.block_roots ∧
    ∃ post : BeaconState Root,
      SameBlocks
        { store with
          block_roots := store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root post }
        store' := by
  have hparent : sb.message.parent_root ∈ store.block_roots := by
    by_contra hnot
    have hnone : on_block cfg ext store sb = none := by
      simp [on_block, hknown, hnot]
    rw [hnone] at hh
    cases hh
  refine ⟨hparent, ?_⟩
  simp only [on_block, if_neg hknown] at hh
  split_ifs at hh <;> try cases hh
  cases hst : ext.state_transition
      (store.block_states sb.message.parent_root) sb with
  | none => rw [hst] at hh; cases hh
  | some post =>
    rw [hst] at hh
    let added : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => none
      | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
          (FastConfirmation.Spec.update_checkpoints
            (FastConfirmation.Spec.update_proposer_boost_root cfg
              (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
        some store' at hh
    cases hn : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      cases hh
      have hf := notify_ptc_messages_frame cfg ext hn
      let timed := record_block_timeliness cfg notified sb.root
      let boosted := update_proposer_boost_root cfg timed
        (get_head cfg store).root sb.root
      let realized := update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      have htail : SameBlocks added
          (compute_pulled_up_tip cfg ext realized sb.root) :=
        hf.sameBlocks.trans
          ((record_block_timeliness_sameBlocks cfg notified sb.root).trans
            ((update_proposer_boost_root_sameBlocks cfg timed
              (get_head cfg store).root sb.root).trans
              ((update_checkpoints_sameBlocks boosted
                post.current_justified_checkpoint post.finalized_checkpoint).trans
                (compute_pulled_up_tip_sameBlocks cfg ext realized sb.root))))
      exact ⟨post, htail⟩

/-- `on_block` preserves the FULL-parent invariant. -/
theorem on_block_fullParentVerified {G store store' : Store Root}
    {sb : SignedBeaconBlock Root} (h : FullParentVerified G store)
    (hh : on_block cfg ext store sb = some store') :
    FullParentVerified G store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · have heq : store' = store := by
      simp [on_block, hknown] at hh
      exact hh.symm
    rw [heq]
    exact h
  · have hpayloads := on_block_payloads cfg ext hh
    obtain ⟨hparent, post, hsb⟩ := on_block_fresh_shape cfg ext hknown hh
    obtain ⟨hbr, hb, _⟩ := hsb
    have hpl : PayloadLE store store' := PayloadLE.of_payloads_eq hpayloads
    have hblocks : store'.blocks =
        Function.update store.blocks sb.root sb.message := hb.symm
    have hroots : store'.block_roots = store.block_roots ++ [sb.root] := hbr.symm
    have hold : ∀ x ∈ store.block_roots, store'.blocks x = store.blocks x := by
      intro x hx
      rw [hblocks]
      have hne : x ≠ sb.root := fun hxe => hknown (by rw [← hxe]; exact hx)
      exact Function.update_of_ne hne _ _
    unfold FullParentVerified at h ⊢
    have hstatus_old : ∀ r ∈ store.block_roots,
        (store.blocks r).parent_root ∈ store.block_roots →
        get_parent_payload_status store' (store'.blocks r) =
          get_parent_payload_status store (store.blocks r) := by
      intro r hr hp
      simp only [get_parent_payload_status, hold r hr, hold _ hp]
    intro r hr
    rw [hroots, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · rcases h r hr with hg | ⟨hp, hfull⟩
      · exact Or.inl hg
      · right
        refine ⟨by rw [hroots, hold r hr]; exact List.mem_append_left _ hp,
          fun hst => ?_⟩
        rw [hstatus_old r hr hp] at hst
        rw [hold r hr]
        exact hpl _ (hfull hst)
    · right
      have hnew : store'.blocks sb.root = sb.message := by
        rw [hblocks]
        exact Function.update_self sb.root sb.message store.blocks
      rw [hnew]
      refine ⟨by rw [hroots]; exact List.mem_append_left _ hparent, fun hst => ?_⟩
      have hst' : get_parent_payload_status store sb.message = .full := by
        simpa only [get_parent_payload_status, hold _ hparent] using hst
      have hfull : is_parent_node_full store sb.message = true := by
        simp [is_parent_node_full, hst']
      exact hpl _ (on_block_fresh_full_parent_verified cfg ext hknown hfull hh)

/-- Every successful event preserves the FULL-parent invariant. -/
theorem apply_event_fullParentVerified {G store store' : Store Root}
    {event : Event Root} (h : FullParentVerified G store)
    (hh : apply_event cfg ext store event = some store') :
    FullParentVerified G store' := by
  cases event with
  | block b => exact on_block_fullParentVerified cfg ext h hh
  | attestation a ifb =>
      exact h.of_sameBlocks (on_attestation_sameBlocks cfg ext hh)
        (PayloadLE.of_payloads_eq (on_attestation_payloads cfg ext hh))
  | attester_slashing sl =>
      exact h.of_sameBlocks (on_attester_slashing_sameBlocks ext hh)
        (PayloadLE.of_payloads_eq (on_attester_slashing_payloads ext hh))
  | execution_payload_envelope envelope observation =>
      exact h.of_sameBlocks (on_execution_payload_envelope_sameBlocks ext hh)
        (on_execution_payload_envelope_payloadLE ext hh)
  | payload_attestation_message message ifb =>
      exact h.of_sameBlocks (on_payload_attestation_message_sameBlocks cfg ext hh)
        (PayloadLE.of_payloads_eq (on_payload_attestation_message_payloads cfg ext hh))

private theorem fullParentVerified_foldl {G : Store Root} :
    ∀ (l : List (Event Root)) (s : Store Root), FullParentVerified G s →
      FullParentVerified G
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons e l ih =>
    intro s h
    rw [List.foldl_cons]
    apply ih
    cases he : apply_event cfg ext s e with
    | none => simpa [he] using h
    | some s' =>
      simp only [Option.getD_some]
      exact apply_event_fullParentVerified cfg ext h he

/-- Every execution store satisfies the FULL-parent invariant relative to the
genesis store. -/
theorem Execution.fullParentVerified (E : Execution Root) (v : ValidatorIndex)
    (n : ℕ) : FullParentVerified E.genesis_store (E.store cfg ext v n) := by
  induction n with
  | zero =>
    unfold FullParentVerified
    intro r hr
    exact Or.inl hr
  | succ n ih =>
    change FullParentVerified E.genesis_store ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    apply fullParentVerified_foldl cfg ext
    exact ih.of_sameBlocks (on_tick_sameBlocks cfg _ _)
      (PayloadLE.of_payloads_eq (on_tick_payloads cfg _ _))

/-- A non-anchor known block with FULL parent status has its parent payload
verified in the same execution store. -/
theorem Execution.full_parent_payload_verified (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) {c : Root}
    (hc : c ∈ (E.store cfg ext v n).block_roots)
    (hcG : c ∉ E.genesis_store.block_roots)
    (hfull : get_parent_payload_status (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks c) = .full) :
    is_payload_verified (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks c).parent_root = true := by
  have hinv := E.fullParentVerified cfg ext v n
  unfold FullParentVerified at hinv
  rcases hinv c hc with hg | ⟨_, hv⟩
  · exact absurd hg hcG
  · exact hv hfull

end FastConfirmation.Spec

end
