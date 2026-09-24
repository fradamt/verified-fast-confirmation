module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGFacts

/-! An observer-only accepted block can expose an uncertified checkpoint at
the opaque PJF boundary. This is an executable abstraction counterexample;
it does not assert the full restricted network premise record for the run. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace ObserverFFGCounterexample

set_option maxRecDepth 10000

def cfg : Config := { mainnet_config with
  slots_per_epoch := 2, slots_per_epoch_pos := by decide
  slot_duration_ms := 1000, slot_duration_ms_pos := by decide
  ptc_size := 0 }
def anchor : Checkpoint Nat := ⟨0, 1⟩
def bad : Checkpoint Nat := ⟨1, 99⟩
def ast : BeaconState Nat := { (default : BeaconState Nat) with
  slot := 0, current_justified_checkpoint := anchor, finalized_checkpoint := anchor }
def ab : SignedBeaconBlock Nat := ⟨{ slot := 0, parent_root := 0 }, 1⟩
def child : SignedBeaconBlock Nat := ⟨{ slot := 2, parent_root := 1 }, 2⟩
def ext : Externals Nat where
  get_beacon_committee := fun _ _ _ => []
  get_committee_count_per_slot := fun _ _ => 0
  process_slots := fun st s => { st with slot := s }
  state_transition := fun st b =>
    if st.slot < b.message.slot then some { st with slot := b.message.slot } else none
  process_justification_and_finalization := fun st =>
    if st.slot = 2 then { st with current_justified_checkpoint := bad } else st
  is_valid_indexed_attestation := fun _ _ => false
  AnchorCommitsToState := fun _ _ => True

def run : Execution Nat where
  verification_horizon := 3
  genesis_store := get_forkchoice_store cfg ast ab
  schedule := fun w n => if w = 0 ∧ n = 2 then [.block child] else []
  honest := ∅
  committee := fun _ => ∅
  vote := fun _ _ => none

def point : run.ScheduledEventPrefix := ⟨0, 1, 0, by decide⟩
def post : Store Nat := (on_block cfg ext (point.store cfg ext) child).getD run.genesis_store

/-- Exact local handler success, with an empty attestation body. -/
theorem accepts : on_block cfg ext (point.store cfg ext) child = some post := by rfl

def transition : run.AcceptedBlockTransition cfg ext where
  atPrefix := point
  signedBlock := child
  event_at := by rfl
  postStore := post
  accepted := accepts

/-- The imported GU read can be false even though the handler succeeds. -/
theorem readback : post.unrealized_justifications 2 = bad ∧
    post.unrealized_justified_checkpoint = bad ∧ bad.root ∉ post.block_roots ∧
    child.message.attestations = [] := by decide

/-- Every outside schedule is empty; the observer's child is absent after erasure. -/
theorem restricted_absent : ¬ (run.withoutObserver 0).AcceptedRoot cfg ext 2 := by
  have hstore : ∀ w n, ((run.withoutObserver 0).store cfg ext w n).block_roots = [1] := by
    intro w n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hnil : (run.withoutObserver 0).schedule w (n + 1) = [] := by
        simp only [Execution.withoutObserver, run]
        split_ifs <;> simp_all
      simp only [Execution.store, hnil, List.foldl_nil]
      rw [(on_tick_sameBlocks cfg _ _).1.symm]
      exact ih
  rintro ⟨st, hs, hr⟩
  cases hs with
  | genesis => exact (by decide : (2 : Nat) ∉ [1]) hr
  | scheduledPrefix p =>
    have hnil : (run.withoutObserver 0).schedule p.node (p.previousSecond + 1) = [] := by
      simp only [Execution.withoutObserver, run]
      split_ifs <;> simp_all
    simp only [Execution.ScheduledEventPrefix.store, hnil, List.take_nil, List.foldl_nil] at hr
    rw [← (on_tick_sameBlocks cfg _ _).1, hstore] at hr
    exact (by decide : (2 : Nat) ∉ [1]) hr

/-- A body-checked inclusion relation is empty in this concrete block universe. -/
theorem bodies_empty {r b} (hb : run.BlockAt r b) : b.attestations = [] := by
  rcases hb with ⟨hr, rfl⟩ | ⟨w, n, sb, hm, _, rfl⟩
  · have hr' : r = 1 := by simpa [run, get_forkchoice_store, ab] using hr
    subst r
    rfl
  · simp only [run] at hm
    split_ifs at hm with hh
    · have hs : sb = child := by simpa using hm
      subst sb
      rfl
    · simp at hm

/-- No non-anchor checkpoint has a body certificate. Authenticity cannot
create the missing body. This names the failing GU-to-AU proof step. -/
theorem no_bad_certificate (included : Nat → Attestation Nat → Prop)
    (body_checked : ∀ {r a}, included r a →
      ∃ b, run.BlockAt r b ∧ a ∈ b.attestations) (carrier : Nat) :
    ¬ IncludedCertifiedJustified cfg run included anchor carrier bad := by
  have hempty : ∀ r a, ¬ included r a := by
    intro r a ha
    obtain ⟨b, hb, hm⟩ := body_checked ha
    rw [bodies_empty hb] at hm
    exact List.not_mem_nil hm
  intro hc
  cases hc with
  | link prev L =>
    have hsigners : L.signers = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨a, ⟨r, _, ha⟩, _⟩ := L.signer_attestation i hi
      exact hempty r a ha
    have hweight : run.weight L.signers = 0 := by simp [hsigners, Execution.weight]
    have hq := L.supermajority
    have hp := run.total_active_pos cfg
    rw [hweight] at hq
    exact (Nat.not_le_of_gt (Nat.mul_pos (by decide : 0 < 2) hp)) hq

/-- All eight pre-FFG observer authenticity clauses hold. There is no signed
attestation in the run. This does not supply the missing content refinement. -/
theorem authenticity : run.ObserverInputAuthenticity cfg ext 0 where
  validity := {
    honest_attestation_valid := by intro st a hs v hv; exact False.elim (Finset.notMem_empty _ hv)
    valid_attestation_honest := by intro st a hs hv; cases hv
    valid_attestation_committee := by intro st a hs hv; cases hv }
  committees_agree := by
    intro n hn s hs
    simp [get_slot_committee, ext, run]
  no_forgery := by
    intro n a fb ha v hv
    exact False.elim (Finset.notMem_empty _ hv)
  block_labels := by
    intro n b hb w k b' hb' hr
    simp only [run] at hb hb'
    split_ifs at hb hb' <;> simp_all
  genesis_blocks := by
    intro n b hb hr
    simp only [run] at hb
    split_ifs at hb <;> simp_all [run, get_forkchoice_store, ab, child]
  anchor_parent := by
    intro r hr n b hb
    simp only [run] at hb
    split_ifs at hb <;> simp_all [run, get_forkchoice_store, ab, child]
  process_slots_validity := by intro st s a hs hlt; rfl
  votes_head := by intro hh; exact False.elim (Finset.notMem_empty _ hh)

/-- The local FFG extension correctly rejects this accepted input run. -/
theorem no_local_extension : ¬ Nonempty (run.ObserverLocalFFG cfg ext 0) := by
  rintro ⟨B⟩
  have ht : transition.atPrefix.node = 0 := rfl
  have hs := B.transition_local transition ht
  have hgu := B.selectors.transition_gu transition ht
  have hbad : B.state.GU child.root = bad := hgu.symm.trans (by rfl)
  have hau := (B.selectors_AU hs transition.root_known).2.1
  change B.state.AU child.root (B.state.GU child.root) at hau
  rw [hbad] at hau
  obtain ⟨carrier, _, hc⟩ := (B.au_certificate hau).1
  exact no_bad_certificate B.state.included
    (fun hi => ⟨_, (B.included_body hi).1, (B.included_body hi).2⟩) carrier hc

end ObserverFFGCounterexample
end FastConfirmation.Spec
end
