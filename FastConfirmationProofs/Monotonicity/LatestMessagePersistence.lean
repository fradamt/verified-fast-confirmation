module
public import FastConfirmationProofs.Execution.Trajectory.LatestMessageProvenance
public import FastConfirmationProofs.Execution.StoreInvariants.StoreInvariants

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Strict latest-message persistence for live reconfirmation

The ordinary store extension relation only tracks nondecreasing latest-message
slots. Reconfirmation also needs the message itself to remain unchanged when
the slot cannot advance. The protocol's update handler uses a strict slot
comparison, so this stronger relation holds along executions.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Each recorded latest message either survives unchanged or is replaced by
a message at a strictly later slot. -/
def LatestMessageStrictLE (old new : Store Root) : Prop :=
  ∀ i m, old.latest_messages i = some m →
    ∃ m', new.latest_messages i = some m' ∧
      (m' = m ∨ m.slot < m'.slot)

namespace LatestMessageStrictLE

theorem refl (s : Store Root) : LatestMessageStrictLE s s := by
  intro i m hm
  exact ⟨m, hm, Or.inl rfl⟩

theorem trans {a b c : Store Root}
    (hab : LatestMessageStrictLE a b)
    (hbc : LatestMessageStrictLE b c) :
    LatestMessageStrictLE a c := by
  intro i m hm
  obtain ⟨m', hm', hstep⟩ := hab i m hm
  obtain ⟨m'', hm'', hstep'⟩ := hbc i m' hm'
  refine ⟨m'', hm'', ?_⟩
  rcases hstep with heq | hlt
  · subst m'
    exact hstep'
  · rcases hstep' with heq | hlt'
    · subst m''
      exact Or.inr hlt
    · exact Or.inr (hlt.trans hlt')

theorem of_latest_eq {a b : Store Root}
    (h : b.latest_messages = a.latest_messages) :
    LatestMessageStrictLE a b := by
  intro i m hm
  exact ⟨m, by rw [h]; exact hm, Or.inl rfl⟩

theorem equal_slot {a b : Store Root}
    (h : LatestMessageStrictLE a b)
    {i : ValidatorIndex} {old new : LatestMessage Root}
    (hold : a.latest_messages i = some old)
    (hnew : b.latest_messages i = some new)
    (hslot : new.slot ≤ old.slot) : old = new := by
  obtain ⟨msg, hmsg, heq | hlt⟩ := h i old hold
  · rw [hnew] at hmsg
    cases Option.some.inj hmsg
    exact heq.symm
  · rw [hnew] at hmsg
    cases Option.some.inj hmsg
    exact False.elim (Nat.not_lt_of_ge hslot hlt)

end LatestMessageStrictLE

variable [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

private theorem latest_strict_foldl
    {α : Type*} {f : Store Root → α → Store Root}
    (hf : ∀ s a, LatestMessageStrictLE s (f s a))
    (l : List α) (s : Store Root) :
    LatestMessageStrictLE s (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact LatestMessageStrictLE.refl s
  | cons a l ih => exact (hf s a).trans (ih (f s a))

theorem update_latest_messages_strictLE (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root) :
    LatestMessageStrictLE store
      (update_latest_messages store indices a) := by
  simp only [update_latest_messages]
  refine latest_strict_foldl (fun s i => ?_) _ store
  dsimp only
  rcases hmi : s.latest_messages i with _ | lm
  · split_ifs with hupd
    · intro j m hm
      rcases eq_or_ne j i with rfl | hji
      · simp [hmi] at hm
      · exact ⟨m, by simpa [Function.update_apply, hji] using hm, Or.inl rfl⟩
    · exact LatestMessageStrictLE.refl _
  · split_ifs with hupd
    · intro j m hm
      rcases eq_or_ne j i with rfl | hji
      · rw [hmi] at hm
        obtain rfl : lm = m := Option.some.inj hm
        have hlt : lm.slot < a.data.slot := by simpa using hupd
        exact ⟨⟨a.data.slot, a.data.beacon_block_root,
            decide (a.data.index = 1)⟩, by simp, Or.inr hlt⟩
      · exact ⟨m, by simpa [Function.update_apply, hji] using hm, Or.inl rfl⟩
    · exact LatestMessageStrictLE.refl _

theorem on_attestation_strictLE {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool}
    (h : on_attestation cfg ext store a ifb = some store') :
    LatestMessageStrictLE store store' := by
  simp only [on_attestation] at h
  split_ifs at h
  cases h
  exact (LatestMessageStrictLE.of_latest_eq
      (store_target_checkpoint_state_latest cfg ext store a.data.target)).trans
    (update_latest_messages_strictLE _ _ _)

theorem apply_event_strictLE {store store' : Store Root}
    {event : Event Root}
    (h : apply_event cfg ext store event = some store') :
    LatestMessageStrictLE store store' := by
  cases event with
  | block b =>
      exact LatestMessageStrictLE.of_latest_eq (on_block_latest cfg ext h)
  | attestation a ifb =>
      exact on_attestation_strictLE cfg ext h
  | attester_slashing s =>
      exact LatestMessageStrictLE.of_latest_eq (on_attester_slashing_latest ext h)
  | execution_payload_envelope envelope observation =>
      exact LatestMessageStrictLE.of_latest_eq
        (on_execution_payload_envelope_frame ext h).latest_messages
  | payload_attestation_message message ifb =>
      exact LatestMessageStrictLE.of_latest_eq
        (on_payload_attestation_message_frame cfg ext h).latest_messages

theorem apply_event_getD_strictLE (store : Store Root)
    (event : Event Root) :
    LatestMessageStrictLE store ((apply_event cfg ext store event).getD store) := by
  cases h : apply_event cfg ext store event with
  | none => exact LatestMessageStrictLE.refl store
  | some next => exact apply_event_strictLE cfg ext h

namespace Execution

variable (E : Execution Root)

theorem store_latestMessageStrictLE_succ (v : ValidatorIndex) (n : ℕ) :
    LatestMessageStrictLE (E.store cfg ext v n)
      (E.store cfg ext v (n + 1)) := by
  change LatestMessageStrictLE (E.store cfg ext v n)
    ((E.schedule v (n + 1)).foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
  exact (LatestMessageStrictLE.of_latest_eq
      (on_tick_latest cfg (E.store cfg ext v n) (E.time_at (n + 1)))).trans
    (latest_strict_foldl (fun s event =>
      apply_event_getD_strictLE cfg ext s event) _ _)

theorem store_latestMessageStrictLE (v : ValidatorIndex)
    {n m : ℕ} (hnm : n ≤ m) :
    LatestMessageStrictLE (E.store cfg ext v n)
      (E.store cfg ext v m) := by
  induction m with
  | zero =>
      cases Nat.le_zero.mp hnm
      exact LatestMessageStrictLE.refl _
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans
          (E.store_latestMessageStrictLE_succ cfg ext v m)
      · cases Nat.le_antisymm hnm hge
        exact LatestMessageStrictLE.refl _

/-- For any validator, not only an honest one, an observer's latest message
in one epoch is stable between two stores. A changed message would need a
strictly later slot, but the validator has at most one committee assignment
in that epoch. -/
theorem latest_message_eq_of_same_epoch_at_observer
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hnm : n ≤ m)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    {i : ValidatorIndex} {src dst : LatestMessage Root}
    (hsrc : (E.store cfg ext w n).latest_messages i = some src)
    (hdst : (E.store cfg ext w m).latest_messages i = some dst)
    (hepoch : get_latest_message_epoch cfg src =
      get_latest_message_epoch cfg dst) :
    src = dst := by
  have hprovSrc := E.latestMessageProvenance cfg ext hwf hec hgen w n hw hHn
  have hprovDst := E.latestMessageProvenance cfg ext hwf hec hgen w m hw hHm
  obtain ⟨a, _, _, _, haEpoch, _, haCommittee, _, _, haSlot⟩ :=
    hprovSrc i src hsrc
  obtain ⟨a', _, _, _, haEpoch', _, haCommittee', _, _, haSlot'⟩ :=
    hprovDst i dst hdst
  have hslotEpoch : compute_epoch_at_slot cfg a.data.slot =
      compute_epoch_at_slot cfg a'.data.slot := by
    rw [haEpoch, hepoch, ← haEpoch']
  have hslot := hec.committee_assignment_unique i a.data.slot a'.data.slot
    haCommittee haCommittee' hslotEpoch
  have hslotLe : dst.slot ≤ src.slot := by
    rw [haSlot, haSlot', hslot]
  exact (E.store_latestMessageStrictLE cfg ext w hnm).equal_slot
    hsrc hdst hslotLe

/-- A latest message from the just-completed epoch is identical at the next
epoch's first slot. The handler cannot apply an attestation from that new
slot yet, and a validator has only one committee slot in the old epoch. -/
theorem latest_message_stable_at_next_epoch_start
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} (hw : w ∈ E.honest)
    {n m : ℕ} (hnm : n ≤ m)
    (hHn : E.WithinHorizon cfg n) (hHm : E.WithinHorizon cfg m)
    {e : Epoch} (hboundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg (e + 1))
    {i : ValidatorIndex} {src : LatestMessage Root}
    (hsrc : (E.store cfg ext w n).latest_messages i = some src)
    (hepoch : get_latest_message_epoch cfg src = e) :
    (E.store cfg ext w m).latest_messages i = some src := by
  obtain ⟨dst, hdst, hslotLe⟩ :=
    (E.store_storeLE cfg ext w hnm).2.2.2 i src hsrc
  have hprov := E.latestMessageProvenance cfg ext hwf hec hgen w m hw hHm
  obtain ⟨_, _, _, _, _, hbefore, _, _, _, hdstSlot⟩ := hprov i dst hdst
  have hdstEpochLt : get_latest_message_epoch cfg dst < e + 1 := by
    apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
    change dst.slot < (e + 1) * cfg.slots_per_epoch
    rw [← compute_start_slot_at_epoch, ← hboundary, hdstSlot]
    exact Nat.lt_of_succ_le hbefore
  have hsrcEpochLe : get_latest_message_epoch cfg src ≤
      get_latest_message_epoch cfg dst := Nat.div_le_div_right hslotLe
  have heqEpoch : get_latest_message_epoch cfg src =
      get_latest_message_epoch cfg dst := by
    rw [hepoch] at hsrcEpochLe ⊢
    exact Nat.le_antisymm hsrcEpochLe (Nat.lt_succ_iff.mp hdstEpochLt)
  have heq := E.latest_message_eq_of_same_epoch_at_observer cfg ext
    hwf hec hgen hw hnm hHn hHm hsrc hdst heqEpoch
  rw [heq]
  exact hdst

end Execution

end FastConfirmation.Spec

end
