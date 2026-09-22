module
public import FastConfirmation.Spec.Proof.CurrentTargetFutureSupport
public import FastConfirmation.Spec.Proof.SelectedA32Support
public import FastConfirmation.Spec.Proof.FFGSourceCoherence
public import FastConfirmation.Spec.Proof.FFGGlobalCheckpointTrajectory
public import FastConfirmation.Spec.Proof.Nucleus
public import FastConfirmation.Spec.Proof.ExportWiring

@[expose] public section

/-!
# Current-target support as concrete A3.2 votes

`CurrentTargetFutureSupport` closes the economic half of the executable
current-target prediction: when the gate passes, the union of already observed
honest supporters and honest future seats has two-thirds weight.  This module
connects that accounting set to actual ground votes.

The first section deliberately reproves the schedule provenance invariant with
the signed target epoch retained.  This is stronger than `SchedLMProv` and is
proved by induction over the real handler trajectory; in particular, schedule
provenance is not introduced as an assumption.

The last source field of an FFG link is kept separate.  Target support does not
by itself imply that different honest heads use one common source.  The
`CurrentTargetSourceAgreement` input below is exactly that missing geometric
fact for the concrete votes produced here.  It can be discharged with the
same-epoch common-ancestor theorems in `FFGSourceCoherence`; no quorum or A3.2
conclusion is hidden in it.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Handler-inductive schedule provenance with the signed target epoch -/

/-- Every current latest message was installed by an actual scheduled
attestation which names the validator and whose signed target epoch, LMD root,
and vote-slot epoch are exactly the recorded message fields. -/
def CurrentTargetScheduledLatestMessageProvenance
    (E : Execution Root) (store : Store Root) : Prop :=
  ∀ (i : ValidatorIndex) (m : LatestMessage Root),
    store.latest_messages i = some m →
    ∃ (a : Attestation Root) (u : ValidatorIndex) (t : ℕ) (ifb : Bool),
      Event.attestation a ifb ∈ E.schedule u t ∧
      i ∈ a.attesting_indices ∧
      a.data.target.epoch = m.epoch ∧
      a.data.beacon_block_root = m.root ∧
      compute_epoch_at_slot cfg a.data.slot = m.epoch

omit [LinearOrder Root] [Inhabited Root] in
private theorem currentTargetScheduledLatestMessageProvenance_of_latest_eq
    {E : Execution Root} {store store' : Store Root}
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (hlm : store'.latest_messages = store.latest_messages) :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  intro i m hm
  rw [hlm] at hm
  exact h i m hm

omit [Inhabited Root] in
private theorem currentTargetScheduledLatestMessageProvenance_on_attestation
    {E : Execution Root} {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool}
    (hsched : ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (hh : on_attestation cfg ext store a ifb = some store') :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  simp only [validate_on_attestation, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨_, hEpoch⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with
    hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact h i m hold
  · obtain ⟨u, t, hmem⟩ := hsched
    refine ⟨a, u, t, ifb, hmem, hi, ?_, ?_, ?_⟩
    · rw [hmeq]
    · rw [hmeq]
    · rw [hmeq]
      exact hEpoch.symm

private theorem currentTargetScheduledLatestMessageProvenance_apply_event
    {E : Execution Root} {store store' : Store Root} {e : Event Root}
    (hsched : ∀ a ifb, e = Event.attestation a ifb →
      ∃ u t, Event.attestation a ifb ∈ E.schedule u t)
    (h : CurrentTargetScheduledLatestMessageProvenance cfg E store)
    (he : apply_event cfg ext store e = some store') :
    CurrentTargetScheduledLatestMessageProvenance cfg E store' := by
  cases e with
  | block b =>
      simp only [apply_event] at he
      exact currentTargetScheduledLatestMessageProvenance_of_latest_eq cfg h
        (on_block_latest cfg ext he)
  | attestation a ifb =>
      simp only [apply_event] at he
      exact currentTargetScheduledLatestMessageProvenance_on_attestation
        cfg ext (hsched a ifb rfl) h he
  | attester_slashing asl =>
      simp only [apply_event] at he
      exact currentTargetScheduledLatestMessageProvenance_of_latest_eq cfg h
        (on_attester_slashing_latest ext he)

private theorem currentTargetScheduledLatestMessageProvenance_foldl
    {E : Execution Root} :
    ∀ (l : List (Event Root)) (store : Store Root),
      (∀ a ifb, Event.attestation a ifb ∈ l →
        ∃ u t, Event.attestation a ifb ∈ E.schedule u t) →
      CurrentTargetScheduledLatestMessageProvenance cfg E store →
      CurrentTargetScheduledLatestMessageProvenance cfg E
        (l.foldl
          (fun st event => (apply_event cfg ext st event).getD st) store) := by
  intro l
  induction l with
  | nil => intro store _ h; exact h
  | cons e rest ih =>
      intro store hl h
      rw [List.foldl_cons]
      have hesched : ∀ a ifb, e = Event.attestation a ifb →
          ∃ u t, Event.attestation a ifb ∈ E.schedule u t :=
        fun a ifb he => hl a ifb (by rw [← he]; exact List.mem_cons_self)
      cases he : apply_event cfg ext store e with
      | none =>
          simp only [Option.getD_none]
          exact ih store
            (fun a ifb ha => hl a ifb (List.mem_cons_of_mem e ha)) h
      | some store' =>
          simp only [Option.getD_some]
          exact ih store'
            (fun a ifb ha => hl a ifb (List.mem_cons_of_mem e ha))
            (currentTargetScheduledLatestMessageProvenance_apply_event
              cfg ext hesched h he)

namespace Execution

variable (E : Execution Root)

/-- The strengthened provenance invariant holds at every execution store.
Its proof follows `on_tick` and the actual scheduled-event fold at each
relative second. -/
theorem currentTargetScheduledLatestMessageProvenance
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) :
    CurrentTargetScheduledLatestMessageProvenance cfg E
      (E.store cfg ext v n) := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hg⟩ := hgen
      intro i m hm
      have hm' : E.genesis_store.latest_messages i = some m := hm
      rw [hg] at hm'
      simp [get_forkchoice_store] at hm'
  | succ n ih =>
      change CurrentTargetScheduledLatestMessageProvenance cfg E
        ((E.schedule v (n + 1)).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
      refine currentTargetScheduledLatestMessageProvenance_foldl cfg ext _ _
        (fun a ifb hmem => ⟨v, n + 1, hmem⟩) ?_
      exact currentTargetScheduledLatestMessageProvenance_of_latest_eq cfg ih
        (on_tick_latest cfg (E.store cfg ext v n) (E.time_at (n + 1)))

end Execution

/-! ## Concrete exact-target vote witnesses -/

namespace Execution

variable (E : Execution Root)

/-- A ground honest vote in canonical validator-spec form, with all timing and
target facts needed by `HonestTargetQuorumBefore`. -/
structure ConcreteHonestTargetVoteBefore
    (i : ValidatorIndex) (deadline : Slot)
    (target : Checkpoint Root) : Type where
  slot : Slot
  time : ℕ
  index : CommitteeIndex
  honest : i ∈ E.honest
  time_within_horizon : E.WithinHorizon cfg time
  slot_at_time : E.slot_at cfg time = slot
  slot_within_horizon : E.SlotWithinHorizon cfg slot
  assigned : i ∈ E.committee slot
  vote : E.vote i slot = some (time,
    honest_attestation cfg ext (E.store cfg ext i time) slot index i)
  slot_epoch : compute_epoch_at_slot cfg slot = target.epoch
  before_deadline : slot < deadline
  target_eq :
    (honest_attestation cfg ext
      (E.store cfg ext i time) slot index i).data.target = target

/-- The concrete signer set certified by the current-target gate. -/
def currentTargetA32Signers
    (store : Store Root) (state : BeaconState Root) :
    Finset ValidatorIndex :=
  E.currentTargetObservedHonestSupporters cfg store state ∪
    (E.currentTargetFutureSpan cfg store).filter (fun i => i ∈ E.honest)

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_lt_next_epoch_start {s : Slot} {e : Epoch}
    (hepoch : compute_epoch_at_slot cfg s = e) :
    s < compute_start_slot_at_epoch cfg (e + 1) := by
  rw [← hepoch]
  simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
  simpa only [Nat.mul_comm] using
    (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) s
      cfg.slots_per_epoch_pos)

omit [LinearOrder Root] [Inhabited Root] in
private theorem epoch_eq_of_epoch_bounds {e : Epoch} {s : Slot}
    (hlo : e * cfg.slots_per_epoch ≤ s)
    (hhi : s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) :
    compute_epoch_at_slot cfg s = e := by
  simp only [compute_epoch_at_slot]
  apply Nat.div_eq_of_lt_le hlo
  calc
    s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := hhi
    _ < e * cfg.slots_per_epoch + cfg.slots_per_epoch :=
      Nat.add_lt_add_left
        (Nat.sub_lt cfg.slots_per_epoch_pos (by omega)) _
    _ = (e + 1) * cfg.slots_per_epoch := by
      simp only [Nat.add_mul, one_mul]

omit [LinearOrder Root] [Inhabited Root] in
private theorem mem_epoch_span_of_committee
    {E : Execution Root} {i : ValidatorIndex} {s : Slot} {e : Epoch}
    (hcommittee : i ∈ E.committee s)
    (hepoch : compute_epoch_at_slot cfg s = e) :
    i ∈ E.span_committee (e * cfg.slots_per_epoch)
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := by
  have hdiv : s / cfg.slots_per_epoch = e := by
    simpa only [compute_epoch_at_slot] using hepoch
  have hlo : e * cfg.slots_per_epoch ≤ s := by
    have h := Nat.div_mul_le_self s cfg.slots_per_epoch
    rwa [hdiv] at h
  have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
    rw [hdiv, Nat.mul_add] at h
    simpa only [Nat.mul_comm, Nat.add_comm, Nat.mul_one] using h
  have hhi : s ≤ e * cfg.slots_per_epoch +
      (cfg.slots_per_epoch - 1) := by
    have hpred := Nat.le_pred_of_lt hlt
    rw [Nat.pred_eq_sub_one,
      Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
    exact hpred
  simp only [Execution.span_committee, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hcommittee⟩

/-- An observed honest contributor to the executable current-target score is
an actual honest ground vote for that exact target.  Schedule provenance and
ordinary latest-message provenance are both derived from the execution.

The boundary-aligned trusted-anchor premise is the checkpoint-sync-safe fact
needed to invoke `votes_head` for historical votes.  It does not identify the
anchor with genesis: boundary alignment and epoch monotonicity put the initial
execution slot before every vote in the current target epoch. -/
theorem currentTargetObservedHonestSupporter_vote
    (hSA : SpecAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root} {i : ValidatorIndex}
    (hiObserved : i ∈ E.currentTargetObservedHonestSupporters cfg
      (E.store cfg ext v n) state) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))
      (get_current_target cfg (E.store cfg ext v n))) := by
  obtain ⟨hgen, hwf, hdiv, hhb, hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hgenSlot, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  simp only [Execution.currentTargetObservedHonestSupporters,
    List.mem_toFinset, List.mem_filter] at hiObserved
  have hi : i ∈ E.honest := (decide_eq_true_eq).mp hiObserved.2
  obtain ⟨_active, _unslashed, lm, hlm, _hnequiv, htarget⟩ :=
    mem_CurrentTargetSupporters cfg hiObserved.1
  have htargetEpoch :
      (get_current_target cfg (E.store cfg ext v n)).epoch = lm.epoch := by
    have h := congrArg Checkpoint.epoch htarget
    simpa only [get_checkpoint_for_block] using h
  obtain ⟨a, u, t, ifb, hsched, hiAttests, haTargetEpoch,
      haRoot, haSlotEpoch⟩ :=
    E.currentTargetScheduledLatestMessageProvenance cfg ext hgen0 v n i lm hlm
  obtain ⟨kGround, aGround, hvoteGround, hdataGround⟩ :=
    hhb.no_forgery u t a ifb hsched i hi hiAttests
  have hiCommittee : i ∈ E.committee a.data.slot :=
    hhb.votes_assigned i hi a.data.slot
      (by rw [hvoteGround]; exact Option.some_ne_none _)
  have hprov := E.latestMessageProvenance cfg ext hwf hec hgen0 v n (by assumption) (by assumption)
  obtain ⟨ap, _hapAttests, _hapTargetEpoch, _hapRoot, hapSlotEpoch,
      hapApplied, hapCommittee, _hlmKnown, _hlmSlot⟩ :=
    hprov i lm hlm
  have haSlotEq : a.data.slot = ap.data.slot :=
    hec.committee_assignment_unique i a.data.slot ap.data.slot
      hiCommittee hapCommittee (haSlotEpoch.trans hapSlotEpoch.symm)
  have haApplied : a.data.slot + 1 ≤ E.slot_at cfg n := by
    rw [haSlotEq]
    exact hapApplied
  have haSlotH : E.SlotWithinHorizon cfg a.data.slot :=
    E.slotWithinHorizon_of_le cfg
      (le_trans (Nat.le_succ _) haApplied) hnH
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcur := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at hcur
    exact hcur.symm
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg (get_current_epoch cfg ast) := by
    simpa only [TrustedAnchorBoundaryAligned, hgeq,
      get_forkchoice_store, Function.update_self] using hboundary
  have hqueryEpoch : compute_epoch_at_slot cfg (E.slot_at cfg n) = lm.epoch := by
    calc
      compute_epoch_at_slot cfg (E.slot_at cfg n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        simp only [get_current_store_epoch]
        rw [E.store_current_slot cfg ext v n]
      _ = (get_current_target cfg (E.store cfg ext v n)).epoch := rfl
      _ = lm.epoch := htargetEpoch
  have hanchorEpochLe : get_current_epoch cfg ast ≤ lm.epoch := by
    calc
      get_current_epoch cfg ast =
          compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
        simp only [get_current_epoch, hslot0]
      _ ≤ compute_epoch_at_slot cfg (E.slot_at cfg n) :=
        Nat.div_le_div_right (E.slot_at_mono cfg (Nat.zero_le n))
      _ = lm.epoch := hqueryEpoch
  have hstartMono : compute_start_slot_at_epoch cfg
      (get_current_epoch cfg ast) ≤
      compute_start_slot_at_epoch cfg lm.epoch := by
    exact Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
  have hstartVote : compute_start_slot_at_epoch cfg lm.epoch ≤
      a.data.slot := by
    have h := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
    have hdivEpoch : a.data.slot / cfg.slots_per_epoch = lm.epoch := by
      simpa only [compute_epoch_at_slot] using haSlotEpoch
    rw [hdivEpoch] at h
    exact h
  have hfrom0 : E.slot_at cfg 0 ≤ a.data.slot := by
    calc
      E.slot_at cfg 0 = ast.slot := hslot0
      _ = ablk.message.slot := hgenSlot
      _ ≤ compute_start_slot_at_epoch cfg (get_current_epoch cfg ast) := hboundary'
      _ ≤ compute_start_slot_at_epoch cfg lm.epoch := hstartMono
      _ ≤ a.data.slot := hstartVote
  obtain ⟨k, index, hkH, hkSlot, hvote⟩ :=
    hhb.votes_head i hi a.data.slot hiCommittee haSlotH hfrom0
  rw [hvote] at hvoteGround
  simp only [Option.some.injEq, Prod.mk.injEq] at hvoteGround
  obtain ⟨_, hcanonical⟩ := hvoteGround
  have hdata : a.data =
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data :=
    hdataGround.trans
      (congrArg (fun x : Attestation Root => x.data) hcanonical.symm)
  have hheadKnown : (get_head cfg (E.store cfg ext i k)).root ∈
      (E.store cfg ext i k).block_roots :=
    E.head_root_known cfg ext hji hi k hkH
  have hjcLe : (E.store cfg ext i k).justified_checkpoint.epoch ≤
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.epoch := by
    calc
      (E.store cfg ext i k).justified_checkpoint.epoch ≤
          get_current_store_epoch cfg (E.store cfg ext i k) :=
        E.store_justified_epoch_le cfg ext hec hdiv
          ⟨ast, ablk, hgeq, hgenSlot⟩ i k
      _ = compute_epoch_at_slot cfg a.data.slot := by
        simp only [get_current_store_epoch]
        rw [E.store_current_slot cfg ext i k, hkSlot]
      _ = a.data.target.epoch := haSlotEpoch.trans haTargetEpoch.symm
      _ = (honest_attestation cfg ext (E.store cfg ext i k)
          a.data.slot index i).data.target.epoch :=
        congrArg (fun d : AttestationData Root => d.target.epoch) hdata
  have hbound := E.hbound_of_justified_block_boundary cfg ext hji hi
    hkH haSlotH hvote hjcLe
  have hwalk := E.head_walk_of_bound cfg ext hwf hec
    ⟨ast, ablk, hgeq, hgenSlot, _hparent⟩ hji hi k hkH
    (compute_start_slot_at_epoch cfg
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.epoch) hbound
  have hrelay : E.slot_at cfg k + 1 ≤ E.slot_at cfg (n + 1) := by
    rw [hkSlot]
    exact haApplied.trans (E.slot_at_mono cfg (Nat.le_succ n))
  have hsub : (E.store cfg ext i k).block_roots ⊆
      (E.store cfg ext v n).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hsync hi hv hkH hnH
      hrelay
  have htransport := E.checkpoint_block_transport cfg ext hwf hsub
    hheadKnown hwalk
  have hheadRoot : (get_head cfg (E.store cfg ext i k)).root = lm.root := by
    calc
      (get_head cfg (E.store cfg ext i k)).root =
          (honest_attestation cfg ext (E.store cfg ext i k)
            a.data.slot index i).data.beacon_block_root := by
        symm
        exact honest_attestation_data_beacon_block_root cfg ext
          (E.store cfg ext i k) a.data.slot index
      _ = a.data.beacon_block_root :=
        (congrArg (fun d : AttestationData Root => d.beacon_block_root) hdata).symm
      _ = lm.root := haRoot
  have hcanonicalEpoch :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.epoch = lm.epoch := by
    exact (congrArg (fun d : AttestationData Root => d.target.epoch) hdata).symm.trans
      haTargetEpoch
  have hcanonicalRoot :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target.root =
        (get_current_target cfg (E.store cfg ext v n)).root := by
    calc
      (honest_attestation cfg ext (E.store cfg ext i k)
          a.data.slot index i).data.target.root =
          get_checkpoint_block cfg (E.store cfg ext i k)
            (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch :=
        honest_attestation_data_target_root cfg ext
          (E.store cfg ext i k) a.data.slot index
      _ = get_checkpoint_block cfg (E.store cfg ext v n)
            (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch := htransport
      _ = get_checkpoint_block cfg (E.store cfg ext v n) lm.root lm.epoch := by
        rw [hheadRoot, hcanonicalEpoch]
      _ = (get_checkpoint_for_block cfg (E.store cfg ext v n)
            lm.root lm.epoch).root := rfl
      _ = (get_current_target cfg (E.store cfg ext v n)).root :=
        congrArg Checkpoint.root htarget.symm
  have htargetExact :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target =
        get_current_target cfg (E.store cfg ext v n) := by
    have hepoch := hcanonicalEpoch.trans htargetEpoch.symm
    generalize hc : (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target = c at hepoch hcanonicalRoot ⊢
    generalize ht : get_current_target cfg (E.store cfg ext v n) = t
      at hepoch hcanonicalRoot ⊢
    cases c
    cases t
    simp only at hepoch hcanonicalRoot ⊢
    subst_vars
    rfl
  refine ⟨⟨a.data.slot, k, index, hi, hkH, hkSlot, haSlotH,
    hiCommittee, hvote, haSlotEpoch.trans htargetEpoch.symm, ?_, htargetExact⟩⟩
  exact slot_lt_next_epoch_start cfg
    (haSlotEpoch.trans htargetEpoch.symm)

/-- Every honest seat in the current epoch's future suffix casts a canonical
ground vote for the exact current target before the next epoch boundary. -/
theorem currentTargetFutureHonestSeat_vote
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} {n : ℕ}
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v n)) n)
    {i : ValidatorIndex}
    (hiFuture : i ∈
      (E.currentTargetFutureSpan cfg (E.store cfg ext v n)).filter
        (fun j => j ∈ E.honest)) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))
      (get_current_target cfg (E.store cfg ext v n))) := by
  simp only [Finset.mem_filter, Execution.currentTargetFutureSpan,
    Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiFuture
  obtain ⟨⟨s, hs, hiCommittee⟩, hi⟩ := hiFuture
  let store := E.store cfg ext v n
  let e := get_current_store_epoch cfg store
  have hloCurrent : e * cfg.slots_per_epoch ≤ get_current_slot cfg store := by
    have h := Nat.div_mul_le_self (get_current_slot cfg store)
      cfg.slots_per_epoch
    simpa only [e, get_current_store_epoch, Nat.mul_comm] using h
  have hsEpoch : compute_epoch_at_slot cfg s = e := by
    apply epoch_eq_of_epoch_bounds cfg
    · exact hloCurrent.trans hs.1
    · simpa only [currentTargetEpochEnd, currentTargetEpochStart,
        compute_start_slot_at_epoch, e, store] using hs.2
  have htargetEpoch :
      (get_current_target cfg store).epoch = e := by
    rfl
  have hsTargetEpoch : compute_epoch_at_slot cfg s =
      (get_current_target cfg store).epoch :=
    hsEpoch.trans htargetEpoch.symm
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_mono cfg hs.2 hendH
  have hquerySlot : E.slot_at cfg n ≤ s := by
    rw [← E.store_current_slot cfg ext v n]
    exact hs.1
  have hs0 : E.slot_at cfg 0 ≤ s :=
    (E.slot_at_mono cfg (Nat.zero_le n)).trans hquerySlot
  obtain ⟨k, index, hkH, hkSlot, hvote⟩ :=
    hhb.votes_head i hi s hiCommittee hsH hs0
  have htarget :
      (honest_attestation cfg ext (E.store cfg ext i k) s index i).data.target =
        get_current_target cfg store :=
    hsupport.2 i hi s hsH hsTargetEpoch hquerySlot k
      (honest_attestation cfg ext (E.store cfg ext i k) s index i) hvote
  refine ⟨⟨s, k, index, hi, hkH, hkSlot, hsH, hiCommittee, hvote,
    hsTargetEpoch, ?_, htarget⟩⟩
  exact slot_lt_next_epoch_start cfg hsTargetEpoch

/-! ## The sole source-geometry input -/

/-- Source agreement restricted to the exact concrete votes used by the
current-target quorum.  It contains no weight statement and no receipt or A3.2
conclusion. -/
def CurrentTargetSourceAgreement
    (signers : Finset ValidatorIndex) (deadline : Slot)
    (source target : Checkpoint Root) : Prop :=
  ∀ i ∈ signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      (honest_attestation cfg ext
        (E.store cfg ext i vote.time) vote.slot vote.index i).data.source = source

/-- The concrete, source-specific honest quorum retained before it is erased
to a `CertifiedJustified` certificate.  This record is the operational
antecedent needed by paper Assumption 3.2: actual ground votes, one common
source, and a two-thirds weight bound.  It contains no AU inclusion, filter,
head, ancestry, or safety conclusion. -/
structure ConcreteA32QuorumBefore
    (deadline : Slot) (target : Checkpoint Root) : Type _ where
  source : Checkpoint Root
  signers : Finset ValidatorIndex
  votes : ∀ i ∈ signers,
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i deadline target)
  source_agreement : CurrentTargetSourceAgreement cfg ext E signers deadline
    source target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers
  source_before_target : source.epoch < target.epoch
  target_epoch_within : target.epoch < E.verification_horizon

/-- The wire events needed to turn a ground-vote quorum into an explicit FFG
link.  Only one scheduled copy is needed for certificate formation; ordinary
synchrony schedules the same copy at every honest receiver. -/
def ConcreteA32QuorumScheduledDelivery
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target) : Prop :=
  ∀ i ∈ Q.signers,
    ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
      Event.attestation
          (honest_attestation cfg ext (E.store cfg ext i vote.time)
            vote.slot vote.index i) false ∈
        E.schedule i (E.slot_start cfg (vote.slot + 1))

/-- The explicit one-slot boundary lookahead supplies the scheduled copy for
every quorum vote, including a last-slot vote whose receipt is just beyond the
public cutoff. -/
theorem ConcreteA32QuorumBefore.scheduledDelivery_of_lookahead
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (hdelivery : HorizonVoteDeliveryLookahead cfg E) :
    ConcreteA32QuorumScheduledDelivery cfg ext E Q := by
  intro i hi vote
  exact hdelivery.attestation_delivery i vote.honest vote.slot vote.time
    (honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i)
    vote.slot_within_horizon vote.time_within_horizon
    (by simpa only using vote.vote) i vote.honest

/-- Compatibility adapter for the previous finite-prefix API.  If the whole
receipt second is still within the horizon, ordinary synchrony supplies the
same local delivery law. -/
theorem ConcreteA32QuorumBefore.scheduledDelivery_of_synchrony
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdeadline : E.WithinHorizon cfg (E.slot_start cfg deadline)) :
    ConcreteA32QuorumScheduledDelivery cfg ext E Q := by
  intro i hi vote
  have hdeliveryLe : E.slot_start cfg (vote.slot + 1) ≤
      E.slot_start cfg deadline := by
    simp only [Execution.slot_start]
    apply Nat.sub_le_sub_right
    apply Nat.add_le_add_left
    exact Nat.div_le_div_right (Nat.mul_le_mul_right
      cfg.slot_duration_ms (Nat.succ_le_of_lt vote.before_deadline))
  have hdeliveryH : E.WithinHorizon cfg
      (E.slot_start cfg (vote.slot + 1)) :=
    E.withinHorizon_mono cfg hdeliveryLe hdeadline
  exact hsync.attestation_delivery i vote.honest vote.slot vote.time
    (honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i)
    vote.slot_within_horizon vote.time_within_horizon
    (by simpa only using vote.vote) hdeliveryH i vote.honest

/-- The paper-facing information retained from one successful invocation of
the executable current-target gate.

The certificate is kept for the existing SIR consumer.  The second field
records the exact state-semantic split produced by the executable arithmetic
gate: either the current target is the trusted anchor, or the gate produced a
concrete source-specific honest quorum.  This deliberately does **not** split
on equality with the store's unrealized justified checkpoint: a non-anchor
unrealized checkpoint is still subject to the same arithmetic gate and honest
target-support proviso.  In the quorum case the source is identified with
Definition 7's selector in the *actual query store*.  Thus votes and source
agreement are outputs of the gate realization, never free inputs to a
paper-A3.2 producer. -/
structure CurrentTargetA32GateRealizationCore
    (anchor : Checkpoint Root) (V : PaperA32StateView cfg E)
    (store : Store Root) : Prop where
  certified : Nonempty (CertifiedJustified cfg E anchor
    (get_current_target cfg store))
  support_branch :
    get_current_target cfg store = anchor ∨
      (get_current_target cfg store ≠ anchor ∧
        ∃ Q : ConcreteA32QuorumBefore cfg ext E
            (compute_start_slot_at_epoch cfg
              ((get_current_target cfg store).epoch + 1))
            (get_current_target cfg store),
          Q.source = V.VSAt cfg store
            (get_current_target cfg store).root
            (get_current_target cfg store).epoch)

/-- Actual-call producer type for `CurrentTargetA32GateRealization`.  Its only
inputs are the executable boolean and the matching normative target-support
proviso.  In particular it takes no signer set, votes, common source, source
agreement, AU fact, or A3.2 conclusion. -/
def CurrentTargetA32GateRealizationProducerAtCore
    (anchor : Checkpoint Root) (V : PaperA32StateView cfg E)
    (q : ℕ) (query : FastConfirmationStore Root) : Prop :=
  will_current_target_be_justified cfg ext query.store = true →
  HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q →
    CurrentTargetA32GateRealizationCore cfg ext E anchor V query.store

/-- The same gate realization after tying its common source to the original
current-epoch carrier `b`, as required by the fixed-source reading of paper
Assumption 3.2. -/
structure FixedSourceCurrentTargetA32GateRealizationCore
    (anchor : Checkpoint Root) (V : PaperA32StateView cfg E)
    (store : Store Root) (b : Root) : Prop where
  certified : Nonempty (CertifiedJustified cfg E anchor
    (get_current_target cfg store))
  support_branch :
    get_current_target cfg store = anchor ∨
      (get_current_target cfg store ≠ anchor ∧
        ∃ Q : ConcreteA32QuorumBefore cfg ext E
            (compute_start_slot_at_epoch cfg
              ((get_current_target cfg store).epoch + 1))
            (get_current_target cfg store),
          Q.source = V.VSAt cfg store b
            (get_current_target cfg store).epoch)

/-- Actual-call producer for the fixed source belonging to the original
selected carrier.  The producer still receives no helper witness. -/
def FixedSourceCurrentTargetA32GateRealizationProducerAtCore
    (anchor : Checkpoint Root) (V : PaperA32StateView cfg E)
    (q : ℕ) (query : FastConfirmationStore Root) (b : Root) : Prop :=
  will_current_target_be_justified cfg ext query.store = true →
  HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q →
    FixedSourceCurrentTargetA32GateRealizationCore cfg ext E anchor V
      query.store b

/-! ### State specializations -/

/-- Gate realization specialized to the scheduled-root state. -/
abbrev CurrentTargetA32GateRealization
    (anchor : Checkpoint Root) (S : ChainFFGState cfg E anchor)
    (store : Store Root) : Prop :=
  CurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32View cfg) store

/-- Actual-call producer specialized to the scheduled-root state. -/
abbrev CurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root) (S : ChainFFGState cfg E anchor)
    (q : ℕ) (query : FastConfirmationStore Root) : Prop :=
  CurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32View cfg) q query

/-- Fixed-source realization specialized to the scheduled-root state. -/
abbrev FixedSourceCurrentTargetA32GateRealization
    (anchor : Checkpoint Root) (S : ChainFFGState cfg E anchor)
    (store : Store Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32View cfg) store b

/-- Fixed-source producer specialized to the scheduled-root state. -/
abbrev FixedSourceCurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root) (S : ChainFFGState cfg E anchor)
    (q : ℕ) (query : FastConfirmationStore Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32View cfg) q query b

/-- Accepted-state gate realization. -/
abbrev AcceptedCurrentTargetA32GateRealization
    (anchor : Checkpoint Root)
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) : Prop :=
  CurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32View cfg ext) store

/-- Accepted-state actual-call producer. -/
abbrev AcceptedCurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root)
    (S : AcceptedChainFFGState cfg ext E anchor)
    (q : ℕ) (query : FastConfirmationStore Root) : Prop :=
  CurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32View cfg ext) q query

/-- Accepted-state fixed-source realization. -/
abbrev AcceptedFixedSourceCurrentTargetA32GateRealization
    (anchor : Checkpoint Root)
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationCore cfg ext E anchor
    (S.paperA32View cfg ext) store b

/-- Accepted-state fixed-source producer. -/
abbrev AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
    (anchor : Checkpoint Root)
    (S : AcceptedChainFFGState cfg ext E anchor)
    (q : ℕ) (query : FastConfirmationStore Root) (b : Root) : Prop :=
  FixedSourceCurrentTargetA32GateRealizationProducerAtCore cfg ext E anchor
    (S.paperA32View cfg ext) q query b

/-- A per-vote common-ancestor segment is sufficient to discharge the source
field.  This is the direct executable-store connection to
`FFGSourceCoherence`; it uses no AU/maximality law of `ChainFFGState`. -/
theorem concreteVote_source_eq_common_ancestor
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    {deadline : Slot} {target : Checkpoint Root}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target)
    (hcore : WellFormedStoreCore (E.store cfg ext i vote.time))
    {common : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots (E.store cfg ext i vote.time)
      common (get_head cfg (E.store cfg ext i vote.time)).root)
    (hvoteEpoch : compute_epoch_at_slot cfg
      ((E.store cfg ext i vote.time).block_states
        (get_head cfg (E.store cfg ext i vote.time)).root).slot =
      compute_epoch_at_slot cfg vote.slot) :
    (honest_attestation cfg ext
      (E.store cfg ext i vote.time) vote.slot vote.index i).data.source =
      S.GJ common := by
  exact E.honest_attestation_source_eq_common_ancestor
    hhistory hphase hcoh hi vote.time_within_horizon hcore hsegment hvoteEpoch

/-- Uniform common-segment geometry for the concrete signer set yields the
minimal source-agreement predicate consumed by the quorum constructor. -/
theorem currentTargetSourceAgreement_of_common_ancestor
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {signers : Finset ValidatorIndex} {deadline : Slot}
    {target : Checkpoint Root} {common : Root}
    (hhonest : signers ⊆ E.honest)
    (hgeometry : ∀ i ∈ signers,
      ∀ vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target,
        WellFormedStoreCore (E.store cfg ext i vote.time) ∧
        KnownSameEpochAncestrySegment cfg E.genesis_store.block_roots
          (E.store cfg ext i vote.time) common
          (get_head cfg (E.store cfg ext i vote.time)).root ∧
        compute_epoch_at_slot cfg
            ((E.store cfg ext i vote.time).block_states
              (get_head cfg (E.store cfg ext i vote.time)).root).slot =
          compute_epoch_at_slot cfg vote.slot) :
    CurrentTargetSourceAgreement cfg ext E signers deadline
      (S.GJ common) target := by
  intro i hi vote
  obtain ⟨hcore, hsegment, hvoteEpoch⟩ := hgeometry i hi vote
  exact E.concreteVote_source_eq_common_ancestor cfg ext hhistory hphase hcoh
    (hhonest hi) vote hcore hsegment hvoteEpoch

/-! ## Receipt and non-slashability facts for the paper-facing record -/

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_start_succ_le_of_slot_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {s : Slot} {m : ℕ} (hsm : s + 1 ≤ E.slot_at cfg m) :
    E.slot_start cfg (s + 1) ≤ m := by
  apply Nat.le_of_not_gt
  intro hlt
  have hslotLt := (E.slot_at_lt_iff cfg hdiv hgenTime).2 hlt
  exact (Nat.not_lt_of_ge hsm) hslotLt

/-- A concrete honest vote has reached every honest view once that view's slot
is at least the vote slot. -/
theorem concreteVote_receivedBy
    (hsync : PaperSafetySynchrony cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {i : ValidatorIndex} {deadline : Slot} {target : Checkpoint Root}
    (vote : ConcreteHonestTargetVoteBefore cfg ext E i deadline target)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hslot : vote.slot + 1 ≤ E.slot_at cfg m) :
    E.AttestationReceivedBy w m
      (honest_attestation cfg ext (E.store cfg ext i vote.time)
        vote.slot vote.index i) := by
  let delivery := E.slot_start cfg (vote.slot + 1)
  have hdeliveryLe : delivery ≤ m :=
    slot_start_succ_le_of_slot_le cfg E hdiv hgenTime hslot
  have hdeliveryH : E.WithinHorizon cfg delivery :=
    E.withinHorizon_mono cfg hdeliveryLe hHm
  refine ⟨delivery, hdeliveryLe, false, ?_⟩
  exact hsync.attestation_delivery i vote.honest vote.slot vote.time
    (honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i) vote.slot_within_horizon
    vote.time_within_horizon vote.vote hdeliveryH w hw

/-- Honest validators cannot belong to the semantic block-chain slashing set:
each included attestation exposes a scheduled wire event, no-forgery recovers
the two ground votes, and `HonestBehavior.not_slashable` contradicts the
purported slashable pair. -/
theorem honest_not_mem_slashableOnChain
    (hhb : HonestBehavior cfg ext E)
    {anchor : Checkpoint Root} (S : ChainFFGState cfg E anchor)
    {tip : Root} {i : ValidatorIndex} (hi : i ∈ E.honest) :
    i ∉ S.slashableOnChain cfg tip := by
  intro hmem
  rw [ChainFFGState.mem_slashableOnChain] at hmem
  obtain ⟨a₁, a₂, hinc₁, hinc₂, hi₁, hi₂, hslash⟩ := hmem
  obtain ⟨carrier₁, _hdesc₁, hincluded₁⟩ := hinc₁
  obtain ⟨carrier₂, _hdesc₂, hincluded₂⟩ := hinc₂
  obtain ⟨w₁, n₁, hsched₁⟩ :=
    (S.includedAttestations.evidence hincluded₁).received_from_block
  obtain ⟨w₂, n₂, hsched₂⟩ :=
    (S.includedAttestations.evidence hincluded₂).received_from_block
  obtain ⟨k₁, vote₁, hvote₁, hdata₁⟩ :=
    hhb.no_forgery w₁ n₁ a₁ true hsched₁ i hi hi₁
  obtain ⟨k₂, vote₂, hvote₂, hdata₂⟩ :=
    hhb.no_forgery w₂ n₂ a₂ true hsched₂ i hi hi₂
  have hslashGround :
      is_slashable_attestation_data vote₁.data vote₂.data = true := by
    rw [← hdata₁, ← hdata₂]
    exact hslash
  have hnot := hhb.not_slashable i hi a₁.data.slot a₂.data.slot
    k₁ k₂ vote₁ vote₂ hvote₁ hvote₂
  rw [hslashGround] at hnot
  contradiction

/-! ## Gate-to-`HonestTargetQuorumBefore` -/

/-- The executable current-target gate, together with its normative
`HonestVotesSupportTarget` proviso and exactly one common-source geometry
input, produces the paper-facing honest two-thirds link before the next epoch
boundary.

Neither latest-message provenance nor a target quorum is assumed: provenance
is derived by handler induction above, and the weight bound is the gate
soundness theorem from `CurrentTargetFutureSupport`. -/
theorem will_current_target_be_justified_honestTargetQuorumBefore
    (hSA : SpecAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root}
    (hstate : state =
      get_pulled_up_head_state cfg ext (E.store cfg ext v n))
    (hval : state.validators = E.registry)
    (htab : get_total_active_balance cfg state = E.total_active cfg)
    (hendH : E.SlotWithinHorizon cfg
      (currentTargetEpochEnd cfg (E.store cfg ext v n)))
    (hanchorH : get_current_epoch cfg E.anchor_state < E.verification_horizon)
    (hfloor : cfg.effective_balance_increment ≤
      E.weight (E.currentTargetAnchorActive cfg))
    (hsupport : HonestVotesSupportTarget cfg E
      (get_current_target cfg (E.store cfg ext v n)) n)
    (hgate : will_current_target_be_justified cfg ext
      (E.store cfg ext v n) = true)
    (source : Checkpoint Root)
    (hsource : CurrentTargetSourceAgreement cfg ext E
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state)
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))
      source (get_current_target cfg (E.store cfg ext v n))) :
    Nonempty (HonestTargetQuorumBefore cfg E
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))
      source (get_current_target cfg (E.store cfg ext v n))) := by
  have hSA0 := hSA
  obtain ⟨hgen, hwf, _hdiv, hhb, _hsync, hec, hsv, hbb, _hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, _hgenSlot, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let store := E.store cfg ext v n
  let target := get_current_target cfg store
  let deadline := compute_start_slot_at_epoch cfg (target.epoch + 1)
  let signers := E.currentTargetA32Signers cfg store state
  change HonestVotesSupportTarget cfg E target n at hsupport
  change CurrentTargetSourceAgreement cfg ext E signers deadline
    source target at hsource
  have hvotes : ∀ i ∈ signers,
      Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i deadline target) := by
    intro i hiSigner
    simp only [signers, Execution.currentTargetA32Signers,
      Finset.mem_union] at hiSigner
    rcases hiSigner with hiObserved | hiFuture
    · simpa only [store, target, deadline] using
        E.currentTargetObservedHonestSupporter_vote cfg ext hSA0 hboundary
          hv hnH hiObserved
    · simpa only [store, target, deadline] using
        E.currentTargetFutureHonestSeat_vote cfg ext hhb hendH
          hsupport hiFuture
  have hsignersHonest : signers ⊆ E.honest := by
    intro i hi
    obtain ⟨vote⟩ := hvotes i hi
    exact vote.honest
  have hsignersEpoch : signers ⊆
      E.span_committee (target.epoch * cfg.slots_per_epoch)
        (target.epoch * cfg.slots_per_epoch +
          (cfg.slots_per_epoch - 1)) := by
    intro i hi
    obtain ⟨vote⟩ := hvotes i hi
    exact mem_epoch_span_of_committee cfg vote.assigned vote.slot_epoch
  have hprov := E.latestMessageProvenance cfg ext hwf hec hgen0 v n (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v n] at hprov
  have hquorum : 2 * E.total_active cfg ≤ 3 * E.weight signers := by
    simpa only [signers, Execution.currentTargetA32Signers, store] using
      E.will_current_target_be_justified_honest_quorum cfg ext hhb hec hsv hbb
        hgen0 hv hnH hstate hval htab hendH hanchorH hfloor hprov hgate
  refine ⟨⟨signers, hsignersHonest, hsignersEpoch, ?_, hquorum⟩⟩
  intro i hi
  obtain ⟨vote⟩ := hvotes i hi
  let a := honest_attestation cfg ext
    (E.store cfg ext i vote.time) vote.slot vote.index i
  refine ⟨vote.time, a, ?_, vote.slot_within_horizon,
    vote.before_deadline, ?_, vote.target_eq⟩
  · simpa only [a, honest_attestation_data_eq,
      honest_attestation_data_slot] using vote.vote
  · simpa only [a] using hsource i hi vote

end Execution

end FastConfirmation.Spec

end
