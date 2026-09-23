module
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetFutureSupport
public import FastConfirmationProofs.FCRRule.SelectedCheckpointInclusionSupport
public import FastConfirmationProofs.FFG.SourceHistory.FFGSourceCoherence
public import FastConfirmationProofs.FFG.State.ScheduledFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.ForkChoice.Head.AheadHeadDominance
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.ForkChoice.Head.HeadStack
public import FastConfirmationProofs.ModelFacts

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
      a.data.target.epoch = (get_latest_message_epoch cfg m) ∧
      a.data.beacon_block_root = m.root ∧
      compute_epoch_at_slot cfg a.data.slot = (get_latest_message_epoch cfg m)

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
  have hEpoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot :=
    hv.1.1.1.1.1.1.1.1.2
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with
    hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact h i m hold
  · obtain ⟨u, t, hmem⟩ := hsched
    refine ⟨a, u, t, ifb, hmem, hi, ?_, ?_, ?_⟩
    · simpa only [hmeq, get_latest_message_epoch] using hEpoch
    · rw [hmeq]
    · simp only [hmeq, get_latest_message_epoch]

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
  | execution_payload_envelope envelope observation =>
      exact currentTargetScheduledLatestMessageProvenance_of_latest_eq cfg h
        (on_execution_payload_envelope_frame ext he).latest_messages
  | payload_attestation_message message fromBlock =>
      exact currentTargetScheduledLatestMessageProvenance_of_latest_eq cfg h
        (on_payload_attestation_message_frame cfg ext he).latest_messages

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

/-- The boundary case of the single synchrony premise supplies the scheduled
copy for every quorum vote, including a last-slot vote whose receipt is just
beyond the public cutoff.  `toDeliveryLookahead` is the derived form of what
used to be the separate `HorizonVoteDeliveryLookahead` assumption. -/
theorem ConcreteA32QuorumBefore.scheduledDelivery_of_lookahead
    {deadline : Slot} {target : Checkpoint Root}
    (Q : ConcreteA32QuorumBefore cfg ext E deadline target)
    (hdelivery : NextSlotSynchronyPremises cfg ext E) :
    ConcreteA32QuorumScheduledDelivery cfg ext E Q := by
  intro i hi vote
  exact hdelivery.toDeliveryLookahead cfg ext i vote.honest vote.slot vote.time
    (honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i)
    vote.slot_within_horizon vote.time_within_horizon
    (by simpa only using vote.vote) i vote.honest


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
    (hsync : NextSlotSynchronyPremises cfg ext E)
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
  exact hsync.toHorizonScopedDelivery cfg ext i vote.honest vote.slot vote.time
    (honest_attestation cfg ext (E.store cfg ext i vote.time)
      vote.slot vote.index i) vote.slot_within_horizon
    vote.time_within_horizon vote.vote hdeliveryH w hw


/-! ## Gate-to-`HonestTargetQuorumBefore` -/


end Execution

end FastConfirmation.Spec

end
