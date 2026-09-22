module
public import FastConfirmation.Spec.Proof.CurrentTargetA32Support
public import FastConfirmation.Spec.Proof.FFGAccountability

@[expose] public section

/-!
# No-conflict certificate pinning (paper Lemma 42)

This module proves the certificate-level meaning of the executable
`will_no_conflicting_checkpoint_be_justified` helper.

There are exactly two executable branches.  If the current target already is
the store's unrealized justified checkpoint, the common semantic FFG state
supplies a concrete certificate for that same checkpoint, and ordinary Casper
accountability pins every same-epoch certificate to it.  Otherwise the helper
commits strictly more than one third of the total weight in *honest* concrete
current-target voters.  Such a set intersects the terminal two-thirds link of
any competing same-epoch certificate; no-forgery and honest non-slashability
then rule out a different target root.

No competing-certificate absence, pinning conclusion, latest-message
provenance, or quorum is assumed.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Exact lower protocol bundle used by certificate pinning.  In particular it
contains neither `JustificationInterface` nor synchrony.  The sole endpoint
domain fact is justified-root knownness, used only to keep `get_head` and the
common semantic checkpoint projection in-domain. -/
structure NoConflictPinningAssumptions (E : Execution Root) : Prop where
  genesis : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block ∧
    anchor_state.slot = anchor_block.message.slot ∧
    anchor_block.message.parent_root ≠ anchor_block.root
  wellFormed : WellFormedExecution E
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  honest_behavior : HonestBehavior cfg ext E
  externals_coherence : ExternalsCoherence cfg ext E
  static_validators : StaticValidatorSet cfg E
  byzantine_bound : ByzantineBound cfg E
  justified_root_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
      (E.store cfg ext w m).justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots

/-- Compatibility projection from the legacy all-in-one bundle.  This theorem
documents the only `JustificationInterface` field retained: local justified
root knownness.  No gate soundness, justified uniqueness/ancestry, head
descent, or checkpoint-boundary field is projected. -/
theorem SpecAssumptions.toNoConflictPinningAssumptions
    {E : Execution Root} (hSA : SpecAssumptions cfg ext E) :
    NoConflictPinningAssumptions cfg ext E := by
  obtain ⟨hgen, hwf, hdiv, hhb, _hsync, hec, hsv, hbb, hji⟩ := hSA
  exact {
    genesis := hgen
    wellFormed := hwf
    whole_seconds := hdiv
    honest_behavior := hhb
    externals_coherence := hec
    static_validators := hsv
    byzantine_bound := hbb
    justified_root_known := fun w hw m hH =>
      (hji.checkpoint_known w hw m hH).1 }

/-- The already-local selected-margin assumptions project to the pinning
bundle without mentioning `JustificationInterface` at all. -/
theorem SelectedMarginAssumptions.toNoConflictPinningAssumptions
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E) :
    NoConflictPinningAssumptions cfg ext E where
  genesis := hA.genesis
  wellFormed := hA.wellFormed
  whole_seconds := hA.whole_seconds
  honest_behavior := hA.honest_behavior
  externals_coherence := hA.externals_coherence
  static_validators := hA.static_validators
  byzantine_bound := hA.byzantine_bound
  justified_root_known := hA.domain.justified_root_known

namespace Execution

variable (E : Execution Root)

/-! ## Arithmetic branch of the executable helper -/

/-- In the non-equality branch, the actual helper arithmetic puts strictly
more than one third of total active weight in the same concrete honest signer
set used by the current-target support bridge. -/
theorem noConflict_arithmeticBranch_oneThird
    (hA : NoConflictPinningAssumptions cfg ext E)
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
    (hne : get_current_target cfg (E.store cfg ext v n) ≠
      (E.store cfg ext v n).unrealized_justified_checkpoint)
    (hgate : will_no_conflicting_checkpoint_be_justified cfg ext
      (E.store cfg ext v n) = true) :
    E.total_active cfg < 3 * E.weight
      (E.currentTargetA32Signers cfg (E.store cfg ext v n) state) := by
  obtain ⟨hgen, hwf, _hdiv, hhb, hec, hsv, hbb, _hknown⟩ := hA
  obtain ⟨ast, ablk, hgeq, _hslot, _hparent⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  let store := E.store cfg ext v n
  let observedHonest := E.currentTargetObservedHonestSupporters cfg store state
  let observedNonhonest :=
    E.currentTargetObservedNonhonestSupporters cfg store state
  let futureHonest := (E.currentTargetFutureSpan cfg store).filter
    (fun i => i ∈ E.honest)
  let score := get_current_target_score cfg ext store
  let start := currentTargetEpochStart cfg store
  let finish := get_current_slot cfg store - 1
  let estimate := estimate_committee_weight_between_slots cfg
    (E.total_active cfg) start finish
  let adversarial := compute_adversarial_weight cfg ext store state start finish
  let remaining := (E.total_active cfg - estimate) / 100 *
    (100 - cfg.confirmation_byzantine_threshold)
  have hcurrentH : E.SlotWithinHorizon cfg (get_current_slot cfg store) := by
    rw [show get_current_slot cfg store = E.slot_at cfg n by
      exact E.store_current_slot cfg ext v n]
    exact ⟨hnH.2.1, hnH.2.2⟩
  have hscore : score =
      E.weight observedHonest + E.weight observedNonhonest := by
    simpa only [score, observedHonest, observedNonhonest, store,
      Execution.currentTargetObservedHonestSupporters,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.current_target_score_eq_honest_add_nonhonest_weight
        cfg ext hstate hval
  have hprov := E.latestMessageProvenance cfg ext hwf hec hgen0 v n (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v n] at hprov
  have hbyz : E.weight observedNonhonest ≤ adversarial := by
    simpa only [observedNonhonest, adversarial, start, finish, store,
      Execution.currentTargetObservedNonhonestSupporters] using
      E.currentTarget_nonhonest_weight_le_adversarial cfg ext
        hhb hec hbb hgen0 hv hnH hval htab hprov
  have hobserved : score - adversarial ≤
      E.weight observedHonest := by
    rw [hscore]
    apply (Nat.sub_le_iff_le_add).2
    exact Nat.add_le_add_left hbyz _
  have hfuture : remaining ≤ E.weight futureHonest := by
    simpa only [remaining, estimate, start, finish, futureHonest, store] using
      E.currentTarget_remaining_honest_le_future_weight cfg ext
        hec hsv hbb hcurrentH hendH hanchorH hfloor
  have hdisjoint : Disjoint observedHonest futureHonest := by
    simpa only [observedHonest, futureHonest, store] using
      E.currentTarget_observed_future_disjoint cfg ext hec hprov
  have hgateArithmetic := hgate
  simp only [will_no_conflicting_checkpoint_be_justified, hne, if_false,
    compute_honest_ffg_support_for_current_target,
    decide_eq_true_eq] at hgateArithmetic
  rw [← hstate, htab] at hgateArithmetic
  have hgateArithmetic' : E.total_active cfg <
      3 * (score - adversarial + remaining) := by
    simpa only [score, adversarial, remaining, estimate, start, finish,
      store, one_mul] using hgateArithmetic
  have hpredict : score - adversarial + remaining ≤
      E.weight observedHonest + E.weight futureHonest :=
    Nat.add_le_add hobserved hfuture
  have honeThird : E.total_active cfg <
      3 * (E.weight observedHonest + E.weight futureHonest) :=
    hgateArithmetic'.trans_le (Nat.mul_le_mul_left 3 hpredict)
  change E.total_active cfg <
    3 * E.weight (observedHonest ∪ futureHonest)
  rw [E.weight_union_disjoint hdisjoint]
  exact honeThird

/-- Both live executable gates of the selector call site reduce to the raw
helper inequality, away from the `get_current_target = unrealized_justified`
short circuit.

This is the boolean-to-arithmetic half of **N4**
(`docs/trunkB-two-case-discharge.md` §5.5, §7): the `previousNoConflict` arm's
`will_no_conflicting_checkpoint_be_justified` *is* that inequality, and the
`currentCrossing` arm's `will_current_target_be_justified` asserts the
strictly stronger `3 · support ≥ 2 · total`, which implies it as soon as the
total active weight is positive.  Stating it once lets the case-β pinning
producers phrase their gate premise uniformly over both arms.  No honesty, no
node, and no store domain occurs. -/
theorem rawGate_of_executableGate {store : Store Root}
    (htab : get_total_active_balance cfg
      (get_pulled_up_head_state cfg ext store) = E.total_active cfg)
    (hpos : 0 < E.total_active cfg)
    (hgate :
      will_no_conflicting_checkpoint_be_justified cfg ext store = true ∨
        will_current_target_be_justified cfg ext store = true) :
    get_current_target cfg store = store.unrealized_justified_checkpoint ∨
      E.total_active cfg <
        3 * compute_honest_ffg_support_for_current_target cfg ext store := by
  by_cases heq : get_current_target cfg store =
      store.unrealized_justified_checkpoint
  · exact Or.inl heq
  refine Or.inr ?_
  rcases hgate with hnoConflict | hcurrentTarget
  · simp only [will_no_conflicting_checkpoint_be_justified, heq, if_false,
      decide_eq_true_eq] at hnoConflict
    rw [htab] at hnoConflict
    simpa only [one_mul] using hnoConflict
  · simp only [will_current_target_be_justified, decide_eq_true_eq]
      at hcurrentTarget
    rw [htab] at hcurrentTarget
    have hdouble : E.total_active cfg < 2 * E.total_active cfg := by
      rw [two_mul]
      exact Nat.lt_add_of_pos_left hpos
    exact Nat.lt_of_lt_of_le hdouble hcurrentTarget

/-- Converse of `Execution.rawGate_of_executableGate` for the no-conflict
boolean: the raw helper inequality is exactly what that boolean asserts, so
the arithmetic branch of `noConflict_arithmeticBranch_oneThird` can be reached
from either form.

This keeps the case-β pinning producers phrased over the raw inequality —
which is what both gate arms share (§5.5) — without duplicating the signer
weight argument. -/
theorem noConflictGate_of_rawGate {store : Store Root}
    (htab : get_total_active_balance cfg
      (get_pulled_up_head_state cfg ext store) = E.total_active cfg)
    (hraw : E.total_active cfg <
      3 * compute_honest_ffg_support_for_current_target cfg ext store) :
    will_no_conflicting_checkpoint_be_justified cfg ext store = true := by
  simp only [will_no_conflicting_checkpoint_be_justified]
  split_ifs with heq
  · rfl
  · simp only [decide_eq_true_eq, htab, one_mul]
    exact hraw

omit [LinearOrder Root] [Inhabited Root] in
private theorem slot_lt_noConflict_next_epoch_start {s : Slot} {e : Epoch}
    (hepoch : compute_epoch_at_slot cfg s = e) :
    s < compute_start_slot_at_epoch cfg (e + 1) := by
  rw [← hepoch]
  simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
  simpa only [Nat.mul_comm] using
    (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) s
      cfg.slots_per_epoch_pos)

/-- An observed honest score contributor is a canonical ground vote for the
exact current target, using the common FFG state's checkpoint projection
instead of any `JustificationInterface` ancestry or head-safety export.

The voter head and the query latest-message root are both known.  Therefore
`FFGTransitionCoherence.checkpoint_of_known` identifies the checkpoint walk
in both stores with one store-independent `S.C`; no cross-store head walk or
checkpoint-boundary assumption is needed. -/
theorem currentTargetObservedHonestSupporter_vote_of_ffgState
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    {state : BeaconState Root} {i : ValidatorIndex}
    (hiObserved : i ∈ E.currentTargetObservedHonestSupporters cfg
      (E.store cfg ext v n) state) :
    Nonempty (ConcreteHonestTargetVoteBefore cfg ext E i
      (compute_start_slot_at_epoch cfg
        ((get_current_target cfg (E.store cfg ext v n)).epoch + 1))
      (get_current_target cfg (E.store cfg ext v n))) := by
  obtain ⟨hgen, hwf, hdiv, hhb, hec, _hsv, _hbb, hjustKnown⟩ := hA
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
      hapApplied, hapCommittee, hlmKnown, _hlmSlot⟩ :=
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
      compute_start_slot_at_epoch cfg lm.epoch :=
    Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
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
      (E.store cfg ext i k).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i k) with h | h
    · exact h
    · rw [h]
      exact hjustKnown i hi k hkH
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
        a.data.slot index i).data.target.epoch = lm.epoch :=
    (congrArg (fun d : AttestationData Root => d.target.epoch) hdata).symm.trans
      haTargetEpoch
  have hgroundProjection := hcoh.checkpoint_of_known i hi k hkH
    (get_head cfg (E.store cfg ext i k)).root hheadKnown
    (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target.epoch
  have hqueryProjection := hcoh.checkpoint_of_known v hv n hnH
    lm.root hlmKnown lm.epoch
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
      _ = (get_checkpoint_for_block cfg (E.store cfg ext i k)
            (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch).root := rfl
      _ = (S.C (get_head cfg (E.store cfg ext i k)).root
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target.epoch).root :=
        (congrArg Checkpoint.root hgroundProjection).symm
      _ = (S.C lm.root lm.epoch).root := by
        rw [hheadRoot, hcanonicalEpoch]
      _ = (get_checkpoint_for_block cfg (E.store cfg ext v n)
            lm.root lm.epoch).root :=
        congrArg Checkpoint.root hqueryProjection
      _ = (get_current_target cfg (E.store cfg ext v n)).root :=
        congrArg Checkpoint.root htarget.symm
  have htargetExact :
      (honest_attestation cfg ext (E.store cfg ext i k)
        a.data.slot index i).data.target =
        get_current_target cfg (E.store cfg ext v n) := by
    have hepoch := hcanonicalEpoch.trans htargetEpoch.symm
    generalize hc : (honest_attestation cfg ext (E.store cfg ext i k)
      a.data.slot index i).data.target = c at hepoch hcanonicalRoot ⊢
    generalize ht : get_current_target cfg (E.store cfg ext v n) = target
      at hepoch hcanonicalRoot ⊢
    cases c
    cases target
    simp only at hepoch hcanonicalRoot ⊢
    subst_vars
    rfl
  refine ⟨⟨a.data.slot, k, index, hi, hkH, hkSlot, haSlotH,
    hiCommittee, hvote, haSlotEpoch.trans htargetEpoch.symm, ?_, htargetExact⟩⟩
  exact slot_lt_noConflict_next_epoch_start cfg
    (haSlotEpoch.trans htargetEpoch.symm)

/-- Every known execution-store root descends from the trusted checkpoint-sync
anchor, using only the lower well-formed trajectory.  This is the local form
needed by the anchor-epoch corner; unlike the legacy theorem with the same
geometry, it does not require synchrony or a cached-checkpoint domain. -/
theorem known_descends_trustedAnchor_noConflict
    (hA : NoConflictPinningAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : ℕ) {r : Root}
    (hr : r ∈ (E.store cfg ext w m).block_roots) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root r) (get_node_for_root anchor.root) = true ∧
      anchor.epoch ≤ get_block_epoch cfg (E.store cfg ext w m) r := by
  obtain ⟨hgen, hwf, _hdiv, _hhb, hec, _hsv, _hbb, _hknown⟩ := hA
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hgen
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hanchorRoot : anchor.root = ablk.root := by
    rw [hanchor, hgenEq]
    rfl
  have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgenEq]
    rfl
  have hanchorKnown0 : ablk.root ∈
      (E.store cfg ext w 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgenEq]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnown : ablk.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorKnown0
  have hwfM : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec hgen
      hwf.anchor_parent_unscheduled w m
  have hnonAnchor := E.store_nonAnchorParentKnown cfg ext hgenEq w m
  have hminimum := E.store_anchor_min_slot cfg ext hwf hec
    hgenEq hanchorSlot hanchorParent w m
  have hanchorBlock :
      (E.store cfg ext w m).blocks ablk.root = ablk.message :=
    E.store_anchor_block cfg ext hwf hgenEq w m hanchorKnown
  have hanchorBlockSlot :
      ((E.store cfg ext w m).blocks ablk.root).slot = ablk.message.slot := by
    rw [hanchorBlock]
  have hwalk : WalkKnown (E.store cfg ext w m) ablk.message.slot r := by
    have hwalkK := E.store_walkKnownK cfg ext hwf hec hgen w m
      ablk.root hanchorKnown r hr
    rwa [hanchorBlockSlot] at hwalkK
  have hlands_of_walk : ∀ {x : Root},
      WalkKnown (E.store cfg ext w m) ablk.message.slot x →
        get_ancestor (E.store cfg ext w m)
          (ForkChoiceNode.mk x) ablk.message.slot =
            ForkChoiceNode.mk ablk.root := by
    intro x hx
    induction hx with
    | @stop x hr' hle =>
        have hre : x = ablk.root := by
          rcases hnonAnchor x hr' with hre | hparentKnown
          · exact hre
          · have hparentLt := hwfM x hr' hparentKnown
            have hparentGe := hminimum _ hparentKnown
            exact False.elim
              ((Nat.not_lt_of_ge hparentGe) (hparentLt.trans_le hle))
        subst x
        exact get_ancestor_stop hle
    | @step x hr' hgt hp ih =>
        rw [get_ancestor_step hwfM hr' hgt hp]
        exact ih
  have hlands : get_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk r) ablk.message.slot =
        ForkChoiceNode.mk ablk.root := hlands_of_walk hwalk
  have hdescends : is_ancestor (E.store cfg ext w m)
      (get_node_for_root r) (get_node_for_root ablk.root) = true := by
    simp only [is_ancestor, get_node_for_root, decide_eq_true_eq,
      hanchorBlockSlot]
    exact hlands
  have hanchorBlockEpoch : get_current_epoch cfg ast =
      get_block_epoch cfg (E.store cfg ext w m) ablk.root := by
    simp only [get_current_epoch, get_block_epoch, hanchorBlockSlot,
      hanchorSlot]
  refine ⟨?_, ?_⟩
  · simpa only [hanchorRoot] using hdescends
  · rw [hanchorEpoch, hanchorBlockEpoch]
    exact ce_mono cfg (by
      simpa only [hanchorBlockSlot] using hminimum r hr)

omit [LinearOrder Root] [Inhabited Root] in
/-- A concrete vote assigned in epoch `e` belongs to the full committee union
for `e`.  This local arithmetic lemma keeps the certificate-pinning module
independent of any hidden signer-set premise. -/
private theorem mem_noConflict_epoch_span_of_committee
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

/-! ## Certificate pinning -/

/-- If the current target differs from the store's unrealized justified
checkpoint, its epoch is strictly after the trusted anchor epoch.

This discharges the apparent bare-anchor corner rather than assuming it.  At
the anchor epoch, the lower store trajectory makes the known query head
descend from the anchor; boundary alignment makes the anchor block exactly the
epoch-boundary checkpoint, so the current target is the anchor.  Meanwhile
`CkptEpochLe` and a concrete certificate for the global unrealized checkpoint
pin that checkpoint to the anchor in the same epoch.  Hence target and
unrealized justified would be equal. -/
theorem currentTarget_anchor_epoch_lt_of_ne_unrealized
    (hA : NoConflictPinningAssumptions cfg ext E)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := E.genesis_store.justified_checkpoint))
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} {n : ℕ}
    (hv : v ∈ E.honest) (hnH : E.WithinHorizon cfg n)
    (hne : get_current_target cfg (E.store cfg ext v n) ≠
      (E.store cfg ext v n).unrealized_justified_checkpoint) :
    anchor.epoch <
      (get_current_target cfg (E.store cfg ext v n)).epoch := by
  classical
  have hA0 := hA
  obtain ⟨hgen, hwf, hdiv, hhb, hec, hsv, hbb, hjustKnown⟩ := hA
  obtain ⟨ast, ablk, hgeq, hgenSlot, hparent⟩ := hgen
  have hgenFull : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hgenSlot, hparent⟩
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgeq, hgenSlot⟩
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  have haccountability : FFGAccountabilityAssumptions cfg ext E := {
    genesis_store := hgen0
    whole_seconds := hdiv
    honest_behavior := hhb
    externals_coherence := hec
    static_validator_set := hsv
    byzantine_bound := hbb }
  let store := E.store cfg ext v n
  let target := get_current_target cfg store
  have hslot0 : E.slot_at cfg 0 = ast.slot := by
    have hcur := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at hcur
    exact hcur.symm
  have hanchorEpoch : anchor.epoch = get_current_epoch cfg ast := by
    rw [hanchor, hgeq]
    rfl
  have hanchorEpoch0 : anchor.epoch =
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
    simpa only [get_current_epoch, hslot0] using hanchorEpoch
  have htargetEpoch : target.epoch =
      compute_epoch_at_slot cfg (E.slot_at cfg n) := by
    simp only [target, store, get_current_target, get_checkpoint_for_block,
      get_current_store_epoch]
    rw [E.store_current_slot cfg ext v n]
  have hanchorLe : anchor.epoch ≤ target.epoch := by
    calc
      anchor.epoch = compute_epoch_at_slot cfg (E.slot_at cfg 0) := hanchorEpoch0
      _ ≤ compute_epoch_at_slot cfg (E.slot_at cfg n) :=
        Nat.div_le_div_right (E.slot_at_mono cfg (Nat.zero_le n))
      _ = target.epoch := htargetEpoch.symm
  apply lt_of_le_of_ne hanchorLe
  intro hepoch
  have hheadKnown : (get_head cfg store).root ∈ store.block_roots := by
    rcases get_head_root_mem_or cfg store with h | h
    · exact h
    · rw [h]
      exact hjustKnown v hv n hnH
  have hheadAnchor :=
    (E.known_descends_trustedAnchor_noConflict cfg ext hA0
      hanchor v n hheadKnown).1
  have hanchorRoot : anchor.root = ablk.root := by
    rw [hanchor, hgeq]
    rfl
  have hanchorMem0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgeq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : anchor.root ∈ store.block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock : store.blocks anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hwf hgeq v n
      (hanchorRoot ▸ hanchorMem)
  have hboundaryAnchor : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := anchor) := by
    rw [hanchor]
    exact hboundary
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgeq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundaryAnchor
  have hblockEpoch : compute_epoch_at_slot cfg ablk.message.slot =
      anchor.epoch := by
    rw [← hgenSlot]
    simpa only [get_current_epoch] using hanchorEpoch.symm
  have hstartLe : compute_start_slot_at_epoch cfg anchor.epoch ≤
      ablk.message.slot := by
    have h := Nat.div_mul_le_self ablk.message.slot cfg.slots_per_epoch
    have hdivEpoch : ablk.message.slot / cfg.slots_per_epoch =
        anchor.epoch := by
      simpa only [compute_epoch_at_slot] using hblockEpoch
    rw [hdivEpoch] at h
    simpa only [compute_start_slot_at_epoch] using h
  have hboundaryEq : ablk.message.slot =
      compute_start_slot_at_epoch cfg anchor.epoch :=
    Nat.le_antisymm hboundary' hstartLe
  have hanchorStoreSlot : (store.blocks anchor.root).slot =
      compute_start_slot_at_epoch cfg anchor.epoch := by
    rw [hanchorBlock, hboundaryEq]
  have hparentSlots : ParentSlotLt store :=
    E.store_parentSlotLt cfg ext hwf hec hgenFull
      hwf.anchor_parent_unscheduled v n
  have hwalk := E.store_walkKnownK cfg ext hwf hec hgenFull v n
    anchor.root hanchorMem (get_head cfg store).root hheadKnown
  have hwalkBoundary : WalkKnown store
      (compute_start_slot_at_epoch cfg anchor.epoch)
      (get_head cfg store).root := by
    rwa [hanchorStoreSlot] at hwalk
  have hcheckpoint := get_checkpoint_block_of_ancestor cfg hparentSlots
    hheadAnchor (Nat.le_of_eq hanchorStoreSlot.symm) hwalkBoundary
  have hself : get_checkpoint_block cfg store anchor.root anchor.epoch =
      anchor.root := by
    simp only [get_checkpoint_block]
    rw [get_ancestor_stop (Nat.le_of_eq hanchorStoreSlot)]
  have htargetRoot : target.root = anchor.root := by
    calc
      target.root = get_checkpoint_block cfg store (get_head cfg store).root
          target.epoch := rfl
      _ = get_checkpoint_block cfg store (get_head cfg store).root
          anchor.epoch := by rw [hepoch]
      _ = get_checkpoint_block cfg store anchor.root anchor.epoch := hcheckpoint
      _ = anchor.root := hself
  have htargetAnchor : target = anchor := by
    generalize ht : target = t at hepoch htargetRoot ⊢
    generalize ha : anchor = a at hepoch htargetRoot ⊢
    cases t
    cases a
    simp only at hepoch htargetRoot ⊢
    subst_vars
    rfl
  have horigins := E.globalCheckpointOrigins cfg ext hcoh
    hgenShort hanchor v n
  have hcertifiedUJ : Nonempty (CertifiedJustified cfg E anchor
      store.unrealized_justified_checkpoint) := by
    rcases horigins.unrealized_justified with hanchorUJ | ⟨r, hr, hgu⟩
    · refine ⟨?_⟩
      rw [hanchorUJ]
      exact CertifiedJustified.anchor
    · obtain ⟨hcertified⟩ := S.gu_certified cfg r
        ⟨_, E.blockAt_of_store_known cfg ext hr⟩
      refine ⟨?_⟩
      rwa [hgu]
  obtain ⟨hUJ⟩ := hcertifiedUJ
  have hUJLeTarget : store.unrealized_justified_checkpoint.epoch ≤
      target.epoch := by
    have hbound := (E.store_CkptEpochLe cfg ext hec hdiv
      hgenShort v n).2
    change store.unrealized_justified_checkpoint.epoch ≤
      compute_epoch_at_slot cfg (E.slot_at cfg n) at hbound
    exact hbound.trans_eq htargetEpoch.symm
  have hanchorLeUJ : anchor.epoch ≤
      store.unrealized_justified_checkpoint.epoch :=
    CertifiedJustified.anchor_epoch_le (cfg := cfg) hUJ
  have hUJEpoch : store.unrealized_justified_checkpoint.epoch =
      anchor.epoch :=
    Nat.le_antisymm (hUJLeTarget.trans_eq hepoch.symm) hanchorLeUJ
  have hUJRoot : store.unrealized_justified_checkpoint.root = anchor.root :=
    E.certified_justified_unique cfg ext haccountability hUJ
      CertifiedJustified.anchor hUJEpoch
  have hUJAnchor : store.unrealized_justified_checkpoint = anchor := by
    generalize hu : store.unrealized_justified_checkpoint = u
      at hUJEpoch hUJRoot ⊢
    generalize ha : anchor = a at hUJEpoch hUJRoot ⊢
    cases u
    cases a
    simp only at hUJEpoch hUJRoot ⊢
    subst_vars
    rfl
  exact hne (htargetAnchor.trans hUJAnchor.symm)

end Execution

end FastConfirmation.Spec

end
