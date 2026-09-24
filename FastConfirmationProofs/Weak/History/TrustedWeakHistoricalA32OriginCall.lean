module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32OriginCall
public import FastConfirmationProofs.Weak.History.TrustedAcceptedHistoricalA32OriginCall
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Geometry
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetCheckpointInclusionSupport

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable (E : Execution Root) {trusted : Store Root → Prop}

def TrustedLazyCertAt (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (obs : ValidatorIndex) (N : ℕ) (c : Checkpoint Root) : Prop :=
  Weak.ObserverPriorCallWriteBackSafe cfg ext E obs N →
    Nonempty (CertifiedJustified cfg E B.anchor c)

/-- Lazy support obligation at the observer, bounded by the write-back second
`N`. -/
def TrustedLazySupportAt (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (obs : ValidatorIndex) (N : ℕ) (origin : Root) (e : Epoch) : Prop :=
  ∀ w : ValidatorIndex, w ∈ E.honest → ∀ m : ℕ, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N
      (compute_start_slot_at_epoch cfg (e + 1)) →
      B.state.C origin e = B.anchor ∨
        Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B origin e)

/-- Widening the second bound weakens the obligation. -/
theorem TrustedLazyCertAt.mono {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {c : Checkpoint Root}
    (h : Weak.TrustedLazyCertAt cfg ext E B obs N c) :
    Weak.TrustedLazyCertAt cfg ext E B obs N' c :=
  fun hprior => h (hprior.mono cfg ext hNN)

/-- Widening the second bound weakens the support obligation. -/
theorem TrustedLazySupportAt.mono {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {origin : Root} {e : Epoch}
    (h : Weak.TrustedLazySupportAt cfg ext E B obs N origin e) :
    Weak.TrustedLazySupportAt cfg ext E B obs N' origin e :=
  fun w hw m hmH hlate hsupply =>
    h w hw m hmH hlate (hsupply.mono_second cfg ext hNN)

/-- Every eagerly certified payload is lazily certified. -/
theorem trusted_lazyCertAt_of_eager {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N : ℕ} {c : Checkpoint Root}
    (h : Nonempty (CertifiedJustified cfg E B.anchor c)) :
    Weak.TrustedLazyCertAt cfg ext E B obs N c :=
  fun _ => h

/-- Every eagerly supported payload is lazily supported. -/
theorem trusted_lazySupportAt_of_eager {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N : ℕ} {origin : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32DeferredSupportAt cfg ext B origin e) :
    Weak.TrustedLazySupportAt cfg ext E B obs N origin e :=
  fun w hw m hmH hlate _ => h w hw m hmH hlate

/-- The trusted-anchor payload discharges both lazy obligations outright. -/
theorem trusted_lazyCertAt_anchor {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N : ℕ} : Weak.TrustedLazyCertAt cfg ext E B obs N B.anchor :=
  fun _ => ⟨CertifiedJustified.anchor⟩

/-- The trusted-anchor support arm, recorded lazily. -/
theorem trusted_lazySupportAt_anchor {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N : ℕ} {origin : Root} {e : Epoch}
    (h : B.state.C origin e = B.anchor) :
    Weak.TrustedLazySupportAt cfg ext E B obs N origin e :=
  fun _ _ _ _ _ _ => Or.inl h

/-- The lazy support closure transports along a same-epoch segment exactly as
the eager one does. -/
theorem trusted_lazySupportAt_transport {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N : ℕ} {origin tip : Root} {e : Epoch}
    (hcheckpoint : B.state.C tip e = B.state.C origin e)
    (hsource : B.state.GJ tip = B.state.GJ origin)
    (h : Weak.TrustedLazySupportAt cfg ext E B obs N origin e) :
    Weak.TrustedLazySupportAt cfg ext E B obs N tip e :=
  fun w hw m hmH hlate hsupply =>
    Execution.TrustedAcceptedHistoricalA32GatePayloadCoreAt.quorumDisjunction_transport
      cfg ext hcheckpoint hsource (h w hw m hmH hlate hsupply)

/-- Widen a lazily instantiated payload's second bound. -/
noncomputable def trusted_observerHistoricalA32LazyPayload_mono {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {origin : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (Weak.TrustedLazyCertAt cfg ext E B obs N)
      (Weak.TrustedLazySupportAt cfg ext E B obs N)) :
    E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (Weak.TrustedLazyCertAt cfg ext E B obs N')
      (Weak.TrustedLazySupportAt cfg ext E B obs N') :=
  (h.mapCert cfg ext (fun hc => hc.mono cfg ext hNN)).mapSupp cfg ext
    (fun hs => hs.mono cfg ext hNN)

/-- Widen a lazily instantiated lineage's second bound: the weak write-back
induction's extension step. -/
noncomputable def trusted_observerHistoricalA32LazyLineage_mono {E : Execution Root}
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {tip : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Weak.TrustedLazyCertAt cfg ext E B obs N)
      (Weak.TrustedLazySupportAt cfg ext E B obs N)) :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Weak.TrustedLazyCertAt cfg ext E B obs N')
      (Weak.TrustedLazySupportAt cfg ext E B obs N') :=
  (h.mapCert cfg ext (fun _ hc => hc.mono cfg ext hNN)).mapSupp cfg ext
    (fun _ hs => hs.mono cfg ext hNN)

/-! ## The observer-side origin-call record -/


namespace ObserverHistoricalA32OriginCallAt
variable {E : Execution Root}
theorem trusted_honestVotesSupportTarget_capped
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {target : Checkpoint Root}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg
        (E.weakFcrStep cfg ext obs second).store + 1) ≤ cap) :
    HonestVotesSupportTarget cfg E target (second + 1) := by
  classical
  obtain ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgenEq, hanchorSlot, hanchorParent⟩
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgenEq⟩
  set q : ℕ := second + 1 with hq
  have hqH : E.WithinHorizon cfg q := h.second_horizon
  have hqStore : (E.weakFcrStep cfg ext obs second).store =
      E.store cfg ext obs q := E.weakFcrStep_store cfg ext obs second
  have hG := Weak.trusted_weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
    hanchor hboundary hcoh (n := second) h.second_horizon
  have hqStart : E.slot_start cfg (E.slot_at cfg q) = q :=
    E.slot_start_eq_succ_of_advance_minimal cfg ext (v := obs) hA second
      h.second_horizon h.is_call
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  have hanchorLe : ∀ (w : ValidatorIndex) (m : ℕ), B.anchor.epoch ≤
      get_current_store_epoch cfg (E.store cfg ext w m) :=
    fun w m => E.trustedAnchor_epoch_le_currentEpoch cfg ext hA hanchor
      hboundary w m
  set epochQ : Epoch :=
    get_current_store_epoch cfg (E.weakFcrStep cfg ext obs second).store
    with hepochQ
  have hanchorLeQ : B.anchor.epoch ≤ epochQ := by
    rw [hepochQ, hqStore]
    exact hanchorLe obs q
  have hqueryParent : ParentSlotLt (E.weakFcrStep cfg ext obs second).store :=
    hG.parent
  have hheadQ : (get_head cfg (E.store cfg ext obs q)).root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [← hqStore]; exact hG.head_known
  have hqueryHeadWalk : WalkKnown (E.weakFcrStep cfg ext obs second).store
      (compute_start_slot_at_epoch cfg epochQ)
      (get_head cfg (E.weakFcrStep cfg ext obs second).store).root := by
    rw [hqStore]
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      obs q (by rw [hepochQ, hqStore] at hanchorLeQ ⊢; exact hanchorLeQ)
      hheadQ
  have horiginKnownQ : origin ∈ (E.store cfg ext obs q).block_roots := by
    rw [← hqStore]; exact h.origin_known
  have hqueryWalk : WalkKnown (E.weakFcrStep cfg ext obs second).store
      (compute_start_slot_at_epoch cfg epochQ) origin := by
    rw [hqStore]
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      obs q (by rw [hepochQ, hqStore] at hanchorLeQ ⊢; exact hanchorLeQ)
      horiginKnownQ
  have hvoterHeadSlot : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      ((E.store cfg ext i k).block_states
        (get_head cfg (E.store cfg ext i k)).root).slot ≤ E.slot_at cfg k := by
    intro i hi k _hqk hHk
    have hheadK := E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
      hi k hHk
    have hstate := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen0 i k).1 _ hheadK
    simpa only [E.store_current_slot] using hstate
  have hvoterParent : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k → ParentSlotLt (E.store cfg ext i k) := by
    intro i hi k _hqk hHk
    exact (E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hgen hA.domain i hi k hHk).1
  have hvoterHeadWalk : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg epochQ)
        (get_head cfg (E.store cfg ext i k)).root := by
    intro i hi k _hqk hHk
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      i k hanchorLeQ
      (E.head_root_known_of_selectedMarginDomain cfg ext hA.domain hi k hHk)
  -- the crossing origin is one-confirmed, hence known at every later honest
  -- endpoint — honesty of the *querying* node replaced by committee readback
  have horiginKnownAt : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k → origin ∈ (E.store cfg ext i k).block_roots := by
    intro i hi k hqk hHk
    refine E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcoh.validity (hcoh.committees_agree q hqH)
      (E.weakFcrStep cfg ext obs second) hqStore origin
      hqH horiginKnownQ ?_ ?_ i hi k (E.slot_at_mono cfg hqk) hHk
    · rw [← hqStore]; exact h.origin_parent_known
    · exact h.origin_confirmed
  have hvoterWalk : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k →
      E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext i k)
        (compute_start_slot_at_epoch cfg epochQ) origin := by
    intro i hi k hqk hHk
    exact E.trustedAnchor_boundaryWalkAtEpoch cfg ext hA hanchor hboundary
      i k hanchorLeQ (horiginKnownAt i hi k hqk hHk)
  have hagree : ∀ i ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ∀ r : Root, r ∈ (E.store cfg ext i k).block_roots →
        r ∈ (E.weakFcrStep cfg ext obs second).store.block_roots →
        (E.store cfg ext i k).blocks r =
          (E.weakFcrStep cfg ext obs second).store.blocks r := by
    intro i _hi k _hqk _hHk r hrK hrQ
    rw [hqStore] at hrQ ⊢
    exact hA.wellFormed.blocks_agree (E.blockProvenance cfg ext i k)
      (E.blockProvenance cfg ext obs q) hrK hrQ
  have hsupport := E.honestVotesSupportTarget_of_engineInv_currentEpochCandidate
    cfg ext hA.honest_behavior hA.externals_coherence.process_slots_slot
    hA.whole_seconds hgenTime
    (query := E.weakFcrStep cfg ext obs second) (b := origin) (q := q)
    hqH hqStart heng hcap hqueryParent h.head_descends h.origin_current
    hqueryHeadWalk hqueryWalk hvoterHeadSlot hvoterParent hvoterHeadWalk
    hvoterWalk hagree
  rw [h.target_eq] at hsupport
  exact hsupport

/-- Recover the origin call's safety from the threaded weak fold output.

The strong twin has to pick the origin node out of `∀ i ∈ E.honest` and then
discharge the strictness side condition; the weak predicate is single-node and
unconditional, so this is a direct application. -/
theorem trusted_safeFrom_of_prior {obs : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      target)
    {n : ℕ} (hlt : second < n)
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n) :
    E.SafeFrom cfg ext origin (second + 1) := by
  have hsafe := hprior second hlt h.second_horizon h.is_call
  rwa [h.origin_writeback] at hsafe

/-- **The fixed-source gate realization at the observer's crossing call**, run
from the rebuilt proviso.  The producer is the unchanged strong one. -/
theorem trusted_fixedSourceGateRealization_capped
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {target : Checkpoint Root}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg
        (E.weakFcrStep cfg ext obs second).store + 1) ≤ cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Execution.TrustedAcceptedFixedSourceCurrentTargetA32GateRealization cfg ext
      B.anchor B.state (E.weakFcrStep cfg ext obs second).store origin := by
  refine hproducer h.gate ?_
  rw [h.target_eq]
  exact h.trusted_honestVotesSupportTarget_capped cfg ext B hT hA hanchor hboundary
    hcoh heng hcap

/-- The certificate half of the lazy payload at the observer. -/
theorem trusted_certifiedFixedSource_capped
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {target : Checkpoint Root}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg
        (E.weakFcrStep cfg ext obs second).store + 1) ≤ cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Nonempty (CertifiedJustified cfg E B.anchor target) := by
  have hreal := h.trusted_fixedSourceGateRealization_capped cfg ext B hT hA hanchor
    hboundary hcoh heng hcap hproducer
  have hcert := hreal.certified
  rwa [h.target_eq] at hcert

/-- The support half of the lazy payload at the observer. -/
theorem trusted_deferredSupport_capped
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {e : Epoch}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      (B.state.C origin e))
    (horiginEpoch : get_block_epoch cfg
      (E.weakFcrStep cfg ext obs second).store origin = e)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg
        (E.weakFcrStep cfg ext obs second).store + 1) ≤ cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    B.state.C origin e = B.anchor ∨
      Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B origin e) := by
  have hreal := h.trusted_fixedSourceGateRealization_capped cfg ext B hT hA hanchor
    hboundary hcoh heng hcap hproducer
  exact
    Execution.TrustedAcceptedHistoricalA32GatePayloadCoreAt.eagerSupport_of_fixedSourceCurrentTarget
      cfg ext B horiginEpoch h.target_eq hreal

/-- **The lazy certificate closure at the observer's crossing call.**
Discharged by `hprior` at the consuming call, which is legitimate exactly when
the origin call sits strictly below the bound. -/
theorem trusted_lazyCert
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {e : Epoch}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      (B.state.C origin e))
    {N : ℕ} (hlt : second < N)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Weak.TrustedLazyCertAt cfg ext E B obs N (B.state.C origin e) := by
  intro hprior
  exact h.trusted_certifiedFixedSource_capped cfg ext B hT hA hanchor hboundary hcoh
    (E.engineInv_of_safeFrom cfg ext
      (h.trusted_safeFrom_of_prior cfg ext hlt hprior)) (le_refl _) hproducer

/-- **The lazy support closure at the observer's crossing call.** -/
theorem trusted_lazySupport
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {e : Epoch}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      (B.state.C origin e))
    (horiginEpoch : get_block_epoch cfg
      (E.weakFcrStep cfg ext obs second).store origin = e)
    {N : ℕ} (hle : second + 1 ≤ N)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Weak.TrustedLazySupportAt cfg ext E B obs N origin e := by
  intro w hw m hmH _hlate hsupply
  have hcurrent : get_current_store_epoch cfg
      (E.weakFcrStep cfg ext obs second).store = e :=
    h.origin_current.symm.trans horiginEpoch
  have heng0 := hsupply second hle h.second_horizon h.is_call
  have heng : EngineInv cfg ext E origin (second + 1)
      (compute_start_slot_at_epoch cfg (e + 1)) := by
    rwa [h.origin_writeback] at heng0
  have hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg
        (E.weakFcrStep cfg ext obs second).store + 1) ≤
      compute_start_slot_at_epoch cfg (e + 1) := by
    rw [hcurrent]
  exact h.trusted_deferredSupport_capped cfg ext B hT hA hanchor hboundary hcoh
    horiginEpoch heng hcap hproducer

end ObserverHistoricalA32OriginCallAt
end Weak
end FastConfirmation.Spec
end
