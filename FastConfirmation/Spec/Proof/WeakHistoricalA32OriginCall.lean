import FastConfirmation.Spec.Proof.AcceptedHistoricalA32OriginCall
import FastConfirmation.Spec.Proof.WeakFCRCallContracts
import FastConfirmation.Spec.Proof.WeakHistoricalA32Geometry

/-!
# Spec / Proof / WeakHistoricalA32OriginCall

Observer-side twin of the strong lazy-crossing plumbing in
`AcceptedHistoricalA32OriginCall.lean`, `docs/weak-final-wave.md` §3.2.

This module sits *below* the whole weak A3.2 stack, because the predicate it
defines is what the weak strict-edge dispatcher and the weak write-back
induction both consume.  It therefore imports only `weakConfirmed`'s defining
module and the strong origin-call file it mirrors.

## Why the weak predicate is simpler than the strong one

`Execution.PriorStrictCallWriteBackSafe` carries two things the weak twin does
not need:

* a quantifier `∀ i ∈ E.honest` — the weak trajectory is about **one** fixed
  observer, so the weak predicate is single-node by construction, and the
  strong proof's "pick the origin node out of the honest quantifier" step
  (`AcceptedHistoricalA32OriginCallAt.safeFrom_of_prior`) disappears; and
* the strictness conjunct
  `E.confirmed v (k + 1) ≠ (E.getLatestConfirmedTraceAt v k).afterObserved`.

The strictness conjunct is a *strong-side artefact*
(`docs/weak-final-wave.md` §3.2, correcting
`docs/crossing-call-support-residue.md` §9.1's Correction to A4).  On the
strong side the `finalizedResetUnchanged` arm recovers safety only through
`finalizedReset_safeFrom_of_nextSlotSynchrony`, which genuinely needs
`slot_at (n + 1) + 1 ≤ slot_at q` and so fails at `q = n + 1`.  The weak fold
has no such arm: `Execution.weak_safeFrom_observerCall_closed` closes **all
four** branches of `Weak.GetLatestConfirmedTrace.candidateHistoryCallBranch`
unconditionally, because the weak fold hands it `hbase` at
`slot_start (slot_at (n + 1)) = n + 1`.  So the weak call step already proves
the unweakened `SafeFrom trace.result (n + 1)` on every branch and merely
throws it away; `Weak.ObserverFoldSafetyAt` keeps it, with no side condition.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable (E : Execution Root)

/-- **The threaded weak fold output the lazy A3.2 transport consumes.**

Every weak FCR call of the observer at a second *strictly below* `n` writes
back a root that is safe from its own write-back second — the **unweakened**
`slot_start`-indexed deadline, not the `followingSlotStart`-mono'd one.

This is exactly the `callSecond` component of `Weak.ObserverFoldSafetyAt`
(`WeakTrajectorySafety.lean`) at the seconds `k + 1 ≤ n`, i.e. precisely what
the weak fold's strengthened induction hypothesis hands out at its `succ n`
step.  Well-foundedness is the strict `k < n`. -/
def ObserverPriorCallWriteBackSafe (obs : ValidatorIndex) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → E.WithinHorizon cfg (k + 1) →
    E.IsFCRCallAt cfg ext obs k →
      E.SafeFrom cfg ext (E.weakConfirmed cfg ext obs (k + 1)) (k + 1)

/-- Monotonicity in the horizon: a wider prior window restricts. -/
theorem ObserverPriorCallWriteBackSafe.mono {E : Execution Root}
    {obs : ValidatorIndex} {n m : ℕ} (hnm : n ≤ m)
    (h : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs m) :
    Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hnm)

/-- **Capped, second-bounded call-safety supply at the observer.**

Weak twin of `Execution.CallWriteBackEngineSafeUpTo`, with the same design: the
bound is `k + 1 ≤ N` rather than `k < N`, so at `N := n + 1` it reaches the
consuming call's own second, and the closure is handed this antecedent
*hypothetically* at construction time. -/
def ObserverCallWriteBackEngineSafeUpTo (obs : ValidatorIndex) (N : ℕ)
    (cap : Slot) : Prop :=
  ∀ k : ℕ, k + 1 ≤ N → E.WithinHorizon cfg (k + 1) →
    E.IsFCRCallAt cfg ext obs k →
      EngineInv cfg ext E (E.weakConfirmed cfg ext obs (k + 1)) (k + 1) cap

/-- Anti-monotone in the second bound: a supply reaching further restricts. -/
theorem ObserverCallWriteBackEngineSafeUpTo.mono_second {E : Execution Root}
    {obs : ValidatorIndex} {N N' : ℕ} {cap : Slot} (hNN : N ≤ N')
    (h : Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N' cap) :
    Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N cap :=
  fun k hk => h k (Nat.le_trans hk hNN)

/-- Monotone downward in the slot cap. -/
theorem ObserverCallWriteBackEngineSafeUpTo.mono_cap {E : Execution Root}
    {obs : ValidatorIndex} {N : ℕ} {cap cap' : Slot} (hcap : cap' ≤ cap)
    (h : Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N cap) :
    Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N cap' :=
  fun k hk hkH hcall => EngineInv.mono cfg ext (h k hk hkH hcall) hcap

/-- **The consumer-side discharge.**  At the observer's call for second `n` the
bound `N := n + 1` splits into the strictly prior calls — handed over by the
threaded weak fold output, uncapped, hence at every cap — and the call's own
second, which the endpoint induction supplies in capped form. -/
theorem observerCallWriteBackEngineSafeUpTo_of_prior_and_current
    {E : Execution Root} {obs : ValidatorIndex} {n : ℕ} {cap : Slot}
    (hprior : Weak.ObserverPriorCallWriteBackSafe cfg ext E obs n)
    (hcurrent : E.WithinHorizon cfg (n + 1) → E.IsFCRCallAt cfg ext obs n →
      EngineInv cfg ext E (E.weakConfirmed cfg ext obs (n + 1)) (n + 1) cap) :
    Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs (n + 1) cap := by
  intro k hk hkH hcall
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact E.engineInv_of_safeFrom cfg ext (hprior k hlt hkH hcall)
  · have hkn : k = n := Nat.le_antisymm (by omega) hge
    subst hkn
    exact hcurrent hkH hcall

/-! ## The lazy payload obligations at the observer

Weak twins of `Execution.LazyCertAt` / `Execution.LazySupportAt`.  The cap is
`start(e + 1)`, not `slot_at m`, for the reason
`docs/crossing-call-support-residue.md` §9.1 Correction 1 gives on the strong
side: the endpoint binder `SelectedCanonicalBeforeEndpointAt` is strict below
`slot_at m`. -/

/-- Lazy certification obligation at the observer, bounded by the write-back
second `N`. -/
def LazyCertAt (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (obs : ValidatorIndex) (N : ℕ) (c : Checkpoint Root) : Prop :=
  Weak.ObserverPriorCallWriteBackSafe cfg ext E obs N →
    Nonempty (CertifiedJustified cfg E B.anchor c)

/-- Lazy support obligation at the observer, bounded by the write-back second
`N`. -/
def LazySupportAt (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (obs : ValidatorIndex) (N : ℕ) (origin : Root) (e : Epoch) : Prop :=
  ∀ w : ValidatorIndex, w ∈ E.honest → ∀ m : ℕ, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    Weak.ObserverCallWriteBackEngineSafeUpTo cfg ext E obs N
      (compute_start_slot_at_epoch cfg (e + 1)) →
      B.state.C origin e = B.anchor ∨
        Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e)

/-- Widening the second bound weakens the obligation. -/
theorem LazyCertAt.mono {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {c : Checkpoint Root}
    (h : Weak.LazyCertAt cfg ext E B obs N c) :
    Weak.LazyCertAt cfg ext E B obs N' c :=
  fun hprior => h (hprior.mono cfg ext hNN)

/-- Widening the second bound weakens the support obligation. -/
theorem LazySupportAt.mono {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {origin : Root} {e : Epoch}
    (h : Weak.LazySupportAt cfg ext E B obs N origin e) :
    Weak.LazySupportAt cfg ext E B obs N' origin e :=
  fun w hw m hmH hlate hsupply =>
    h w hw m hmH hlate (hsupply.mono_second cfg ext hNN)

/-- Every eagerly certified payload is lazily certified. -/
theorem lazyCertAt_of_eager {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N : ℕ} {c : Checkpoint Root}
    (h : Nonempty (CertifiedJustified cfg E B.anchor c)) :
    Weak.LazyCertAt cfg ext E B obs N c :=
  fun _ => h

/-- Every eagerly supported payload is lazily supported. -/
theorem lazySupportAt_of_eager {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N : ℕ} {origin : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32DeferredSupportAt cfg ext B origin e) :
    Weak.LazySupportAt cfg ext E B obs N origin e :=
  fun w hw m hmH hlate _ => h w hw m hmH hlate

/-- The trusted-anchor payload discharges both lazy obligations outright. -/
theorem lazyCertAt_anchor {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N : ℕ} : Weak.LazyCertAt cfg ext E B obs N B.anchor :=
  fun _ => ⟨CertifiedJustified.anchor⟩

/-- The trusted-anchor support arm, recorded lazily. -/
theorem lazySupportAt_anchor {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N : ℕ} {origin : Root} {e : Epoch}
    (h : B.state.C origin e = B.anchor) :
    Weak.LazySupportAt cfg ext E B obs N origin e :=
  fun _ _ _ _ _ _ => Or.inl h

/-- The lazy support closure transports along a same-epoch segment exactly as
the eager one does. -/
theorem lazySupportAt_transport {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N : ℕ} {origin tip : Root} {e : Epoch}
    (hcheckpoint : B.state.C tip e = B.state.C origin e)
    (hsource : B.state.GJ tip = B.state.GJ origin)
    (h : Weak.LazySupportAt cfg ext E B obs N origin e) :
    Weak.LazySupportAt cfg ext E B obs N tip e :=
  fun w hw m hmH hlate hsupply =>
    Execution.AcceptedHistoricalA32GatePayloadCoreAt.quorumDisjunction_transport
      cfg ext hcheckpoint hsource (h w hw m hmH hlate hsupply)

/-- Widen a lazily instantiated payload's second bound. -/
noncomputable def observerHistoricalA32LazyPayload_mono {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {origin : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (Weak.LazyCertAt cfg ext E B obs N)
      (Weak.LazySupportAt cfg ext E B obs N)) :
    E.AcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (Weak.LazyCertAt cfg ext E B obs N')
      (Weak.LazySupportAt cfg ext E B obs N') :=
  (h.mapCert cfg ext (fun hc => hc.mono cfg ext hNN)).mapSupp cfg ext
    (fun hs => hs.mono cfg ext hNN)

/-- Widen a lazily instantiated lineage's second bound: the weak write-back
induction's extension step. -/
noncomputable def observerHistoricalA32LazyLineage_mono {E : Execution Root}
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E} {obs : ValidatorIndex}
    {N N' : ℕ} (hNN : N ≤ N') {tip : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Weak.LazyCertAt cfg ext E B obs N)
      (Weak.LazySupportAt cfg ext E B obs N)) :
    E.AcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (Weak.LazyCertAt cfg ext E B obs N')
      (Weak.LazySupportAt cfg ext E B obs N') :=
  (h.mapCert cfg ext (fun _ hc => hc.mono cfg ext hNN)).mapSupp cfg ext
    (fun _ hs => hs.mono cfg ext hNN)

/-! ## The observer-side origin-call record -/

/-- **The origin-call record of a weak historical A3.2 crossing.**

Weak twin of `Execution.AcceptedHistoricalA32OriginCallAt`, with two fields
deleted (`docs/weak-final-wave.md` §1, §3.2):

* `node_honest` — the observer is not honest.  All four of its strong
  consumptions have honesty-free observer substitutes: `ParentSlotLt` and head
  knownness come from the weak geometry hub
  `Weak.weakFcrStep_historicalA32QueryGeometryAt`, dissemination of the
  one-confirmed origin comes from
  `Execution.confirmed_known_at_all_honest_endpoints_at_observer` (honesty
  replaced by committee readback at the observer's own store), and picking the
  origin node out of the honest quantifier disappears because
  `Weak.ObserverPriorCallWriteBackSafe` is single-node by construction;
* `origin_strict` — the weak `callSecond` is unconditional (§3.2), so the weak
  prior-call predicate carries no strictness conjunct and nothing needs it.

Everything else is field-for-field the strong record with the evaluator swapped
to `E.weakFcrStep` / `E.weakConfirmed`. -/
structure ObserverHistoricalA32OriginCallAt (E : Execution Root)
    (obs : ValidatorIndex) (second : ℕ) (origin : Root)
    (target : Checkpoint Root) : Prop where
  second_horizon : E.WithinHorizon cfg (second + 1)
  is_call : E.IsFCRCallAt cfg ext obs second
  origin_known : origin ∈ (E.weakFcrStep cfg ext obs second).store.block_roots
  origin_parent_known :
    ((E.weakFcrStep cfg ext obs second).store.blocks origin).parent_root ∈
      (E.weakFcrStep cfg ext obs second).store.block_roots
  origin_confirmed : _root_.FastConfirmation.Spec.is_one_confirmed cfg ext
    (E.weakFcrStep cfg ext obs second).store
    (get_current_balance_source (E.weakFcrStep cfg ext obs second)) origin =
      true
  origin_current : get_block_epoch cfg
      (E.weakFcrStep cfg ext obs second).store origin =
    get_current_store_epoch cfg (E.weakFcrStep cfg ext obs second).store
  head_descends : is_ancestor (E.weakFcrStep cfg ext obs second).store
    (get_head cfg (E.weakFcrStep cfg ext obs second).store)
    (get_node_for_root origin) = true
  /-- The origin *is* the root this weak call writes back. -/
  origin_writeback : E.weakConfirmed cfg ext obs (second + 1) = origin
  gate : _root_.FastConfirmation.Spec.will_current_target_be_justified cfg ext
    (E.weakFcrStep cfg ext obs second).store = true
  target_eq : get_current_target cfg
      (E.weakFcrStep cfg ext obs second).store = target

namespace ObserverHistoricalA32OriginCallAt

variable {E : Execution Root}

/-- **The lazy reconstruction at the observer.**

Weak twin of `Execution.AcceptedHistoricalA32OriginCallAt.
honestVotesSupportTarget_capped`.  Same seventeen-hypothesis application of
`honestVotesSupportTarget_of_engineInv_currentEpochCandidate`, whose query
argument is a bare `FastConfirmationStore` with **no** honesty binder and **no**
committee-membership hypothesis on the querying node
(`docs/weak-final-wave.md` §1.1).  The three honesty-dependent supplies of the
strong proof are replaced by:

* `hparentQ` → `hG.parent`, `hheadQ` → `hG.head_known`, both from the weak
  geometry hub, which takes `hcoh : E.ObserverCoherence` instead of `hv`;
* `confirmed_known_at_all_honest_endpoints_minimal` →
  `confirmed_known_at_all_honest_endpoints_at_observer`, whose only replacement
  for `hv` is `hcomm : E.PrefixCommitteeAgreement (E.store cfg ext obs q)`,
  i.e. exactly `hcoh.committees_agree`.

The voter-side families are untouched: they are already quantified over
`E.honest`. -/
theorem honestVotesSupportTarget_capped
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
  have hG := Weak.weakFcrStep_historicalA32QueryGeometryAt cfg ext B hT
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
      obs q (hcoh.committees_agree q hqH)
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
theorem safeFrom_of_prior {obs : ValidatorIndex} {second : ℕ} {origin : Root}
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
theorem fixedSourceGateRealization_capped
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Execution.AcceptedFixedSourceCurrentTargetA32GateRealization cfg ext E
      B.anchor B.state (E.weakFcrStep cfg ext obs second).store origin := by
  refine hproducer h.gate ?_
  rw [h.target_eq]
  exact h.honestVotesSupportTarget_capped cfg ext B hT hA hanchor hboundary
    hcoh heng hcap

/-- The certificate half of the lazy payload at the observer. -/
theorem certifiedFixedSource_capped
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Nonempty (CertifiedJustified cfg E B.anchor target) := by
  have hreal := h.fixedSourceGateRealization_capped cfg ext B hT hA hanchor
    hboundary hcoh heng hcap hproducer
  have hcert := hreal.certified
  rwa [h.target_eq] at hcert

/-- The support half of the lazy payload at the observer. -/
theorem deferredSupport_capped
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    B.state.C origin e = B.anchor ∨
      Nonempty (E.AcceptedHistoricalA32QuorumAt cfg ext B origin e) := by
  have hreal := h.fixedSourceGateRealization_capped cfg ext B hT hA hanchor
    hboundary hcoh heng hcap hproducer
  exact
    Execution.AcceptedHistoricalA32GatePayloadCoreAt.eagerSupport_of_fixedSourceCurrentTarget
      cfg ext B horiginEpoch h.target_eq hreal

/-- **The lazy certificate closure at the observer's crossing call.**
Discharged by `hprior` at the consuming call, which is legitimate exactly when
the origin call sits strictly below the bound. -/
theorem lazyCert
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hA : SelectedMarginAssumptions cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {second : ℕ} {origin : Root} {e : Epoch}
    (h : Weak.ObserverHistoricalA32OriginCallAt cfg ext E obs second origin
      (B.state.C origin e))
    {N : ℕ} (hlt : second < N)
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Weak.LazyCertAt cfg ext E B obs N (B.state.C origin e) := by
  intro hprior
  exact h.certifiedFixedSource_capped cfg ext B hT hA hanchor hboundary hcoh
    (E.engineInv_of_safeFrom cfg ext
      (h.safeFrom_of_prior cfg ext hlt hprior)) (le_refl _) hproducer

/-- **The lazy support closure at the observer's crossing call.** -/
theorem lazySupport
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
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
    (hproducer : E.AcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1)
      (E.weakFcrStep cfg ext obs second) origin) :
    Weak.LazySupportAt cfg ext E B obs N origin e := by
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
  exact h.deferredSupport_capped cfg ext B hT hA hanchor hboundary hcoh
    horiginEpoch heng hcap hproducer

end ObserverHistoricalA32OriginCallAt

end Weak

end FastConfirmation.Spec
