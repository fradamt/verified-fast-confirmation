module
public import FastConfirmationProofs.Weak.History.AcceptedHistoricalA32OriginCall
public import FastConfirmationProofs.Execution.History.TrustedHistoricalCheckpointInclusionPayload
public import FastConfirmationProofs.FFG.CurrentTarget.TrustedCurrentTargetCheckpointInclusionSupport

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root) {trusted : Store Root → Prop}
namespace AcceptedHistoricalA32OriginCallAt

theorem trusted_gateRealization_capped
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext node second).store + 1) ≤
      cap)
    (hproducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S (second + 1) (E.fcrStoreAtCall cfg ext node second)) :
    TrustedAcceptedCurrentTargetA32GateRealization cfg ext anchor S
      (E.fcrStoreAtCall cfg ext node second).store := by
  refine hproducer h.gate ?_
  rw [h.target_eq]
  exact h.honestVotesSupportTarget_capped cfg ext E hA hanchor hboundary heng
    hcap

/-- Uncapped form, unchanged. -/
theorem trusted_gateRealization
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    (hsafe : E.SafeFrom cfg ext origin (second + 1))
    (hproducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S (second + 1) (E.fcrStoreAtCall cfg ext node second)) :
    TrustedAcceptedCurrentTargetA32GateRealization cfg ext anchor S
      (E.fcrStoreAtCall cfg ext node second).store :=
  h.trusted_gateRealization_capped cfg ext E hA hanchor hboundary
    (E.engineInv_of_safeFrom cfg ext hsafe) (le_refl _) hproducer

/-- **The fixed-source twin.**  Same reconstruction, run against the
*fixed-source* producer, which is the one the crossing branch actually holds
(`AcceptedHistoricalA32Crossing.lean`).  Its output carries both payload
obligations at once: the certificate and the anchor-or-quorum disjunction. -/
theorem trusted_fixedSourceGateRealization_capped
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext node second).store + 1) ≤
      cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext anchor S (second + 1) (E.fcrStoreAtCall cfg ext node second) origin) :
    TrustedAcceptedFixedSourceCurrentTargetA32GateRealization cfg ext anchor S
      (E.fcrStoreAtCall cfg ext node second).store origin := by
  refine hproducer h.gate ?_
  rw [h.target_eq]
  exact h.honestVotesSupportTarget_capped cfg ext E hA hanchor hboundary heng
    hcap

/-- **A3, second half** — the certificate the two `currentHistorical` arms
actually read, rebuilt at the consuming call.

`docs/trunkA-final-discharge.md` §1: the only thing either arm extracts from
the payload's old `certified` field is
`Nonempty (CertifiedJustified anchor T)`, consumed once by
`CertificateAccountability.justified_unique`.  This produces exactly that, from
origin-call data plus the origin's safety. -/
theorem trusted_certified
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    (hsafe : E.SafeFrom cfg ext origin (second + 1))
    (hproducer : E.TrustedAcceptedCurrentTargetA32GateRealizationProducerAt cfg ext
      anchor S (second + 1) (E.fcrStoreAtCall cfg ext node second)) :
    Nonempty (CertifiedJustified cfg E anchor target) := by
  have hreal := h.trusted_gateRealization cfg ext E hA hanchor hboundary hsafe hproducer
  have hcert := hreal.certified
  rwa [h.target_eq] at hcert

/-- **T4c, the certificate half of the lazy payload.**  The capped
fixed-source realization's certificate, re-indexed by the retained
checkpoint. -/
theorem trusted_certifiedFixedSource_capped
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {node : ValidatorIndex} {second : ℕ} {origin : Root}
    {target : Checkpoint Root}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin target)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext node second).store + 1) ≤
      cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext anchor S (second + 1) (E.fcrStoreAtCall cfg ext node second) origin) :
    Nonempty (CertifiedJustified cfg E anchor target) := by
  have hreal := h.trusted_fixedSourceGateRealization_capped cfg ext E hA hanchor
    hboundary heng hcap hproducer
  have hcert := hreal.certified
  rwa [h.target_eq] at hcert

/-- **T4c, the support half of the lazy payload.**

Origin-call data plus *capped* safety at the origin rebuilds the retained
anchor-or-quorum disjunction at the crossing call, through the unchanged
fixed-source gate realization and the unchanged dependent rewriting of
`TrustedAcceptedHistoricalA32GatePayloadCoreAt.eagerSupport_of_fixedSourceCurrentTarget`.
This is what the lazy `Supp` closure evaluates to once its antecedent is
discharged at the consuming call. -/
theorem trusted_deferredSupport_capped
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {node : ValidatorIndex} {second : ℕ} {origin : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin
      (B.state.C origin e))
    (horiginEpoch : get_block_epoch cfg
      (E.fcrStoreAtCall cfg ext node second).store origin = e)
    {cap : Slot}
    (heng : EngineInv cfg ext E origin (second + 1) cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext node second).store + 1) ≤
      cap)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1) (E.fcrStoreAtCall cfg ext node second)
      origin) :
    B.state.C origin e = B.anchor ∨
      Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B origin e) := by
  have hreal := h.trusted_fixedSourceGateRealization_capped cfg ext E hA hanchor
    hboundary heng hcap hproducer
  exact
    TrustedAcceptedHistoricalA32GatePayloadCoreAt.eagerSupport_of_fixedSourceCurrentTarget
      cfg ext B horiginEpoch h.target_eq hreal


end AcceptedHistoricalA32OriginCallAt

def TrustedLazyCertAt (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (N : ℕ) (c : Checkpoint Root) : Prop :=
  E.PriorStrictCallWriteBackSafe cfg ext N →
    Nonempty (CertifiedJustified cfg E B.anchor c)

/-- Lazy support obligation, bounded by the owning validator `v` and the
write-back second `N`.

The antecedent is the *capped* supply at the epoch boundary `start(e + 1)`,
which `docs/crossing-call-support-residue.md` §2.3 shows is exactly enough:
every vote the A3.2 quorum consumes is cast at a slot of epoch `e`, hence
strictly below that boundary.  The single `support_branch` consumer (A1,
`TrustedAcceptedHistoricalA32LineageAt.lateVisibleSeedAt`) is guarded by
`e + 2 ≤ currentEpoch`, and under that guard the endpoint induction's own
`SelectedCanonicalBeforeEndpointAt` binder supplies exactly this cap — see
`engineInv_of_selectedCanonical_lateEndpoint`.

(The cap is `start(e + 1)` and **not** `slot_at m`: the endpoint binder is
strict below `slot_at m`, so `slot_at m` itself is not available.  §2.3's own
arithmetic already uses the boundary form.) -/
def TrustedLazySupportAt (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (v : ValidatorIndex) (N : ℕ) (origin : Root) (e : Epoch) : Prop :=
  ∀ w : ValidatorIndex, w ∈ E.honest → ∀ m : ℕ, E.WithinHorizon cfg m →
    e + 2 ≤ get_current_store_epoch cfg (E.store cfg ext w m) →
    E.CallWriteBackEngineSafeUpTo cfg ext v N
      (compute_start_slot_at_epoch cfg (e + 1)) →
      B.state.C origin e = B.anchor ∨
        Nonempty (E.TrustedAcceptedHistoricalA32QuorumAt cfg ext B origin e)

/-- Widening the second bound weakens the obligation, because both antecedents
are anti-monotone in it.  This is what the write-back induction's extension
step uses. -/
theorem TrustedLazyCertAt.mono {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {N N' : ℕ} (hNN : N ≤ N') {c : Checkpoint Root}
    (h : E.TrustedLazyCertAt cfg ext B N c) : E.TrustedLazyCertAt cfg ext B N' c :=
  fun hprior => h (hprior.mono cfg ext E hNN)

/-- Widening the second bound weakens the support obligation. -/
theorem TrustedLazySupportAt.mono {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N N' : ℕ} (hNN : N ≤ N') {origin : Root} {e : Epoch}
    (h : E.TrustedLazySupportAt cfg ext B v N origin e) :
    E.TrustedLazySupportAt cfg ext B v N' origin e :=
  fun w hw m hmH hlate hsupply =>
    h w hw m hmH hlate (hsupply.mono_second cfg ext E hNN)

/-- Every eagerly certified payload is lazily certified. -/
theorem trusted_lazyCertAt_of_eager {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {N : ℕ} {c : Checkpoint Root}
    (h : Nonempty (CertifiedJustified cfg E B.anchor c)) :
    E.TrustedLazyCertAt cfg ext B N c :=
  fun _ => h

/-- Every eagerly supported payload is lazily supported. -/
theorem trusted_lazySupportAt_of_eager {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N : ℕ} {origin : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32DeferredSupportAt cfg ext B origin e) :
    E.TrustedLazySupportAt cfg ext B v N origin e :=
  fun w hw m hmH hlate _ => h w hw m hmH hlate

/-- The trusted-anchor payload discharges both lazy obligations outright. -/
theorem trusted_lazyCertAt_anchor {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {N : ℕ} : E.TrustedLazyCertAt cfg ext B N B.anchor :=
  fun _ => ⟨CertifiedJustified.anchor⟩

/-- The trusted-anchor support arm, recorded lazily. -/
theorem trusted_lazySupportAt_anchor {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N : ℕ} {origin : Root} {e : Epoch}
    (h : B.state.C origin e = B.anchor) :
    E.TrustedLazySupportAt cfg ext B v N origin e :=
  fun _ _ _ _ _ _ => Or.inl h

/-- The lazy support closure transports along a same-epoch segment exactly as
the eager one does: only the anchor-or-quorum disjunction moves, and the
antecedent does not mention the origin root. -/
theorem trusted_lazySupportAt_transport
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N : ℕ} {origin tip : Root} {e : Epoch}
    (hcheckpoint : B.state.C tip e = B.state.C origin e)
    (hsource : B.state.GJ tip = B.state.GJ origin)
    (h : E.TrustedLazySupportAt cfg ext B v N origin e) :
    E.TrustedLazySupportAt cfg ext B v N tip e :=
  fun w hw m hmH hlate hsupply =>
    TrustedAcceptedHistoricalA32GatePayloadCoreAt.quorumDisjunction_transport cfg ext
      hcheckpoint hsource (h w hw m hmH hlate hsupply)

/-- Widen a lazily instantiated payload's second bound. -/
noncomputable def trusted_acceptedHistoricalA32LazyPayload_mono
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N N' : ℕ} (hNN : N ≤ N')
    {origin : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (E.TrustedLazyCertAt cfg ext B N) (E.TrustedLazySupportAt cfg ext B v N)) :
    E.TrustedAcceptedHistoricalA32GatePayloadCoreAt cfg ext B origin e
      (E.TrustedLazyCertAt cfg ext B N') (E.TrustedLazySupportAt cfg ext B v N') :=
  (h.mapCert cfg ext (fun hc => hc.mono cfg ext E hNN)).mapSupp cfg ext
    (fun hs => hs.mono cfg ext E hNN)

/-- Widen a lazily instantiated lineage's second bound.  This is the write-back
induction's extension step: moving from `N = n` to `N = n + 1` is *weakening*,
because both closures' antecedents are anti-monotone in the bound. -/
noncomputable def trusted_acceptedHistoricalA32LazyLineage_mono
    {B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted}
    {v : ValidatorIndex} {N N' : ℕ} (hNN : N ≤ N')
    {tip : Root} {e : Epoch}
    (h : E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (E.TrustedLazyCertAt cfg ext B N) (E.TrustedLazySupportAt cfg ext B v N)) :
    E.TrustedAcceptedHistoricalA32LineageCoreAt cfg ext B tip e
      (E.TrustedLazyCertAt cfg ext B N') (E.TrustedLazySupportAt cfg ext B v N') :=
  (h.mapCert cfg ext (fun _ hc => hc.mono cfg ext E hNN)).mapSupp cfg ext
    (fun _ hs => hs.mono cfg ext E hNN)


namespace AcceptedHistoricalA32OriginCallAt
theorem trusted_lazyCert
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {node : ValidatorIndex} {second : ℕ} {origin : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin
      (B.state.C origin e))
    {N : ℕ} (hlt : second < N)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1) (E.fcrStoreAtCall cfg ext node second)
      origin) :
    E.TrustedLazyCertAt cfg ext B N (B.state.C origin e) := by
  intro hprior
  exact h.trusted_certifiedFixedSource_capped cfg ext E hA hanchor hboundary
    (E.engineInv_of_safeFrom cfg ext
      (h.safeFrom_of_prior cfg ext E hlt hprior)) (le_refl _) hproducer

/-- **The lazy support closure at a crossing call.**

The consuming call instantiates the capped supply at `k := second`, which the
bound `second + 1 ≤ N` permits; `origin_writeback` turns the fold output into
`EngineInv origin (second + 1) (slot_at m)`, and the `e + 2` guard makes
`start(e + 1) < start(e + 2) ≤ slot_at m`, so the cap dominates the whole
epoch-`e` vote span. -/
theorem trusted_lazySupport
    (hA : SelectedMarginAssumptions cfg ext E)
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {node : ValidatorIndex} {second : ℕ} {origin : Root} {e : Epoch}
    (h : E.AcceptedHistoricalA32OriginCallAt cfg ext node second origin
      (B.state.C origin e))
    (horiginEpoch : get_block_epoch cfg
      (E.fcrStoreAtCall cfg ext node second).store origin = e)
    {N : ℕ} (hle : second + 1 ≤ N)
    (hproducer : E.TrustedAcceptedFixedSourceCurrentTargetA32GateRealizationProducerAt
      cfg ext B.anchor B.state (second + 1) (E.fcrStoreAtCall cfg ext node second)
      origin) :
    E.TrustedLazySupportAt cfg ext B node N origin e := by
  intro w hw m hmH _hlate hsupply
  -- the origin call's store is current at epoch `e`
  have hcurrent : get_current_store_epoch cfg
      (E.fcrStoreAtCall cfg ext node second).store = e :=
    h.origin_current.symm.trans horiginEpoch
  -- the capped fold supply at the origin call's own second
  have heng0 := hsupply second hle h.second_horizon h.is_call
    (by rw [h.origin_writeback]; exact h.origin_strict)
  have heng : EngineInv cfg ext E origin (second + 1)
      (compute_start_slot_at_epoch cfg (e + 1)) := by
    rwa [h.origin_writeback] at heng0
  have hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.fcrStoreAtCall cfg ext node second).store + 1) ≤
      compute_start_slot_at_epoch cfg (e + 1) := by
    rw [hcurrent]
  exact h.trusted_deferredSupport_capped cfg ext E hA B hanchor hboundary
    horiginEpoch heng hcap hproducer

end AcceptedHistoricalA32OriginCallAt
end Execution
end FastConfirmation.Spec
end
