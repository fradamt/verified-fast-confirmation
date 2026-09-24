module
public import FastConfirmationProofs.FFG.SourceHistory.FFGJustifiedMaximality
public import FastConfirmationProofs.Weak.Certificates.WeakBankedJustification
public import FastConfirmationProofs.Weak.History.WeakCandidateHistoryRecurrence

@[expose] public section

/-!
# Spec / Proof / WeakObservedRestartAdoption

Stage 2 of the **weak full-rule** effort (`docs/weak-full-rule.md`): the weak
twin of `Execution.ActualFCRGuardedObservedAdoption`
(`AcceptedObservedRestartAdoption.lean`) — *the banked observed checkpoint's
epoch is at most every in-horizon honest endpoint's realized justified epoch at
the call second*, with the querying node's honesty binder dropped.

## What the strong proof spends honesty on, and what replaces it

The strong adoption lemma reads the observed field's installation provenance off
`AcceptedUJCacheInstallationAt` (`anchor ∨ GU carrier`) and then relays the GU
carrier tip from the *querying node's own store* to every honest endpoint with
`NextSlotSynchronyPremises.block_relay`, which needs that node to be honest.  Rule
delta 5 replaces the provenance record and the relay in one move: the gated
epoch-start write banks `store.unrealized_justifications (get_head store).root`
for a head that carries a broadcast certificate, so

* the provenance is the certificate's own `banked_eq` — the banked checkpoint
  *is* the supplier's `GU` (`Execution.accepted_unrealized_justification_eq`,
  node-generic), so the carrier is the certified head rather than a cache
  ancestor; and
* the relay is `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`,
  i.e. `Execution.certificate_dissemination` at the supplier.

Everything downstream of those two — `AcceptedOldGURealized.oldGU` at the
endpoint, via `CausalPrefixFFGInterpretation`'s justified maximality — already
quantifies only over the *receiving* endpoint's causal store, which the weak
model keeps.

## The temporal carry (installation second → call second)

The banked value is installed at an epoch boundary `h.second ≤ n + 1`, possibly
many seconds before the call, and the strong argument's "the carrier predates
the boundary" step is what has to be re-obtained across that gap.  It is
supplied here by the certificate's own span, not by a new bridge:

* `Weak.BankedJustificationCertificate.supplier_slot_lt` (new, this file) —
  `has_carrier_broadcast_certificate` fixes the certificate's end slot at
  `get_current_slot store - 1`, so `Weak.has_broadcast_certificate_span_nonempty`
  plus the structure's `second_pos` fill put the supplier's block *strictly*
  below the banking second's own slot.  This is the observation the
  `has_broadcast_certificate_span_nonempty` docstring anticipates ("what makes
  the certified head a pre-boundary block"), used here for the first time.
* `Execution.slot_at_mono` then carries that slot bound forward from `h.second`
  to the call second, and the same `h.second_le`/`slot_at_mono` pair discharges
  the dissemination gate `E.slot_at h.second ≤ E.slot_at m` of the consumption
  lemma.  No new temporal bridge is needed.

Only the **certified arm** of `Weak.CertifiedBankedJustification` is treated
here.  The anchor arm carries no supplier and no epoch bound at all; it is
closed on the safety side instead, by stage 3
(`WeakObservedRestartDynamicSafety.lean`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## The certified supplier is a pre-boundary block -/

/-- **The banked justification's supplier is strictly older than its own
banking second.** `has_carrier_broadcast_certificate` evaluates the certificate on
the span `[get_block_slot store supplier, get_current_slot store - 1]`, and a
true certificate has a non-empty span
(`Weak.has_broadcast_certificate_span_nonempty`), so the supplier's block slot
is at most `get_current_slot store - 1`; the structure's `second_pos` fill turns
that into a strict inequality against the banking second's own slot.

This is the weak replacement for the strong adoption proof's
`htipSlotLtBoundary`, which reads the carrier's age off the *cache
installation's* second instead. -/
theorem BankedJustificationCertificate.supplier_slot_lt
    {E : Execution Root} {obs : ValidatorIndex} {n : ℕ}
    {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store) :
    get_block_slot (E.store cfg ext obs h.second) h.supplier <
      E.slot_at cfg h.second := by
  have hcert : Weak.has_broadcast_certificate cfg ext
      (E.store cfg ext obs h.second) h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1) = true := by
    have hc := h.certificate
    exact hc
  have hspan := Weak.has_broadcast_certificate_span_nonempty cfg ext hcert
  have hpos := h.second_pos
  have hslotEq : E.slot_at cfg h.second =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    (E.store_current_slot cfg ext obs h.second).symm
  have hend : get_current_slot cfg (E.store cfg ext obs h.second) - 1 <
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos) Nat.zero_lt_one
  rw [hslotEq]
  exact Nat.lt_of_le_of_lt hspan hend

/-! ## The adoption law -/

/-- **Boundary adoption from a banked justification certificate.** The banked
checkpoint's epoch is at most the realized justified epoch of every in-horizon
honest endpoint, at any second `m` whose slot is an epoch start at or after the
banking second's slot.

Weak twin of the conclusion of
`Execution.ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption`,
with the querying node's honesty dropped: the strong proof's two uses of that
node — relaying the carrier tip and reading the cache installation's origin —
are replaced by `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`
(certificate dissemination) and the certificate's own `banked_eq`.

Like the strong lemma the conclusion is deliberately only an epoch inequality:
it orders no checkpoint roots and does not itself imply any head or `SafeFrom`
statement. -/
theorem bankedCheckpoint_epoch_le_honestJustified
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : E.slot_at cfg h.second ≤ E.slot_at cfg m)
    (hstart : is_start_slot_at_epoch cfg (E.slot_at cfg m) = true) :
    fcr_store.current_epoch_observed_justified_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch := by
  obtain ⟨ast, ablk, hgeq, hslotEq, _hparentNe⟩ := hT.genesis_structure
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgeq, hslotEq⟩
  -- The certified supplier reaches the endpoint by certificate dissemination.
  have hsupplierW : h.supplier ∈ (E.store cfg ext w m).block_roots :=
    (Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA B hT
      hanchor hboundary hsync  hA.genesis hcomm h hw hmH hgate).1
  -- The banked checkpoint *is* that supplier's own `GU`.
  have hGU : fcr_store.current_epoch_observed_justified_checkpoint =
      B.state.GU h.supplier := by
    rw [h.banked_eq]
    exact E.accepted_unrealized_justification_eq
      B.coherence.toFFGSelectorsMatchBeaconStates obs h.second h.supplier_known
  -- The supplier predates the boundary, at the endpoint's own store.
  have hblocksAgree : (E.store cfg ext obs h.second).blocks h.supplier =
      (E.store cfg ext w m).blocks h.supplier :=
    hT.wellFormed.blocks_agree (E.blockProvenance cfg ext obs h.second)
      (E.blockProvenance cfg ext w m) h.supplier_known hsupplierW
  have hsupplierSlotLt :
      ((E.store cfg ext w m).blocks h.supplier).slot < E.slot_at cfg m := by
    have hlt := Weak.BankedJustificationCertificate.supplier_slot_lt cfg ext h
    simp only [get_block_slot, hblocksAgree] at hlt
    exact hlt.trans_le hgate
  have hcurrentEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      compute_epoch_at_slot cfg (E.slot_at cfg m) := by
    simp only [get_current_store_epoch, E.store_current_slot]
  have hstartZero : compute_slots_since_epoch_start cfg (E.slot_at cfg m) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundary : E.slot_at cfg m =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg m)) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hold : get_block_epoch cfg (E.store cfg ext w m) h.supplier <
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    rw [hcurrentEpoch]
    rw [hslotBoundary] at hsupplierSlotLt
    simp only [get_block_epoch, compute_epoch_at_slot]
    exact (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2 hsupplierSlotLt
  -- The endpoint's own realized justified maximum has already absorbed it.
  have hendpoint : E.CausalStore cfg ext (E.store cfg ext w m) :=
    E.store_causal cfg ext w m
  have hmax := hendpoint.acceptedFFGJustifiedMaximality
    B hT.whole_seconds hgenShort hanchor
  have hcarrier : E.AcceptedCarrierIn (cfg := cfg) (ext := ext)
      (E.store cfg ext w m) h.supplier :=
    Execution.AcceptedCarrierIn.of_causal_known hendpoint hsupplierW
  rw [hGU]
  exact hmax.oldGU h.supplier hcarrier hold

/-! ## The call-indexed form -/

/-- **Boundary adoption, scoped to an actual weak epoch-start restart.** Weak
twin of `Execution.ActualFCRGuardedObservedAdoption`, at the weak query store
`E.weakFcrStep` and at an observer carrying no honesty binder. -/
def GuardedObservedAdoption (E : Execution Root) (obs : ValidatorIndex)
    (n : ℕ) : Prop :=
  ∀ w ∈ E.honest, E.WithinHorizon cfg (n + 1) →
    (E.weakFcrStep cfg ext obs n
      ).current_epoch_observed_justified_checkpoint.epoch ≤
      (E.store cfg ext w (n + 1)).justified_checkpoint.epoch

/-- **The weak observed-reset branch's boundary adoption**, from the banking
certificate the trajectory already maintains
(`Weak.weakFcr_certifiedBankedJustification`, certified arm) plus the branch's
own epoch-start conjunct.

Weak twin of
`Execution.ObservedResetCandidateInputAt.actualFCRGuardedObservedAdoption`. The
epoch-start hypothesis of `bankedCheckpoint_epoch_le_honestJustified` is read
off `Weak.ObservedResetCandidateInputAt.epoch_start`, and the dissemination
gate off the certificate's `second_le` — the temporal carry from the
installation second to the call second is exactly `Execution.slot_at_mono`. -/
theorem ObservedResetCandidateInputAt.guardedObservedAdoption
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (hsync : NextSlotSynchronyPremises cfg ext E)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ}
    {trace : Weak.LatestConfirmedCallTrace cfg ext (E.weakFcrStep cfg ext obs n)}
    (hinput : Weak.ObservedResetCandidateInputAt cfg ext
      (E.weakFcrStep cfg ext obs n) trace)
    (hcert : Weak.BankedJustificationCertificate cfg ext E obs (n + 1)
      (E.weakFcrStep cfg ext obs n)) :
    Weak.GuardedObservedAdoption cfg ext E obs n := by
  intro w hw hHn1
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.weakFcrStep_store, E.store_current_slot] using hinput.epoch_start
  exact Weak.bankedCheckpoint_epoch_le_honestJustified cfg ext hA B hT hanchor
    hboundary hsync  hcomm hcert hw hHn1
    (E.slot_at_mono cfg hcert.second_le) hstart

end Weak

end FastConfirmation.Spec

end
