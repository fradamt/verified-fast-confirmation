import FastConfirmation.Spec.Proof.WeakSeedDissemination
import FastConfirmation.Spec.Proof.WeakSelectedTrace
import FastConfirmation.Spec.Proof.WeakSelectorInversion
import FastConfirmation.Spec.Proof.AcceptedPhaseSourceSupply

/-!
# Spec / Proof / WeakEarlyPhaseSourceWiring

Stage S5 of the `hfilter`-discharge wave (`/tmp/hfilter-wave-design.md`): weak
twins of `AcceptedEarlyPhaseSourceWiring.lean`'s executable head-cache
knownness lemmas and of `AcceptedPhaseSourceSupply.lean`'s two actual-call
source-supply theorems (sites 3 and 6 of the wave's site inventory), all
re-indexed over `E.weakFcrStep` / `E.weakFcr` (`WeakFCRCallContracts.lean`),
per `/tmp/delta5-proposal.md` §5.

## What is delivered so far

* `Weak.weakFcr_currentSlotHead_known` / `Weak.weakFcrStep_previousSlotHead_known`
  — weak twins of `Execution.fcr_currentSlotHead_known` /
  `Execution.fcrStep_previousSlotHead_known`. The strong
  `head_root_known_of_selectedMarginDomain cfg ext hdomain hv` call is replaced
  by the honesty-free `Execution.head_root_known_at_observer`
  (`WeakObserverDomain.lean`), driven by `hcoh : E.ObserverCoherence cfg ext
  obs`; `SelectedMarginDomain` is dropped entirely from the signature (it fed
  nothing else in either strong proof).
* `Weak.fcrStep_previous_endpointRecentSourceSeed` (site 3) — weak twin of
  `StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointRecentSourceSeed`.
  The observer-as-sender `hsync.block_relay` of `previous_slot_head` is
  replaced by `Weak.witnessSeed_known_at_all_honest_endpoints_at_observer`,
  fed the certificate from `Weak.PreviousSelectedEntryWitness.witness_certificate`
  (a named field of the trace-origin's previous-loop witness, S2). Because the
  certificate lemma is anchored at the *query second itself* rather than at an
  earlier cached second, the strong proof's whole "recover `previous_slot_head`
  at `(v, n)` via `fcr_currentSlotHead_known`, then relay" detour collapses:
  `Weak.weakFcrStep_previousSlotHead_known` alone supplies the witness's
  knownness at the query second, so `hcall : E.IsFCRCallAt cfg ext obs n` and
  the `fcrStep_previousSlotHead_eq_currentSlotHead` bookkeeping step are both
  unused and dropped from the signature.

Site 6 lands in a subsequent commit.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-! ## Executable weak FCR head-cache knownness -/

/-- Weak twin of `Execution.fcr_currentSlotHead_known`. -/
theorem weakFcr_currentSlotHead_known
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) (n : Nat)
    (hH : E.WithinHorizon cfg n) :
    (E.weakFcr cfg ext obs n).current_slot_head ∈
      (E.store cfg ext obs n).block_roots := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hgen
      change (E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots)
      rw [hgenEq]
      simp [get_forkchoice_store]
  | succ n ih =>
      have hnH : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hH
      have hknownN := ih hnH
      by_cases hcall : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hhead := E.head_root_known_at_observer cfg ext hcoh (n + 1) hH
        simp only [Execution.weakFcr, hcall, if_true, Weak.on_fast_confirmation,
          Weak.update_fast_confirmation_variables]
        split_ifs <;> exact hhead
      · have hcarry :=
          (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
        simpa only [Execution.weakFcr, hcall, if_false] using hcarry

/-- Weak twin of `Execution.fcrStep_previousSlotHead_known`. -/
theorem weakFcrStep_previousSlotHead_known
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) (n : Nat)
    (hH : E.WithinHorizon cfg (n + 1)) :
    (E.weakFcrStep cfg ext obs n).previous_slot_head ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
  have hnH : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hH
  have hknownN := weakFcr_currentSlotHead_known cfg ext hgen hcoh n hnH
  have hknownN1 :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
  simp only [Execution.weakFcrStep, Weak.update_fast_confirmation_variables]
  split_ifs <;> exact hknownN1

/-! ## Site 3 — actual `weakFcrStep` previous cell, no observer relay -/

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_previous_
endpointRecentSourceSeed`. See the module docstring for the `hcall` /
`fcrStep_previousSlotHead_eq_currentSlotHead` simplification. -/
theorem StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input result : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input result)
    (hprevious : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store result + 1 =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnm : n + 1 ≤ m)
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store) :
    Execution.RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hslotForward : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    E.slot_at_mono cfg hnm
  have hselectedM : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs (n + 1) hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
      h.confirmed w hw m hslotForward hmH
  have hqueryCausal : E.CausalStore cfg ext
      (E.weakFcrStep cfg ext obs n).store := by
    rw [hqCurrent]; exact E.store_causal cfg ext obs (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis hcoh (n + 1) hn1H
  have hqueryParent : ParentSlotLt (E.weakFcrStep cfg ext obs n).store := by
    simpa only [hqCurrent] using hparentN1
  have hqueryProvenance : BlockProvenance E
      (E.weakFcrStep cfg ext obs n).store := by
    simpa only [hqCurrent] using E.blockProvenance cfg ext obs (n + 1)
  have hqueryWalk : ∀ t ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
      ∀ r ∈ (E.weakFcrStep cfg ext obs n).store.block_roots,
        WalkKnown (E.weakFcrStep cfg ext obs n).store
          ((E.weakFcrStep cfg ext obs n).store.blocks t).slot r := by
    simpa only [hqCurrent] using hwalkN1
  have hclock : get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store ≤
      get_current_store_epoch cfg (E.store cfg ext w m) :=
    Nat.le_of_eq hsameEpoch.symm
  rcases h.trace_origin with
    ⟨_a, _hedge, hentry, hrecent, hdesc⟩ |
      ⟨_a, _hedge, hentry, hfinal⟩
  · -- previous-loop origin: the witness certificate discharges the
    -- observer-as-sender relay.
    have hseedQ :=
      weakFcrStep_previousSlotHead_known cfg ext hT.genesis hcoh n hn1H
    have hwitness_known : (E.weakFcrStep cfg ext obs n).previous_slot_head ∈
        (E.store cfg ext obs (n + 1)).block_roots := by
      rw [← hqCurrent]; exact hseedQ
    have hepochPos : 1 ≤ get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store := by
      rw [← hprevious]; exact Nat.le_add_left 1 _
    have hslotPos : 1 ≤ get_current_slot cfg (E.weakFcrStep cfg ext obs n).store := by
      rcases Nat.eq_zero_or_pos
          (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) with hz | hpos
      · exfalso
        have hz0 : get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store = 0 := by
          simp only [get_current_store_epoch, compute_epoch_at_slot, hz, Nat.zero_div]
        rw [hz0] at hepochPos
        exact absurd hepochPos (by decide)
      · exact hpos
    have hcurSlotEq : get_current_slot cfg (E.weakFcrStep cfg ext obs n).store =
        E.slot_at cfg (n + 1) := by
      rw [hqCurrent]; exact E.store_current_slot cfg ext obs (n + 1)
    have hslotPosAt : 1 ≤ E.slot_at cfg (n + 1) := by
      rw [← hcurSlotEq]; exact hslotPos
    have hgate : (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store - 1) + 1 ≤
        E.slot_at cfg m := by
      rw [hcurSlotEq, Nat.sub_add_cancel hslotPosAt]
      exact hslotForward
    have hseedM : (E.weakFcrStep cfg ext obs n).previous_slot_head ∈
        (E.store cfg ext w m).block_roots :=
      Weak.witnessSeed_known_at_all_honest_endpoints_at_observer cfg ext hA
        hsync hji hn1H hcommN1 hqCurrent hentry.witness_certificate
        hwitness_known hw hmH hgate
    exact E.recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
      cfg ext B hT.wellFormed hT.externals_coherence
      hgen hgenSlot hgenParent hqueryCausal hendpointCausal
      hqueryParent hqueryProvenance
      (hqueryWalk result h.result_known _ hseedQ)
      hselectedM hseedQ hseedM hdesc hclock hsameEpoch hrecent
  · unfold TentativeSelectedResultWitness at hfinal
    rcases hfinal with hcurrentEq | ⟨hrecent, _houter⟩
    · have hbad : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store result + 1 =
          get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store result :=
        hprevious.trans hcurrentEq.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
    · exact E.recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
        cfg ext B hT.wellFormed hT.externals_coherence
        hgen hgenSlot hgenParent hqueryCausal hendpointCausal
        hqueryParent hqueryProvenance
        (hqueryWalk result h.result_known result h.result_known)
        hselectedM h.result_known hselectedM
        (is_ancestor_refl _ _) hclock hsameEpoch hrecent

end Weak

end FastConfirmation.Spec
