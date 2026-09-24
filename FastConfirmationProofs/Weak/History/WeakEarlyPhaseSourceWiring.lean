module
public import FastConfirmationProofs.Weak.Common.WeakSeedDissemination
public import FastConfirmationProofs.Weak.Selection.WeakSelectedTrace
public import FastConfirmationProofs.Weak.Selection.WeakSelectorInversion
public import FastConfirmationProofs.Execution.Delivery.EarlyPhaseSourceDelivery

@[expose] public section

/-!
# Spec / Proof / WeakEarlyPhaseSourceWiring

Stage S5 of the `hfilter`-discharge wave (`/tmp/hfilter-wave-design.md`): weak
twins of `AcceptedEarlyPhaseSourceWiring.lean`'s executable head-cache
knownness lemmas and of `AcceptedPhaseSourceSupply.lean`'s two actual-call
source-supply theorems (sites 3 and 6 of the wave's site inventory), all
re-indexed over `E.weakFcrStep` / `E.weakFcr` (`WeakFCRCallContracts.lean`),
per `/tmp/delta5-proposal.md` §5.

## What is delivered

* `Weak.weakFcr_currentSlotHead_known` / `Weak.weakFcrStep_previousSlotHead_known`
  — weak twins of `Execution.fcr_currentSlotHead_known` /
  `Execution.fcrStep_previousSlotHead_known`. The strong
  `head_root_known_of_selectedMarginDomain cfg ext hdomain hv` call is replaced
  by the honesty-free `Execution.head_root_known_at_observer`
  (`WeakObserverDomain.lean`), driven by `hcoh : E.ObserverCoherence cfg ext
  obs`; `SelectedMarginDomain` is dropped entirely from the signature (it fed
  nothing else in either strong proof).
* `Weak.strictSelectedResult_below_head` — weak twin of
  `HistoricalCurrentTargetTrajectory.strictSelectedResult_below_head`, over
  `Weak.find_latest_confirmed_descendant` and the already-landed
  `weak_prev_epoch_loop_spec` / `weak_tentative_loop_spec`
  (`WeakSelectorInversion.lean`). Needed because
  `current_lemma13SourceSeed_of_notStart`'s below-head step has no existing
  weak twin.
* `Weak.StrictSelectedResultMechanicalFacts.not_epochStart_of_current` — a
  verbatim clone of the strong lemma of the same name (the mechanical-facts
  argument `h` is only ever used through `h.result_known`, so the clone is
  type-for-type identical modulo `Weak.StrictSelectedResultMechanicalFacts`).
* `Weak.StrictSelectedResultMechanicalFacts.currentHeadLemma13SourceSeedCertified_of_notStart`
  — **deviation from a literal clone of `current_lemma13SourceSeed_of_notStart`**,
  documented in the wave report: the strong lemma returns the erased
  existential `AcceptedLemma13SourceSeedAt`, but site 6 needs the seed's
  *identity* (the query fork-choice head) intact so the certificate-based
  dissemination lemma can be applied to it, and per hfilter §(A) also needs the
  `has_carrier_broadcast_certificate` flag the tentative-entry witness's surviving
  disjunct carries alongside the GU bound. Rather than returning an existential
  and a separate certificate lemma (which would force re-deriving the
  case split), this single lemma exposes both facts, head-indexed, from one
  case split.
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
  knownness at the query second, so `hcall : E.IsScheduledFCRCallAt cfg ext obs n` and
  the `fcrStep_previousSlotHead_eq_currentSlotHead` bookkeeping step are both
  unused and dropped from the signature.
* `Weak.fcrStep_currentNext_endpointRecentSourceSeed` (site 6) — weak twin of
  `StrictSelectedResultMechanicalFacts.fcrStep_currentNext_endpointRecentSourceSeed`.
  Per hfilter §(A), the ∀-shaped `hseedM` is **not** reproduced (it would
  assert the observer's entire store disseminates, which is false at a
  non-honest observer and is exactly the premise the wave's finding declares
  unnecessary). Instead the two roots the strong proof's `hseedM` was ever
  actually instantiated at are supplied directly: the selected result via
  `Execution.confirmed_known_at_all_honest_endpoints_at_observer`, and the
  query head via `Weak.headSeed_known_at_all_honest_endpoints_at_observer`
  (certificate from the combined lemma above). `Weak.recentSourceSeedAt_endpointNext_of_lemma13`
  is a **clone**, not a verbatim reuse, of `Execution.recentSourceSeedAt_endpointNext_of_lemma13`
  with its single internal `hseedM seed hseedQ` application replaced by a
  directly-supplied membership hypothesis — the clone route was chosen over an
  adapter because a real term of the ∀ type would have to hold at *every* root
  of `query.block_roots`, which is not provable at a non-honest observer (the
  adapter is not merely larger, it is unsound); see the wave report for the
  full comparison.
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

/-! ## Weak below-head selector fact -/

/-- Weak twin of `strictSelectedResult_below_head`
(`HistoricalCurrentTargetTrajectory.lean`): a strict weak-selector output is on
the query head chain even without assuming the input is. Reuses the
selector-independent ancestry helpers (`get_ancestor_roots_mem`,
`get_ancestor_roots_descends`, `ancestorRoots_member_below_head`) and the
already-landed weak loop inversions (`weak_prev_epoch_loop_spec`,
`weak_tentative_loop_spec`, `WeakSelectorInversion.lean`). -/
theorem strictSelectedResult_below_certified_head
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hstrict : Weak.find_latest_confirmed_descendant cfg ext query input ≠ input) :
    is_ancestor query.store
      (get_node_for_root (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)))
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query input)) = true := by
  let head := Weak.get_certified_head cfg ext query.store (get_current_balance_source query)
  have hhead := Weak.get_certified_head_known cfg ext query.store
    (get_current_balance_source query) hhead
  set P : Root → Prop := fun r =>
    r ∈ query.store.block_roots ∧
      (r = input ∨ is_ancestor query.store (get_node_for_root head)
        (get_node_for_root r) = true) with hP
  have base : P input := ⟨hinput, Or.inl rfl⟩
  have hprev : ∀ (ce : Epoch) (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_prev_epoch_loop cfg ext query ce
        (get_ancestor_roots query.store head acc) acc) := by
    intro ce acc hacc
    rcases weak_prev_epoch_loop_spec cfg ext query ce
        (get_ancestor_roots query.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ query.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown, Or.inr
        (Execution.ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr)⟩
  have htent : ∀ (acc : Root), P acc →
      P (Weak.find_latest_confirmed_descendant_tentative_loop cfg ext query
        (get_ancestor_roots query.store head acc) acc) := by
    intro acc hacc
    rcases weak_tentative_loop_spec cfg ext query
        (get_ancestor_roots query.store head acc) acc with
      heq | ⟨r, hr, heq, _hconfirmed⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      have hrKnown : r ∈ query.store.block_roots :=
        get_ancestor_roots_mem hwf
          (hwalk acc hacc.1 head (by simpa only [head] using hhead)) hr
      exact ⟨hrKnown, Or.inr
        (Execution.ancestorRoots_member_below_head hwf hwalk
          (by simpa only [head] using hhead) hacc.1 hr)⟩
  have hresult : P
      (Weak.find_latest_confirmed_descendant cfg ext query input) := by
    generalize hout : Weak.find_latest_confirmed_descendant cfg ext query input = result
    rw [Weak.find_latest_confirmed_descendant] at hout
    simp only at hout
    split_ifs at hout with hc1 hc2 hc3 hc4 hc5 <;>
      subst hout <;>
        first
        | exact base
        | (apply htent; first | exact base | exact hprev _ _ base)
        | exact hprev _ _ base
  rcases hresult.2 with heq | hbelow
  · exact False.elim (hstrict heq)
  · simpa only [head, get_node_for_root] using hbelow

theorem strictSelectedResult_below_head
    {query : FastConfirmationStore Root}
    (hwf : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    {input : Root} (hinput : input ∈ query.store.block_roots)
    (hstrict : Weak.find_latest_confirmed_descendant cfg ext query input ≠ input) :
    is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query input)) = true  := by
  have hc := Weak.get_certified_head_known cfg ext query.store
    (get_current_balance_source query) hhead
  have hr := (weak_find_latest_confirmed_descendant_ge cfg ext query hwf hwalk
    hhead input hinput).2
  exact is_ancestor_trans hwf (hwalk _ hr _ hhead) (hwalk _ hr _ hc)
    (Weak.get_certified_head_below_head cfg ext query.store (get_current_balance_source query))
    (strictSelectedResult_below_certified_head cfg ext hwf hwalk hhead hinput hstrict)

/-! ## Query-local not-epoch-start / current-head Lemma-13 facts -/

/-- Weak twin of `StrictSelectedResultMechanicalFacts.not_epochStart_of_current`.
`h` is consumed only through `h.result_known`, so this is a verbatim clone with
`Weak.StrictSelectedResultMechanicalFacts` substituted for the strong
structure. -/
theorem StrictSelectedResultMechanicalFacts.not_epochStart_of_current
    {q : Nat} {query : FastConfirmationStore Root} {input result : Root}
    (hclock : get_current_slot cfg query.store = E.slot_at cfg q)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hpast : E.ConfirmedPastDescendantSlotWitnessAt cfg q query.store result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store) :
    is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true := by
  intro hstart
  obtain ⟨pastSecond, descendant, hpastLt, hdescendant,
      hdescends, hdescendantSlot⟩ := hpast
  have hresultSlotLeD : (query.store.blocks result).slot ≤
      (query.store.blocks descendant).slot :=
    Execution.ancestor_slot_le hparent
      (hwalk result h.result_known descendant hdescendant) hdescends
  have hqueryBoundary : get_current_slot cfg query.store =
      compute_start_slot_at_epoch cfg
        (get_current_store_epoch cfg query.store) := by
    have hzero : compute_slots_since_epoch_start cfg
        (get_current_slot cfg query.store) = 0 := by
      simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hzero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hquerySlotLeResult : E.slot_at cfg q ≤
      (query.store.blocks result).slot := by
    rw [← hclock, hqueryBoundary, ← hcurrent]
    exact start_slot_at_block_epoch_le cfg query.store result
  have : E.slot_at cfg q ≤ E.slot_at cfg pastSecond := by
    calc
      E.slot_at cfg q ≤ (query.store.blocks result).slot := hquerySlotLeResult
      _ ≤ (query.store.blocks descendant).slot := hresultSlotLeD
      _ ≤ E.slot_at cfg pastSecond := hdescendantSlot
  exact (Nat.not_le_of_gt hpastLt) this

/-- Combined weak twin of `current_lemma13SourceSeed_of_notStart`, extended
with the certificate flag site 6 also needs (see module docstring). Away from
the epoch-start escape, a strict current-epoch tentative weak-selector result
mechanically realizes the Lemma-13 GU seed *and* the certificate at the exact
query head: the previous-loop origin is impossible (`hedge.gates`'s first
conjunct contradicts `hcurrent`), and the tentative entry's surviving arm
(`hnotStart` eliminates the epoch-start disjunct) is precisely the pair
`⟨GU-recency, has_carrier_broadcast_certificate⟩` at the head. -/
theorem StrictSelectedResultMechanicalFacts.currentHeadLemma13SourceSeedCertified_of_notStart
    (B : CausalPrefixFFGInterpretation cfg ext E)
    {query : FastConfirmationStore Root} {input result : Root}
    (hstore : E.CausalStore cfg ext query.store)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : input ∈ query.store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true) :
    is_ancestor query.store (get_node_for_root (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)))
        (get_node_for_root result) = true ∧
      (B.state.GU (Weak.get_certified_head cfg ext query.store (get_current_balance_source query))).epoch + 1 ≥
        get_current_store_epoch cfg query.store ∧
      Weak.has_carrier_broadcast_certificate cfg ext query.store
        (get_current_balance_source query) = true := by
  rcases h.trace_origin with
    ⟨_a, hedge, _hentry, _hrecent, _hdesc⟩ |
      ⟨_a, _hedge, hentry, _hfinal⟩
  · exact False.elim ((hedge.gates cfg ext).1 hcurrent)
  · rcases hentry with hstart | ⟨hgu, hheadCert⟩
    · exact False.elim (hnotStart hstart)
    · have hbelow : is_ancestor query.store
          (get_node_for_root (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)))
          (get_node_for_root result) = true := by
        have hstrict' :
            Weak.find_latest_confirmed_descendant cfg ext query input ≠ input := by
          simpa only [hout] using hstrict
        simpa only [hout] using
          strictSelectedResult_below_certified_head cfg ext hparent hwalk hhead
            hinput hstrict'
      have hprojection :=
        Execution.CausalPrefixFFGInterpretation.causalStoreProjection
          B hstore
      have hguEq : query.store.unrealized_justifications
          (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)) =
        B.state.GU (Weak.get_certified_head cfg ext query.store (get_current_balance_source query)) :=
        hprojection.unrealized_justification _
          (Weak.get_certified_head_known cfg ext _ _ hhead)
      exact ⟨hbelow, by simpa only [hguEq] using hgu, hheadCert⟩

/-! ## Site 3 — actual `weakFcrStep` previous cell, no observer relay -/

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_previous_
endpointRecentSourceSeed`. See the module docstring for the `hcall` /
`fcrStep_previousSlotHead_eq_currentSlotHead` simplification. -/
theorem StrictSelectedResultMechanicalFacts.fcrStep_previous_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
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
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hslotForward : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m :=
    E.slot_at_mono cfg hnm
  have hselectedM : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs (n + 1) hcoh.validity hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
      h.confirmed w hw m hslotForward hmH
  have hqueryCausal : E.CausalStore cfg ext
      (E.weakFcrStep cfg ext obs n).store := by
    rw [hqCurrent]; exact E.store_causal cfg ext obs (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hcoh (n + 1) hn1H
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
      weakFcrStep_previousSlotHead_known cfg ext hT.genesis_structure hcoh n hn1H
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
      h.result_known hseedQ hseedM hdesc hclock hsameEpoch hrecent
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
        h.result_known h.result_known hselectedM
        (is_ancestor_refl _ _) hclock hsameEpoch hrecent

/-! ## Site 6 — actual `weakFcrStep` current/next cell, no observer relay -/

/-- Clone (not verbatim reuse) of `Execution.recentSourceSeedAt_endpointNext_
of_lemma13` with the single internal `hseedM seed hseedQ` application replaced
by a directly-supplied membership hypothesis, so callers never have to inhabit
the ∀-shaped relay. See the module docstring for why this is the smaller and
only sound option. -/
theorem recentSourceSeedAt_endpointNext_of_lemma13
    (B : CausalPrefixFFGInterpretation cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : BeaconExternalsPremises cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hgenSlot : ast.slot = ablk.message.slot)
    (hgenParent : ablk.message.parent_root ≠ ablk.root)
    {query : Store Root} {w : ValidatorIndex} {m : Nat} {selected : Root}
    (hquery : E.CausalStore cfg ext query)
    (hendpoint : E.CausalStore cfg ext (E.store cfg ext w m))
    (hqueryParent : ParentSlotLt query)
    (hqueryProvenance : BlockProvenance E query)
    (hqueryWalk : ∀ t ∈ query.block_roots,
      ∀ r ∈ query.block_roots,
        WalkKnown query (query.blocks t).slot r)
    (hqueryNonfuture : BlocksSlotLe (get_current_slot cfg query) query)
    (hselectedQ : selected ∈ query.block_roots)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query + 1)
    {seed : Root}
    (hseedQ : seed ∈ query.block_roots)
    (hseedSelectedQ : is_ancestor query (get_node_for_root seed)
      (get_node_for_root selected) = true)
    (hguRecent : (B.state.GU seed).epoch + 1 ≥
      get_current_store_epoch cfg query)
    (hseedM : seed ∈ (E.store cfg ext w m).block_roots) :
    Execution.RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      (hqueryWalk selected hselectedQ seed hseedQ) hseedSelectedQ
  have hseedSelectedM : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed)
      (get_node_for_root selected) = true :=
    E.store_ancestor_of_rootDescends_for_storeReflection cfg ext hwf hec
      hgen hgenSlot hgenParent hseedM hselectedM hsemantic
  have hseedEpochLe : get_block_epoch cfg query seed ≤
      get_current_store_epoch cfg query := by
    exact ce_mono cfg (hqueryNonfuture seed hseedQ)
  have hqueryAt : E.AcceptedBlockAt cfg ext seed (query.blocks seed) :=
    E.acceptedBlockAt_of_causal_known cfg ext hquery hseedQ
  have hendpointAt : E.AcceptedBlockAt cfg ext seed
      ((E.store cfg ext w m).blocks seed) :=
    E.acceptedBlockAt_of_causal_known cfg ext hendpoint hseedM
  have hblock : query.blocks seed = (E.store cfg ext w m).blocks seed :=
    hqueryAt.unique cfg ext E hwf hendpointAt
  have hseedOld : get_current_store_epoch cfg (E.store cfg ext w m) >
      get_block_epoch cfg (E.store cfg ext w m) seed := by
    rw [hnextEpoch]
    simp only [get_block_epoch, ← hblock]
    exact Nat.lt_succ_of_le hseedEpochLe
  have hsourceEq : get_voting_source cfg (E.store cfg ext w m) seed =
      B.state.GU seed := by
    rw [hendpoint.getVotingSource_eq_acceptedSelector cfg ext B hseedM]
    exact if_pos hseedOld
  refine ⟨seed, hseedM, hseedSelectedM, ?_⟩
  rw [hsourceEq, hnextEpoch]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    Nat.add_le_add_right hguRecent 1

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_currentNext_
endpointRecentSourceSeed`. See the module docstring for the `hseedM`
non-reproduction and the `recentSourceSeedAt_endpointNext_of_lemma13` clone. -/
theorem StrictSelectedResultMechanicalFacts.fcrStep_currentNext_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hji : JustificationInterface cfg ext E)
    (B : CausalPrefixFFGInterpretation cfg ext E)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) {n : Nat}
    (hn1H : E.WithinHorizon cfg (n + 1))
    {input result : Root}
    (hinput : input ∈ (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hout : Weak.find_latest_confirmed_descendant cfg ext
      (E.weakFcrStep cfg ext obs n) input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.weakFcrStep cfg ext obs n) input result)
    (hcurrent : get_block_epoch cfg (E.weakFcrStep cfg ext obs n).store result =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hmH : E.WithinHorizon cfg m)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg (E.weakFcrStep cfg ext obs n).store + 1) :
    Execution.RecentSourceSeedAt cfg (E.store cfg ext w m) result := by
  let hA : SelectedMarginAssumptions cfg ext E :=
    { genesis := hT.genesis_structure
      wellFormed := hT.wellFormed
      whole_seconds := hT.whole_seconds
      honest_behavior := hT.honest_behavior
      synchrony := hsync
      externals_coherence := hT.externals_coherence
      static_validators := hstatic
      byzantine_bound := hbyz
      domain := hdomain }
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis_structure
  have hqCurrent : (E.weakFcrStep cfg ext obs n).store = E.store cfg ext obs (n + 1) :=
    E.weakFcrStep_store cfg ext obs n
  have hcommN1 : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs (n + 1)) :=
    hcoh.committees_agree (n + 1) hn1H
  have hqueryCausal : E.CausalStore cfg ext
      (E.weakFcrStep cfg ext obs n).store := by
    rw [hqCurrent]; exact E.store_causal cfg ext obs (n + 1)
  have hendpointCausal := E.store_causal cfg ext w m
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.observerStoreDomainK cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis_structure hcoh (n + 1) hn1H
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
  have hhead : (get_head cfg (E.weakFcrStep cfg ext obs n).store).root ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
    simpa only [hqCurrent] using
      E.head_root_known_at_observer cfg ext hcoh (n + 1) hn1H
  have hpast := h.confirmedPastDescendantSlotWitness_at_observer cfg ext hA
    hcoh.validity hcommN1 hn1H hqCurrent
  have hnotStart := h.not_epochStart_of_current cfg ext
    (q := n + 1)
    (by rw [hqCurrent, E.store_current_slot cfg ext obs (n + 1)])
    hqueryParent hqueryWalk hpast hcurrent
  obtain ⟨hbelow, hguRecent, hheadCert⟩ :=
    h.currentHeadLemma13SourceSeedCertified_of_notStart cfg ext B
      hqueryCausal hqueryParent hqueryWalk hhead hinput hout hstrict hcurrent
      hnotStart
  have hnextSlots : compute_epoch_at_slot cfg (E.slot_at cfg m) =
      compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) + 1 := by
    simpa only [get_current_store_epoch, hqCurrent,
      E.store_current_slot cfg ext w m,
      E.store_current_slot cfg ext obs (n + 1)] using hnextEpoch
  have hslotLt : E.slot_at cfg (n + 1) < E.slot_at cfg m := by
    by_contra hnot
    have hle : E.slot_at cfg m ≤ E.slot_at cfg (n + 1) :=
      Nat.le_of_not_gt hnot
    have hepochLe := ce_mono cfg hle
    rw [hnextSlots] at hepochLe
    exact (Nat.not_succ_le_self _) hepochLe
  have hslotForward : E.slot_at cfg (n + 1) ≤ E.slot_at cfg m := hslotLt.le
  have hselectedM : result ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs (n + 1) hcoh.validity hcommN1 (E.weakFcrStep cfg ext obs n) hqCurrent result hn1H
      (by simpa only [hqCurrent] using h.result_known)
      (by simpa only [hqCurrent] using h.parent_known)
      h.confirmed w hw m hslotForward hmH
  have hstart0 : is_start_slot_at_epoch cfg 0 = true := by
    simp [is_start_slot_at_epoch, compute_slots_since_epoch_start]
  have hslotPos : 1 ≤ get_current_slot cfg (E.weakFcrStep cfg ext obs n).store := by
    rcases Nat.eq_zero_or_pos
        (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store) with hz | hpos
    · exact absurd (hz ▸ hstart0) hnotStart
    · exact hpos
  have hcurSlotEq : get_current_slot cfg (E.weakFcrStep cfg ext obs n).store =
      E.slot_at cfg (n + 1) := by
    rw [hqCurrent]; exact E.store_current_slot cfg ext obs (n + 1)
  have hslotPosAt : 1 ≤ E.slot_at cfg (n + 1) := by
    rw [← hcurSlotEq]; exact hslotPos
  have hheadGate : (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store - 1) + 1 ≤
      E.slot_at cfg m := by
    rw [hcurSlotEq, Nat.sub_add_cancel hslotPosAt]
    exact hslotForward
  have hheadKnownEndpoint : (Weak.get_certified_head cfg ext (E.weakFcrStep cfg ext obs n).store
        (get_current_balance_source (E.weakFcrStep cfg ext obs n))) ∈
      (E.store cfg ext w m).block_roots :=
    Weak.headSeed_known_at_all_honest_endpoints_at_observer cfg ext hA
      hsync hji hn1H hcoh hqCurrent hheadCert hw hmH hheadGate
  have hqueryNonfuture : BlocksSlotLe
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store)
      (E.weakFcrStep cfg ext obs n).store := by
    simpa only [hqCurrent] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hgenSlot⟩ obs (n + 1)
  exact recentSourceSeedAt_endpointNext_of_lemma13 cfg ext B
    hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
    hqueryCausal hendpointCausal hqueryParent hqueryProvenance
    hqueryWalk hqueryNonfuture h.result_known hselectedM hnextEpoch
    (Weak.get_certified_head_known cfg ext _ _ hhead) hbelow hguRecent hheadKnownEndpoint

end Weak

end FastConfirmation.Spec

end
