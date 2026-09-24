module
public import FastConfirmationProofs.Weak.History.WeakEarlyPhaseSourceWiring
public import FastConfirmationProofs.Execution.Delivery.TrustedEarlyPhaseSourceDelivery
public import FastConfirmationProofs.FFG.SelectedSource.TrustedEarlyPhaseSource
public import FastConfirmationProofs.FFG.SelectedSource.TrustedPhaseSourceCarriers
public import FastConfirmationProofs.Weak.Certificates.TrustedWeakBankedJustification

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {trusted : Store Root → Prop}

theorem StrictSelectedResultMechanicalFacts.trusted_currentHeadLemma13SourceSeedCertified_of_notStart
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
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
        Execution.TrustedCausalPrefixFFGInterpretation.causalStoreProjection
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
theorem StrictSelectedResultMechanicalFacts.trusted_fcrStep_previous_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)

    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
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
        hsync  hn1H hcommN1 hqCurrent hentry.witness_certificate
        hwitness_known hw hmH hgate
    exact E.trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
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
    · exact E.trusted_recentSourceSeedAt_endpoint_of_explicitSeed_sameEpoch
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
theorem trusted_recentSourceSeedAt_endpointNext_of_lemma13
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
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
    rw [hendpoint.trusted_getVotingSource_eq_acceptedSelector cfg ext B hseedM]
    exact if_pos hseedOld
  refine ⟨seed, hseedM, hseedSelectedM, ?_⟩
  rw [hsourceEq, hnextEpoch]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    Nat.add_le_add_right hguRecent 1

/-- Weak twin of `StrictSelectedResultMechanicalFacts.fcrStep_currentNext_
endpointRecentSourceSeed`. See the module docstring for the `hseedM`
non-reproduction and the `trusted_recentSourceSeedAt_endpointNext_of_lemma13` clone. -/
theorem StrictSelectedResultMechanicalFacts.trusted_fcrStep_currentNext_endpointRecentSourceSeed
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineWeightPremises cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)

    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
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
    h.trusted_currentHeadLemma13SourceSeedCertified_of_notStart cfg ext B
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
      hsync  hn1H hcoh hqCurrent hheadCert hw hmH hheadGate
  have hqueryNonfuture : BlocksSlotLe
      (get_current_slot cfg (E.weakFcrStep cfg ext obs n).store)
      (E.weakFcrStep cfg ext obs n).store := by
    simpa only [hqCurrent] using
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds
        ⟨ast, ablk, hgen, hgenSlot⟩ obs (n + 1)
  exact trusted_recentSourceSeedAt_endpointNext_of_lemma13 cfg ext B
    hT.wellFormed hT.externals_coherence hgen hgenSlot hgenParent
    hqueryCausal hendpointCausal hqueryParent hqueryProvenance
    hqueryWalk hqueryNonfuture h.result_known hselectedM hnextEpoch
    (Weak.get_certified_head_known cfg ext _ _ hhead) hbelow hguRecent hheadKnownEndpoint

end Weak
end FastConfirmation.Spec
end
