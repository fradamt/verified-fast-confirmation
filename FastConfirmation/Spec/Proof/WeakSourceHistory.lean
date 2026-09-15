import FastConfirmation.Spec.Proof.AcceptedCurrentSameSourceHistory
import FastConfirmation.Spec.Proof.WeakConfirmedDissemination
import FastConfirmation.Spec.Proof.WeakObserverDomain

/-!
# Spec / Proof / WeakSourceHistory

Stage S4 of the `hfilter`-discharge wave: the two source-history relays that
the accepted stack performs *into* the query store are closed at an observer
that need not be honest.

## Site 5 — `confirmed_honestPastHeadBelow`

`Execution.confirmed_honestPastHeadBelow`
(`AcceptedCurrentSameSourceHistory.lean:184`) uses the query node's honesty
three times:

1. `honestSupporter_of_confirmed_known_at_minimal … hv` — replaced by
   `Execution.honestSupporter_of_confirmed_known_at_observer`
   (`WeakConfirmedSupporter.lean:91`), driven by
   `hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q)`;
2. `hsync.block_relay i hi nu _ hnuH hheadPast obs hv q hqH hrelayGate` —
   **no relay is needed at all**. `pastHead_of_honestSupporter_known`
   (`:93`) already computes, internally,
   `hlmKnown : lm.root ∈ (E.store cfg ext obs q).block_roots` out of
   `Execution.latestMessageProvenance` (which consumes only `hwf`, `hec` and
   the genesis shape — never the receiver's honesty), together with
   `hhead : (get_head cfg (E.store cfg ext i nu)).root = lm.root`; it then
   discards `hlmKnown`. `hhead ▸ hlmKnown` *is* the relayed fact. The clone
   `pastHead_known_at_observer` below exposes it as a fifth conclusion
   conjunct instead of discarding it — the same "expose, don't
   re-existentialize" move `WeakConfirmedDissemination
   .past_descendant_known_at_observer` already makes;
3. `store_domainK_of_selectedMarginDomain … obs hv q hqH` — its honest-only
   third component `_hjustifiedQ` is discarded at the call site, so the two
   surviving components come from the honesty-free
   `Execution.storeDomainParentWalk` (`WeakObserverDomain.lean`, stage S0).

The produced record `AcceptedHonestPastHeadBelowAt` has no field mentioning
the query store, so the conclusion type is unchanged.

## Site 2 — `confirmedPastDescendantSlotWitness`

`StrictSelectedResultMechanicalFacts.confirmedPastDescendantSlotWitness`
(`AcceptedEarlyPhaseSourceWiring.lean:278`) consumes its
`StrictSelectedResultMechanicalFacts` argument only through the three
store-level fields `confirmed` / `result_known` / `parent_known`, and uses
`hv` only for `honestSupporter_of_confirmed_known_at_minimal` and for one
`block_relay` moving the past descendant into the query store.
`Execution.confirmed_pastDescendant_at_observer`
(`WeakConfirmedDissemination.lean:282`) supplies both in one shot: its fifth
conjunct *is* `hdQuery`, `hdAgree` follows from `WellFormedExecution
.blocks_agree` between the fourth and fifth, and `hdSlotLePast` is
`store_blocks_slot_le_current` at `(u, nu)`.

`StrictSelectedResultMechanicalFacts` itself is stated over the *strong*
selector's trace and entry-witness types (`findLatestSelectedTrace`,
`PreviousAcceptedEdge`, `PreviousSelectedEntryWitness`,
`TentativeSelectedEntryWitness`), which the weak development only acquires in
stage S2. The weak twin is therefore landed here in its underlying
store-level form, `Weak.confirmedPastDescendantSlotWitness_core`, stated over
a bare query store plus a confirmed root; the `Weak
.StrictSelectedResultMechanicalFacts`-shaped wrapper is a one-line
application of it once S2 exists.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Narrow lower bundle adapter

`AcceptedCurrentSameSourceHistory.selectedMarginAssumptions_of_sourceHistory
Inputs` is `private`, hence invisible here; it is restated verbatim (the same
pattern `WeakConfirmedSupporter.lean` uses for `MinimalSelectedDomain.lean`'s
private arithmetic helpers). -/

private def selectedMarginAssumptions_of_weakSourceHistoryInputs
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E) :
    SelectedMarginAssumptions cfg ext E :=
  { genesis := hT.genesis
    wellFormed := hT.wellFormed
    whole_seconds := hT.whole_seconds
    honest_behavior := hT.honest_behavior
    synchrony := hsync
    externals_coherence := hT.externals_coherence
    static_validators := hstatic
    byzantine_bound := hbyz
    domain := hdomain }

/-! ## Site 5 — strictly-past honest head provenance at a non-honest observer -/

/-- `pastHead_of_honestSupporter_known`
(`AcceptedCurrentSameSourceHistory.lean:93`) with one extra conclusion
conjunct: the honest supporter's past executable head root is also a member of
the *observing* store's block map.

That fact is already present inside the original proof — it is
`Execution.latestMessageProvenance`'s `hlmKnown` component, transported along
the internal head equation `hhead : (get_head cfg (E.store cfg ext i nu)).root
= lm.root` — and is simply discarded there. `latestMessageProvenance` needs
only well-formedness, externals coherence and the genesis shape, so `obs` need
not be honest: no relay, and no new premise.

The binder list is kept identical to the original's. `hsync`, `hstatic` and
`hbyz` are unused here exactly as they are unused there — the original feeds
them to a `SelectedMarginAssumptions` bundle its body never reads — and are
retained so that call sites of the two lemmas stay interchangeable. -/
theorem pastHead_known_at_observer
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (obs : ValidatorIndex) (q : Nat) (b : Root)
    (hH : E.WithinHorizon cfg q)
    (i : ValidatorIndex) (hi : i ∈ E.honest) (lm : LatestMessage Root)
    (hlm : (E.store cfg ext obs q).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext obs q)
      (get_supported_node (E.store cfg ext obs q) lm)
      (get_node_for_root b) = true) :
    ∃ nu : Nat,
      E.WithinHorizon cfg nu ∧
      E.slot_at cfg nu < E.slot_at cfg q ∧
      (get_head cfg (E.store cfg ext i nu)).root ∈
        (E.store cfg ext i nu).block_roots ∧
      is_ancestor (E.store cfg ext obs q)
        (get_head cfg (E.store cfg ext i nu))
        (get_node_for_root b) = true ∧
      (get_head cfg (E.store cfg ext i nu)).root ∈
        (E.store cfg ext obs q).block_roots := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hT.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext obs 0
    rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hT.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  obtain ⟨a', sender, sentAt, ifb, hsched, hiatt, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen0 obs q i lm hlm
  obtain ⟨_voteAt, own, hvote, hdata⟩ :=
    hT.honest_behavior.no_forgery sender sentAt a' ifb hsched i hi hiatt
  set s := a'.data.slot
  have hcomm : i ∈ E.committee s :=
    hT.honest_behavior.votes_assigned i hi s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨ap, _hiap, _htarget, _hbbrap, hapEpoch, hapBound, hapComm,
      hlmKnown, hlmSlot⟩ :=
    E.latestMessageProvenance cfg ext hT.wellFormed
      hT.externals_coherence hgen0 obs q i lm hlm
  have hepoch : compute_epoch_at_slot cfg s =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, hapEpoch]
  have hsap : s = ap.data.slot :=
    hT.externals_coherence.committee_assignment_unique i s ap.data.slot
      hcomm hapComm hepoch
  have hslt : s < E.slot_at cfg q := by
    rw [hsap]
    exact Nat.lt_of_succ_le hapBound
  have hanchorle : ablk.message.slot ≤
      ((E.store cfg ext obs q).blocks lm.root).slot :=
    E.store_anchor_min_slot cfg ext hT.wellFormed hT.externals_coherence
      hgeq hslot hroot obs q lm.root hlmKnown
  have hs0 : E.slot_at cfg 0 ≤ s := by
    rw [hcur0, hsap]
    exact hanchorle.trans hlmSlot
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hslt) hH
  obtain ⟨nu, index, hHnu, hnu, hvoteHead⟩ :=
    hT.honest_behavior.votes_head i hi s hcomm hsH hs0
  rw [hvoteHead] at hvote
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote
  obtain ⟨_, hown⟩ := hvote
  have hrootEq : own.data.beacon_block_root = lm.root := by
    rw [← hdata]
    exact hbbr
  have hhead : (get_head cfg (E.store cfg ext i nu)).root = lm.root := by
    rw [← hrootEq, ← hown]
    rfl
  have hheadKnown : (get_head cfg (E.store cfg ext i nu)).root ∈
      (E.store cfg ext i nu).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i nu) with hmem | heq
    · exact hmem
    · rw [heq]
      exact hdomain.justified_root_known i hi nu hHnu
  refine ⟨nu, hHnu, ?_, hheadKnown, ?_, ?_⟩
  · rw [hnu]
    exact hslt
  · change is_ancestor (E.store cfg ext obs q)
      (ForkChoiceNode.mk (get_head cfg (E.store cfg ext i nu)).root)
      (get_node_for_root b) = true
    rw [hhead]
    simpa only [get_supported_node, get_node_for_root] using hsupp
  · rw [hhead]
    exact hlmKnown

/-- `confirmed_honestPastHeadBelow`
(`AcceptedCurrentSameSourceHistory.lean:184`) at an observer that need not be
honest: the honesty binder `hv : obs ∈ E.honest` is replaced by the
committee-readback fact `hcomm`, and the conclusion is unchanged
(`AcceptedHonestPastHeadBelowAt` has no field indexed at the query store).

Ingredient substitutions, in order of use:
`honestSupporter_of_confirmed_known_at_observer` for
`honestSupporter_of_confirmed_known_at_minimal`; `pastHead_known_at_observer`
for `pastHead_of_honestSupporter_known` *and* for the `block_relay` that
followed it; `storeDomainParentWalk` for
`store_domainK_of_selectedMarginDomain` (whose honest-only third component was
discarded at this call site anyway). -/
theorem confirmed_honestPastHeadBelow_at_observer
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {obs : ValidatorIndex} {q : Nat}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext obs q)
    {candidate : Root}
    (hcandidate : candidate ∈ query.store.block_roots)
    (hparentCandidate : (query.store.blocks candidate).parent_root ∈
      query.store.block_roots)
    (hconfirmed : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) candidate = true) :
    Nonempty (E.AcceptedHonestPastHeadBelowAt cfg ext obs q candidate) := by
  let hA := E.selectedMarginAssumptions_of_weakSourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_observer cfg ext hA obs q hcomm
      query hquery candidate hqH
      (by simpa only [hquery] using hcandidate)
      (by simpa only [hquery] using hparentCandidate) hconfirmed
  obtain ⟨nu, hnuH, hnuq, hheadPast, hheadCandidateQ, hheadQueryE⟩ :=
    E.pastHead_known_at_observer cfg ext hT hsync hstatic hbyz
      hdomain obs q candidate hqH i hi lm hlm hsupp
  obtain ⟨hparentQ, hwalkQ⟩ :=
    E.storeDomainParentWalk cfg ext hT.wellFormed hT.externals_coherence
      hT.genesis obs q
  have hsemantic : E.RootDescends
      (get_head cfg (E.store cfg ext i nu)).root candidate :=
    E.rootDescends_of_store_ancestor (E.blockProvenance cfg ext obs q)
      (by simpa only [hquery] using hparentQ)
      (by
        have hw := hwalkQ candidate
          (by simpa only [hquery] using hcandidate)
          (get_head cfg (E.store cfg ext i nu)).root hheadQueryE
        simpa only [hquery] using hw)
      (by simpa only [hquery] using hheadCandidateQ)
  obtain ⟨ast, ablk, hgen, hslot, hanchorParent⟩ := hT.genesis
  have hcandidateRoot : E.ExecutionRoot candidate :=
    ⟨query.store.blocks candidate,
      by
        rw [hquery]
        exact E.blockAt_of_store_known cfg ext
          (by simpa only [hquery] using hcandidate)⟩
  obtain ⟨hcandidatePast, hheadCandidatePast⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
      hT.wellFormed hT.externals_coherence hgen hslot hanchorParent
      hheadPast hcandidateRoot hsemantic
  exact ⟨{
    validator := i
    second := nu
    validator_honest := hi
    second_within := hnuH
    strictly_past := hnuq
    candidate_known := hcandidatePast
    head_known := hheadPast
    head_descends_candidate := hheadCandidatePast
  }⟩

end Execution

namespace Weak

variable {E : Execution Root}

/-! ## Site 2 — the confirmed past-descendant slot witness at a non-honest
observer -/

/-- Store-level weak twin of
`StrictSelectedResultMechanicalFacts.confirmedPastDescendantSlotWitness`
(`AcceptedEarlyPhaseSourceWiring.lean:278`).

The strong adapter reads only `confirmed` / `result_known` / `parent_known`
off its `StrictSelectedResultMechanicalFacts` argument, so those three are
taken here as bare hypotheses about the query store: the enclosing record is
indexed by the *strong* selector's trace and entry-witness types, whose weak
counterparts arrive only in stage S2. Once they exist, the
`Weak.StrictSelectedResultMechanicalFacts`-shaped wrapper is a projection of
this lemma.

The query node's honesty is replaced by `hcomm`, and the strong proof's
`block_relay` disappears into `Execution.confirmed_pastDescendant_at_observer`,
whose five-conjunct conclusion supplies `hdQuery` directly (fifth conjunct),
`hdAgree` via `WellFormedExecution.blocks_agree` between the fourth and fifth,
and `hdSlotLePast` via `store_blocks_slot_le_current` at `(u, nu)`.

`is_one_confirmed` / `get_current_balance_source` are written `Spec`-qualified
because inside `namespace Weak` the bare names would resolve to the weak
rule's `Weak.is_one_confirmed` (`Spec/Model/WeakSynchrony.lean:215`); the
confirmation predicate meant here is the ordinary one. -/
theorem confirmedPastDescendantSlotWitness_core
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : Nat}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {result : Root}
    (hquery : query.store = E.store cfg ext obs q)
    (hresult : result ∈ query.store.block_roots)
    (hparent : (query.store.blocks result).parent_root ∈
      query.store.block_roots)
    (hconfirmed : Spec.is_one_confirmed cfg ext query.store
      (Spec.get_current_balance_source query) result = true) :
    E.ConfirmedPastDescendantSlotWitnessAt cfg q query.store result := by
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hdPast, hdQueryE, hdResult⟩ :=
    E.confirmed_pastDescendant_at_observer cfg ext hA obs q hcomm
      query hquery result hqH
      (by simpa only [hquery] using hresult)
      (by simpa only [hquery] using hparent) hconfirmed
  have hdQuery : d ∈ query.store.block_roots := by
    simpa only [hquery] using hdQueryE
  have hdAgree : (E.store cfg ext u nu).blocks d = query.store.blocks d := by
    simpa only [hquery] using
      hA.wellFormed.blocks_agree
        (E.blockProvenance cfg ext u nu)
        (E.blockProvenance cfg ext obs q) hdPast hdQueryE
  have hdSlotLePast : ((E.store cfg ext u nu).blocks d).slot ≤
      E.slot_at cfg nu := by
    have hle := E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      (by
        obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hA.genesis
        exact ⟨ast, ablk, hgen, hslot⟩)
      u nu d hdPast
    simpa only [E.store_current_slot cfg ext u nu] using hle
  refine ⟨nu, d, hnuq, hdQuery, ?_, ?_⟩
  · simpa only [hquery] using hdResult
  · rw [← hdAgree]
    exact hdSlotLePast

end Weak

end FastConfirmation.Spec
