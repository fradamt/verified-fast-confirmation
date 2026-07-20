import Mathlib.Tactic
import FastConfirmation.Spec.Proof.AcceptedEarlyPhaseSourceWiring
import FastConfirmation.Spec.Proof.AcceptedPathLocalFinalizedTransport
import FastConfirmation.Spec.Proof.AcceptedFFGJustifiedMaximality
import FastConfirmation.Spec.Proof.AcceptedCandidateHistoryRecurrence
import FastConfirmation.Spec.Proof.AcceptedFinalizationTiming

/-!
# Accepted current/same-epoch source history

This module isolates the exact paper-Lemmas-22--26 boundary needed by the
`currentSame` early phase.  It proves all of the post-history mechanics:

* a concrete confirmation yields an honest, strictly earlier voting head;
* query ancestry is reflected into that honest past store;
* the past executable HFC head is inverted without assuming endpoint filter
  membership;
* a Lemma-24 epoch-start seed implies the Lemma-25 `GJ` lower bound using the
  accepted-only justified maximum; and
* the viable-leaf arm becomes a recent accepted source carrier while retaining
  the same leaf's exact finalized check and path.

The temporal core is an induction over the exact ordered FCR recurrence.  It
retains a candidate-specific Lemma-13 origin while a confirmed root is current,
advances that origin through Lemmas 22--24 at the next boundary, and handles
finalized resets using the accepted state-transition finalization-delay law.
The evaluator-trace theorem has no temporal callback premise. A broader
arbitrary-query interface is also stated for generic callers.

The executable `get_head` has a justified-root fallback which need not be a
member of the filtered output.  Consequently the final theorem deliberately
returns either that exact fallback or the path-local Lemma-26 carrier.  It
does not manufacture a filter witness in the fallback branch.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Narrow lower bundle adapter -/

/-- Reassemble the lower selected domain only inside proofs.
Public current-same theorems expose its independent constituents instead of
exporting `SelectedMarginAssumptions` as a completion premise. -/
private def selectedMarginAssumptions_of_sourceHistoryInputs
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

/-! ## Strictly-past honest head provenance -/

/-- The exact honest past view recovered from one concrete confirmation.
Unlike the older minimal projection, this record retains that the descendant
is the honest validator's actual executable `get_head`, and reflects the
candidate ancestry into that same past store. -/
structure AcceptedHonestPastHeadBelowAt
    (v : ValidatorIndex) (q : Nat) (candidate : Root) where
  validator : ValidatorIndex
  second : Nat
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  strictly_past : E.slot_at cfg second < E.slot_at cfg q
  candidate_known : candidate ∈
    (E.store cfg ext validator second).block_roots
  head_known : (get_head cfg
    (E.store cfg ext validator second)).root ∈
      (E.store cfg ext validator second).block_roots
  head_descends_candidate : is_ancestor
    (E.store cfg ext validator second)
    (get_head cfg (E.store cfg ext validator second))
    (get_node_for_root candidate) = true

/-- Honest-supporter unwinding with the actual past `get_head` equation kept
in the result.  This is the same validator-spec argument as the old minimal
projection, but no longer erases the fact needed for HFC inversion. -/
theorem pastHead_of_honestSupporter_known
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (v : ValidatorIndex) (n : Nat) (b : Root)
    (hH : E.WithinHorizon cfg n)
    (i : ValidatorIndex) (hi : i ∈ E.honest) (lm : LatestMessage Root)
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext v n)
      (get_supported_node (E.store cfg ext v n) lm)
      (get_node_for_root b) = true) :
    ∃ nu : Nat,
      E.WithinHorizon cfg nu ∧
      E.slot_at cfg nu < E.slot_at cfg n ∧
      (get_head cfg (E.store cfg ext i nu)).root ∈
        (E.store cfg ext i nu).block_roots ∧
      is_ancestor (E.store cfg ext v n)
        (get_head cfg (E.store cfg ext i nu))
        (get_node_for_root b) = true := by
  let hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hT.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk :=
    ⟨ast, ablk, hgeq⟩
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hT.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  obtain ⟨a', sender, sentAt, ifb, hsched, hiatt, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen0 v n i lm hlm
  obtain ⟨_voteAt, own, hvote, hdata⟩ :=
    hT.honest_behavior.no_forgery sender sentAt a' ifb hsched i hi hiatt
  set s := a'.data.slot
  have hcomm : i ∈ E.committee s :=
    hT.honest_behavior.votes_assigned i hi s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨ap, _hiap, _htarget, _hbbrap, hapEpoch, hapBound, hapComm,
      hlmKnown, hlmSlot⟩ :=
    E.latestMessageProvenance cfg ext hT.wellFormed
      hT.externals_coherence hgen0 v n i lm hlm
  have hepoch : compute_epoch_at_slot cfg s =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, hapEpoch]
  have hsap : s = ap.data.slot :=
    hT.externals_coherence.committee_assignment_unique i s ap.data.slot
      hcomm hapComm hepoch
  have hslt : s < E.slot_at cfg n := by
    rw [hsap]
    exact Nat.lt_of_succ_le hapBound
  have hanchorle : ablk.message.slot ≤
      ((E.store cfg ext v n).blocks lm.root).slot :=
    E.store_anchor_min_slot cfg ext hT.wellFormed hT.externals_coherence
      hgeq hslot hroot v n lm.root hlmKnown
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
  refine ⟨nu, hHnu, ?_, hheadKnown, ?_⟩
  · rw [hnu]
    exact hslt
  · change is_ancestor (E.store cfg ext v n)
      (ForkChoiceNode.mk (get_head cfg (E.store cfg ext i nu)).root)
      (get_node_for_root b) = true
    rw [hhead]
    simpa only [get_supported_node, get_node_for_root] using hsupp

/-- A concrete confirmation produces the full strictly-past honest-head
carrier.  Semantic execution ancestry is extracted in the query store and
reflected into the past store, so no cross-store total-map equality is used. -/
theorem confirmed_honestPastHeadBelow
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    (hquery : query.store = E.store cfg ext v q)
    {candidate : Root}
    (hcandidate : candidate ∈ query.store.block_roots)
    (hparentCandidate : (query.store.blocks candidate).parent_root ∈
      query.store.block_roots)
    (hconfirmed : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) candidate = true) :
    Nonempty (E.AcceptedHonestPastHeadBelowAt cfg ext v q candidate) := by
  let hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv q
      query hquery candidate hqH
      (by simpa only [hquery] using hcandidate)
      (by simpa only [hquery] using hparentCandidate) hconfirmed
  obtain ⟨nu, hnuH, hnuq, hheadPast, hheadCandidateQ⟩ :=
    E.pastHead_of_honestSupporter_known cfg ext hT hsync hstatic hbyz
      hdomain v q candidate hqH i hi lm hlm hsupp
  have hrelayGate : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
    (Nat.succ_le_iff.mpr hnuq).trans
      (E.slot_at_mono cfg (Nat.le_succ q))
  have hheadQueryE : (get_head cfg (E.store cfg ext i nu)).root ∈
      (E.store cfg ext v q).block_roots :=
    hsync.block_relay i hi nu _ hnuH hheadPast v hv q hqH hrelayGate
  have hheadQuery : (get_head cfg (E.store cfg ext i nu)).root ∈
      query.store.block_roots := by
    simpa only [hquery] using hheadQueryE
  obtain ⟨hparentQ, hwalkQ, _hjustifiedQ⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv q hqH
  have hsemantic : E.RootDescends
      (get_head cfg (E.store cfg ext i nu)).root candidate :=
    E.rootDescends_of_store_ancestor (E.blockProvenance cfg ext v q)
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

/-! ## Past HFC inversion -/

/-- Add the one path demanded by the path-local finality consumer to an
ordinary executable viable-leaf witness. -/
theorem pathLocalFilterViableLeafBelow_of_filterViable
    {store : Store Root} {candidate : Root}
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    (hcandidate : candidate ∈ store.block_roots)
    (h : FilterViableLeafBelow cfg store candidate) :
    PathLocalFilterViableLeafBelow cfg store candidate := by
  obtain ⟨tip, htip, hdesc, hleaf, hsource, hfinalized⟩ := h
  exact ⟨tip, htip, hdesc, hleaf, hsource, hfinalized,
    hwalk candidate hcandidate tip htip⟩

/-- Exact past-head split.  The right branch is the same HFC leaf and path
which later supplies both source recency and finalized compatibility. -/
theorem AcceptedHonestPastHeadBelowAt.directJustified_or_pathLocal
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} {q : Nat} {candidate : Root}
    (h : E.AcceptedHonestPastHeadBelowAt cfg ext v q candidate) :
    is_ancestor (E.store cfg ext h.validator h.second)
        (get_node_for_root
          (E.store cfg ext h.validator h.second).justified_checkpoint.root)
        (get_node_for_root candidate) = true ∨
      PathLocalFilterViableLeafBelow cfg
        (E.store cfg ext h.validator h.second) candidate := by
  obtain ⟨hparent, hwalk, _hjustified⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain h.validator
      h.validator_honest h.second h.second_within
  have hsplit := queryHead_direct_or_viableLeafBelow cfg hparent hwalk
    (hdomain.justified_root_known h.validator h.validator_honest
      h.second h.second_within)
    h.candidate_known h.head_descends_candidate
  rcases hsplit with hdirect | hviable
  · exact Or.inl hdirect
  · exact Or.inr
      (pathLocalFilterViableLeafBelow_of_filterViable cfg hwalk
        h.candidate_known hviable)

/-! ## Lemmas 24 and 25 -/

/-- Paper Lemma 24 in its exact accepted-store form: at the first second of
epoch `e`, this honest validator knows one root whose executable voting source
is at most two epochs old.  This is source-only history, not a filter or
safety conclusion. -/
structure AcceptedLemma24EpochStartSourceAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (e : Epoch) (w : ValidatorIndex) where
  seed : Root
  seed_known : seed ∈
    (E.store cfg ext w
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots
  source_recent : e ≤
    (get_voting_source cfg
      (E.store cfg ext w
        (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) seed).epoch + 2

/-- The exact boundary specialization of paper Lemma 22.

The seed is retained in both places named by the paper: an honest view which
strictly predates the epoch boundary and the same validator's view at the
boundary itself.  Its ancestry to the previous-epoch candidate is checked in
the former store, while the executable voting source is read in the latter.
`relay_gate` is the literal one-slot synchrony deadline used by Lemma 24; it
does not assert that any other validator has already received the seed. -/
structure AcceptedLemma22EpochStartCandidateSourceAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (e : Epoch) (candidate : Root) where
  validator : ValidatorIndex
  second : Nat
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  boundary_within : E.WithinHorizon cfg
    (E.slot_start cfg (compute_start_slot_at_epoch cfg e))
  strictly_before_boundary : second <
    E.slot_start cfg (compute_start_slot_at_epoch cfg e)
  relay_gate : E.slot_at cfg second + 1 ≤
    E.slot_at cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e) + 1)
  candidate_known : candidate ∈
    (E.store cfg ext validator second).block_roots
  seed : Root
  seed_known_past : seed ∈
    (E.store cfg ext validator second).block_roots
  seed_descends_candidate : is_ancestor
    (E.store cfg ext validator second)
    (get_node_for_root seed) (get_node_for_root candidate) = true
  seed_known_boundary : seed ∈
    (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots
  boundary_epoch : get_current_store_epoch cfg
    (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) = e
  source_recent : e ≤
    (get_voting_source cfg
      (E.store cfg ext validator
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) seed).epoch + 2

/-- The candidate-specific payload retained while a confirmed candidate is
current-epoch.  This is the information which paper Lemma 22 needs one epoch
later: the candidate and its Lemma-13 seed were already known together in an
honest store, the seed descended from the candidate there, and its accepted
`GU` was at most one epoch behind that store's clock.

Unlike `AcceptedLemma13SourceSeedAt`, this structure remembers the exact
installation second.  That temporal index is essential: at the next epoch
boundary the old-block executable selector reads `GU(seed)`, and synchrony
can relay the same concrete seed from the pre-boundary store. -/
structure AcceptedCurrentCandidateSourceOriginAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (upper : Nat) (candidate : Root) where
  originSecond : Nat
  origin_le : originSecond ≤ upper
  origin_within : E.WithinHorizon cfg originSecond
  candidate_known : candidate ∈
    (E.store cfg ext v originSecond).block_roots
  candidate_current : get_block_epoch cfg
      (E.store cfg ext v originSecond) candidate =
    get_current_store_epoch cfg (E.store cfg ext v originSecond)
  seed : Root
  seed_known : seed ∈ (E.store cfg ext v originSecond).block_roots
  seed_descends_candidate : is_ancestor
    (E.store cfg ext v originSecond)
    (get_node_for_root seed) (get_node_for_root candidate) = true
  gu_recent : get_current_store_epoch cfg
      (E.store cfg ext v originSecond) ≤ (B.state.GU seed).epoch + 1

/-- Forget only the upper time bound; the candidate-specific origin itself is
unchanged. -/
def AcceptedCurrentCandidateSourceOriginAt.mono_upper
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    {v : ValidatorIndex} {n m : Nat} {candidate : Root}
    (h : E.AcceptedCurrentCandidateSourceOriginAt
      cfg ext B v n candidate)
    (hnm : n ≤ m) :
    E.AcceptedCurrentCandidateSourceOriginAt cfg ext B v m candidate :=
  { h with origin_le := h.origin_le.trans hnm }

/-- A strict current-epoch selector advance installs a fresh
candidate-specific history origin.  All expensive query reasoning remains in
the Lemma-13 producer; this theorem retains the query
second instead of erasing it. -/
theorem StrictSelectedResultMechanicalFacts.currentCandidateSourceOrigin
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {v : ValidatorIndex} {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext v q)
    (hparent : ParentSlotLt query.store)
    (hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : input ∈ query.store.block_roots)
    (hout : find_latest_confirmed_descendant cfg ext query input = result)
    (hstrict : result ≠ input)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) ≠ true) :
    Nonempty (E.AcceptedCurrentCandidateSourceOriginAt
      cfg ext B v q result) := by
  obtain ⟨seed, hseed, hdesc, hrecent⟩ :=
    h.current_lemma13SourceSeed_of_notStart cfg ext B
      (by rw [hquery]; exact E.store_causal cfg ext v q)
      hparent hwalk hhead hinput hout hstrict hcurrent hnotStart
  exact ⟨{
    originSecond := q
    origin_le := Nat.le_refl q
    origin_within := hqH
    candidate_known := by simpa only [hquery] using h.result_known
    candidate_current := by simpa only [hquery] using hcurrent
    seed := seed
    seed_known := by simpa only [hquery] using hseed
    seed_descends_candidate := by simpa only [hquery] using hdesc
    gu_recent := by simpa only [hquery] using hrecent
  }⟩

/-- Every accepted eager selector carries a certified checkpoint and is
therefore no earlier than the trusted anchor. -/
theorem ExactPrefixAcceptedFFGSemantics.anchor_epoch_le_gu
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {r : Root} (hr : E.AcceptedRoot cfg ext r) :
    B.anchor.epoch ≤ (B.state.GU r).epoch := by
  obtain ⟨_carrier, _hdesc, hformed⟩ := B.state.gu_AU cfg ext hr
  obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
  exact CertifiedJustified.anchor_epoch_le (cfg := cfg)
    (IncludedCertifiedJustified.toCertifiedJustified
      (cfg := cfg)
      (Execution.AcceptedIncludedAttestationRelation.relation
        cfg ext E B.state.includedAttestations) hincluded)

/-- The trusted anchor itself is a valid current-candidate origin whenever
its concrete root is current-epoch.  This handles initialization and the
only finalized-reset exception left by the causal finalization-lag law. -/
theorem acceptedCurrentCandidateSourceOriginAt_anchor
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} {n : Nat}
    (hHn : E.WithinHorizon cfg n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v n) B.anchor.root =
      get_current_store_epoch cfg (E.store cfg ext v n)) :
    Nonempty (E.AcceptedCurrentCandidateSourceOriginAt
      cfg ext B v n B.anchor.root) := by
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary v n
  have haccepted : E.AcceptedRoot cfg ext B.anchor.root :=
    E.acceptedRoot_of_causal_known cfg ext
      (E.store_causal cfg ext v n) hreal.root_known
  have hblockEpochLeAnchor : get_block_epoch cfg
      (E.store cfg ext v n) B.anchor.root ≤ B.anchor.epoch := by
    have hscaled : get_block_epoch cfg
          (E.store cfg ext v n) B.anchor.root * cfg.slots_per_epoch ≤
        B.anchor.epoch * cfg.slots_per_epoch :=
      (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v n) B.anchor.root).trans
          hreal.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hanchorLeGU :=
    ExactPrefixAcceptedFFGSemantics.anchor_epoch_le_gu
      (E := E) cfg ext B haccepted
  exact ⟨{
    originSecond := n
    origin_le := Nat.le_refl n
    origin_within := hHn
    candidate_known := hreal.root_known
    candidate_current := hcurrent
    seed := B.anchor.root
    seed_known := hreal.root_known
    seed_descends_candidate := is_ancestor_refl _ _
    gu_recent := by
      rw [← hcurrent]
      exact hblockEpochLeAnchor.trans
        (hanchorLeGU.trans (Nat.le_add_right _ _))
  }⟩

/-- Carry a current-epoch candidate origin through the next actual epoch
boundary.  At that boundary the retained seed is old, so the executable
voting-source selector is exactly its accepted `GU`; the Lemma-13 `+1` bound
therefore becomes the paper-Lemma-22 `+2` bound.

The two boundary equations are deliberately explicit.  The trajectory
induction proves them once from the actual FCR call and reuses this theorem in
both the carried and strict-carried boundary branches. -/
theorem AcceptedCurrentCandidateSourceOriginAt.toLemma22AtNextBoundary
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {e : Epoch} {candidate : Root}
    (hboundarySecond : E.slot_start cfg
      (compute_start_slot_at_epoch cfg e) = n + 1)
    (hboundaryEpoch : get_current_store_epoch cfg
      (E.store cfg ext v (n + 1)) = e)
    (hcandidateBoundary : candidate ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (hprevious : get_block_epoch cfg
      (E.store cfg ext v (n + 1)) candidate + 1 = e)
    (h : E.AcceptedCurrentCandidateSourceOriginAt
      cfg ext B v n candidate) :
    Nonempty (E.AcceptedLemma22EpochStartCandidateSourceAt
      cfg ext B e candidate) := by
  obtain ⟨ast, ablk, hgen, hgenSlot, _hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  have horiginLeBoundary : h.originSecond ≤ n + 1 :=
    h.origin_le.trans (Nat.le_succ n)
  have hseedBoundary : h.seed ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v horiginLeBoundary).1 h.seed_known
  have hcandidateAgree :
      (E.store cfg ext v h.originSecond).blocks candidate =
        (E.store cfg ext v (n + 1)).blocks candidate :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v h.originSecond)
      (E.blockProvenance cfg ext v (n + 1))
      h.candidate_known hcandidateBoundary
  have hseedAgree :
      (E.store cfg ext v h.originSecond).blocks h.seed =
        (E.store cfg ext v (n + 1)).blocks h.seed :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v h.originSecond)
      (E.blockProvenance cfg ext v (n + 1))
      h.seed_known hseedBoundary
  have horiginEpochSucc : get_current_store_epoch cfg
        (E.store cfg ext v h.originSecond) + 1 = e := by
    calc
      get_current_store_epoch cfg (E.store cfg ext v h.originSecond) + 1 =
          get_block_epoch cfg
              (E.store cfg ext v h.originSecond) candidate + 1 := by
        rw [h.candidate_current]
      _ = get_block_epoch cfg
              (E.store cfg ext v (n + 1)) candidate + 1 := by
        simp only [get_block_epoch, hcandidateAgree]
      _ = e := hprevious
  have hseedEpochLeOrigin : get_block_epoch cfg
        (E.store cfg ext v h.originSecond) h.seed ≤
      get_current_store_epoch cfg (E.store cfg ext v h.originSecond) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
            v h.originSecond h.seed h.seed_known)
  have hseedOld : get_current_store_epoch cfg
        (E.store cfg ext v (n + 1)) >
      get_block_epoch cfg (E.store cfg ext v (n + 1)) h.seed := by
    rw [hboundaryEpoch]
    have hseedEpochLeOrigin' : get_block_epoch cfg
          (E.store cfg ext v (n + 1)) h.seed ≤
        get_current_store_epoch cfg
          (E.store cfg ext v h.originSecond) := by
      simpa only [get_block_epoch, hseedAgree] using hseedEpochLeOrigin
    exact hseedEpochLeOrigin'.trans_lt
      (by exact Nat.lt_of_succ_le (horiginEpochSucc.le))
  have hsourceEq : get_voting_source cfg
      (E.store cfg ext v (n + 1)) h.seed = B.state.GU h.seed := by
    rw [(E.store_causal cfg ext v (n + 1)
      ).getVotingSource_eq_acceptedSelector cfg ext B hseedBoundary]
    exact if_pos hseedOld
  have hstrictlyBefore : h.originSecond <
      E.slot_start cfg (compute_start_slot_at_epoch cfg e) := by
    rw [hboundarySecond]
    exact lt_of_le_of_lt h.origin_le (Nat.lt_succ_self n)
  have hrelayGate : E.slot_at cfg h.originSecond + 1 ≤
      E.slot_at cfg
        (E.slot_start cfg (compute_start_slot_at_epoch cfg e) + 1) := by
    rw [hboundarySecond]
    have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
      unfold IsFCRCallAt at hcall
      simpa only [E.store_current_slot] using hcall
    calc
      E.slot_at cfg h.originSecond + 1 ≤ E.slot_at cfg n + 1 :=
        Nat.add_le_add_right (E.slot_at_mono cfg h.origin_le) 1
      _ ≤ E.slot_at cfg (n + 1) := Nat.succ_le_iff.mpr hslotAdvance
      _ ≤ E.slot_at cfg (n + 1 + 1) :=
        E.slot_at_mono cfg (Nat.le_succ _)
  exact ⟨{
    validator := v
    second := h.originSecond
    validator_honest := hv
    second_within := h.origin_within
    boundary_within := by simpa only [hboundarySecond] using hHn1
    strictly_before_boundary := hstrictlyBefore
    relay_gate := hrelayGate
    candidate_known := h.candidate_known
    seed := h.seed
    seed_known_past := h.seed_known
    seed_descends_candidate := h.seed_descends_candidate
    seed_known_boundary := by
      simpa only [hboundarySecond] using hseedBoundary
    boundary_epoch := by
      simpa only [hboundarySecond] using hboundaryEpoch
    source_recent := by
      rw [hboundarySecond, hsourceEq]
      calc
        e = get_current_store_epoch cfg
              (E.store cfg ext v h.originSecond) + 1 :=
          horiginEpochSucc.symm
        _ ≤ ((B.state.GU h.seed).epoch + 1) + 1 :=
          Nat.add_le_add_right h.gu_recent 1
        _ = (B.state.GU h.seed).epoch + 2 := by
          simp only [Nat.add_assoc, Nat.reduceAdd]
  }⟩

/-- Paper Lemma 24 from one exact Lemma-22 boundary witness.

The past copy of the seed is relayed to the target validator at the epoch
boundary.  Accepted fixed-root selector monotonicity then transports the
source epoch between the two same-epoch causal stores. -/
theorem AcceptedLemma22EpochStartCandidateSourceAt.lemma24
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    {e : Epoch} {candidate : Root}
    (h : E.AcceptedLemma22EpochStartCandidateSourceAt
      cfg ext B e candidate)
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B e w) := by
  let boundary := E.slot_start cfg (compute_start_slot_at_epoch cfg e)
  have hseedW : h.seed ∈ (E.store cfg ext w boundary).block_roots :=
    hsync.block_relay h.validator h.validator_honest h.second h.seed
      h.second_within h.seed_known_past w hw boundary h.boundary_within
        (by simpa only [boundary] using h.relay_gate)
  have hwEpoch : get_current_store_epoch cfg
      (E.store cfg ext w boundary) = e := by
    simpa only [get_current_store_epoch, E.store_current_slot, boundary]
      using h.boundary_epoch
  have hclock : get_current_store_epoch cfg
      (E.store cfg ext h.validator boundary) ≤
      get_current_store_epoch cfg (E.store cfg ext w boundary) := by
    rw [h.boundary_epoch, hwEpoch]
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hT.wellFormed
      (E.store_causal cfg ext h.validator boundary)
      (E.store_causal cfg ext w boundary)
      (by simpa only [boundary] using h.seed_known_boundary)
      hseedW hclock
  exact ⟨{
    seed := h.seed
    seed_known := by simpa only [boundary] using hseedW
    source_recent := h.source_recent.trans
      (Nat.add_le_add_right hsourceMono 2)
  }⟩

/-- The observed-restart arm of one actual epoch-start FCR call supplies the
exact paper-Lemma-22 seed.  The cache ghost identifies an installation
second `k ≤ n`.  If the installed UJ checkpoint is `GU(tip)`, that accepted
installer tip is the seed; if it is the trusted anchor, the anchor root is the
seed.  In both cases the executable query guard supplies the previous-epoch
equation, and the accepted reset realization supplies the checkpoint-root
geometry. -/
theorem ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {trace : GetLatestConfirmedTrace cfg ext (E.fcrStep cfg ext v n)}
    (h : ObservedResetCandidateInputAt cfg ext
      (E.fcrStep cfg ext v n) trace) :
    Nonempty (E.AcceptedLemma22EpochStartCandidateSourceAt cfg ext B
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
      (E.fcrStep cfg ext v n
        ).current_epoch_observed_justified_checkpoint.root) := by
  let hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  let e := get_current_store_epoch cfg (E.store cfg ext v (n + 1))
  let c := (E.fcrStep cfg ext v n
    ).current_epoch_observed_justified_checkpoint
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hgenSlot⟩
  obtain ⟨hi⟩ :=
    FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedInstallation
      (E := E) cfg ext B hgenShort hanchor hspe h
  have horiginLeBoundary : hi.originSecond ≤ n + 1 :=
    hi.origin_le.trans (Nat.le_succ n)
  have horiginH : E.WithinHorizon cfg hi.originSecond :=
    E.withinHorizon_mono cfg horiginLeBoundary hHn1
  have hstart : is_start_slot_at_epoch cfg (E.slot_at cfg (n + 1)) = true := by
    simpa only [E.fcrStep_store, E.store_current_slot] using h.epoch_start
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    have hslotAdvanceRaw := hcall
    unfold IsFCRCallAt at hslotAdvanceRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hslotAdvanceRaw
    exact hslotAdvanceRaw
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq] using hstart
  have hslotBoundaryRaw : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg e := by
    simpa only [e, get_current_store_epoch, E.store_current_slot]
      using hslotBoundaryRaw
  have hboundarySecond :
      E.slot_start cfg (compute_start_slot_at_epoch cfg e) = n + 1 := by
    rw [← hslotBoundary]
    obtain ⟨hstartLe, _hstartH, hslotStart, _hgate⟩ :=
      E.query_slot_start_facts_minimal cfg ext hA (n + 1) hHn1
    apply Nat.le_antisymm hstartLe
    by_contra hnot
    have hlt : E.slot_start cfg (E.slot_at cfg (n + 1)) < n + 1 :=
      Nat.lt_of_not_ge hnot
    have hleN : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ n :=
      Nat.lt_succ_iff.mp hlt
    have hslotLe := E.slot_at_mono cfg hleN
    rw [hslotStart] at hslotLe
    exact (Nat.not_lt_of_ge hslotLe) hslotAdvance
  have hcPrevEpoch : get_block_epoch cfg (E.store cfg ext v (n + 1))
      c.root + 1 = e := by
    simpa only [E.fcrStep_store, c, e] using h.observed_previous_epoch
  have hcField : c =
      (E.store cfg ext v hi.originSecond
        ).unrealized_justified_checkpoint := hi.field_eq
  have hrealOrigin : E.ResetCheckpointRealizedAt cfg B.anchor
      (E.store cfg ext v hi.originSecond) c := by
    have hrealField :=
      E.unrealizedJustifiedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
        cfg ext B hT hanchor hboundary (w := v) hi.originSecond
    simpa only [hcField] using hrealField
  have hrealBoundary : E.ResetCheckpointRealizedAt cfg B.anchor
      (E.store cfg ext v (n + 1)) c :=
    hrealOrigin.mono_of_trajectory cfg ext E hT horiginLeBoundary
  have hcBlockEpochLe : get_block_epoch cfg
      (E.store cfg ext v (n + 1)) c.root ≤ c.epoch := by
    have hscaled : get_block_epoch cfg
          (E.store cfg ext v (n + 1)) c.root * cfg.slots_per_epoch ≤
        c.epoch * cfg.slots_per_epoch := by
      exact (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v (n + 1)) c.root).trans
          hrealBoundary.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hcRecent : e ≤ c.epoch + 2 := by
    calc
      e = get_block_epoch cfg (E.store cfg ext v (n + 1)) c.root + 1 :=
        hcPrevEpoch.symm
      _ ≤ c.epoch + 1 := Nat.add_le_add_right hcBlockEpochLe 1
      _ ≤ c.epoch + 2 := Nat.add_le_add_left (Nat.le_succ 1) c.epoch
  have hboundaryEpoch : get_current_store_epoch cfg
      (E.store cfg ext v
        (E.slot_start cfg (compute_start_slot_at_epoch cfg e))) = e := by
    rw [hboundarySecond]
  have hcandidateKnownBoundary : c.root ∈
      (E.store cfg ext v
        (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots := by
    rw [hboundarySecond]
    exact hrealBoundary.root_known
  have hboundaryH : E.WithinHorizon cfg
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e)) := by
    rw [hboundarySecond]
    exact hHn1
  have hstrictlyBefore : hi.originSecond <
      E.slot_start cfg (compute_start_slot_at_epoch cfg e) := by
    rw [hboundarySecond]
    exact lt_of_le_of_lt hi.origin_le (Nat.lt_succ_self n)
  have hrelayGate : E.slot_at cfg hi.originSecond + 1 ≤
      E.slot_at cfg
        (E.slot_start cfg (compute_start_slot_at_epoch cfg e) + 1) := by
    rw [hboundarySecond]
    calc
      E.slot_at cfg hi.originSecond + 1 ≤
          E.slot_at cfg n + 1 :=
        Nat.add_le_add_right (E.slot_at_mono cfg hi.origin_le) 1
      _ ≤ E.slot_at cfg (n + 1) := Nat.succ_le_iff.mpr hslotAdvance
      _ ≤ E.slot_at cfg (n + 1 + 1) :=
        E.slot_at_mono cfg (Nat.le_succ _)
  rcases hi.accepted_origin with hanchorField | ⟨tip, htip, hguField⟩
  · have hcAnchor : c = B.anchor := hcField.trans hanchorField
    have hcRootEpochLt : get_block_epoch cfg
        (E.store cfg ext v (n + 1)) c.root < e := by
      rw [← hcPrevEpoch]
      exact Nat.lt_succ_self _
    have hcRootOld : get_current_store_epoch cfg
        (E.store cfg ext v (n + 1)) >
          get_block_epoch cfg (E.store cfg ext v (n + 1)) c.root := by
      simpa only [e] using hcRootEpochLt
    have hcAccepted : E.AcceptedRoot cfg ext c.root :=
      E.acceptedRoot_of_causal_known cfg ext
        (E.store_causal cfg ext v (n + 1)) hrealBoundary.root_known
    obtain ⟨carrier, _hdesc, hformed⟩ :=
      B.state.gu_AU cfg ext hcAccepted
    obtain ⟨hincluded⟩ := (B.state.formed_evidence hformed).certified
    have hguCertified : CertifiedJustified cfg E B.anchor
        (B.state.GU c.root) :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation
          cfg ext E B.state.includedAttestations) hincluded
    have hanchorEpochLeGU : B.anchor.epoch ≤
        (B.state.GU c.root).epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hguCertified
    have hcEpochLeGU : c.epoch ≤ (B.state.GU c.root).epoch := by
      exact (congrArg Checkpoint.epoch hcAnchor).le.trans hanchorEpochLeGU
    have hsourceEq : get_voting_source cfg
        (E.store cfg ext v (n + 1)) c.root = B.state.GU c.root := by
      rw [(E.store_causal cfg ext v (n + 1)
        ).getVotingSource_eq_acceptedSelector cfg ext B
          hrealBoundary.root_known]
      exact if_pos hcRootOld
    exact ⟨{
      validator := v
      second := hi.originSecond
      validator_honest := hv
      second_within := horiginH
      boundary_within := hboundaryH
      strictly_before_boundary := hstrictlyBefore
      relay_gate := hrelayGate
      candidate_known := hrealOrigin.root_known
      seed := c.root
      seed_known_past := hrealOrigin.root_known
      seed_descends_candidate := is_ancestor_refl _ _
      seed_known_boundary := hcandidateKnownBoundary
      boundary_epoch := hboundaryEpoch
      source_recent := by
        rw [hboundarySecond, hsourceEq]
        exact hcRecent.trans (Nat.add_le_add_right hcEpochLeGU 2)
    }⟩
  · have hcGU : c = B.state.GU tip := hcField.trans hguField
    have htipBoundary : tip ∈
        (E.store cfg ext v (n + 1)).block_roots :=
      (E.store_storeLE cfg ext v horiginLeBoundary).1 htip.known
    have htipBoundaryNamed : tip ∈
        (E.store cfg ext v
          (E.slot_start cfg (compute_start_slot_at_epoch cfg e))).block_roots := by
      simpa only [hboundarySecond] using htipBoundary
    have hparentOrigin : ParentSlotLt
        (E.store cfg ext v hi.originSecond) :=
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩
        hT.wellFormed.anchor_parent_unscheduled v hi.originSecond
    have hwalkTipCandidate : WalkKnown
        (E.store cfg ext v hi.originSecond)
        ((E.store cfg ext v hi.originSecond).blocks c.root).slot tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ v hi.originSecond
        c.root hrealOrigin.root_known tip htip.known
    have hAU : B.state.AU cfg ext tip c := by
      rw [hcGU]
      exact B.state.gu_AU cfg ext htip.acceptedRoot
    have hcheckpoint : c = get_checkpoint_for_block cfg
        (E.store cfg ext v hi.originSecond) tip c.epoch :=
      B.coherence.au_checkpoint_of_known
        (E.store_causal cfg ext v hi.originSecond) tip htip.known c hAU
    have heta : get_ancestor (E.store cfg ext v hi.originSecond)
        (get_node_for_root tip)
        (compute_start_slot_at_epoch cfg c.epoch) =
          get_node_for_root c.root := by
      have hroot := congrArg Checkpoint.root hcheckpoint
      have htargetRoot : get_checkpoint_block cfg
          (E.store cfg ext v hi.originSecond) tip c.epoch = c.root := by
        simpa only [get_checkpoint_for_block] using hroot.symm
      simp only [get_checkpoint_block] at htargetRoot
      generalize hnode : get_ancestor (E.store cfg ext v hi.originSecond)
        (get_node_for_root tip)
        (compute_start_slot_at_epoch cfg c.epoch) = node
      simp only [get_node_for_root] at hnode ⊢
      rw [hnode] at htargetRoot
      obtain ⟨r⟩ := node
      change r = c.root at htargetRoot
      cases htargetRoot
      rfl
    have htipCandidate : is_ancestor
        (E.store cfg ext v hi.originSecond)
        (get_node_for_root tip) (get_node_for_root c.root) = true := by
      have hcomp := get_ancestor_comp hparentOrigin
        hrealOrigin.root_slot_le_boundary hwalkTipCandidate
      simp only [get_node_for_root] at heta hcomp
      rw [heta] at hcomp
      have hstop : get_ancestor (E.store cfg ext v hi.originSecond)
          (get_node_for_root c.root)
          ((E.store cfg ext v hi.originSecond).blocks c.root).slot =
            get_node_for_root c.root :=
        get_ancestor_stop (Nat.le_refl _)
      simp only [get_node_for_root] at hstop hcomp
      simp only [is_ancestor, get_node_for_root, decide_eq_true_eq]
      exact hcomp.symm.trans hstop
    have htipBlockAgree :
        (E.store cfg ext v hi.originSecond).blocks tip =
          (E.store cfg ext v (n + 1)).blocks tip :=
      hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext v hi.originSecond)
        (E.blockProvenance cfg ext v (n + 1)) htip.known htipBoundary
    have htipSlotOriginRaw :
        ((E.store cfg ext v hi.originSecond).blocks tip).slot ≤
          get_current_slot cfg (E.store cfg ext v hi.originSecond) :=
      E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
        v hi.originSecond tip htip.known
    have htipSlotOrigin :
        ((E.store cfg ext v hi.originSecond).blocks tip).slot ≤
          E.slot_at cfg hi.originSecond := by
      simpa only [E.store_current_slot] using htipSlotOriginRaw
    have htipSlotLtBoundary :
        ((E.store cfg ext v (n + 1)).blocks tip).slot <
          E.slot_at cfg (n + 1) := by
      rw [← htipBlockAgree]
      exact htipSlotOrigin.trans
        (E.slot_at_mono cfg hi.origin_le) |>.trans_lt hslotAdvance
    have htipOld : get_current_store_epoch cfg
        (E.store cfg ext v (n + 1)) >
          get_block_epoch cfg (E.store cfg ext v (n + 1)) tip := by
      have hepochLt : get_block_epoch cfg
          (E.store cfg ext v (n + 1)) tip < e := by
        have htipSlotLtStart := htipSlotLtBoundary
        rw [hslotBoundary] at htipSlotLtStart
        simp only [get_block_epoch, compute_epoch_at_slot]
        apply (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).2
        simpa only [compute_start_slot_at_epoch] using htipSlotLtStart
      simpa only [e] using hepochLt
    have hsourceEq : get_voting_source cfg
        (E.store cfg ext v (n + 1)) tip = c := by
      rw [(E.store_causal cfg ext v (n + 1)
        ).getVotingSource_eq_acceptedSelector cfg ext B htipBoundary]
      rw [if_pos htipOld]
      exact hcGU.symm
    exact ⟨{
      validator := v
      second := hi.originSecond
      validator_honest := hv
      second_within := horiginH
      boundary_within := hboundaryH
      strictly_before_boundary := hstrictlyBefore
      relay_gate := hrelayGate
      candidate_known := hrealOrigin.root_known
      seed := tip
      seed_known_past := htip.known
      seed_descends_candidate := htipCandidate
      seed_known_boundary := htipBoundaryNamed
      boundary_epoch := hboundaryEpoch
      source_recent := by
        rw [hboundarySecond, hsourceEq]
        exact hcRecent
    }⟩

/-- Low epochs discharge the paper's truncated `e - 2` bound without any
candidate-history induction.  The trusted genesis root is carried into the
epoch-start store and every checkpoint epoch is nonnegative. -/
noncomputable def acceptedLemma24EpochStartSourceAt_of_epoch_le_two
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {e : Epoch} (he : e ≤ 2) (w : ValidatorIndex) :
    E.AcceptedLemma24EpochStartSourceAt cfg ext B e w := by
  refine {
    seed := B.anchor.root
    seed_known := ?_
    source_recent := ?_
  }
  · obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
    have hanchorRoot : B.anchor.root = ablk.root := by
      rw [hanchor, hgen]
      rfl
    have hknown0 : B.anchor.root ∈ (E.store cfg ext w 0).block_roots := by
      change B.anchor.root ∈ E.genesis_store.block_roots
      rw [hgen, hanchorRoot]
      simp only [get_forkchoice_store, List.mem_singleton]
    exact (E.store_storeLE cfg ext w (Nat.zero_le
      (E.slot_start cfg (compute_start_slot_at_epoch cfg e)))).1 hknown0
  · exact he.trans (Nat.le_add_left 2 _)

/-- Checkpoint-sync-safe low/base case.  Absolute `e ≤ 2` is sufficient for
fresh genesis, but a trusted checkpoint-sync anchor may start at a nonzero
epoch.  In that setting the correct base region is
`e ≤ anchor.epoch + 2`: the anchor root is known at the boundary and either
accepted selector arm (`GJ` or `GU`) is certified above the anchor. -/
theorem acceptedLemma24EpochStartSourceAt_of_anchor_near
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {e : Epoch} (he : e ≤ B.anchor.epoch + 2)
    (w : ValidatorIndex) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B e w) := by
  let boundary := E.slot_start cfg (compute_start_slot_at_epoch cfg e)
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary w boundary
  have haccepted : E.AcceptedRoot cfg ext B.anchor.root :=
    E.acceptedRoot_of_causal_known cfg ext
      (E.store_causal cfg ext w boundary) hreal.root_known
  have hanchorLeSource : B.anchor.epoch ≤
      (get_voting_source cfg (E.store cfg ext w boundary)
        B.anchor.root).epoch := by
    rw [(E.store_causal cfg ext w boundary
      ).getVotingSource_eq_acceptedSelector cfg ext B hreal.root_known]
    split_ifs
    · exact ExactPrefixAcceptedFFGSemantics.anchor_epoch_le_gu
        (E := E) cfg ext B haccepted
    · obtain ⟨hcertified⟩ := B.state.gj_certified cfg ext haccepted
      exact CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
  exact ⟨{
    seed := B.anchor.root
    seed_known := by simpa only [boundary] using hreal.root_known
    source_recent := he.trans (Nat.add_le_add_right hanchorLeSource 2)
  }⟩

/-! ### One-second clock geometry used by the history fold -/

/-- A whole-second execution advances by at most one slot per trajectory
second. -/
private theorem sourceHistory_slot_at_succ_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (n : Nat) : E.slot_at cfg (n + 1) ≤ E.slot_at cfg n + 1 := by
  obtain ⟨secondsPerSlot, hduration⟩ := hdiv
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  have hdenPos : 0 < cfg.slot_duration_ms / 1000 := by
    rw [hduration, Nat.mul_div_cancel_left secondsPerSlot
      (by omega : (0 : Nat) < 1000)]
    exact hsecondsPos
  have hdiv' : 1000 ∣ cfg.slot_duration_ms := ⟨secondsPerSlot, hduration⟩
  rw [E.slot_at_eq cfg hdiv', E.slot_at_eq cfg hdiv']
  have hnum : E.genesis_store.time + (n + 1) -
        E.genesis_store.genesis_time =
      (E.genesis_store.time + n - E.genesis_store.genesis_time) + 1 := by
    omega
  rw [hnum]
  let a := E.genesis_store.time + n - E.genesis_store.genesis_time
  calc
    (a + 1) / (cfg.slot_duration_ms / 1000) ≤
        (a + cfg.slot_duration_ms / 1000) /
          (cfg.slot_duration_ms / 1000) :=
      Nat.div_le_div_right (by omega)
    _ = a / (cfg.slot_duration_ms / 1000) + 1 :=
      Nat.add_div_right a hdenPos

/-- Crossing an epoch in exactly one slot lands at an epoch boundary. -/
private theorem sourceHistory_slotsSince_succ_eq_zero_of_epoch_lt
    (s : Slot)
    (h : compute_epoch_at_slot cfg s <
      compute_epoch_at_slot cfg (s + 1)) :
    compute_slots_since_epoch_start cfg (s + 1) = 0 := by
  change s / cfg.slots_per_epoch <
    (s + 1) / cfg.slots_per_epoch at h
  have hq : s / cfg.slots_per_epoch + 1 ≤
      (s + 1) / cfg.slots_per_epoch := Nat.succ_le_of_lt h
  have hlo : (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch ≤
      s + 1 :=
    (Nat.le_div_iff_mul_le cfg.slots_per_epoch_pos).mp hq
  have hhi : s <
      (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch :=
    (Nat.div_lt_iff_lt_mul cfg.slots_per_epoch_pos).mp
      (Nat.lt_succ_self (s / cfg.slots_per_epoch))
  have heq : s + 1 =
      (s / cfg.slots_per_epoch + 1) * cfg.slots_per_epoch :=
    Nat.le_antisymm (Nat.succ_le_of_lt hhi) hlo
  simp only [compute_slots_since_epoch_start,
    compute_start_slot_at_epoch, compute_epoch_at_slot]
  rw [heq, Nat.mul_div_cancel _ cfg.slots_per_epoch_pos]
  exact Nat.sub_self _

/-- An actual call which lands away from an epoch start stays in the previous
store's epoch. -/
theorem actualCall_currentEpoch_eq_of_notStart
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hnotStart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) ≠ true) :
    get_current_store_epoch cfg (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
      ).time_ge_genesis
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hslt : s < next := by
    have hsltRaw := hcall
    unfold IsFCRCallAt at hsltRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hsltRaw
    exact hsltRaw
  have hnextLe : next ≤ s + 1 := by
    exact E.sourceHistory_slot_at_succ_le cfg hT.whole_seconds hgenTime n
  have hnextEq : next = s + 1 := Nat.le_antisymm hnextLe
    (Nat.succ_le_of_lt hslt)
  have hnz : compute_slots_since_epoch_start cfg next ≠ 0 := by
    intro hz
    apply hnotStart
    simp only [is_start_slot_at_epoch, E.store_current_slot, next, hz,
      decide_true]
  have hreverse : compute_epoch_at_slot cfg next ≤
      compute_epoch_at_slot cfg s := by
    rw [hnextEq] at hnz ⊢
    by_contra hle
    exact hnz (sourceHistory_slotsSince_succ_eq_zero_of_epoch_lt
      (cfg := cfg) s (Nat.lt_of_not_ge hle))
  have hforward : compute_epoch_at_slot cfg s ≤
      compute_epoch_at_slot cfg next := ce_mono cfg hslt.le
  simpa only [get_current_store_epoch, E.store_current_slot, s, next] using
    Nat.le_antisymm hforward hreverse

/-- An actual call which lands at an epoch start came from the immediately
previous epoch. -/
theorem actualCall_currentEpoch_succ_of_start
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true) :
    get_current_store_epoch cfg (E.store cfg ext v n) + 1 =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
  obtain ⟨ast, ablk, hgen, hslot, hparent⟩ := hT.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    rw [hgen]
    exact (wellFormedStore_get_forkchoice_store cfg ast ablk hslot hparent
      ).time_ge_genesis
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hslt : s < next := by
    have hsltRaw := hcall
    unfold IsFCRCallAt at hsltRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hsltRaw
    exact hsltRaw
  have hnextLe : next ≤ s + 1 :=
    E.sourceHistory_slot_at_succ_le cfg hT.whole_seconds hgenTime n
  have hnextEq : next = s + 1 := Nat.le_antisymm hnextLe
    (Nat.succ_le_of_lt hslt)
  have hzero : compute_slots_since_epoch_start cfg next = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
      E.store_current_slot, next] using hstart
  have hboundary : next = compute_start_slot_at_epoch cfg
      (compute_epoch_at_slot cfg next) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hzero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hzero)
      (Nat.div_mul_le_self next cfg.slots_per_epoch)
  have hepochLt : compute_epoch_at_slot cfg s <
      compute_epoch_at_slot cfg next := by
    apply Nat.lt_of_le_of_ne (ce_mono cfg hslt.le)
    intro heq
    have hstartLeS : compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg next) ≤ s := by
      rw [← heq]
      exact Nat.div_mul_le_self s cfg.slots_per_epoch
    rw [← hboundary] at hstartLeS
    exact (Nat.not_le_of_gt hslt) hstartLeS
  have hepochUpper : compute_epoch_at_slot cfg next ≤
      compute_epoch_at_slot cfg s + 1 := by
    rw [hnextEq]
    simp only [compute_epoch_at_slot]
    calc
      (s + 1) / cfg.slots_per_epoch ≤
          (s + cfg.slots_per_epoch) / cfg.slots_per_epoch :=
        Nat.div_le_div_right
          (Nat.add_le_add_left cfg.slots_per_epoch_pos s)
      _ = s / cfg.slots_per_epoch + 1 :=
        Nat.add_div_right s cfg.slots_per_epoch_pos
  have heq : compute_epoch_at_slot cfg s + 1 =
      compute_epoch_at_slot cfg next :=
    Nat.le_antisymm (Nat.succ_le_of_lt hepochLt) hepochUpper
  simpa only [get_current_store_epoch, E.store_current_slot, s, next] using heq

/-- The execution second of an actual call landing at an epoch boundary is
the canonical `slot_start` second used in Lemmas 22 and 24. -/
theorem actualCall_epochStart_boundarySecond
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (_hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true) :
    E.slot_start cfg (compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1)))) = n + 1 := by
  let hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  let e := get_current_store_epoch cfg (E.store cfg ext v (n + 1))
  have hstartZero : compute_slots_since_epoch_start cfg
      (E.slot_at cfg (n + 1)) = 0 := by
    simpa only [is_start_slot_at_epoch, decide_eq_true_eq,
      E.store_current_slot] using hstart
  have hslotBoundaryRaw : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (E.slot_at cfg (n + 1))) := by
    simp only [compute_slots_since_epoch_start,
      compute_start_slot_at_epoch] at hstartZero ⊢
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hstartZero)
      (Nat.div_mul_le_self _ cfg.slots_per_epoch)
  have hslotBoundary : E.slot_at cfg (n + 1) =
      compute_start_slot_at_epoch cfg e := by
    simpa only [e, get_current_store_epoch, E.store_current_slot]
      using hslotBoundaryRaw
  rw [← hslotBoundary]
  obtain ⟨hstartLe, _hstartH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA (n + 1) hHn1
  apply Nat.le_antisymm hstartLe
  by_contra hnot
  have hlt : E.slot_start cfg (E.slot_at cfg (n + 1)) < n + 1 :=
    Nat.lt_of_not_ge hnot
  have hleN : E.slot_start cfg (E.slot_at cfg (n + 1)) ≤ n :=
    Nat.lt_succ_iff.mp hlt
  have hslotLe := E.slot_at_mono cfg hleN
  rw [hslotStart] at hslotLe
  have hslotAdvance : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    have hslotAdvanceRaw := hcall
    unfold IsFCRCallAt at hslotAdvanceRaw
    rw [E.store_current_slot cfg ext v n,
      E.store_current_slot cfg ext v (n + 1)] at hslotAdvanceRaw
    exact hslotAdvanceRaw
  exact (Nat.not_lt_of_ge hslotLe) hslotAdvance

/-! ### Finalized-reset consumers of the narrow lag invariant -/

/-- A recent finalized reset can only inhabit the trusted-anchor base region.
For a non-anchor finalized checkpoint the causal lag theorem makes its
realized root strictly stale, contradicting recency. -/
theorem finalizedRecent_epoch_le_anchor_add_two
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hrealized : E.ResetCheckpointRealizedAt cfg B.anchor store
      store.finalized_checkpoint)
    (hrecent : get_block_epoch cfg store
          store.finalized_checkpoint.root + 1 ≥
        get_current_store_epoch cfg store) :
    get_current_store_epoch cfg store ≤ B.anchor.epoch + 2 := by
  by_cases hanchorField : store.finalized_checkpoint = B.anchor
  · have hblockEpochLeAnchor : get_block_epoch cfg store
        store.finalized_checkpoint.root ≤ B.anchor.epoch := by
      have hscaled : get_block_epoch cfg store
            store.finalized_checkpoint.root * cfg.slots_per_epoch ≤
          B.anchor.epoch * cfg.slots_per_epoch := by
        have hrootBound : (store.blocks B.anchor.root).slot ≤
            compute_start_slot_at_epoch cfg B.anchor.epoch := by
          simpa only [hanchorField] using hrealized.root_slot_le_boundary
        rw [hanchorField]
        exact (start_slot_at_block_epoch_le cfg store B.anchor.root).trans
          hrootBound
      exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
    exact hrecent.trans
      ((Nat.add_le_add_right hblockEpochLeAnchor 1).trans
        (Nat.add_le_add_left (Nat.le_succ 1) B.anchor.epoch))
  ·
    have hstale := E.finalizedResetRoot_stale_of_causalLag
      cfg ext hLag hstore hrealized hanchorField
    exact False.elim ((Nat.not_lt_of_ge hrecent) hstale)

/-- A finalized root which is current-epoch must be the trusted anchor. -/
theorem finalizedCheckpoint_eq_anchor_of_root_current
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    (hrealized : E.ResetCheckpointRealizedAt cfg B.anchor store
      store.finalized_checkpoint)
    (hcurrent : get_block_epoch cfg store
        store.finalized_checkpoint.root =
      get_current_store_epoch cfg store) :
    store.finalized_checkpoint = B.anchor := by
  by_cases hanchorField : store.finalized_checkpoint = B.anchor
  · exact hanchorField
  · exfalso
    have hstale := E.finalizedResetRoot_stale_of_causalLag
      cfg ext hLag hstore hrealized hanchorField
    rw [hcurrent] at hstale
    exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) hstale

/-- Enrich the strict arm of the exact recurrence with the existing
query-local mechanical facts.  The selector guard plus ordinary block
non-futurity supplies its only missing premise: the input is in the current
or previous block epoch. -/
theorem StrictSelectorAdvanceAt.mechanicalFacts
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root}
    {trace : GetLatestConfirmedTrace cfg ext query}
    (hquery : query.store = E.store cfg ext v q)
    (hinput : trace.afterObserved ∈ query.store.block_roots)
    (h : StrictSelectorAdvanceAt cfg ext query trace) :
    StrictSelectedResultMechanicalFacts cfg ext query
      trace.afterObserved trace.result := by
  let hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
    hT hsync hstatic hbyz hdomain
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hinputEpochUpper : get_block_epoch cfg query.store
        trace.afterObserved ≤ get_current_store_epoch cfg query.store := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        rw [hquery]
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
            v q trace.afterObserved (by simpa only [hquery] using hinput))
  have hinputEpoch : get_block_epoch cfg query.store
          trace.afterObserved = get_current_store_epoch cfg query.store ∨
      get_block_epoch cfg query.store trace.afterObserved + 1 =
        get_current_store_epoch cfg query.store := by
    have hrecent := h.input_recent
    rcases Nat.eq_or_lt_of_le hinputEpochUpper with heq | hlt
    · exact Or.inl heq
    · exact Or.inr (Nat.le_antisymm (Nat.succ_le_iff.mpr hlt) hrecent)
  have hstrictFind : find_latest_confirmed_descendant cfg ext query
      trace.afterObserved ≠ trace.afterObserved := by
    intro hfixed
    exact h.result_ne_input (h.result_eq.trans hfixed)
  have hfacts := E.strictSelectedResultMechanicalFacts cfg ext hA hv hqH
    query hquery trace.afterObserved hinput hinputEpoch hstrictFind
  simpa only [← h.result_eq] using hfacts

/-- At an actual epoch-start call, a recent carried confirmed input was
current-epoch in the immediately preceding store.  This is the exact bridge
from Lemma 23's boundary backtracking to the retained current-origin field. -/
theorem previousConfirmed_current_of_boundary_recent
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true)
    (hknownN : E.confirmed cfg ext v n ∈
      (E.store cfg ext v n).block_roots)
    (hrecentQ : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          (E.confirmed cfg ext v n) + 1 ≥
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) :
    get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v n) := by
  obtain ⟨ast, ablk, hgen, hslot, _hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgen, hslot⟩
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 hknownN
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.confirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1)) hknownN hknownN1
  have hblockEpochEq : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_block_epoch cfg (E.fcrStep cfg ext v n).store
        (E.confirmed cfg ext v n) := by
    rw [E.fcrStep_store]
    simp only [get_block_epoch, hblockAgree]
  have hblockUpper : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) ≤
      get_current_store_epoch cfg (E.store cfg ext v n) := by
    simp only [get_block_epoch, get_current_store_epoch,
      compute_epoch_at_slot]
    exact Nat.div_le_div_right
      (by
        simpa only [E.store_current_slot] using
          E.store_blocks_slot_le_current cfg ext hT.whole_seconds hgenShort
            v n (E.confirmed cfg ext v n) hknownN)
  have hepochSucc := E.actualCall_currentEpoch_succ_of_start
    cfg ext hT hcall hstart
  have hlowerPlus : get_current_store_epoch cfg (E.store cfg ext v n) + 1 ≤
      get_block_epoch cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n) + 1 := by
    calc
      get_current_store_epoch cfg (E.store cfg ext v n) + 1 =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
        hepochSucc
      _ ≤ get_block_epoch cfg (E.fcrStep cfg ext v n).store
            (E.confirmed cfg ext v n) + 1 := by
        simpa only [E.fcrStep_store] using hrecentQ
      _ = get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) + 1 := by rw [← hblockEpochEq]
  exact Nat.le_antisymm hblockUpper
    (Nat.le_of_add_le_add_right hlowerPlus)

/-! ## Candidate-indexed confirmed-history invariant -/

/-- The exact induction payload replacing the broad temporal callback.

For the actual confirmed root at second `n`, every executable-recent case
already owns paper Lemma 24 at the start of that store's epoch.  When the
root is current-epoch, the stronger candidate-specific origin is retained as
well, because that is what advances Lemma 24 across the next boundary.

The source field is quantified over the receiving honest validator, matching
the synchrony conclusion of Lemma 24.  It is not quantified over arbitrary
roots or stores. -/
structure AcceptedConfirmedSourceHistoryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (n : Nat) : Prop where
  confirmed_known : E.confirmed cfg ext v n ∈
    (E.store cfg ext v n).block_roots
  recent_epochStartSource :
    get_block_epoch cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n) + 1 ≥
        get_current_store_epoch cfg (E.store cfg ext v n) →
      ∀ w ∈ E.honest,
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v n)) w)
  current_origin :
    get_block_epoch cfg (E.store cfg ext v n)
          (E.confirmed cfg ext v n) =
        get_current_store_epoch cfg (E.store cfg ext v n) →
      Nonempty (E.AcceptedCurrentCandidateSourceOriginAt
        cfg ext B v n (E.confirmed cfg ext v n))

/-- Initialization of the candidate-indexed history invariant.  This is
checkpoint-sync safe: the numeric base is relative to the trusted anchor
epoch rather than to absolute genesis epoch zero. -/
theorem acceptedConfirmedSourceHistoryAt_zero
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (v : ValidatorIndex) (hH0 : E.WithinHorizon cfg 0) :
    E.AcceptedConfirmedSourceHistoryAt cfg ext B v 0 := by
  obtain ⟨ast, ablk, hgen, _hslot, _hparent⟩ := hT.genesis
  have hconfirmedAnchor : E.confirmed cfg ext v 0 = B.anchor.root := by
    rw [E.confirmed_zero, hanchor]
    change E.genesis_store.finalized_checkpoint.root =
      E.genesis_store.justified_checkpoint.root
    rw [hgen]
    rfl
  have hreal := E.resetCheckpointRealizedAt_anchor_of_acceptedTrajectory
    cfg ext hT hanchor hboundary v 0
  have hblockEpochLeAnchor : get_block_epoch cfg
      (E.store cfg ext v 0) B.anchor.root ≤ B.anchor.epoch := by
    have hscaled : get_block_epoch cfg
          (E.store cfg ext v 0) B.anchor.root * cfg.slots_per_epoch ≤
        B.anchor.epoch * cfg.slots_per_epoch :=
      (start_slot_at_block_epoch_le cfg
        (E.store cfg ext v 0) B.anchor.root).trans
          hreal.root_slot_le_boundary
    exact Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  exact {
    confirmed_known := by simpa only [hconfirmedAnchor] using hreal.root_known
    recent_epochStartSource := by
      intro hrecent w _hw
      have hnear : get_current_store_epoch cfg (E.store cfg ext v 0) ≤
          B.anchor.epoch + 2 := by
        rw [← hconfirmedAnchor] at hblockEpochLeAnchor
        exact hrecent.trans
          ((Nat.add_le_add_right hblockEpochLeAnchor 1).trans
            (Nat.add_le_add_left (Nat.le_succ 1) B.anchor.epoch))
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary hnear w
    current_origin := by
      intro hcurrent
      rw [hconfirmedAnchor] at hcurrent ⊢
      exact E.acceptedCurrentCandidateSourceOriginAt_anchor
        cfg ext B hT hanchor hboundary
          hH0 hcurrent
  }

/-- Between actual FCR calls the cached candidate, its clock epoch, and its
candidate-specific history are all carried definitionally through the
monotone store trajectory. -/
theorem AcceptedConfirmedSourceHistoryAt.succ_of_noCall
    {B : ExactPrefixAcceptedFFGSemantics cfg ext E}
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {n : Nat}
    (hnoCall : ¬ E.IsFCRCallAt cfg ext v n)
    (h : E.AcceptedConfirmedSourceHistoryAt cfg ext B v n) :
    E.AcceptedConfirmedSourceHistoryAt cfg ext B v (n + 1) := by
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 h.confirmed_known
  have hconfirmedEq : E.confirmed cfg ext v (n + 1) =
      E.confirmed cfg ext v n :=
    E.confirmed_succ_of_no_advance cfg ext v n hnoCall
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.confirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1))
      h.confirmed_known hknownN1
  have hslotMono : get_current_slot cfg (E.store cfg ext v n) ≤
      get_current_slot cfg (E.store cfg ext v (n + 1)) := by
    simpa only [E.store_current_slot] using
      E.slot_at_mono cfg (Nat.le_succ n)
  have hslotEq : get_current_slot cfg (E.store cfg ext v n) =
      get_current_slot cfg (E.store cfg ext v (n + 1)) :=
    Nat.le_antisymm hslotMono (Nat.le_of_not_gt hnoCall)
  have hcurrentEpochEq : get_current_store_epoch cfg
      (E.store cfg ext v n) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    simp only [get_current_store_epoch, hslotEq]
  have hblockEpochEq : get_block_epoch cfg (E.store cfg ext v n)
        (E.confirmed cfg ext v n) =
      get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) := by
    simp only [get_block_epoch, hblockAgree]
  exact {
    confirmed_known := by simpa only [hconfirmedEq] using hknownN1
    recent_epochStartSource := by
      intro hrecent w hw
      have hrecentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) + 1 ≥
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochEq, hcurrentEpochEq, ← hconfirmedEq]
        exact hrecent
      have hsource := h.recent_epochStartSource hrecentN w hw
      simpa only [hcurrentEpochEq] using hsource
    current_origin := by
      intro hcurrent
      have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochEq, hcurrentEpochEq, ← hconfirmedEq]
        exact hcurrent
      obtain ⟨horigin⟩ := h.current_origin hcurrentN
      exact ⟨by
        simpa only [hconfirmedEq] using
          (horigin.mono_upper cfg ext (Nat.le_succ n))⟩
  }

/-- Current-origin half of one actual-call history step.  Operationally
unchanged carried roots reuse the induction origin, finalized-current roots
reduce to the trusted anchor, observed-reset roots are previous-epoch, and a
strict current result installs a fresh Lemma-13 origin. -/
theorem AcceptedConfirmedSourceHistoryAt.currentOrigin_succ_of_call
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (h : E.AcceptedConfirmedSourceHistoryAt cfg ext B v n)
    (hcurrent : get_block_epoch cfg (E.store cfg ext v (n + 1))
          (E.confirmed cfg ext v (n + 1)) =
        get_current_store_epoch cfg (E.store cfg ext v (n + 1))) :
    Nonempty (E.AcceptedCurrentCandidateSourceOriginAt cfg ext B v (n + 1)
      (E.confirmed cfg ext v (n + 1))) := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.confirmed cfg ext v (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have htraceCurrent : get_block_epoch cfg query.store trace.result =
      get_current_store_epoch cfg query.store := by
    rw [hconfirmedOut] at hcurrent
    simpa only [query, trace, E.fcrStep_store] using hcurrent
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 h.confirmed_known
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hHn1
  cases hrec.branch with
  | carriedUnchanged hinput hselector =>
      have hresultPrev : trace.result = E.confirmed cfg ext v n := by
        calc
          trace.result = trace.afterObserved :=
            hselector.result_eq_input cfg ext
          _ = query.confirmed_root := hinput.input_eq
          _ = E.confirmed cfg ext v n := by
            simpa only [query] using E.fcrStep_confirmed_root cfg ext v n
      have hblockAgree :
          (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
            (E.store cfg ext v (n + 1)).blocks
              (E.confirmed cfg ext v n) :=
        hT.wellFormed.blocks_agree
          (E.blockProvenance cfg ext v n)
          (E.blockProvenance cfg ext v (n + 1))
          h.confirmed_known hknownN1
      obtain ⟨ast, ablk, hgen, hslot, _hgenParent⟩ := hT.genesis
      have hgenShort : ∃ (ast : BeaconState Root)
          (ablk : SignedBeaconBlock Root),
          E.genesis_store = get_forkchoice_store cfg ast ablk ∧
            ast.slot = ablk.message.slot :=
        ⟨ast, ablk, hgen, hslot⟩
      have hblockUpperN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) ≤
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        simp only [get_block_epoch, get_current_store_epoch,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right
          (by
            simpa only [E.store_current_slot] using
              E.store_blocks_slot_le_current cfg ext hT.whole_seconds
                hgenShort v n (E.confirmed cfg ext v n) h.confirmed_known)
      have hclockMono : get_current_store_epoch cfg (E.store cfg ext v n) ≤
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        simp only [get_current_store_epoch, E.store_current_slot,
          compute_epoch_at_slot]
        exact Nat.div_le_div_right (E.slot_at_mono cfg (Nat.le_succ n))
      have hblockEpochEq : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_block_epoch cfg (E.store cfg ext v (n + 1))
            (E.confirmed cfg ext v n) := by
        simp only [get_block_epoch, hblockAgree]
      have hclockEq : get_current_store_epoch cfg (E.store cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        apply Nat.le_antisymm hclockMono
        have hqueryReverse : get_current_store_epoch cfg query.store ≤
            get_block_epoch cfg query.store (E.confirmed cfg ext v n) := by
          rw [← hresultPrev]
          exact htraceCurrent.symm.le
        calc
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) ≤
              get_block_epoch cfg (E.store cfg ext v (n + 1))
                (E.confirmed cfg ext v n) := by
            simpa only [query, E.fcrStep_store] using hqueryReverse
          _ = get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) := hblockEpochEq.symm
          _ ≤ get_current_store_epoch cfg (E.store cfg ext v n) :=
            hblockUpperN
      have hcurrentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) =
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        rw [hblockEpochEq, hclockEq, ← hresultPrev]
        simpa only [query, E.fcrStep_store] using htraceCurrent
      obtain ⟨horigin⟩ := h.current_origin hcurrentN
      exact ⟨by
        simpa only [hconfirmedOut, hresultPrev] using
          (horigin.mono_upper cfg ext (Nat.le_succ n))⟩
  | finalizedResetUnchanged hinput hselector =>
      have hresultFinalized : trace.result =
          query.store.finalized_checkpoint.root :=
        (hselector.result_eq_input cfg ext).trans hinput.input_eq
      have hfinalizedCurrent : get_block_epoch cfg query.store
            query.store.finalized_checkpoint.root =
          get_current_store_epoch cfg query.store := by
        simpa only [hresultFinalized] using htraceCurrent
      have hfieldAnchor := E.finalizedCheckpoint_eq_anchor_of_root_current
        cfg ext hLag
          (by simpa only [query, E.fcrStep_store] using
            E.store_causal cfg ext v (n + 1))
          (by simpa only [query, E.fcrStep_store] using hfinalized)
          hfinalizedCurrent
      have hresultAnchor : trace.result = B.anchor.root := by
        rw [hresultFinalized, hfieldAnchor]
      have hanchorCurrent : get_block_epoch cfg
            (E.store cfg ext v (n + 1)) B.anchor.root =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        simpa only [query, E.fcrStep_store, hresultAnchor] using htraceCurrent
      obtain ⟨horigin⟩ := E.acceptedCurrentCandidateSourceOriginAt_anchor
        cfg ext B hT hanchor hboundary hHn1 hanchorCurrent
      exact ⟨by simpa only [hconfirmedOut, hresultAnchor] using horigin⟩
  | observedResetUnchanged hinput hselector =>
      have hresultObserved : trace.result =
          query.current_epoch_observed_justified_checkpoint.root :=
        (hselector.result_eq_input cfg ext).trans hinput.input_eq
      have hbad : get_block_epoch cfg query.store
              query.current_epoch_observed_justified_checkpoint.root + 1 =
            get_block_epoch cfg query.store
              query.current_epoch_observed_justified_checkpoint.root := by
        calc
          _ = get_current_store_epoch cfg query.store :=
            hinput.observed_previous_epoch
          _ = get_block_epoch cfg query.store
                query.current_epoch_observed_justified_checkpoint.root := by
            rw [← hresultObserved]
            exact htraceCurrent.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
  | strictSelected horigin hselector =>
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        cases horigin with
        | carried hinput =>
            change trace.afterObserved ∈
              (E.fcrStep cfg ext v n).store.block_roots
            rw [hinput.input_eq, E.fcrStep_confirmed_root,
              E.fcrStep_store]
            exact hknownN1
        | finalizedReset hinput =>
            change trace.afterObserved ∈
              (E.fcrStep cfg ext v n).store.block_roots
            rw [hinput.input_eq, E.fcrStep_store]
            exact hfinalized.root_known
        | observedReset hinput =>
            have htag := E.actualObservedRestartInputAt cfg ext B hT hanchor
              hboundary v n trace hinput.observed_guard_true
            simpa only [query, htag.afterObserved_eq] using htag.root_known
      have hfacts :=
        FastConfirmation.Spec.Execution.StrictSelectorAdvanceAt.mechanicalFacts
          (E := E) cfg ext hT hsync hstatic hbyz hdomain hv hHn1
            (by simpa only [query] using E.fcrStep_store cfg ext v n)
            hinputKnown hselector
      have hA := E.selectedMarginAssumptions_of_sourceHistoryInputs cfg ext
        hT hsync hstatic hbyz hdomain
      have hnotStart := hfacts.not_epochStart_of_current_of_selectedMargin
        cfg ext hA hv hHn1
          (by simpa only [query] using E.fcrStep_store cfg ext v n)
          htraceCurrent
      have hnew := hfacts.currentCandidateSourceOrigin cfg ext B hHn1
        (by simpa only [query] using E.fcrStep_store cfg ext v n)
        hparent hwalk hhead hinputKnown hselector.result_eq.symm
          hselector.result_ne_input htraceCurrent hnotStart
      simpa only [hconfirmedOut] using hnew

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The exhaustive operational branch fold needs a larger elaboration budget.
/-- Recent-source half of one actual-call history step.  Away from an epoch
boundary the exact evaluator recurrence reduces a recent result to either the
previous confirmed root or the realized finalized checkpoint.  At a boundary,
carried roots consume the retained current-origin field through Lemma 22,
observed resets use their accepted installation witness, and finalized resets
are confined to the trusted-anchor base region by the causal lag law. -/
theorem AcceptedConfirmedSourceHistoryAt.recentSource_succ_of_call
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (h : E.AcceptedConfirmedSourceHistoryAt cfg ext B v n)
    (hrecent : get_block_epoch cfg (E.store cfg ext v (n + 1))
          (E.confirmed cfg ext v (n + 1)) + 1 ≥
        get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
      (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) w) := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.confirmed cfg ext v (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have htraceRecent : get_block_epoch cfg query.store trace.result + 1 ≥
      get_current_store_epoch cfg query.store := by
    rw [hconfirmedOut] at hrecent
    simpa only [query, trace, E.fcrStep_store] using hrecent
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 h.confirmed_known
  have hblockAgree :
      (E.store cfg ext v n).blocks (E.confirmed cfg ext v n) =
        (E.store cfg ext v (n + 1)).blocks
          (E.confirmed cfg ext v n) :=
    hT.wellFormed.blocks_agree
      (E.blockProvenance cfg ext v n)
      (E.blockProvenance cfg ext v (n + 1))
      h.confirmed_known hknownN1
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  by_cases hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = true
  · have hboundarySecond := E.actualCall_epochStart_boundarySecond
      cfg ext hT hsync hstatic hbyz hdomain hv hHn1 hcall hstart
    have hepochSucc := E.actualCall_currentEpoch_succ_of_start
      cfg ext hT hcall hstart
    have carriedBoundarySource
        (hrecentPrevQ : get_block_epoch cfg query.store
              (E.confirmed cfg ext v n) + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) w) := by
      have hpreviousCurrent := E.previousConfirmed_current_of_boundary_recent
        cfg ext hT hcall hstart h.confirmed_known
          (by simpa only [query] using hrecentPrevQ)
      obtain ⟨horigin⟩ := h.current_origin hpreviousCurrent
      have hprevious : get_block_epoch cfg
            (E.store cfg ext v (n + 1)) (E.confirmed cfg ext v n) + 1 =
          get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
        calc
          get_block_epoch cfg (E.store cfg ext v (n + 1))
                (E.confirmed cfg ext v n) + 1 =
              get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) + 1 := by
            simp only [get_block_epoch, hblockAgree]
          _ = get_current_store_epoch cfg (E.store cfg ext v n) + 1 := by
            rw [hpreviousCurrent]
          _ = get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
            hepochSucc
      obtain ⟨hlemma22⟩ := horigin.toLemma22AtNextBoundary cfg ext B hT hv
        hHn1 hcall hboundarySecond rfl hknownN1 hprevious
      exact hlemma22.lemma24 cfg ext B hT hsync w hw
    have finalizedBoundarySource
        (hrecentFinalized : get_block_epoch cfg query.store
              query.store.finalized_checkpoint.root + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) w) := by
      have hnear := E.finalizedRecent_epoch_le_anchor_add_two cfg ext hLag
        (by simpa only [query, E.fcrStep_store] using
          E.store_causal cfg ext v (n + 1))
        (by simpa only [query, E.fcrStep_store] using hfinalized)
        hrecentFinalized
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary
          (by simpa only [query, E.fcrStep_store] using hnear) w
    cases hrec.branch with
    | carriedUnchanged hinput _hselector =>
        exact carriedBoundarySource
          (by simpa only [query, E.fcrStep_confirmed_root] using
            hinput.confirmed_recent cfg ext)
    | finalizedResetUnchanged hinput hselector =>
        apply finalizedBoundarySource
        have hresult : trace.result = query.store.finalized_checkpoint.root :=
          (hselector.result_eq_input cfg ext).trans hinput.input_eq
        simpa only [hresult] using htraceRecent
    | observedResetUnchanged hinput _hselector =>
        obtain ⟨hlemma22⟩ :=
          FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
            (E := E) cfg ext B hT hsync hstatic hbyz hdomain hanchor
              hboundary hspe hv hHn1 hcall hinput
        exact hlemma22.lemma24 cfg ext B hT hsync w hw
    | strictSelected horigin hselector =>
        cases horigin with
        | carried hinput =>
            apply carriedBoundarySource
            simpa only [query, E.fcrStep_confirmed_root, hinput.input_eq] using
              hselector.input_recent
        | finalizedReset hinput =>
            apply finalizedBoundarySource
            simpa only [hinput.input_eq] using hselector.input_recent
        | observedReset hinput =>
            obtain ⟨hlemma22⟩ :=
              FastConfirmation.Spec.Execution.ObservedResetCandidateInputAt.acceptedLemma22EpochStartCandidateSource
                (E := E) cfg ext B hT hsync hstatic hbyz hdomain hanchor
                  hboundary hspe hv hHn1 hcall hinput
            exact hlemma22.lemma24 cfg ext B hT hsync w hw
  · have hepochEq := E.actualCall_currentEpoch_eq_of_notStart
      cfg ext hT hcall hstart
    have previousMidSource
        (hprevious : get_block_epoch cfg query.store
              (E.confirmed cfg ext v n) + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) w) := by
      have hprevious' : get_current_store_epoch cfg
            (E.store cfg ext v (n + 1)) ≤
          get_block_epoch cfg query.store (E.confirmed cfg ext v n) + 1 := by
        simpa only [query, E.fcrStep_store] using hprevious
      have hrecentN : get_block_epoch cfg (E.store cfg ext v n)
            (E.confirmed cfg ext v n) + 1 ≥
          get_current_store_epoch cfg (E.store cfg ext v n) := by
        calc
          get_current_store_epoch cfg (E.store cfg ext v n) =
              get_current_store_epoch cfg (E.store cfg ext v (n + 1)) :=
            hepochEq
          _ ≤ get_block_epoch cfg query.store
                (E.confirmed cfg ext v n) + 1 := hprevious'
          _ = get_block_epoch cfg (E.store cfg ext v n)
                (E.confirmed cfg ext v n) + 1 := by
            simp only [query, E.fcrStep_store, get_block_epoch, hblockAgree]
      have hsource := h.recent_epochStartSource hrecentN w hw
      simpa only [hepochEq] using hsource
    have finalizedMidSource
        (hfinalizedRecent : get_block_epoch cfg query.store
              query.store.finalized_checkpoint.root + 1 ≥
            get_current_store_epoch cfg query.store) :
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg (E.store cfg ext v (n + 1))) w) := by
      have hnear := E.finalizedRecent_epoch_le_anchor_add_two cfg ext hLag
        (by simpa only [query, E.fcrStep_store] using
          E.store_causal cfg ext v (n + 1))
        (by simpa only [query, E.fcrStep_store] using hfinalized)
        hfinalizedRecent
      exact E.acceptedLemma24EpochStartSourceAt_of_anchor_near
        cfg ext B hT hanchor hboundary
          (by simpa only [query, E.fcrStep_store] using hnear) w
    cases hrec.branch with
    | carriedUnchanged hinput _hselector =>
        apply previousMidSource
        simpa only [query, E.fcrStep_confirmed_root] using
          hinput.confirmed_recent cfg ext
    | finalizedResetUnchanged hinput hselector =>
        apply finalizedMidSource
        have hresult : trace.result = query.store.finalized_checkpoint.root :=
          (hselector.result_eq_input cfg ext).trans hinput.input_eq
        simpa only [hresult] using htraceRecent
    | observedResetUnchanged hinput _hselector =>
        exfalso
        apply hstart
        simpa only [query, E.fcrStep_store] using hinput.epoch_start
    | strictSelected horigin hselector =>
        cases horigin with
        | carried hinput =>
            apply previousMidSource
            simpa only [query, E.fcrStep_confirmed_root, hinput.input_eq] using
              hselector.input_recent
        | finalizedReset hinput =>
            apply finalizedMidSource
            simpa only [hinput.input_eq] using hselector.input_recent
        | observedReset hinput =>
            exfalso
            apply hstart
            simpa only [query, E.fcrStep_store] using hinput.epoch_start

/-- Knownness half of one actual-call step.  Each reset branch uses its exact
accepted realization, while a strict selected result uses the ordinary
query-local descendant geometry. -/
theorem AcceptedConfirmedSourceHistoryAt.confirmedKnown_succ_of_call
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (h : E.AcceptedConfirmedSourceHistoryAt cfg ext B v n) :
    E.confirmed cfg ext v (n + 1) ∈
      (E.store cfg ext v (n + 1)).block_roots := by
  let query := E.fcrStep cfg ext v n
  let trace := E.getLatestConfirmedTraceAt cfg ext v n
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hconfirmedOut : E.confirmed cfg ext v (n + 1) = trace.result := by
    simpa only [trace] using hrec.result_writeback
  have hknownN1 : E.confirmed cfg ext v n ∈
      (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.le_succ n)).1 h.confirmed_known
  have hfinalized :=
    E.finalizedCheckpoint_resetRealizedAt_of_acceptedGlobalTrajectory
      cfg ext B hT hanchor hboundary (w := v) (n + 1)
  obtain ⟨hparentN1, hwalkN1, _hjustifiedN1⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hT.wellFormed
      hT.externals_coherence hT.genesis hdomain v hv (n + 1) hHn1
  have hparent : ParentSlotLt query.store := by
    simpa only [query, E.fcrStep_store] using hparentN1
  have hwalk : ∀ t ∈ query.store.block_roots,
      ∀ r ∈ query.store.block_roots,
        WalkKnown query.store (query.store.blocks t).slot r := by
    simpa only [query, E.fcrStep_store] using hwalkN1
  have hhead : (get_head cfg query.store).root ∈ query.store.block_roots := by
    simpa only [query, E.fcrStep_store] using
      E.head_root_known_of_selectedMarginDomain cfg ext hdomain hv
        (n + 1) hHn1
  have observedKnown
      (hinput : ObservedResetCandidateInputAt cfg ext query trace) :
      trace.afterObserved ∈ query.store.block_roots := by
    have htag := E.actualObservedRestartInputAt cfg ext B hT hanchor
      hboundary v n trace hinput.observed_guard_true
    simpa only [htag.afterObserved_eq] using htag.root_known
  cases hrec.branch with
  | carriedUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext, hinput.input_eq]
      simpa only [query, E.fcrStep_confirmed_root] using hknownN1
  | finalizedResetUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext, hinput.input_eq]
      simpa only [query, E.fcrStep_store] using hfinalized.root_known
  | observedResetUnchanged hinput hselector =>
      rw [hconfirmedOut, hselector.result_eq_input cfg ext]
      simpa only [query, E.fcrStep_store] using observedKnown hinput
  | strictSelected horigin hselector =>
      have hinputKnown : trace.afterObserved ∈ query.store.block_roots := by
        cases horigin with
        | carried hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.fcrStep_confirmed_root, E.fcrStep_store]
              using hknownN1
        | finalizedReset hinput =>
            rw [hinput.input_eq]
            simpa only [query, E.fcrStep_store] using hfinalized.root_known
        | observedReset hinput => exact observedKnown hinput
      have hgeometry := hselector.geometry cfg ext hparent hwalk hhead hinputKnown
      rw [hconfirmedOut]
      simpa only [query, E.fcrStep_store] using hgeometry.result_known

/-- The complete one-call transformer for the candidate-indexed source
history invariant. -/
theorem AcceptedConfirmedSourceHistoryAt.succ_of_call
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (h : E.AcceptedConfirmedSourceHistoryAt cfg ext B v n) :
    E.AcceptedConfirmedSourceHistoryAt cfg ext B v (n + 1) := {
  confirmed_known := h.confirmedKnown_succ_of_call cfg ext B hT hdomain
    hanchor hboundary hv hHn1 hcall
  recent_epochStartSource := fun hrecent w hw =>
    h.recentSource_succ_of_call cfg ext B hT hsync hstatic hbyz hdomain
      hanchor hboundary hLag hspe hv hHn1 hcall hrecent w hw
  current_origin := fun hcurrent =>
    h.currentOrigin_succ_of_call cfg ext B hT hsync hstatic hbyz hdomain
      hanchor hboundary hLag hv hHn1 hcall hcurrent
}

/-- Candidate-source history for every honest in-horizon execution second.
The sole primitive paper-facing timing contract is the faithful accepted
realized-finalization delay at the opaque state-transition boundary. -/
theorem acceptedConfirmedSourceHistoryAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) :
    ∀ n : Nat, E.WithinHorizon cfg n →
      E.AcceptedConfirmedSourceHistoryAt cfg ext B v n := by
  have hLag : E.CausalRealizedFinalizationLag cfg ext B :=
    E.causalRealizedFinalizationLag_of_acceptedDelay
      cfg ext B hT hanchor hDelay
  intro n
  induction n with
  | zero =>
      intro hH0
      exact E.acceptedConfirmedSourceHistoryAt_zero cfg ext B hT hanchor
        hboundary v hH0
  | succ n ih =>
      intro hHn1
      have hHn : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
      have hn := ih hHn
      by_cases hcall : E.IsFCRCallAt cfg ext v n
      · exact hn.succ_of_call cfg ext B hT hsync hstatic hbyz hdomain
          hanchor hboundary hLag hspe hv hHn1 hcall
      · exact hn.succ_of_noCall cfg ext hT hcall

/-- Callback-free paper-Lemma-24 export for the current result of one actual
evaluator call.  The result is tied to the executable write-back equation, so
the all-seconds invariant supplies the epoch-start source directly. -/
theorem getLatestConfirmedTraceAt_current_epochStartSource
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    (hcurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          (E.getLatestConfirmedTraceAt cfg ext v n).result =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store)
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
      (get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) w) := by
  have hhistory := E.acceptedConfirmedSourceHistoryAt cfg ext B hT hsync
    hstatic hbyz hdomain hanchor hboundary hDelay hspe hv (n + 1) hHn1
  have hrec := E.actualCandidateHistoryRecurrence cfg ext hcall
  have hstoredCurrent : get_block_epoch cfg (E.store cfg ext v (n + 1))
          (E.confirmed cfg ext v (n + 1)) =
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    rw [hrec.result_writeback]
    simpa only [E.fcrStep_store] using hcurrent
  have hstoredRecent : get_block_epoch cfg (E.store cfg ext v (n + 1))
          (E.confirmed cfg ext v (n + 1)) + 1 ≥
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)) := by
    rw [hstoredCurrent]
    exact Nat.le_succ _
  have hsource := hhistory.recent_epochStartSource hstoredRecent w hw
  simpa only [E.fcrStep_store] using hsource

/-- Lemma 25 from Lemma 24 and the accepted handler-driven justified maximum.
The epoch-start seed is transported only forward in the same validator's
store trajectory; no endpoint source freshness is assumed. -/
theorem AcceptedLemma24EpochStartSourceAt.justified_recent
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {e : Epoch} {w : ValidatorIndex}
    (h : E.AcceptedLemma24EpochStartSourceAt cfg ext B e w)
    {m : Nat} (hmH : E.WithinHorizon cfg m)
    (hmEpoch : get_current_store_epoch cfg (E.store cfg ext w m) = e) :
    e ≤ (E.store cfg ext w m).justified_checkpoint.epoch + 2 := by
  obtain ⟨ast, ablk, hgen, hgenSlot, hgenParent⟩ := hT.genesis
  let boundary := compute_start_slot_at_epoch cfg e
  let start := E.slot_start cfg boundary
  have hboundaryLeM : boundary ≤ E.slot_at cfg m := by
    have hmEpoch' : E.slot_at cfg m / cfg.slots_per_epoch = e := by
      simpa only [get_current_store_epoch, E.store_current_slot,
        compute_epoch_at_slot] using hmEpoch
    change e * cfg.slots_per_epoch ≤ E.slot_at cfg m
    rw [← hmEpoch']
    exact Nat.div_mul_le_self (E.slot_at cfg m) cfg.slots_per_epoch
  have hstartLeM : start ≤ m := by
    have hmul : boundary * cfg.slot_duration_ms ≤
        E.slot_at cfg m * cfg.slot_duration_ms :=
      Nat.mul_le_mul_right cfg.slot_duration_ms hboundaryLeM
    have hdiv : boundary * cfg.slot_duration_ms / 1000 ≤
        E.slot_at cfg m * cfg.slot_duration_ms / 1000 :=
      Nat.div_le_div_right hmul
    have hadd : E.genesis_store.genesis_time +
          boundary * cfg.slot_duration_ms / 1000 ≤
        E.genesis_store.genesis_time +
          E.slot_at cfg m * cfg.slot_duration_ms / 1000 :=
      Nat.add_le_add_left hdiv _
    have hsub : E.genesis_store.genesis_time +
          boundary * cfg.slot_duration_ms / 1000 -
            E.genesis_store.time ≤
        E.genesis_store.genesis_time +
          E.slot_at cfg m * cfg.slot_duration_ms / 1000 -
            E.genesis_store.time :=
      Nat.sub_le_sub_right hadd _
    have hmStart : E.slot_start cfg (E.slot_at cfg m) ≤ m := by
      have hgenTime : E.genesis_store.genesis_time ≤
          E.genesis_store.time := by
        rw [hgen]
        exact (wellFormedStore_get_forkchoice_store cfg ast ablk hgenSlot
          hgenParent).time_ge_genesis
      exact E.slot_start_le_of_slot_at cfg hT.whole_seconds hgenTime rfl
    exact hsub.trans hmStart
  have hseedM : h.seed ∈ (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w hstartLeM).1 h.seed_known
  have hclock : get_current_store_epoch cfg
      (E.store cfg ext w start) ≤
      get_current_store_epoch cfg (E.store cfg ext w m) := by
    simp only [get_current_store_epoch, E.store_current_slot]
    exact ce_mono cfg (E.slot_at_mono cfg hstartLeM)
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hT.wellFormed (E.store_causal cfg ext w start)
      (E.store_causal cfg ext w m) h.seed_known hseedM hclock
  have hsourceRecentM : e ≤
      (get_voting_source cfg (E.store cfg ext w m) h.seed).epoch + 2 :=
    h.source_recent.trans (Nat.add_le_add_right hsourceMono 2)
  have hsourceLeJ := B.causalVotingSource_epoch_le_justified
    hT.whole_seconds ⟨ast, ablk, hgen, hgenSlot⟩ hanchor
      (E.store_causal cfg ext w m) hseedM
  exact hsourceRecentM.trans (Nat.add_le_add_right hsourceLeJ 2)

/-! ## Consumer-shaped path-local Lemma-26 carrier -/

/-- A strictly-past honest HFC leaf below the current candidate, with its
recent accepted source and exact path-local filter evidence kept on the same
tip. -/
structure AcceptedRecentCandidateSourceCarrierAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (q : Nat) (candidate : Root) where
  validator : ValidatorIndex
  second : Nat
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  strictly_past : E.slot_at cfg second < E.slot_at cfg q
  candidate_known : candidate ∈
    (E.store cfg ext validator second).block_roots
  tip : Root
  tip_known : tip ∈ (E.store cfg ext validator second).block_roots
  tip_descends_candidate : is_ancestor
    (E.store cfg ext validator second)
    (get_node_for_root tip) (get_node_for_root candidate) = true
  tip_semantic_descends_candidate : E.RootDescends tip candidate
  tip_is_leaf : (E.store cfg ext validator second).block_roots.filter
    (fun r => ((E.store cfg ext validator second).blocks r).parent_root = tip) = []
  past_justified_check :
    (E.store cfg ext validator second).justified_checkpoint.epoch =
        GENESIS_EPOCH ∨
      (get_voting_source cfg (E.store cfg ext validator second) tip).epoch =
          (E.store cfg ext validator second).justified_checkpoint.epoch ∨
      (get_voting_source cfg (E.store cfg ext validator second) tip).epoch + 2 ≥
        get_current_store_epoch cfg (E.store cfg ext validator second)
  past_finalized_check :
    (E.store cfg ext validator second).finalized_checkpoint.epoch =
        GENESIS_EPOCH ∨
      (E.store cfg ext validator second).finalized_checkpoint.root =
        get_checkpoint_block cfg (E.store cfg ext validator second) tip
          (E.store cfg ext validator second).finalized_checkpoint.epoch
  tip_to_candidate_walk : WalkKnown
    (E.store cfg ext validator second)
    ((E.store cfg ext validator second).blocks candidate).slot tip
  source_au : B.state.AU cfg ext tip
    (get_voting_source cfg (E.store cfg ext validator second) tip)
  source_recent : get_current_store_epoch cfg (E.store cfg ext v q) ≤
    (get_voting_source cfg (E.store cfg ext validator second) tip).epoch + 2

/-- Resolve the exact viable-leaf source guard with Lemma 25.  The genesis,
`source = J`, and numeric arms remain separate until this constructor. -/
theorem AcceptedRecentCandidateSourceCarrierAt.of_pathLocal
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {v : ValidatorIndex} {q : Nat} {candidate : Root}
    (hpast : E.AcceptedHonestPastHeadBelowAt cfg ext v q candidate)
    (hepoch : get_current_store_epoch cfg
        (E.store cfg ext hpast.validator hpast.second) =
      get_current_store_epoch cfg (E.store cfg ext v q))
    (hJRecent : get_current_store_epoch cfg (E.store cfg ext v q) ≤
      (E.store cfg ext hpast.validator hpast.second
        ).justified_checkpoint.epoch + 2)
    (hpath : PathLocalFilterViableLeafBelow cfg
      (E.store cfg ext hpast.validator hpast.second) candidate) :
    Nonempty (E.AcceptedRecentCandidateSourceCarrierAt
      cfg ext B v q candidate) := by
  obtain ⟨tip, htip, hdesc, hleaf, hsource, hfinalized, hwalk⟩ := hpath
  let past := E.store cfg ext hpast.validator hpast.second
  have hsourceRecent : get_current_store_epoch cfg (E.store cfg ext v q) ≤
      (get_voting_source cfg past tip).epoch + 2 := by
    rcases hsource with hgenesis | hsourceEq | hnumeric
    · have hqueryLeTwo : get_current_store_epoch cfg
          (E.store cfg ext v q) ≤ 2 := by
        simpa only [past, hgenesis, GENESIS_EPOCH, Nat.zero_add] using hJRecent
      exact hqueryLeTwo.trans (Nat.le_add_left 2 _)
    · simpa only [past, hsourceEq] using hJRecent
    · rw [← hepoch]
      exact hnumeric
  have hsemantic : E.RootDescends tip candidate :=
    E.rootDescends_of_store_ancestor
      (E.blockProvenance cfg ext hpast.validator hpast.second)
      (E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        hT.genesis hT.wellFormed.anchor_parent_unscheduled
        hpast.validator hpast.second)
      hwalk hdesc
  exact ⟨{
    validator := hpast.validator
    second := hpast.second
    validator_honest := hpast.validator_honest
    second_within := hpast.second_within
    strictly_past := hpast.strictly_past
    candidate_known := hpast.candidate_known
    tip := tip
    tip_known := htip
    tip_descends_candidate := hdesc
    tip_semantic_descends_candidate := hsemantic
    tip_is_leaf := hleaf
    past_justified_check := hsource
    past_finalized_check := hfinalized
    tip_to_candidate_walk := hwalk
    source_au := (E.store_causal cfg ext hpast.validator hpast.second
      ).getVotingSource_AU cfg ext B htip
    source_recent := hsourceRecent
  }⟩

/-! ## Source-history split -/

/-- Generic source-history interface for arbitrary query/result tuples. The
executable theorem below instead derives the source from
`acceptedConfirmedSourceHistoryAt` and the evaluator write-back equation. -/
def AcceptedLemma23To24SourceHistory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E) : Prop :=
  ∀ v ∈ E.honest, ∀ q : Nat, E.WithinHorizon cfg q →
    ∀ (query : FastConfirmationStore Root),
      query.store = E.store cfg ext v q →
    ∀ input result : Root,
      StrictSelectedResultMechanicalFacts cfg ext query input result →
      get_block_epoch cfg query.store result =
        get_current_store_epoch cfg query.store →
      ∀ w ∈ E.honest,
        Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
          (get_current_store_epoch cfg query.store) w)

/-- Preserve the executable justified-root fallback as an explicit outcome;
it is not a filtered leaf and therefore not silently converted into a source
carrier. -/
structure AcceptedPastJustifiedFallbackAt
    (v : ValidatorIndex) (q : Nat) (candidate : Root) where
  past : E.AcceptedHonestPastHeadBelowAt cfg ext v q candidate
  justified_descends_candidate : is_ancestor
    (E.store cfg ext past.validator past.second)
    (get_node_for_root
      (E.store cfg ext past.validator past.second
        ).justified_checkpoint.root)
    (get_node_for_root candidate) = true

inductive AcceptedCurrentSameSourceHistoryOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (v : ValidatorIndex) (q : Nat) (candidate : Root) : Prop
  | justifiedFallback :
      Nonempty (E.AcceptedPastJustifiedFallbackAt cfg ext v q candidate) →
      AcceptedCurrentSameSourceHistoryOutcome B v q candidate
  | recentCarrier :
      Nonempty (E.AcceptedRecentCandidateSourceCarrierAt
        cfg ext B v q candidate) →
      AcceptedCurrentSameSourceHistoryOutcome B v q candidate

/-- Query-local Lemma-26 consumer once the exact epoch-start Lemma-24 source
has been supplied for every honest receiving validator. -/
theorem StrictSelectedResultMechanicalFacts.currentSame_sourceHistoryOutcome_of_epochStartSource
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext v q)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store)
    (hsource : ∀ w ∈ E.honest,
      Nonempty (E.AcceptedLemma24EpochStartSourceAt cfg ext B
        (get_current_store_epoch cfg query.store) w)) :
    E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B v q result := by
  obtain ⟨hpast⟩ := E.confirmed_honestPastHeadBelow cfg ext hT hsync
    hstatic hbyz hdomain hv hqH hquery h.result_known h.parent_known h.confirmed
  have hpastEpoch : get_current_store_epoch cfg
      (E.store cfg ext hpast.validator hpast.second) =
      get_current_store_epoch cfg (E.store cfg ext v q) := by
    have hblockAgree : query.store.blocks result =
        (E.store cfg ext hpast.validator hpast.second).blocks result := by
      rw [hquery]
      exact hT.wellFormed.blocks_agree
        (E.blockProvenance cfg ext v q)
        (E.blockProvenance cfg ext hpast.validator hpast.second)
        (by simpa only [hquery] using h.result_known) hpast.candidate_known
    have hlower : get_current_store_epoch cfg (E.store cfg ext v q) ≤
        get_current_store_epoch cfg
          (E.store cfg ext hpast.validator hpast.second) := by
      rw [← hquery, ← hcurrent]
      simp only [get_block_epoch, hblockAgree]
      exact ce_mono cfg
        (E.store_blocks_slot_le_current cfg ext hT.whole_seconds
          (by
            obtain ⟨ast, ablk, hgen, hslot, _⟩ := hT.genesis
            exact ⟨ast, ablk, hgen, hslot⟩)
          hpast.validator hpast.second result hpast.candidate_known)
    have hupper : get_current_store_epoch cfg
        (E.store cfg ext hpast.validator hpast.second) ≤
        get_current_store_epoch cfg (E.store cfg ext v q) := by
      simp only [get_current_store_epoch, E.store_current_slot]
      exact ce_mono cfg hpast.strictly_past.le
    exact Nat.le_antisymm hupper hlower
  rcases hpast.directJustified_or_pathLocal cfg ext hT hdomain with
      hdirect | hpath
  · exact .justifiedFallback ⟨{
      past := hpast
      justified_descends_candidate := hdirect
    }⟩
  · let e := get_current_store_epoch cfg query.store
    obtain ⟨hlemma24⟩ :=
      hsource hpast.validator hpast.validator_honest
    have hJRecentQuery : get_current_store_epoch cfg query.store ≤
        (E.store cfg ext hpast.validator hpast.second
          ).justified_checkpoint.epoch + 2 := by
      have hJ := hlemma24.justified_recent cfg ext B hT hanchor
        hpast.second_within
        (by simpa only [hquery] using hpastEpoch)
      simpa only [e] using hJ
    have hJRecent : get_current_store_epoch cfg (E.store cfg ext v q) ≤
        (E.store cfg ext hpast.validator hpast.second
          ).justified_checkpoint.epoch + 2 := by
      simpa only [← hquery] using hJRecentQuery
    exact .recentCarrier
      (AcceptedRecentCandidateSourceCarrierAt.of_pathLocal cfg ext B hT
        hpast hpastEpoch hJRecent hpath)

/-- Arbitrary-query form of the source-history result. The evaluator-specific
`actualCurrentSame_sourceHistoryOutcome` derives its source history directly
from the executable recurrence. -/
theorem StrictSelectedResultMechanicalFacts.currentSame_sourceHistoryOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hhistory : E.AcceptedLemma23To24SourceHistory cfg ext B)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : Nat}
    (hqH : E.WithinHorizon cfg q)
    {query : FastConfirmationStore Root} {input result : Root}
    (hquery : query.store = E.store cfg ext v q)
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hcurrent : get_block_epoch cfg query.store result =
      get_current_store_epoch cfg query.store) :
    E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B v q result := by
  apply h.currentSame_sourceHistoryOutcome_of_epochStartSource cfg ext B hT
    hsync hstatic hbyz hdomain hanchor hv hqH hquery hcurrent
  intro w hw
  exact hhistory v hv q hqH query hquery input result h hcurrent w hw

/-- Preferred callback-free Lemma-26 export for a strict current result of
the actual evaluator.  Its only paper-facing timing premise is the accepted
realized-finalization delay at the opaque state-transition boundary. -/
theorem StrictSelectedResultMechanicalFacts.actualCurrentSame_sourceHistoryOutcome
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hsync : PaperSafetySynchrony cfg ext E)
    (hstatic : StaticValidatorSet cfg E)
    (hbyz : ByzantineBound cfg E)
    (hdomain : SelectedMarginDomain cfg ext E)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.AcceptedRealizedFinalizationDelay cfg ext B)
    (hspe : 1 < cfg.slots_per_epoch)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : Nat}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hcall : E.IsFCRCallAt cfg ext v n)
    {input : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext
      (E.fcrStep cfg ext v n) input
        (E.getLatestConfirmedTraceAt cfg ext v n).result)
    (hcurrent : get_block_epoch cfg (E.fcrStep cfg ext v n).store
          (E.getLatestConfirmedTraceAt cfg ext v n).result =
        get_current_store_epoch cfg (E.fcrStep cfg ext v n).store) :
    E.AcceptedCurrentSameSourceHistoryOutcome cfg ext B v (n + 1)
      (E.getLatestConfirmedTraceAt cfg ext v n).result := by
  apply h.currentSame_sourceHistoryOutcome_of_epochStartSource cfg ext B hT
    hsync hstatic hbyz hdomain hanchor hv hHn1
      (E.fcrStep_store cfg ext v n) hcurrent
  intro w hw
  exact E.getLatestConfirmedTraceAt_current_epochStartSource cfg ext B hT
    hsync hstatic hbyz hdomain hanchor hboundary hDelay hspe hv hHn1 hcall
      hcurrent w hw


end Execution

end FastConfirmation.Spec
