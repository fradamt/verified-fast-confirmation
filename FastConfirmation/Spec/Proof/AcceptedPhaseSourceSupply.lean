module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedPhaseSourceCarriers
public import FastConfirmation.Spec.Proof.SelectedPreQuerySIR
public import FastConfirmation.Spec.Proof.HistoricalCurrentTargetTrajectory

@[expose] public section

/-!
# Accepted early-phase source supply

This module supplies the two early endpoint cells which are mechanical once
the executable selected trace and the accepted FFG projection are fixed:

* a previous-epoch selected result uses the previous-loop head, or the
  tentative result's own source, at an endpoint in the same epoch; and
* a current-epoch selected result at the next-epoch endpoint uses the paper
  Lemma 13 shape: a concrete descendant whose accepted GU epoch is at least
  the query epoch minus one.

The same-epoch current-result cell is intentionally absent. Its producer is
the distinct Lemmas 22--26/H4 history argument. In particular, this file does
not assume source visibility, filter success, SafeFrom, a justification
interface, or a safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-! ## Consumer-shaped seed predicates -/

/-- The exact numeric source seed requested by the early endpoint consumer. -/
def RecentSourceSeedAt (store : Store Root) (selected : Root) : Prop :=
  ∃ seed : Root,
    seed ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root seed)
        (get_node_for_root selected) = true ∧
      (get_voting_source cfg store seed).epoch + 2 ≥
        get_current_store_epoch cfg store

/-- The accepted Lemma 13 payload at the query store. This is deliberately
about semantic GU, rather than the query's executable voting-source selector:
a current-epoch seed reads GJ at the query but reads GU at the next-epoch
endpoint. -/
def AcceptedLemma13SourceSeedAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (store : Store Root) (selected : Root) : Prop :=
  ∃ seed : Root,
    seed ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root seed)
        (get_node_for_root selected) = true ∧
      (B.state.GU seed).epoch + 1 ≥
        get_current_store_epoch cfg store

/-! ## Query-local executable producers -/

/-- A strict previous-epoch result has a query-local recent seed.

If the actual producing trace is the previous loop, its exact entry guard
supplies previous_slot_head. If it is the tentative loop, the result cannot
take the current-epoch arm of the final guard, so its own voting source is
recent. Knownness of the previous-slot head is kept explicit because the
total executable is_ancestor function alone does not imply domain membership.
-/
theorem StrictSelectedResultMechanicalFacts.previous_queryRecentSourceSeed
    {query : FastConfirmationStore Root} {input result : Root}
    (h : StrictSelectedResultMechanicalFacts cfg ext query input result)
    (hprevious : get_block_epoch cfg query.store result + 1 =
      get_current_store_epoch cfg query.store)
    (hpreviousHeadKnown : query.previous_slot_head ∈
      query.store.block_roots) :
    RecentSourceSeedAt cfg query.store result := by
  rcases h.trace_origin with
    ⟨a, _hedge, _hentry, hrecent, hdesc⟩ |
      ⟨a, _hedge, _hentry, hfinal⟩
  · exact ⟨query.previous_slot_head, hpreviousHeadKnown, hdesc, hrecent⟩
  · unfold TentativeSelectedResultWitness at hfinal
    rcases hfinal with hcurrent | ⟨hrecent, _houter⟩
    · have hbad : get_block_epoch cfg query.store result + 1 =
          get_block_epoch cfg query.store result :=
        hprevious.trans hcurrent.symm
      exact False.elim ((Nat.ne_of_gt (Nat.lt_succ_self _)) hbad)
    · exact ⟨result, h.result_known,
        is_ancestor_refl query.store (get_node_for_root result), hrecent⟩

/-- Away from the epoch-start escape, a strict current-epoch tentative result
mechanically realizes the Lemma 13 GU seed using the exact query head.

The previous-loop origin is impossible because every retained previous edge
has a non-current child. The tentative entry's remaining arm is precisely the
head's cached unrealized-justification bound, and the accepted causal
projection identifies that cache entry with GU(head).
-/
theorem StrictSelectedResultMechanicalFacts.current_lemma13SourceSeed_of_notStart
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    {query : FastConfirmationStore Root} {input result : Root}
    (hstore : E.CausalStore cfg ext query.store)
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
    AcceptedLemma13SourceSeedAt cfg ext B query.store result := by
  rcases h.trace_origin with
    ⟨a, hedge, _hentry, _hrecent, _hdesc⟩ |
      ⟨a, _hedge, hentry, _hfinal⟩
  · exact False.elim ((hedge.gates cfg ext).1 hcurrent)
  · rcases hentry with hstart | hgu
    · exact False.elim (hnotStart hstart)
    · let head := (get_head cfg query.store).root
      have hbelow : is_ancestor query.store (get_node_for_root head)
          (get_node_for_root result) = true := by
        have hstrict' :
            find_latest_confirmed_descendant cfg ext query input ≠ input := by
          simpa only [hout] using hstrict
        simpa only [head, hout] using
          strictSelectedResult_below_head cfg ext hparent hwalk hhead
            hinput hstrict'
      have hprojection :=
        Execution.ExactPrefixAcceptedFFGSemantics.causalStoreProjection
          B hstore
      have hguEq : query.store.unrealized_justifications head =
          B.state.GU head := hprojection.unrealized_justification head hhead
      refine ⟨head, hhead, hbelow, ?_⟩
      simpa only [head, hguEq] using hgu

/-! ## Cross-store accepted transport -/

/-- Same-epoch transport of a query-local recent seed to an endpoint.

Local query ancestry is converted to semantic accepted descent and then
reflected in the concrete execution endpoint. Fixed-root accepted selector
monotonicity transports the numeric source bound.
-/
theorem recentSourceSeedAt_endpoint_of_query_sameEpoch
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
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
    (hselectedQ : selected ∈ query.block_roots)
    (hselectedM : selected ∈ (E.store cfg ext w m).block_roots)
    (hseedM : ∀ seed, seed ∈ query.block_roots →
      seed ∈ (E.store cfg ext w m).block_roots)
    (hclock : get_current_store_epoch cfg query ≤
      get_current_store_epoch cfg (E.store cfg ext w m))
    (hsameEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query)
    (hseed : RecentSourceSeedAt cfg query selected) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedQ, hseedSelectedQ, hrecentQ⟩ := hseed
  have hseedEndpoint : seed ∈ (E.store cfg ext w m).block_roots :=
    hseedM seed hseedQ
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      (hqueryWalk selected hselectedQ seed hseedQ) hseedSelectedQ
  have hseedSelectedM : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed)
      (get_node_for_root selected) = true :=
    E.store_ancestor_of_rootDescends_for_storeReflection cfg ext hwf hec
      hgen hgenSlot hgenParent hseedEndpoint hselectedM hsemantic
  have hsourceMono := E.acceptedVotingSource_epoch_le_of_currentEpoch_le
    cfg ext B hwf hquery hendpoint hseedQ hseedEndpoint hclock
  refine ⟨seed, hseedEndpoint, hseedSelectedM, ?_⟩
  rw [hsameEpoch]
  exact hrecentQ.trans (Nat.add_le_add_right hsourceMono 2)

/-- A Lemma 13 GU seed at a current-epoch query becomes an executable recent
source seed at the next-epoch endpoint. The endpoint selector is forced onto
its old-block GU branch; this is why Lemma 13, rather than Lemma 26, is the
right input for this cell.
-/
theorem recentSourceSeedAt_endpointNext_of_lemma13
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
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
    (hseedM : ∀ seed, seed ∈ query.block_roots →
      seed ∈ (E.store cfg ext w m).block_roots)
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query + 1)
    (hseed : AcceptedLemma13SourceSeedAt cfg ext B query selected) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedQ, hseedSelectedQ, hguRecent⟩ := hseed
  have hseedEndpoint : seed ∈ (E.store cfg ext w m).block_roots :=
    hseedM seed hseedQ
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      (hqueryWalk selected hselectedQ seed hseedQ) hseedSelectedQ
  have hseedSelectedM : is_ancestor (E.store cfg ext w m)
      (get_node_for_root seed)
      (get_node_for_root selected) = true :=
    E.store_ancestor_of_rootDescends_for_storeReflection cfg ext hwf hec
      hgen hgenSlot hgenParent hseedEndpoint hselectedM hsemantic
  have hseedEpochLe : get_block_epoch cfg query seed ≤
      get_current_store_epoch cfg query := by
    exact ce_mono cfg (hqueryNonfuture seed hseedQ)
  have hqueryAt : E.AcceptedBlockAt cfg ext seed (query.blocks seed) :=
    E.acceptedBlockAt_of_causal_known cfg ext hquery hseedQ
  have hendpointAt : E.AcceptedBlockAt cfg ext seed
      ((E.store cfg ext w m).blocks seed) :=
    E.acceptedBlockAt_of_causal_known cfg ext hendpoint hseedEndpoint
  have hblock : query.blocks seed = (E.store cfg ext w m).blocks seed :=
    hqueryAt.unique cfg ext E hwf hendpointAt
  have hseedOld : get_current_store_epoch cfg (E.store cfg ext w m) >
      get_block_epoch cfg (E.store cfg ext w m) seed := by
    rw [hnextEpoch]
    simp only [get_block_epoch, ← hblock]
    exact Nat.lt_succ_of_le hseedEpochLe
  have hsourceEq : get_voting_source cfg (E.store cfg ext w m) seed =
      B.state.GU seed := by
    rw [hendpoint.getVotingSource_eq_acceptedSelector cfg ext B hseedEndpoint]
    exact if_pos hseedOld
  refine ⟨seed, hseedEndpoint, hseedSelectedM, ?_⟩
  rw [hsourceEq, hnextEpoch]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    Nat.add_le_add_right hguRecent 1


end Execution

end FastConfirmation.Spec

end
