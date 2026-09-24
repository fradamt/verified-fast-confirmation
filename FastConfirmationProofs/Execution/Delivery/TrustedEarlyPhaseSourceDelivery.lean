module
public import FastConfirmationProofs.Execution.Delivery.EarlyPhaseSourceDelivery
public import FastConfirmationProofs.FFG.SelectedSource.TrustedPhaseSourceCarriers

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable {E : Execution Root} {trusted : Store Root → Prop}

def TrustedAcceptedLemma13SourceSeedAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (store : Store Root) (selected : Root) : Prop :=
  ∃ seed : Root,
    seed ∈ store.block_roots ∧
      is_ancestor store (get_node_for_root seed)
        (get_node_for_root selected) = true ∧
      (B.state.GU seed).epoch + 1 ≥
        get_current_store_epoch cfg store

/-! ## Query-local executable producers -/


/-- Away from the epoch-start escape, a strict current-epoch tentative result
mechanically realizes the Lemma 13 GU seed using the exact query head.

The previous-loop origin is impossible because every retained previous edge
has a non-current child. The tentative entry's remaining arm is precisely the
head's cached unrealized-justification bound, and the accepted causal
projection identifies that cache entry with GU(head).
-/
theorem StrictSelectedResultMechanicalFacts.trusted_current_lemma13SourceSeed_of_notStart
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
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
    TrustedAcceptedLemma13SourceSeedAt cfg ext B query.store result := by
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
        have hb := strictSelectedResult_below_head cfg ext hparent hwalk hhead
          hinput hstrict'
        rw [hout] at hb
        exact (congrArg (· = true) (is_ancestor_pending_root_eq query.store
          (get_head cfg query.store).root result .pending
          (get_head cfg query.store).payload_status)).mpr hb
      have hprojection :=
        Execution.TrustedCausalPrefixFFGInterpretation.causalStoreProjection
          B hstore
      have hguEq : query.store.unrealized_justifications head =
          B.state.GU head := hprojection.unrealized_justification head hhead
      refine ⟨head, hhead, hbelow, ?_⟩
      simpa only [head, hguEq] using hgu

/-! ## Cross-store accepted transport -/


/-- A Lemma 13 GU seed at a current-epoch query becomes an executable recent
source seed at the next-epoch endpoint. The endpoint selector is forced onto
its old-block GU branch; this is why Lemma 13, rather than Lemma 26, is the
right input for this cell.
-/
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
    (hnextEpoch : get_current_store_epoch cfg (E.store cfg ext w m) =
      get_current_store_epoch cfg query + 1)
    (hseed : ∃ seed : Root,
      seed ∈ query.block_roots ∧
      is_ancestor query (get_node_for_root seed)
        (get_node_for_root selected) = true ∧
      (B.state.GU seed).epoch + 1 ≥ get_current_store_epoch cfg query ∧
      seed ∈ (E.store cfg ext w m).block_roots) :
    RecentSourceSeedAt cfg (E.store cfg ext w m) selected := by
  obtain ⟨seed, hseedQ, hseedSelectedQ, hguRecent, hseedEndpoint⟩ := hseed
  have hsemantic : E.RootDescends seed selected :=
    E.rootDescends_of_store_ancestor hqueryProvenance hqueryParent
      (hqueryWalk selected hselectedQ seed hseedQ) hseedSelectedQ
  have hselectedRoot : E.ExecutionRoot selected := by
    rcases hqueryProvenance selected hselectedQ with hanchor | hscheduled
    · exact ⟨query.blocks selected, Or.inl hanchor⟩
    · obtain ⟨sb, ⟨u, k, hevent⟩, hroot, hmessage⟩ := hscheduled
      exact ⟨query.blocks selected,
        Or.inr ⟨u, k, sb, hevent, hroot, hmessage.symm⟩⟩
  have ⟨hselectedM, hseedSelectedM⟩ :=
    E.store_known_ancestor_of_rootDescends_for_storeReflection
      cfg ext hwf hec hgen hgenSlot hgenParent
      hseedEndpoint hselectedRoot hsemantic
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
    rw [hendpoint.trusted_getVotingSource_eq_acceptedSelector cfg ext B hseedEndpoint]
    exact if_pos hseedOld
  refine ⟨seed, hseedEndpoint, hseedSelectedM, ?_⟩
  rw [hsourceEq, hnextEpoch]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    Nat.add_le_add_right hguRecent 1


end Execution
end FastConfirmation.Spec
end
