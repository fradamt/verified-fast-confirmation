module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunContent

/-! Checkpoint reads agree on common accepted roots at every epoch. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

private theorem event_blocks_of_no_root {r : Root} (store : Store Root) (ev : Event Root)
    (hno : ∀ sb, ev = Event.block sb → r ≠ sb.root) :
    ((apply_event cfg ext store ev).getD store).blocks r = store.blocks r := by
  cases hh : apply_event cfg ext store ev with
  | none => rfl
  | some result =>
    simp only [Option.getD_some]
    cases ev with
    | block sb => exact on_block_other_root_blocks hh (hno sb rfl)
    | attestation a fb => exact congrFun (on_attestation_sameBlocks cfg ext hh).2.1.symm r
    | attester_slashing sl => exact congrFun (on_attester_slashing_sameBlocks ext hh).2.1.symm r
    | execution_payload_envelope env ob =>
      exact congrFun (on_execution_payload_envelope_sameBlocks ext hh).2.1.symm r
    | payload_attestation_message msg fb =>
      exact congrFun (on_payload_attestation_message_sameBlocks cfg ext hh).2.1.symm r

private theorem fold_blocks_of_no_root {r : Root} (events : List (Event Root))
    (hno : ∀ sb, Event.block sb ∈ events → r ≠ sb.root) (store : Store Root) :
    (events.foldl (fun s e => (apply_event cfg ext s e).getD s) store).blocks r =
      store.blocks r := by
  induction events generalizing store with
  | nil => rfl
  | cons ev rest ih =>
    rw [List.foldl_cons]
    apply (ih (fun sb hb => hno sb (List.mem_cons_of_mem _ hb)) _).trans
    exact event_blocks_of_no_root store ev
      (fun sb he => hno sb (by simp only [List.mem_cons]; exact Or.inl he.symm))

private theorem schedule_no_root {r : Root} (h : ¬ E.ExecutionRoot r)
    (w n) (sb : SignedBeaconBlock Root) (hb : Event.block sb ∈ E.schedule w n) :
    r ≠ sb.root := by
  intro heq
  exact h ⟨sb.message, Or.inr ⟨w, n, sb, hb, heq.symm, rfl⟩⟩

private theorem boundary_blocks_of_no_root {r : Root} (h : ¬ E.ExecutionRoot r) (w n) :
    (E.store cfg ext w n).blocks r = E.genesis_store.blocks r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((E.schedule w (n + 1)).foldl
      (fun s ev => (apply_event cfg ext s ev).getD s)
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))).blocks r = _
    rw [fold_blocks_of_no_root _ (schedule_no_root h w (n + 1))]
    exact (congrFun (on_tick_sameBlocks cfg _ _).2.1.symm r).trans ih

private theorem causal_blocks_of_no_root {r : Root} (h : ¬ E.ExecutionRoot r)
    {store : Store Root} (hs : E.CausalStore cfg ext store) :
    store.blocks r = E.genesis_store.blocks r := by
  cases hs with
  | genesis => rfl
  | scheduledPrefix p =>
    unfold ScheduledEventPrefix.store
    rw [fold_blocks_of_no_root _ (fun sb hb => schedule_no_root h p.node
      (p.previousSecond + 1) sb (List.mem_of_mem_take hb))]
    exact (congrFun (on_tick_sameBlocks cfg _ _).2.1.symm r).trans
      (boundary_blocks_of_no_root h p.node p.previousSecond)

private theorem aux_default_root {store : Store Root} {r : Root}
    (h : store.blocks r = default) (slot fuel) (status : PayloadStatus) :
    (get_ancestor_aux store slot fuel (ForkChoiceNode.mk r status)).root = r := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hslot : (store.blocks r).slot = 0 := by rw [h]; rfl
    simp only [get_ancestor_aux, hslot, Nat.not_lt_zero, if_false]

private theorem aux_common_roots {s t : Store Root} {anchorRoot : Root}
    {anchorBlock : BeaconBlock Root}
    (ha : s.blocks anchorRoot = anchorBlock) (hb : t.blocks anchorRoot = anchorBlock)
    (hda : s.blocks anchorBlock.parent_root = default)
    (hdb : t.blocks anchorBlock.parent_root = default)
    (hpa : NonAnchorParentKnown anchorRoot s) (hpb : NonAnchorParentKnown anchorRoot t)
    (hagree : ∀ r, r ∈ s.block_roots → r ∈ t.block_roots → s.blocks r = t.blocks r)
    (slot fuel : ℕ) {r} (hs : r ∈ s.block_roots) (ht : r ∈ t.block_roots)
    (sta stb : PayloadStatus) :
    (get_ancestor_aux s slot fuel (ForkChoiceNode.mk r sta)).root =
      (get_ancestor_aux t slot fuel (ForkChoiceNode.mk r stb)).root := by
  induction fuel generalizing r sta stb with
  | zero => rfl
  | succ fuel ih =>
    have heq := hagree r hs ht
    simp only [get_ancestor_aux]
    rw [← heq]
    split_ifs with hslot
    · by_cases hr : r = anchorRoot
      · subst r
        rw [ha]
        exact (aux_default_root hda slot fuel _).trans (aux_default_root hdb slot fuel _).symm
      · apply ih ((hpa r hs).resolve_left hr)
        · rw [heq]; exact (hpb r ht).resolve_left hr
    · rfl

/-- Common causal-store roots give identical checkpoint reads, also below the
anchor epoch. The dangling anchor parent keeps its initial default block. -/
theorem checkpoint_reads_agree
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {s t : Store Root} (hs : E.CausalStore cfg ext s) (ht : E.CausalStore cfg ext t)
    {r} (hrs : r ∈ s.block_roots) (hrt : r ∈ t.block_roots) (e : Epoch) :
    get_checkpoint_for_block cfg s r e = get_checkpoint_for_block cfg t r e := by
  obtain ⟨ast, ablk, hg, _, _, hp⟩ := core.genesis
  have hgE : E.genesis_store = get_forkchoice_store cfg ast ablk := hg
  have hwf := localInputs.wellFormed cfg ext core.base.wellFormed
  have hno : ¬ E.ExecutionRoot ablk.message.parent_root :=
    E.anchorParent_not_executionRoot_for_storeReflection cfg hwf hgE hp
  have hd0 : E.genesis_store.blocks ablk.message.parent_root = default := by
    simp only [hgE, get_forkchoice_store, Function.update_of_ne hp]
  have hda := (causal_blocks_of_no_root hno hs).trans hd0
  have hdb := (causal_blocks_of_no_root hno ht).trans hd0
  have common : ∀ x, x ∈ s.block_roots → x ∈ t.block_roots → s.blocks x = t.blocks x :=
    fun x hx hy => hwf.blocks_agree (hs.blockProvenance cfg ext E)
      (ht.blockProvenance cfg ext E) hx hy
  have props : ∀ {store}, E.CausalStore cfg ext store →
      store.blocks ablk.root = ablk.message ∧ NonAnchorParentKnown ablk.root store := by
    intro store hstore
    have hk : ablk.root ∈ store.block_roots := by
      have hk0 : ablk.root ∈ E.genesis_store.block_roots := by
        simp only [hgE, get_forkchoice_store, List.mem_singleton]
      cases hstore with
      | genesis => exact hk0
      | scheduledPrefix p => exact (p.genesisStoreLE cfg ext).1 hk0
    have ha : E.AcceptedBlockAt cfg ext ablk.root ablk.message :=
      ⟨E.genesis_store, .genesis, by simp [hgE, get_forkchoice_store], by
        simp [hgE, get_forkchoice_store]⟩
    refine ⟨(hstore.acceptedBlockAt_iff_eq cfg ext E hwf hk).mp ha, ?_⟩
    cases hstore with
    | genesis => exact E.store_nonAnchorParentKnown cfg ext hgE 0 0
    | scheduledPrefix p => exact p.nonAnchorParentKnown cfg ext hgE
  have hroot : (get_ancestor s (get_node_for_root r)
      (compute_start_slot_at_epoch cfg e)).root =
      (get_ancestor t (get_node_for_root r) (compute_start_slot_at_epoch cfg e)).root := by
    simp only [get_ancestor, get_node_for_root]
    rw [common r hrs hrt]
    exact aux_common_roots (props hs).1 (props ht).1 hda hdb (props hs).2 (props ht).2
      common _ _ hrs hrt _ _
  exact congrArg (fun x => Checkpoint.mk e x) hroot

/-- Shared and local checkpoint selectors agree on every common accepted root. -/
theorem checkpoints_agree
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r} (hs : (E.withoutObserver obs).AcceptedRoot cfg ext r) (hl : B.state.domain r) (e) :
    B.state.C r e = core.semantics.state.C r e := by
  obtain ⟨n, hn⟩ := local_known ((B.domain_local r).mp hl)
  obtain ⟨w, hw, m, hm⟩ := shared_known hs
  have hshared := core.semantics.coherence.checkpoint_of_known
    ((E.withoutObserver obs).store_causal cfg ext w m) r
    (by simpa only [withoutObserver_store cfg ext E obs w hw m] using hm) e
  rw [withoutObserver_store cfg ext E obs w hw m] at hshared
  rw [B.checkpoint_of_known (store_observerCausal n) r hn e, hshared]
  exact checkpoint_reads_agree core localInputs (E.store_causal cfg ext obs n)
    (E.store_causal cfg ext w m) hn hm e

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
