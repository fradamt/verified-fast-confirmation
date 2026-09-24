module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGAuthenticity
public import FastConfirmationProofs.Execution.StoreInvariants.BlockStateAgreement
public import FastConfirmationProofs.Weak.LocalFFG.ObserverFFGGlobalTrajectory

/-! Observer FFG consumers derived from local calls and content certificates. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}

private def replay (E : Execution Root) : Execution Root := { E with honest := ∅ }

private theorem replay_store (w : ValidatorIndex) (n : ℕ) :
    (replay E).store cfg ext w n = E.store cfg ext w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [store, replay, time_at] at ih ⊢; rw [ih]

private theorem replay_no_validation (state : BeaconState Root) :
    ¬ (replay E).ReachableValidationState cfg ext state := by
  rintro ⟨st, hs, _⟩
  cases hs with
  | genesis hh _ => exact Finset.not_nonempty_empty hh
  | scheduledPrefix p hh _ => exact Finset.notMem_empty _ hh

/-- Operational replay only needs the uniform primitive laws. Erasing honesty
makes the unrelated honest-validation clauses empty; it leaves every store
unchanged. This construction asserts no synchrony for the replay. -/
private def replay_externals
    (core : E.WeakObserverRestrictedCore cfg ext obs) :
    BeaconExternalsPremises cfg ext (replay E) where
  process_slots_slot := core.base.externals_coherence.process_slots_slot
  process_slots_registry := core.base.externals_coherence.process_slots_registry
  state_transition_slot := core.base.externals_coherence.state_transition_slot
  state_transition_registry := core.base.externals_coherence.state_transition_registry
  state_transition_pre_slot_lt := core.base.externals_coherence.state_transition_pre_slot_lt
  state_transition_checkpoint_epoch := core.base.externals_coherence.state_transition_checkpoint_epoch
  pjf_checkpoint_epoch := core.base.externals_coherence.pjf_checkpoint_epoch
  committees_agree := by intro v hv; exact False.elim (Finset.notMem_empty _ hv)
  honest_attestation_valid := by intro st a hs; exact False.elim (replay_no_validation st hs)
  valid_attestation_honest := by intro st a hs; exact False.elim (replay_no_validation st hs)
  valid_attestation_committee := by intro st a hs; exact False.elim (replay_no_validation st hs)
  committee_assignment_unique := core.base.externals_coherence.committee_assignment_unique
  committee_coverage := core.base.externals_coherence.committee_coverage
  committee_members_active := core.base.externals_coherence.committee_members_active
  valid_attestation_default := core.base.externals_coherence.valid_attestation_default
  process_slots_attestation_valid := by
    intro st slot a hs; exact False.elim (replay_no_validation st hs)
  verify_envelope_deterministic := core.base.externals_coherence.verify_envelope_deterministic

namespace ObserverLocalFFG

/-- A local known root belongs to the content certificate domain. -/
theorem known_domain (B : E.ObserverLocalFFG cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) {r} (hr : r ∈ store.block_roots) :
    B.state.domain r := (B.domain_local r).2 ⟨store, hs, hr⟩

/-- A formed content carrier has local occurrence, not restricted occurrence. -/
theorem formed_local (B : E.ObserverLocalFFG cfg ext obs) {r c}
    (hf : B.state.formed r c) : E.ObserverAcceptedRoot cfg ext obs r :=
  (B.domain_local r).1 (B.state.formed_domain hf)

/-- All four selectors of a locally known block have AU evidence. -/
theorem selectors_AU (B : E.ObserverLocalFFG cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) {r} (hr : r ∈ store.block_roots) :
    B.state.AU r (B.state.GJ r) ∧ B.state.AU r (B.state.GU r) ∧
    B.state.AU r (B.state.GF r) ∧ B.state.AU r (B.state.GUF r) := by
  have hd := B.known_domain hs hr
  exact ⟨B.state.gj_mem r hd, B.state.gu_mem r hd,
    B.state.gf_mem r hd, B.state.guf_mem r hd⟩

/-- The five block-state reads at every local prefix follow from successful
calls. No store-wide selector equation is assumed. -/
theorem store_projection (B : E.ObserverLocalFFG cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) :
    ObserverFFG.AcceptedFFGStoreProjection B.state store :=
  ObserverFFG.Execution.observerCausalStore_projection hs B.selectors

/-- Store-global origins are proved by handler induction at local prefixes. -/
theorem global_origins (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) :
    ObserverFFG.AcceptedFFGGlobalCheckpointOrigins B.state store := by
  obtain ⟨st, b, hg, hslot, _⟩ := core.genesis
  exact ObserverFFG.Execution.observerCausalStore_origins hs B.selectors
    ⟨st, b, hg, hslot⟩ rfl

/-- AU carries an actual content certificate and cannot predate the anchor. -/
theorem au_certificate (B : E.ObserverLocalFFG cfg ext obs) {r c}
    (h : B.state.AU r c) :
    (∃ carrier, E.RootDescends r carrier ∧
      IncludedCertifiedJustified cfg E B.state.included
        E.genesis_store.justified_checkpoint carrier c) ∧
    E.genesis_store.justified_checkpoint.epoch ≤ c.epoch := by
  obtain ⟨carrier, hd, hf⟩ := h
  have hc := B.state.formed_certificate hf
  refine ⟨⟨carrier, hd, hc⟩, ?_⟩
  clear hf
  induction hc with
  | anchor => exact le_rfl
  | link prev L ih => exact ih.trans (Nat.le_of_lt L.source_before_target)

/-- The global justified checkpoint has a known local supplier. -/
theorem justified_AU (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) :
    store.justified_checkpoint = E.genesis_store.justified_checkpoint ∨
    ∃ r ∈ store.block_roots, B.state.AU r store.justified_checkpoint := by
  rcases (B.global_origins core hs).justified with ha | ⟨r, hr, hj | hu⟩
  · exact Or.inl ha
  · exact Or.inr ⟨r, hr.1, hj ▸ (B.selectors_AU hs hr.1).1⟩
  · exact Or.inr ⟨r, hr.1, hu ▸ (B.selectors_AU hs hr.1).2.1⟩

/-- The unrealized justified checkpoint has a known local supplier. -/
theorem unrealized_justified_AU (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) :
    store.unrealized_justified_checkpoint = E.genesis_store.justified_checkpoint ∨
    ∃ r ∈ store.block_roots, B.state.AU r store.unrealized_justified_checkpoint := by
  rcases (B.global_origins core hs).unrealized_justified with ha | ⟨r, hr, hu⟩
  · exact Or.inl ha
  · exact Or.inr ⟨r, hr.1, hu ▸ (B.selectors_AU hs hr.1).2.1⟩

/-- The finalized store field retains the included finalizing link. -/
theorem finalized_certificate (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) :
    store.finalized_checkpoint = E.genesis_store.justified_checkpoint ∨
    ∃ r ∈ store.block_roots, Nonempty (IncludedCertifiedFinalized cfg E B.state.included
      E.genesis_store.justified_checkpoint r store.finalized_checkpoint) := by
  rcases (B.global_origins core hs).finalized with ha | ⟨r, hr, hf | hu⟩
  · exact Or.inl ha
  · rw [hf]
    exact (B.state.gf_evidence r (B.known_domain hs hr.1)).imp_right (fun h => ⟨r, hr.1, h⟩)
  · rw [hu]
    exact (B.state.guf_evidence r (B.known_domain hs hr.1)).imp_right (fun h => ⟨r, hr.1, h⟩)

/-- Same-store checkpoint-root knownness follows from reflection and the
concrete boundary walk, with no remote carrier membership. -/
theorem checkpoint_root_known (B : E.ObserverLocalFFG cfg ext obs) {store : Store Root}
    (hs : E.ObserverCausalStore cfg ext obs store) {r c} (hr : r ∈ store.block_roots)
    (hau : B.state.AU r c) (hp : ParentSlotLt store)
    (hw : WalkKnown store (compute_start_slot_at_epoch cfg c.epoch) r) :
    c.root ∈ store.block_roots := by
  have hc := congrArg Checkpoint.root (B.au_checkpoint_of_known hs r hr c hau)
  change c.root = get_checkpoint_block cfg store r c.epoch at hc
  rw [hc]
  exact (get_ancestor_spec hp hw).1

/-- The observer's justified root is derived from its local FFG extension and
operational replay. The restricted core is never asked for that root. -/
theorem justified_root_known (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n : ℕ) :
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  let R := replay E
  have hec : BeaconExternalsPremises cfg ext R := replay_externals core
  have hwfE : WellFormedExecution E := localInputs.wellFormed cfg ext core.base.wellFormed
  have hwf : WellFormedExecution R :=
    ⟨hwfE.blocks_root_injective, hwfE.genesis_blocks_agree, hwfE.anchor_parent_unscheduled⟩
  obtain ⟨ast, ablk, hg, hslot, _hcommit, hparent⟩ := core.genesis
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk := hg
  have hanchorRoot : E.genesis_store.justified_checkpoint.root = ablk.root := by
    simp only [hgen, get_forkchoice_store]
  have hmem0 : E.genesis_store.justified_checkpoint.root ∈ E.genesis_store.block_roots := by
    simp only [hgen, get_forkchoice_store, List.mem_singleton]
  have hmem : E.genesis_store.justified_checkpoint.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hmem0
  have hb : (E.store cfg ext obs n).blocks E.genesis_store.justified_checkpoint.root =
      ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext (localInputs.wellFormed cfg ext core.base.wellFormed)
      hgen obs n (hanchorRoot ▸ hmem)
  have hboundary : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg E.genesis_store.justified_checkpoint.epoch := by
    have hh := core.anchor_boundary
    rw [core.anchor_eq] at hh
    simpa only [TrustedAnchorBoundaryAligned, withoutObserver, hgen,
      get_forkchoice_store, Function.update_self] using hh
  have hp : ParentSlotLt (E.store cfg ext obs n) := by
    have h := R.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hg, hslot, hparent⟩ hwf.anchor_parent_unscheduled obs n
    simpa only [R, replay_store] using h
  have hs : E.ObserverCausalStore cfg ext obs (E.store cfg ext obs n) := store_observerCausal n
  rcases B.justified_AU core hs with ha | ⟨r, hr, hau⟩
  · rw [ha]; exact hmem
  · have hw : WalkKnown (E.store cfg ext obs n)
        ((E.store cfg ext obs n).blocks E.genesis_store.justified_checkpoint.root).slot r := by
      have h := R.store_walkKnownK cfg ext hwf hec
        ⟨ast, ablk, hg, hslot, hparent⟩ obs n
        E.genesis_store.justified_checkpoint.root
        (by simpa only [R, replay_store] using hmem) r
        (by simpa only [R, replay_store] using hr)
      simpa only [R, replay_store] using h
    apply B.checkpoint_root_known hs hr hau hp
    apply hw.mono
    rw [hb]
    exact hboundary.trans (Nat.mul_le_mul_right _ (B.au_certificate hau).2)

/-- The old observer coherence record is a result, not a new local premise. -/
def observerCoherence (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) : E.ObserverCoherence cfg ext obs where
  validity := localInputs.validity
  committees_agree := localInputs.committees_agree
  justified_root_known := fun n _ => B.justified_root_known core localInputs n

/-- A content root has a concrete message from the observer's own run. -/
theorem content_blockAt (B : E.ObserverLocalFFG cfg ext obs) {r}
    (hr : B.state.domain r) : E.BlockAt r (B.state.blocks r) := by
  obtain ⟨st, hs, hk⟩ := (B.domain_local r).1 hr
  rw [B.block_read hs r hk]
  rcases hs.causal.blockProvenance cfg ext E r hk with hgen | ⟨sb, ⟨w, n, hb⟩, heq, hm⟩
  · exact Or.inl hgen
  · exact Or.inr ⟨w, n, sb, hb, heq, hm.symm⟩

/-- Local inclusion preserves both body membership and actual carrier identity. -/
theorem included_body (B : E.ObserverLocalFFG cfg ext obs) {r a}
    (ha : B.state.included r a) : E.BlockAt r (B.state.blocks r) ∧
      a ∈ (B.state.blocks r).attestations := by
  let ev := B.included_evidence ha
  have hd := B.known_domain ev.carrier_local ev.carrier_known
  exact ⟨B.content_blockAt hd, ev.body_member⟩

private theorem replay_descends {a b : Root} (h : E.RootDescends a b) :
    (replay E).RootDescends a b := by
  induction h with
  | refl r => exact .refl r
  | step hp _ ih => exact .step hp ih

/-- Inclusion on a known local tip's chain is strictly earlier than that tip.
This is a local ancestry fact; it does not relay the containing block. -/
theorem included_slot_before_tip (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n : ℕ) {tip a}
    (htip : tip ∈ (E.store cfg ext obs n).block_roots)
    (hin : AttestationIncludedOnChain E B.state.included tip a) :
    a.data.slot < (B.state.blocks tip).slot := by
  let R := replay E
  have hec : BeaconExternalsPremises cfg ext R := replay_externals core
  have hwfE := localInputs.wellFormed cfg ext core.base.wellFormed
  have hwf : WellFormedExecution R :=
    ⟨hwfE.blocks_root_injective, hwfE.genesis_blocks_agree, hwfE.anchor_parent_unscheduled⟩
  obtain ⟨ast, ablk, hg, hslot, _hc, hparent⟩ := core.genesis
  obtain ⟨containing, hd, hi⟩ := hin
  have hcontainingRoot : R.ExecutionRoot containing :=
    ⟨B.state.blocks containing, (B.included_body hi).1⟩
  have htipR : tip ∈ (R.store cfg ext obs n).block_roots := by
    simpa only [R, replay_store] using htip
  have hreflect := R.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
    hwf hec hg hslot hparent htipR hcontainingRoot (replay_descends hd)
  have hp := R.store_parentSlotLt cfg ext hwf hec
    ⟨ast, ablk, hg, hslot, hparent⟩ hwf.anchor_parent_unscheduled obs n
  have hw := R.store_walkKnownK cfg ext hwf hec
    ⟨ast, ablk, hg, hslot, hparent⟩ obs n containing hreflect.1 tip htipR
  have hle := get_ancestor_slot_le hp hw
  have hanc := hreflect.2
  simp only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] at hanc
  rw [hanc] at hle
  have hs : E.ObserverCausalStore cfg ext obs (E.store cfg ext obs n) := store_observerCausal n
  have hk : containing ∈ (E.store cfg ext obs n).block_roots := by
    simpa only [R, replay_store] using hreflect.1
  have hm := (B.included_evidence hi).slot_before_carrier
  rw [B.block_read hs containing hk] at hm
  rw [B.block_read hs tip htip]
  exact hm.trans_le (by simpa only [R, replay_store] using hle)

/-- The exact observer transition belongs to the local causal domain. -/
theorem transition_local (B : E.ObserverLocalFFG cfg ext obs)
    (t : E.AcceptedBlockTransition cfg ext) (ht : t.atPrefix.node = obs) :
    E.ObserverCausalStore cfg ext obs t.postStore := by
  rw [← t.successorPrefix_store]
  exact .scheduledPrefix t.successorPrefix ht

/-- The local content map agrees with the exact input, including duplicates. -/
theorem transition_body (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (t : E.AcceptedBlockTransition cfg ext) (ht : t.atPrefix.node = obs) :
    B.state.blocks t.signedBlock.root = t.signedBlock.message := by
  obtain ⟨hlt, hevent⟩ := List.getElem?_eq_some_iff.mp t.event_at
  have hm := List.getElem_mem hlt
  rw [hevent] at hm
  exact E.blockAt_unique (localInputs.wellFormed cfg ext core.base.wellFormed)
    (B.content_blockAt (B.known_domain (B.transition_local t ht) t.root_known))
    (Or.inr ⟨t.atPrefix.node, t.atPrefix.previousSecond + 1, t.signedBlock, hm, rfl, rfl⟩)

private theorem root_known_at_second_end (cfg : Config) (ext : Externals Root)
    (t : E.AcceptedBlockTransition cfg ext) :
    t.signedBlock.root ∈
      (E.store cfg ext t.atPrefix.node
        (t.atPrefix.previousSecond + 1)).block_roots := by
  let p := t.successorPrefix
  let events := E.schedule p.node (p.previousSecond + 1)
  let ticked := on_tick cfg (E.store cfg ext p.node p.previousSecond)
    (E.time_at (p.previousSecond + 1))
  have hrootPrefix : t.signedBlock.root ∈
      (p.store cfg ext).block_roots := by
    change t.signedBlock.root ∈
      (t.successorPrefix.store cfg ext).block_roots
    rw [t.successorPrefix_store]
    exact t.root_known
  have hprefix : p.store cfg ext =
      (events.take p.processedCount).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked := by
    rfl
  have hle : StoreLE (p.store cfg ext)
      (events.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) := by
    have hfull : events.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ticked =
        (events.drop p.processedCount).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ((events.take p.processedCount).foldl
            (fun store event => (apply_event cfg ext store event).getD store)
            ticked) := by
      rw [← List.foldl_append, List.take_append_drop]
    rw [hfull, ← hprefix]
    exact foldl_storeLE cfg ext _ _
  rw [Execution.store]
  change t.signedBlock.root ∈
    (events.foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      ticked).block_roots
  exact hle.1 hrootPrefix


/-- The one-epoch GUF lag follows from the body certificate. Only the
realized two-epoch GF lag is a new local transition assumption. -/
theorem pulled_finalized_lag (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    (t : E.AcceptedBlockTransition cfg ext) (ht : t.atPrefix.node = obs) :
    let c := (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)).finalized_checkpoint
    c = E.genesis_store.justified_checkpoint ∨
      c.epoch + 1 ≤ compute_epoch_at_slot cfg t.signedBlock.message.slot := by
  dsimp only
  rw [B.selectors.transition_guf t ht]
  rcases B.state.guf_evidence t.signedBlock.root
      (B.known_domain (B.transition_local t ht) t.root_known) with ha | hcert
  · exact Or.inl ha
  right
  obtain ⟨F⟩ := hcert
  obtain ⟨i, hi, _⟩ := B.link_honest_signer core F.finalizing_link
  obtain ⟨a, hchain, _, _, htarget⟩ := F.finalizing_link.signer_attestation i hi
  have hk := root_known_at_second_end cfg ext t
  rw [ht] at hk
  have hslot := B.included_slot_before_tip core localInputs _ hk hchain
  rw [B.transition_body core localInputs t ht] at hslot
  obtain ⟨containing, _, hin⟩ := hchain
  have he := (B.included_evidence hin).target_epoch
  rw [htarget, F.child_epoch] at he
  rw [he]
  exact Nat.div_le_div_right (Nat.le_of_lt hslot)

/-- Common roots have identical local and shared block selectors. This is
state determinism, not a requirement that a local root occur remotely. -/
theorem shared_selectors_agree (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n m : ℕ)
    {w : ValidatorIndex} (hw : w ≠ obs) {r : Root}
    (hl : r ∈ (E.store cfg ext obs n).block_roots)
    (hr : r ∈ (E.store cfg ext w m).block_roots) :
    B.state.GJ r = core.semantics.state.GJ r ∧
    B.state.GF r = core.semantics.state.GF r ∧
    B.state.GU r = core.semantics.state.GU r ∧
    B.state.GUF r = core.semantics.state.GUF r := by
  let R := replay E
  have hec : BeaconExternalsPremises cfg ext R := replay_externals core
  have hwfE := localInputs.wellFormed cfg ext core.base.wellFormed
  have hwf : WellFormedExecution R :=
    ⟨hwfE.blocks_root_injective, hwfE.genesis_blocks_agree, hwfE.anchor_parent_unscheduled⟩
  have heq := R.causal_block_states_agree cfg ext hwf hec
    (R.store_causal cfg ext obs n) (R.store_causal cfg ext w m)
    (by simpa only [R, replay_store] using hl)
    (by simpa only [R, replay_store] using hr)
  simp only [R, replay_store] at heq
  have lp := B.store_projection (store_observerCausal n)
  have rp := Execution.CausalPrefixFFGInterpretation.causalStoreProjection core.semantics
    ((E.withoutObserver obs).store_causal cfg ext w m)
  rw [withoutObserver_store cfg ext E obs w hw m] at rp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← lp.block_state_gj r hl, ← rp.block_state_gj r hr, heq]
  · rw [← lp.block_state_gf r hl, ← rp.block_state_gf r hr, heq]
  · rw [← lp.pulled_up_gu r hl, ← rp.pulled_up_gu r hr, heq]
  · rw [← lp.pulled_up_guf r hl, ← rp.pulled_up_guf r hr, heq]

private theorem known_checkpoint_walk
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (w : ValidatorIndex) (n : ℕ)
    {r : Root} (hr : r ∈ (E.store cfg ext w n).block_roots) {e : Epoch}
    (he : E.genesis_store.justified_checkpoint.epoch ≤ e) :
    WalkKnown (E.store cfg ext w n) (compute_start_slot_at_epoch cfg e) r := by
  let R := replay E
  have hec : BeaconExternalsPremises cfg ext R := replay_externals core
  have hwfE := localInputs.wellFormed cfg ext core.base.wellFormed
  have hwf : WellFormedExecution R :=
    ⟨hwfE.blocks_root_injective, hwfE.genesis_blocks_agree, hwfE.anchor_parent_unscheduled⟩
  obtain ⟨ast, ablk, hg, hslot, _, hparent⟩ := core.genesis
  have hgen : E.genesis_store = get_forkchoice_store cfg ast ablk := hg
  have hm0 : ablk.root ∈ E.genesis_store.block_roots := by
    simp only [hgen, get_forkchoice_store, List.mem_singleton]
  have hm := (E.store_storeLE cfg ext w (Nat.zero_le n)).1 hm0
  have hb := E.store_anchor_block cfg ext hwfE hgen w n hm
  have hboundary : ablk.message.slot ≤ compute_start_slot_at_epoch cfg e := by
    have hh := core.anchor_boundary
    rw [core.anchor_eq] at hh
    have hh' : ablk.message.slot ≤
        compute_start_slot_at_epoch cfg E.genesis_store.justified_checkpoint.epoch := by
      simpa only [TrustedAnchorBoundaryAligned, withoutObserver, hgen,
        get_forkchoice_store, Function.update_self] using hh
    exact hh'.trans (Nat.mul_le_mul_right _ he)
  have hwalk := R.store_walkKnownK cfg ext hwf hec
    ⟨ast, ablk, hg, hslot, hparent⟩ w n ablk.root
    (by simpa only [R, replay_store] using hm) r
    (by simpa only [R, replay_store] using hr)
  simp only [R, replay_store] at hwalk
  apply hwalk.mono
  rw [hb]
  exact hboundary

/-- Checkpoint selectors agree on common known roots from the anchor epoch
onward. The two concrete stores compute the same ancestor walk. -/
theorem shared_checkpoint_agree (B : E.ObserverLocalFFG cfg ext obs)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n m : ℕ)
    {w : ValidatorIndex} (hw : w ≠ obs) {r : Root}
    (hl : r ∈ (E.store cfg ext obs n).block_roots)
    (hr : r ∈ (E.store cfg ext w m).block_roots) {e : Epoch}
    (he : E.genesis_store.justified_checkpoint.epoch ≤ e) :
    B.state.C r e = core.semantics.state.C r e := by
  have hwf := localInputs.wellFormed cfg ext core.base.wellFormed
  have hagree : ∀ x, x ∈ (E.store cfg ext obs n).block_roots →
      x ∈ (E.store cfg ext w m).block_roots →
      (E.store cfg ext obs n).blocks x = (E.store cfg ext w m).blocks x :=
    fun _ hl hr => hwf.blocks_agree (E.blockProvenance cfg ext obs n)
      (E.blockProvenance cfg ext w m) hl hr
  have hwalk := get_ancestor_congr_common_walk hagree
    (known_checkpoint_walk core localInputs obs n hl he)
    (known_checkpoint_walk core localInputs w m hr he)
  have hp := core.semantics.coherence.checkpoint_of_known
    ((E.withoutObserver obs).store_causal cfg ext w m) r
    (by simpa only [withoutObserver_store cfg ext E obs w hw m] using hr) e
  rw [withoutObserver_store cfg ext E obs w hw m] at hp
  rw [B.checkpoint_of_known (store_observerCausal n) r hl e, hp]
  exact congrArg (fun node : ForkChoiceNode Root =>
    ({ epoch := e, root := node.root } : Checkpoint Root)) hwalk

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
