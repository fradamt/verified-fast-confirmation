module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverCertificateSupply
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationProofs.FFG.SelectedSource.FFGEndpointRealization

/-! Finalized roots read at a non-honest observer are safe at honest endpoints. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

/-- Every event in the erased execution occurs in the actual execution. -/
theorem withoutObserver_event {w n} {event : Event Root}
    (h : event ∈ (E.withoutObserver obs).schedule w n) : event ∈ E.schedule w n := by
  by_cases hw : w = obs
  · simp [withoutObserver, hw] at h
  · simpa only [withoutObserver, if_neg hw] using h

/-- Erasing a schedule removes parent edges and cannot add them. -/
theorem withoutObserver_descends {a b : Root}
    (h : (E.withoutObserver obs).RootDescends a b) : E.RootDescends a b := by
  induction h with
  | refl r => exact .refl r
  | step hp _ ih =>
    apply RootDescends.step ?_ ih
    rcases hp with hg | ⟨w, n, block, hb, hchild, hparent⟩
    · exact Or.inl hg
    · exact Or.inr ⟨w, n, block, withoutObserver_event hb, hchild, hparent⟩

/-- Shared scheduled certificates remain certificates of the actual run. -/
def withoutObserver_link {source target : Checkpoint Root}
    (L : SupermajorityLink cfg (E.withoutObserver obs) source target) :
    SupermajorityLink cfg E source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := withoutObserver_descends L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨w, n, a, fb, ha, hia, hs, ht⟩ := L.signer_attestation i hi
    exact ⟨w, n, a, fb, withoutObserver_event ha, hia, hs, ht⟩
  supermajority := L.supermajority

/-- Shared justification uses the same anchor and signed messages. -/
theorem withoutObserver_justified {anchor c : Checkpoint Root}
    (h : CertifiedJustified cfg (E.withoutObserver obs) anchor c) :
    CertifiedJustified cfg E anchor c := by
  induction h with
  | anchor => exact .anchor
  | link _ L ih => exact .link ih (withoutObserver_link L)

/-- The certificate accountability premises transfer without a head-path law
at the non-honest observer. -/
def nonhonest_accountability
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    FFGAccountabilityAssumptions cfg ext E where
  genesis_store := by
    obtain ⟨st, block, hg, _⟩ := core.genesis
    exact ⟨st, block, hg⟩
  whole_seconds := core.base.whole_seconds
  honest_behavior := nonhonest_honestBehavior hobs core localInputs
  externals_coherence := nonhonest_externals hobs core
  static_validator_set := nonhonest_staticValidators core
  byzantine_bound := nonhonest_byzantineBound hobs core

namespace ObserverLocalFFG

/-- A finalized checkpoint is known in the observer's own store. -/
theorem finalized_root_known (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (n : ℕ) :
    (E.store cfg ext obs n).finalized_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  have hs := store_observerCausal (cfg := cfg) (ext := ext) (E := E) (obs := obs) n
  rcases (B.global_origins core hs).finalized with ha | ⟨r, hr, hf | hu⟩
  · rw [ha]
    apply (E.store_storeLE cfg ext obs (Nat.zero_le n)).1
    obtain ⟨st, block, hg, _⟩ := core.genesis
    have hgE : E.genesis_store = get_forkchoice_store cfg st block := hg
    simp only [store, hgE, get_forkchoice_store, List.mem_singleton]
  · exact (B.auCheckpoint_known_and_below_tip hobs core localInputs n hr.1
      (hf ▸ (B.selectors_AU hs hr.1).2.2.1)).1
  · exact (B.auCheckpoint_known_and_below_tip hobs core localInputs n hr.1
      (hu ▸ (B.selectors_AU hs hr.1).2.2.2)).1

/-- The local finalized root lies on an honest endpoint's justified chain
in the same or a later slot. All relays have honest source and receiver. -/
theorem finalized_on_honest_justified
    (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {q m : ℕ}
    (hm : E.WithinHorizon cfg m)
    (hqm : E.slot_at cfg q ≤ E.slot_at cfg m) :
    (E.store cfg ext obs q).finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root (E.store cfg ext obs q).finalized_checkpoint.root) = true := by
  let R := E.withoutObserver obs
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hwR : w ∈ R.honest := (withoutObserver_honest hobs).symm ▸ hw
  have hstore := withoutObserver_store cfg ext E obs w hwne m
  obtain ⟨st, block, hg, hslot, hcommit, hparent⟩ := core.genesis
  obtain ⟨hc⟩ := CausalPrefixFFGInterpretation.endpointJustified_certificate
    cfg ext core.semantics ⟨st, block, hg, hslot⟩ core.anchor_eq
      (R.store_causal cfg ext w m)
  have hj := withoutObserver_justified hc
  have hanchorEq : core.semantics.anchor = E.genesis_store.justified_checkpoint := core.anchor_eq
  rw [hanchorEq, hstore] at hj
  have hsemantic : E.RootDescends
      (E.store cfg ext w m).justified_checkpoint.root
      (E.store cfg ext obs q).finalized_checkpoint.root := by
    rcases B.finalized_certified hobs core localInputs (store_observerCausal q) with
        ha | hfin
    · rw [ha]; exact hj.descends_anchor cfg
    · exact E.certified_finalized_prefix cfg ext
        (nonhonest_accountability hobs core localInputs) (Classical.choice hfin) hj
        (B.finalized_epoch_le_honest_justified hobs core localInputs hw hm hqm)
  have hjKnown := core.base.domain.justified_root_known w hwR m hm
  rw [hstore] at hjKnown
  have hfKnown := B.finalized_root_known hobs core localInputs q
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
    hT.wellFormed hT.externals_coherence hg hslot hparent hjKnown
      ⟨_, E.blockAt_of_store_known cfg ext hfKnown⟩ hsemantic

/-- A non-honest observer's finalized root is safe from the start of its
query slot. This closes the finalized-reset branch from restricted inputs. -/
theorem finalized_safeFrom (B : E.ObserverLocalFFG cfg ext obs)
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (q : ℕ) :
    E.SafeFrom cfg ext (E.store cfg ext obs q).finalized_checkpoint.root
      (E.slot_start cfg (E.slot_at cfg q)) := by
  let hT := nonhonest_scheduledPrefix hobs core localInputs
  obtain ⟨st, block, hg, hslot, hcommit, hparent⟩ := core.genesis
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    have hgE : E.genesis_store = get_forkchoice_store cfg st block := hg
    rw [hgE]; simp only [get_forkchoice_store]; omega
  intro w hw m hqm hm
  have hwne : w ≠ obs := by intro he; subst w; exact hobs hw
  have hwR : w ∈ (E.withoutObserver obs).honest :=
    (withoutObserver_honest hobs).symm ▸ hw
  have hjKnown := core.base.domain.justified_root_known w hwR m hm
  rw [withoutObserver_store cfg ext E obs w hwne m] at hjKnown
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← E.slot_at_slot_start cfg core.base.whole_seconds
      (E.slot_at_mono cfg (Nat.zero_le q)) hgenTime]
    exact E.slot_at_mono cfg hqm
  obtain ⟨hfKnown, hanc⟩ := B.finalized_on_honest_justified hobs core localInputs hw hm hslotQM
  exact head_ge_of_justified_ge_K cfg
    (E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨st, block, hg, hslot, hparent⟩ hT.wellFormed.anchor_parent_unscheduled w m)
    (E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨st, block, hg, hslot, hparent⟩ w m) hjKnown hfKnown hanc

end ObserverLocalFFG
end Execution
end FastConfirmation.Spec
end
