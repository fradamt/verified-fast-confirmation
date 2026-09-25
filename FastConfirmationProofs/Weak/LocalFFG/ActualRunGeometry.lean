module
public import FastConfirmationProofs.Weak.LocalFFG.ActualRunCertificates

/-! Accepted-root geometry connects shared and local FFG carrier chains. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {obs : ValidatorIndex}
namespace ActualRunFFG

/-- A shared accepted root is known at a non-observer boundary store. -/
theorem shared_known {r} (h : (E.withoutObserver obs).AcceptedRoot cfg ext r) :
    ∃ w, w ≠ obs ∧ ∃ n, r ∈ (E.store cfg ext w n).block_roots := by
  obtain ⟨store, hs, hr⟩ := h
  cases hs with
  | genesis => exact ⟨obs + 1, Nat.succ_ne_self obs, 0, hr⟩
  | scheduledPrefix p =>
    have hr' := (prefix_le_boundary p).1 hr
    by_cases hp : p.node = obs
    · rw [hp, (erased_blocks (cfg := cfg) (ext := ext) (E := E)
        (obs := obs) (p.previousSecond + 1)).1] at hr'
      exact ⟨obs + 1, Nat.succ_ne_self obs, 0, hr'⟩
    · rw [withoutObserver_store cfg ext E obs p.node hp] at hr'
      exact ⟨p.node, hp, p.previousSecond + 1, hr'⟩

/-- Actual accepted roots have an execution block label. -/
theorem accepted_executionRoot {r} (h : E.AcceptedRoot cfg ext r) : E.ExecutionRoot r := by
  obtain ⟨store, hs, hr⟩ := h
  rcases hs.blockProvenance cfg ext E r hr with hg | ⟨b, ⟨w, n, hb⟩, heq, hm⟩
  · exact ⟨store.blocks r, Or.inl hg⟩
  · exact ⟨b.message, Or.inr ⟨w, n, b, hb, heq, rfl⟩⟩

/-- A semantic accepted ancestor is known in the tip's own boundary store. -/
theorem known_ancestor (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {w n r carrier} (hr : r ∈ (E.store cfg ext w n).block_roots)
    (hc : E.AcceptedRoot cfg ext carrier) (hd : E.RootDescends r carrier) :
    carrier ∈ (E.store cfg ext w n).block_roots ∧
      is_ancestor (E.store cfg ext w n) (get_node_for_root r)
        (get_node_for_root carrier) = true := by
  obtain ⟨st, b, hg, hslot, _, hp⟩ := core.genesis
  exact E.store_known_ancestor_of_rootDescends_for_storeReflection cfg ext
    (localInputs.wellFormed cfg ext core.base.wellFormed) (nonhonest_externals hobs core)
    hg hslot hp hr (accepted_executionRoot hc) hd

/-- Descent from a shared accepted tip can be read entirely in the shared run. -/
theorem shared_descends (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {r carrier} (hr : (E.withoutObserver obs).AcceptedRoot cfg ext r)
    (hc : E.AcceptedRoot cfg ext carrier) (hd : E.RootDescends r carrier) :
    (E.withoutObserver obs).AcceptedRoot cfg ext carrier ∧
      (E.withoutObserver obs).RootDescends r carrier := by
  obtain ⟨w, hw, n, hk⟩ := shared_known hr
  obtain ⟨hcKnown, hanc⟩ := known_ancestor hobs core localInputs hk hc hd
  have hstore := withoutObserver_store cfg ext E obs w hw n
  have hkR : r ∈ ((E.withoutObserver obs).store cfg ext w n).block_roots :=
    hstore.symm ▸ hk
  have hcR : carrier ∈ ((E.withoutObserver obs).store cfg ext w n).block_roots :=
    hstore.symm ▸ hcKnown
  obtain ⟨st, b, hg, hslot, _, hp⟩ := core.genesis
  let R := E.withoutObserver obs
  have hps := R.store_parentSlotLt cfg ext core.base.wellFormed
    core.base.externals_coherence ⟨st, b, hg, hslot, hp⟩
    core.base.wellFormed.anchor_parent_unscheduled w n
  have hwalk := R.store_walkKnownK cfg ext core.base.wellFormed
    core.base.externals_coherence ⟨st, b, hg, hslot, hp⟩ w n carrier hcR r hkR
  exact ⟨⟨_, R.store_causal cfg ext w n, hcR⟩,
    R.rootDescends_of_store_ancestor (R.blockProvenance cfg ext w n) hps hwalk
      (hstore.symm ▸ hanc)⟩

/-- A local accepted tip contains every accepted carrier on its chain. -/
theorem local_descends (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r carrier} (hr : B.state.domain r) (hc : E.AcceptedRoot cfg ext carrier)
    (hd : E.RootDescends r carrier) : B.state.domain carrier := by
  obtain ⟨n, hk⟩ := local_known ((B.domain_local r).mp hr)
  exact B.known_domain (store_observerCausal n)
    (known_ancestor hobs core localInputs hk hc hd).1

/-- The selectors agree on the intersection of the two accepted domains. -/
theorem selectors_agree
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r} (hs : (E.withoutObserver obs).AcceptedRoot cfg ext r) (hl : B.state.domain r) :
    B.state.GJ r = core.semantics.state.GJ r ∧
    B.state.GF r = core.semantics.state.GF r ∧
    B.state.GU r = core.semantics.state.GU r ∧
    B.state.GUF r = core.semantics.state.GUF r := by
  obtain ⟨n, hn⟩ := local_known ((B.domain_local r).mp hl)
  obtain ⟨w, hw, m, hm⟩ := shared_known hs
  exact B.shared_selectors_agree core localInputs n m hw hn hm

/-- Local block content agrees with every accepted carrier for the same root. -/
theorem local_block_agree
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) (B : E.ObserverLocalFFG cfg ext obs)
    {r b} (hr : B.state.domain r) (hb : E.AcceptedBlockAt cfg ext r b) :
    B.state.blocks r = b := by
  obtain ⟨store, hs, hk⟩ := (B.domain_local r).mp hr
  exact AcceptedBlockAt.unique cfg ext E (localInputs.wellFormed cfg ext core.base.wellFormed)
    ⟨store, hs.causal, hk, (B.block_read hs r hk).symm⟩ hb

/-- The ancestor test cannot name a block later than its tip. -/
theorem ancestor_slot_le {store : Store Root} {r carrier}
    (h : is_ancestor store (get_node_for_root r) (get_node_for_root carrier) = true) :
    (store.blocks carrier).slot ≤ (store.blocks r).slot := by
  by_contra hn
  have hle : (store.blocks r).slot ≤ (store.blocks carrier).slot := (Nat.lt_of_not_ge hn).le
  have heq : r = carrier := by
    simp only [get_node_for_root] at h
    rw [is_ancestor_pending, get_ancestor_stop hle] at h
    exact of_decide_eq_true h
  subst carrier
  exact hn le_rfl

/-- Semantic descent orders the slots of exact accepted carriers. -/
theorem accepted_slot_le (hobs : obs ∉ E.honest)
    (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs)
    {r carrier b bc} (hb : E.AcceptedBlockAt cfg ext r b)
    (hc : E.AcceptedBlockAt cfg ext carrier bc) (hd : E.RootDescends r carrier) :
    bc.slot ≤ b.slot := by
  obtain ⟨store, hs, hr, hbr⟩ := hb
  have hb : E.AcceptedBlockAt cfg ext r b := ⟨store, hs, hr, hbr⟩
  obtain ⟨w, n, hk⟩ : ∃ w n, r ∈ (E.store cfg ext w n).block_roots := by
    cases hs with
    | genesis => exact ⟨obs, 0, hr⟩
    | scheduledPrefix p => exact ⟨p.node, p.previousSecond + 1, (prefix_le_boundary p).1 hr⟩
  obtain ⟨hck, ha⟩ := known_ancestor hobs core localInputs hk hc.acceptedRoot hd
  have hwf := localInputs.wellFormed cfg ext core.base.wellFormed
  have heq := (E.store_causal cfg ext w n).acceptedBlockAt_iff_eq cfg ext E hwf hk |>.mp hb
  have heqc := (E.store_causal cfg ext w n).acceptedBlockAt_iff_eq cfg ext E hwf hck |>.mp hc
  simpa only [heq, heqc] using ancestor_slot_le ha

end ActualRunFFG
end Execution
end FastConfirmation.Spec
end
