import FastConfirmation.Spec.Proof.MinimalSelectedDomain

/-!
# Same-slot transport for confirmation-time LMD classes

An arbitrary permitted confirmation query may occur after the first second of
its slot.  Consequently the query store cannot be transported wholesale to the
slot-start store: the latter is earlier in execution time.  The votes read by
`is_one_confirmed`, however, stop at `current_slot - 1`.  Their honest block
roots originate in strictly earlier-slot stores and are therefore already
relayed to every honest node at the current slot boundary.

This module records the timing-correct primitive used by that argument.  The
target is ordered by *slot*, not by relative-second index.  In particular it
allows `m = slot_start (slot_at q)` with `m < q`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Recover a query-known ancestor `b` in an honest earlier-slot store holding
the descendant `d`, then relay both roots and their ancestry to any honest
target whose slot is not before the query slot.  No containment between the
query store and the (possibly earlier-in-seconds) target store is assumed. -/
theorem pastDescendant_ancestry_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ) (b : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hnuH : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg q)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true) :
    d ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root d) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hgateUQ : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ q))
  have hsubUQ : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v q).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hnuH hr v hv q hqH hgateUQ
  have hagreeUQ : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext v q).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext v q)
      hr (hsubUQ hr)
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hpslU : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := E.store_walkKnownK cfg ext hA.wellFormed
      hA.externals_coherence hgen u nu ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  set sb := ((E.store cfg ext v q).blocks b).slot
  have hbound : ablk.message.slot ≤ sb :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hstateSlot hroot v q b hb
  have hwalkB : WalkKnown (E.store cfg ext u nu) sb d := hwalk0.mono hbound
  have hlandsQ : get_ancestor (E.store cfg ext v q) (ForkChoiceNode.mk d) sb =
      ForkChoiceNode.mk b := by
    simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq, sb] using hdb
  have hlandsU : get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d) sb =
      ForkChoiceNode.mk b := by
    rw [get_ancestor_congr hagreeUQ hd hwalkB]
    exact hlandsQ
  have hbU : b ∈ (E.store cfg ext u nu).block_roots := by
    have hspec := (get_ancestor_spec hpslU hwalkB).1
    rw [hlandsU] at hspec
    exact hspec
  have hwalkUB : WalkKnown (E.store cfg ext u nu)
      ((E.store cfg ext u nu).blocks b).slot d := by
    have hslots : ((E.store cfg ext u nu).blocks b).slot = sb := by
      rw [hagreeUQ b hbU]
    rwa [hslots]
  have hdbU : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root d) (get_node_for_root b) = true := by
    simp only [get_node_for_root] at hdb ⊢
    rw [is_ancestor_congr hagreeUQ hd hbU hwalkUB]
    exact hdb
  have hgateUM : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    (Nat.succ_le_iff.mpr hslot).trans hslotTarget
  have hsubUM : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext w m).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hnuH hr w hw m hmH hgateUM
  have hagreeUM : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext w m).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
      hr (hsubUM hr)
  refine ⟨hsubUM hd, hsubUM hbU, ?_⟩
  simp only [get_node_for_root] at hdbU ⊢
  rwa [← is_ancestor_congr hagreeUM hd hbU hwalkUB]

/-- The reverse-orientation companion.  A query-known ancestor `r` of `b` is
recovered together with `b` from one honest past descendant of `b`, then the
pair is relayed to the slot endpoint. -/
theorem pastDescendant_ancestorPair_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ) (b r : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hr : r ∈ (E.store cfg ext v q).block_roots)
    (hbr : is_ancestor (E.store cfg ext v q)
      (get_node_for_root b) (get_node_for_root r) = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hnuH : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg q)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true) :
    b ∈ (E.store cfg ext w m).block_roots ∧
      r ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r) = true := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hgateUQ : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ q))
  have hsubUQ : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v q).block_roots := fun x hx =>
    hA.synchrony.block_relay u hu nu x hnuH hx v hv q hqH hgateUQ
  have hagreeUQ : ∀ x ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks x = (E.store cfg ext v q).blocks x :=
    fun x hx => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext v q)
      hx (hsubUQ hx)
  have hdQ : d ∈ (E.store cfg ext v q).block_roots := hsubUQ hd
  have hpslQ : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled v q
  have hwalkQ := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen v q
  have hdr : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root r) = true :=
    is_ancestor_trans hpslQ (hwalkQ r hr d hdQ) (hwalkQ r hr b hb) hdb hbr
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hpslU : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen
      hA.wellFormed.anchor_parent_unscheduled u nu
  have hwalkU := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := hwalkU ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  have recover (x : Root) (hx : x ∈ (E.store cfg ext v q).block_roots)
      (hdx : is_ancestor (E.store cfg ext v q)
        (get_node_for_root d) (get_node_for_root x) = true) :
      x ∈ (E.store cfg ext u nu).block_roots := by
    set sx := ((E.store cfg ext v q).blocks x).slot
    have hbound : ablk.message.slot ≤ sx :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hstateSlot hroot v q x hx
    have hwalkX : WalkKnown (E.store cfg ext u nu) sx d := hwalk0.mono hbound
    have hlandsQ : get_ancestor (E.store cfg ext v q) (ForkChoiceNode.mk d) sx =
        ForkChoiceNode.mk x := by
      simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq, sx] using hdx
    have hlandsU : get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d) sx =
        ForkChoiceNode.mk x := by
      rw [get_ancestor_congr hagreeUQ hd hwalkX]
      exact hlandsQ
    have hspec := (get_ancestor_spec hpslU hwalkX).1
    rw [hlandsU] at hspec
    exact hspec
  have hbU : b ∈ (E.store cfg ext u nu).block_roots := recover b hb hdb
  have hrU : r ∈ (E.store cfg ext u nu).block_roots := recover r hr hdr
  have hwalkBR : WalkKnown (E.store cfg ext u nu)
      ((E.store cfg ext u nu).blocks r).slot b := hwalkU r hrU b hbU
  have hbrU : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root b) (get_node_for_root r) = true := by
    simp only [get_node_for_root] at hbr ⊢
    rw [is_ancestor_congr hagreeUQ hbU hrU hwalkBR]
    exact hbr
  have hgateUM : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    (Nat.succ_le_iff.mpr hslot).trans hslotTarget
  have hsubUM : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext w m).block_roots := fun x hx =>
    hA.synchrony.block_relay u hu nu x hnuH hx w hw m hmH hgateUM
  have hagreeUM : ∀ x ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks x = (E.store cfg ext w m).blocks x :=
    fun x hx => hA.wellFormed.blocks_agree
      (E.blockProvenance cfg ext u nu) (E.blockProvenance cfg ext w m)
      hx (hsubUM hx)
  refine ⟨hsubUM hbU, hsubUM hrU, ?_⟩
  simp only [get_node_for_root] at hbrU ⊢
  rwa [← is_ancestor_congr hagreeUM hbU hrU hwalkBR]

/-- The exact clock facts for an arbitrary query's slot boundary. -/
theorem query_slot_start_facts_minimal
    (hA : SelectedMarginAssumptions cfg ext E) (q : ℕ)
    (hqH : E.WithinHorizon cfg q) :
    let m := E.slot_start cfg (E.slot_at cfg q)
    m ≤ q ∧ E.WithinHorizon cfg m ∧
      E.slot_at cfg m = E.slot_at cfg q ∧
      E.slot_at cfg q ≤ E.slot_at cfg (m + 1) := by
  dsimp only
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgws : WellFormedStore E.genesis_store := by
    rw [hgeq]
    exact wellFormedStore_get_forkchoice_store cfg ast ablk hslot hroot
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time :=
    hgws.time_ge_genesis
  have hstart : E.slot_start cfg (E.slot_at cfg q) ≤ q :=
    E.slot_start_le_of_slot_at cfg hA.whole_seconds hgenTime rfl
  have hslot : E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q)) =
      E.slot_at cfg q :=
    E.slot_at_slot_start cfg hA.whole_seconds
      (E.slot_at_mono cfg (Nat.zero_le q)) hgenTime
  have hnext : E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q)) ≤
      E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q) + 1) :=
    E.slot_at_mono cfg (Nat.le_succ _)
  have hgate : E.slot_at cfg q ≤
      E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q) + 1) := by
    calc
      E.slot_at cfg q = E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q)) := hslot.symm
      _ ≤ E.slot_at cfg (E.slot_start cfg (E.slot_at cfg q) + 1) := hnext
  exact ⟨hstart, E.withinHorizon_mono cfg hstart hqH, hslot, hgate⟩

/-- A concrete confirmation supplies the honest past descendant needed by
the reverse-orientation transport. -/
theorem confirmed_pastDescendant_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (b : Root) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true) :
    ∃ (u : ValidatorIndex) (nu : ℕ) (d : Root),
      u ∈ E.honest ∧ E.WithinHorizon cfg nu ∧
      E.slot_at cfg nu < E.slot_at cfg q ∧
      d ∈ (E.store cfg ext u nu).block_roots ∧
      is_ancestor (E.store cfg ext v q)
        (get_node_for_root d) (get_node_for_root b) = true := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv q query
      hquery b hqH hb hparent hconf
  exact E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
    v hv q b hqH i hi lm hlm hsupp

/-- A successful selected confirmation cannot occur in the truncated
`current_slot = 0` cutoff corner: its honest recorded supporter comes from a
strictly earlier slot.  Hence `current_slot - 1` is genuinely below the query
slot. -/
theorem confirmed_cutoff_lt_query_slot_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (b : Root) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    {es : Slot} (hes : es = get_current_slot cfg query.store - 1) :
    es < E.slot_at cfg q := by
  obtain ⟨_, _, _, _, _, hnuq, _, _⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery b
      hqH hb hparent hconf
  have hqpos : 0 < E.slot_at cfg q := lt_of_le_of_lt (Nat.zero_le _) hnuq
  rw [hquery, E.store_current_slot cfg ext v q] at hes
  rw [hes]
  exact Nat.sub_lt hqpos Nat.one_pos

/-- A confirmed candidate is already known at the first second of its query
slot, even when the successful query itself occurs later in that slot. -/
theorem confirmed_known_at_query_slot_start_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (b : Root) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) :
    b ∈ (E.store cfg ext w (E.slot_start cfg (E.slot_at cfg q))).block_roots := by
  obtain ⟨_hle, hmH, _hslot, hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hd, hdb⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery b
      hqH hb hparent hconf
  exact (E.pastDescendant_ancestry_at_slot_endpoint_minimal cfg ext hA
    v hv q b hqH hb w hw (E.slot_start cfg (E.slot_at cfg q)) hmH hgate
    u hu nu hnuH d hnuq hd hdb).2.1

/-- An honest newest vote through a ledger window is its validator-spec head
vote in an in-horizon source store.  Window membership rules out a spurious
pre-anchor `Execution.vote`: the validator must also vote at its window
assignment, so newestness forces that assignment no later than `t`. -/
theorem honest_newest_vote_source_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {lo es t : Slot} (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    (hiSpan : i ∈ E.span_committee lo es)
    {k : ℕ} {a : Attestation Root}
    (ht : t ≤ es) (hvote : E.vote i t = some (k, a))
    (hnewest : ∀ t' : Slot, t < t' → t' ≤ es → E.vote i t' = none) :
    ∃ (nu : ℕ) (index : CommitteeIndex),
      E.WithinHorizon cfg nu ∧ E.slot_at cfg nu = t ∧
      a = honest_attestation cfg ext (E.store cfg ext i nu) t index i ∧
      a.data.beacon_block_root ∈ (E.store cfg ext i nu).block_roots := by
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiSpan
  obtain ⟨s, ⟨hloS, hsEs⟩, hiS⟩ := hiSpan
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_mono cfg hsEs hesH
  obtain ⟨ns, indexS, hnsH, hnsSlot, hvoteS⟩ :=
    hA.honest_behavior.votes_head i hi s hiS hsH (hlo0.trans hloS)
  have hst : s ≤ t := by
    apply le_of_not_gt
    intro hts
    have hnone := hnewest s hts hsEs
    rw [hvoteS] at hnone
    contradiction
  have htH : E.SlotWithinHorizon cfg t :=
    E.slotWithinHorizon_mono cfg ht hesH
  have hiT : i ∈ E.committee t :=
    hA.honest_behavior.votes_assigned i hi t
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨nu, index, hnuH, hnuSlot, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi t hiT htH
      (hlo0.trans (hloS.trans hst))
  rw [hvoteHead] at hvote
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote
  obtain ⟨_hknu, hheadEq⟩ := hvote
  have hrootHead :
      (honest_attestation cfg ext (E.store cfg ext i nu) t index i).data.beacon_block_root ∈
        (E.store cfg ext i nu).block_roots := by
    change (get_head cfg (E.store cfg ext i nu)).root ∈
      (E.store cfg ext i nu).block_roots
    rcases get_head_root_mem_or cfg (E.store cfg ext i nu) with hmem | heq
    · exact hmem
    · rw [heq]
      exact hA.domain.justified_root_known i hi nu hnuH
  refine ⟨nu, index, hnuH, hnuSlot, hheadEq.symm, ?_⟩
  rwa [← hheadEq]

/-- Honest `SupportsDesc` transports from an arbitrary late query to any
endpoint in the same-or-later slot.  The vote witness itself supplies the
past honest descendant used for the backwards-in-seconds ancestry recovery. -/
theorem honest_supportsDesc_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ) (b : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    {lo es : Slot} (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    (hiSpan : i ∈ E.span_committee lo es)
    (hS : E.SupportsDesc cfg ext v q b es i) :
    E.SupportsDesc cfg ext w m b es i := by
  obtain ⟨t, k, a, ht, hvote, hnewest, hanc⟩ := hS
  obtain ⟨nu, index, hnuH, hnuSlot, _ha, hroot⟩ :=
    E.honest_newest_vote_source_minimal cfg ext hA hlo0 hesH hi hiSpan
      ht hvote hnewest
  have hnuq : E.slot_at cfg nu < E.slot_at cfg q := by
    rw [hnuSlot]
    exact lt_of_le_of_lt ht hesq
  have hancEnd := (E.pastDescendant_ancestry_at_slot_endpoint_minimal cfg ext hA
    v hv q b hqH hb w hw m hmH hslotTarget i hi nu hnuH
    a.data.beacon_block_root hnuq hroot hanc).2.2
  exact ⟨t, k, a, ht, hvote, hnewest, hancEnd⟩

/-- Honest `AncestorOrVoteless` transport in the same timing regime.  The
voteless branch is store-independent.  In the voting branch, a single honest
past descendant supplied by the concrete confirmation recovers `b` and the
vote-root ancestor together at the earlier endpoint. -/
theorem honest_ancestorOrVoteless_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ) (b : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    {lo es : Slot} (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu0 : ℕ)
    (hnu0H : E.WithinHorizon cfg nu0) (d : Root)
    (hnu0q : E.slot_at cfg nu0 < E.slot_at cfg q)
    (hd : d ∈ (E.store cfg ext u nu0).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    (hiSpan : i ∈ E.span_committee lo es)
    (hAq : E.AncestorOrVoteless cfg ext v q b es i) :
    E.AncestorOrVoteless cfg ext w m b es i := by
  rcases hAq with hvoteless | ⟨t, k, a, ht, hvote, hnewest, hanc⟩
  · exact Or.inl hvoteless
  · obtain ⟨nu, index, hnuH, hnuSlot, _ha, hroot⟩ :=
      E.honest_newest_vote_source_minimal cfg ext hA hlo0 hesH hi hiSpan
        ht hvote hnewest
    have hnuq : E.slot_at cfg nu < E.slot_at cfg q := by
      rw [hnuSlot]
      exact lt_of_le_of_lt ht hesq
    have hgateIQ : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
      hnuq.trans_le (E.slot_at_mono cfg (Nat.le_succ q))
    have hrootQ : a.data.beacon_block_root ∈
        (E.store cfg ext v q).block_roots :=
      hA.synchrony.block_relay i hi nu a.data.beacon_block_root hnuH hroot
        v hv q hqH hgateIQ
    have hancEnd := (E.pastDescendant_ancestorPair_at_slot_endpoint_minimal
      cfg ext hA v hv q b a.data.beacon_block_root hqH hb hrootQ hanc
      w hw m hmH hslotTarget u hu nu0 hnu0H d hnu0q hd hdb).2.2
    exact Or.inr ⟨t, k, a, ht, hvote, hnewest, hancEnd⟩

/-- The ledger-facing honest base transport.  This is deliberately a pair of
weight inequalities, rather than the historical `∀ i` predicate transport:
the classes filter to honest window members, while synchrony imposes no
same-slot delivery discipline on Byzantine ground votes. -/
theorem honest_classes_base_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ) (b : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    (lo es : Slot) (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu0 : ℕ)
    (hnu0H : E.WithinHorizon cfg nu0) (d : Root)
    (hnu0q : E.slot_at cfg nu0 < E.slot_at cfg q)
    (hd : d ∈ (E.store cfg ext u nu0).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true) :
    E.Sval cfg ext v q b lo es ≤ E.Sval cfg ext w m b lo es ∧
      E.Xval cfg ext w m b lo es ≤ E.Xval cfg ext v q b lo es := by
  classical
  have hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i →
      E.SupportsDesc cfg ext w m b es i := by
    intro i hi hiSpan hS
    exact E.honest_supportsDesc_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq hi hiSpan hS
  have hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
      E.AncestorOrVoteless cfg ext w m b es i := by
    intro i hi hiSpan hAnc
    exact E.honest_ancestorOrVoteless_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq
      u hu nu0 hnu0H d hnu0q hd hdb hi hiSpan hAnc
  constructor
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  · apply E.weight_mono
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hS => hi.2.1 (hSt i hi.1.2 hi.1.1 hS),
      fun hAnc => hi.2.2 (hAt i hi.1.2 hi.1.1 hAnc)⟩

/-- Concrete confirmation wrapper exposing exactly the two honest-window
transport functions used by the selected-margin records.  The confirmed past
descendant is extracted once and shared by all ancestor/voteless members. -/
theorem confirmed_honest_class_transports_at_slot_endpoint_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (b : Root) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    (lo es : Slot) (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q) :
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i) ∧
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i) := by
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hd, hdb⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery b
      hqH hb hparent hconf
  constructor
  · intro i hi hiSpan hS
    exact E.honest_supportsDesc_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq hi hiSpan hS
  · intro i hi hiSpan hAnc
    exact E.honest_ancestorOrVoteless_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq
      u hu nu hnuH d hnuq hd hdb hi hiSpan hAnc

/-- Call-site form of the preceding wrapper.  The actual confirmation cutoff
supplies both the cutoff horizon and its strict position before the query
slot; only the window's lower anchor bound remains explicit. -/
theorem confirmed_honest_class_transports_of_cutoff_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (q : ℕ)
    (query : FastConfirmationStore Root)
    (hquery : query.store = E.store cfg ext v q)
    (b : Root) (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext v q).block_roots)
    (hparent : ((E.store cfg ext v q).blocks b).parent_root ∈
      (E.store cfg ext v q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hmH : E.WithinHorizon cfg m)
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg (m + 1))
    (lo es : Slot) (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hcutoff : es = get_current_slot cfg query.store - 1) :
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i) ∧
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i) := by
  have hcurrent : get_current_slot cfg query.store = E.slot_at cfg q := by
    rw [hquery, E.store_current_slot cfg ext v q]
  have hesLe : es ≤ E.slot_at cfg q := by
    rw [hcutoff, hcurrent]
    exact Nat.sub_le _ _
  have hesH : E.SlotWithinHorizon cfg es :=
    E.slotWithinHorizon_of_le cfg hesLe hqH
  have hesq := E.confirmed_cutoff_lt_query_slot_minimal cfg ext hA
    v hv q query hquery b hqH hb hparent hconf hcutoff
  exact E.confirmed_honest_class_transports_at_slot_endpoint_minimal cfg ext hA
    v hv q query hquery b hqH hb hparent hconf w hw m hmH hslotTarget
    lo es hlo0 hesH hesq

end Execution

end FastConfirmation.Spec
