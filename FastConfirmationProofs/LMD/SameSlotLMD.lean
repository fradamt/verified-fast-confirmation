module
public import FastConfirmationProofs.FCRRule.MinimalSelectedDomain

@[expose] public section

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
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hnuH : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg q)
    (hdeadline : nu ≤ E.slot_start cfg (E.slot_at cfg nu) +
      get_attestation_due_ms cfg / 1000)
    (hhead : d = (get_head cfg (E.store cfg ext u nu)).root)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hdQ : d ∈ (E.store cfg ext v q).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true) :
    d ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root d) (get_node_for_root b) = true := by
  have hdw : d ∈ (E.store cfg ext w m).block_roots := by
    rw [hhead]
    exact E.honest_head_known_at_later_slot_minimal cfg ext hA hu hw
      hnuH hmH hdeadline (hslot.trans_le hslotTarget)
  have hb := E.ancestor_at_common_descendant_minimal cfg ext hA hdQ hdw hb hdb
  exact ⟨hdw, hb⟩

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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hnuH : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg q)
    (hdeadline : nu ≤ E.slot_start cfg (E.slot_at cfg nu) +
      get_attestation_due_ms cfg / 1000)
    (hhead : d = (get_head cfg (E.store cfg ext u nu)).root)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hdQ : d ∈ (E.store cfg ext v q).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true) :
    b ∈ (E.store cfg ext w m).block_roots ∧
      r ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r) = true := by
  obtain ⟨hrw, hbw, hbrw⟩ := E.ancestry_of_known_honest_past_descendant_minimal
    cfg ext hA v hv q b r hqH hb hr hbr w hw m hslotTarget hmH
      u hu nu hnuH d hslot hdeadline hhead hd hdQ hdb
  exact ⟨hbw, hrw, hbrw⟩

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
      nu ≤ E.slot_start cfg (E.slot_at cfg nu) +
        get_attestation_due_ms cfg / 1000 ∧
      d = (get_head cfg (E.store cfg ext u nu)).root ∧
      d ∈ (E.store cfg ext u nu).block_roots ∧
      d ∈ (E.store cfg ext v q).block_roots ∧
      is_ancestor (E.store cfg ext v q)
        (get_node_for_root d) (get_node_for_root b) = true := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv q query
      hquery b hqH hb hparent hconf
  obtain ⟨u, nu, d, hu, hHnu, hslot, hdeadline, hhead, hd, hdQuery, hdesc⟩ :=
    E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
      v hv q b hqH i hi lm hlm hsupp
  exact ⟨u, nu, d, hu, hHnu, hslot, hdeadline, hhead, hd, hdQuery, hdesc⟩

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
  obtain ⟨_, _, _, _, _, hnuq, _, _, _, _⟩ :=
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
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hdeadline, hhead, hd, hdQuery, hdb⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery b
      hqH hb hparent hconf
  exact (E.pastDescendant_ancestry_at_slot_endpoint_minimal cfg ext hA
    v hv q b hqH hb w hw (E.slot_start cfg (E.slot_at cfg q)) hmH _hslot.symm.le
    u hu nu hnuH d hnuq hdeadline hhead hd hdQuery hdb).2.1

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
      nu ≤ E.slot_start cfg (E.slot_at cfg nu) + get_attestation_due_ms cfg / 1000 ∧
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
  refine ⟨nu, index, hnuH, hnuSlot, ?_, hheadEq.symm, ?_⟩
  · simpa only [hnuSlot] using
      (hA.honest_behavior.vote_deadline i hi t nu _ hvoteHead).2
  · rwa [← hheadEq]

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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
    {lo es : Slot} (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    (hiSpan : i ∈ E.span_committee lo es)
    (hS : E.SupportsDesc cfg ext v q b es i) :
    E.SupportsDesc cfg ext w m b es i := by
  obtain ⟨t, k, a, ht, hvote, hnewest, hanc⟩ := hS
  obtain ⟨nu, index, hnuH, hnuSlot, hdue, ha, hroot⟩ :=
    E.honest_newest_vote_source_minimal cfg ext hA hlo0 hesH hi hiSpan
      ht hvote hnewest
  have hnuq : E.slot_at cfg nu < E.slot_at cfg q := by
    rw [hnuSlot]
    exact lt_of_le_of_lt ht hesq
  have hgateIQ : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
    hnuq.trans_le (E.slot_at_mono cfg (Nat.le_succ q))
  have hrootQ : a.data.beacon_block_root ∈
      (E.store cfg ext v q).block_roots :=
    by
      have h := E.honest_head_known_at_later_slot_minimal cfg ext hA
        hi hv hnuH hqH hdue hnuq
      simpa only [ha, honest_attestation_data_beacon_block_root] using h
  have hancEnd := (E.pastDescendant_ancestry_at_slot_endpoint_minimal cfg ext hA
    v hv q b hqH hb w hw m hmH hslotTarget i hi nu hnuH
    a.data.beacon_block_root hnuq hdue
      (by rw [ha]; rfl) hroot hrootQ hanc).2.2
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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
    {lo es : Slot} (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu0 : ℕ)
    (hnu0H : E.WithinHorizon cfg nu0) (d : Root)
    (hnu0q : E.slot_at cfg nu0 < E.slot_at cfg q)
    (hdeadline : nu0 ≤ E.slot_start cfg (E.slot_at cfg nu0) +
      get_attestation_due_ms cfg / 1000)
    (hhead : d = (get_head cfg (E.store cfg ext u nu0)).root)
    (hd : d ∈ (E.store cfg ext u nu0).block_roots)
    (hdQ : d ∈ (E.store cfg ext v q).block_roots)
    (hdb : is_ancestor (E.store cfg ext v q)
      (get_node_for_root d) (get_node_for_root b) = true)
    {i : ValidatorIndex} (hi : i ∈ E.honest)
    (hiSpan : i ∈ E.span_committee lo es)
    (hAq : E.AncestorOrVoteless cfg ext v q b es i) :
    E.AncestorOrVoteless cfg ext w m b es i := by
  rcases hAq with hvoteless | ⟨t, k, a, ht, hvote, hnewest, hanc⟩
  · exact Or.inl hvoteless
  · obtain ⟨nu, index, hnuH, hnuSlot, hdue, ha, hroot⟩ :=
      E.honest_newest_vote_source_minimal cfg ext hA hlo0 hesH hi hiSpan
        ht hvote hnewest
    have hnuq : E.slot_at cfg nu < E.slot_at cfg q := by
      rw [hnuSlot]
      exact lt_of_le_of_lt ht hesq
    have hgateIQ : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (q + 1) :=
      hnuq.trans_le (E.slot_at_mono cfg (Nat.le_succ q))
    have hrootQ : a.data.beacon_block_root ∈
        (E.store cfg ext v q).block_roots :=
      by
        have h := E.honest_head_known_at_later_slot_minimal cfg ext hA
          hi hv hnuH hqH hdue hnuq
        simpa only [ha, honest_attestation_data_beacon_block_root] using h
    have hancEnd := (E.pastDescendant_ancestorPair_at_slot_endpoint_minimal
      cfg ext hA v hv q b a.data.beacon_block_root hqH hb hrootQ hanc
      w hw m hmH hslotTarget u hu nu0 hnu0H d hnu0q hdeadline hhead hd hdQ hdb).2.2
    exact Or.inr ⟨t, k, a, ht, hvote, hnewest, hancEnd⟩


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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
    (lo es : Slot) (hlo0 : E.slot_at cfg 0 ≤ lo)
    (hesH : E.SlotWithinHorizon cfg es) (hesq : es < E.slot_at cfg q) :
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i) ∧
    (∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i →
        E.AncestorOrVoteless cfg ext w m b es i) := by
  obtain ⟨u, nu, d, hu, hnuH, hnuq, hdeadline, hhead, hd, hdQuery, hdb⟩ :=
    E.confirmed_pastDescendant_minimal cfg ext hA v hv q query hquery b
      hqH hb hparent hconf
  constructor
  · intro i hi hiSpan hS
    exact E.honest_supportsDesc_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq hi hiSpan hS
  · intro i hi hiSpan hAnc
    exact E.honest_ancestorOrVoteless_at_slot_endpoint_minimal cfg ext hA
      v hv q b hqH hb w hw m hmH hslotTarget hlo0 hesH hesq
      u hu nu hnuH d hnuq hdeadline hhead hd hdQuery hdb hi hiSpan hAnc

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
    (hslotTarget : E.slot_at cfg q ≤ E.slot_at cfg m)
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

end
