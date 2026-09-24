module
public import FastConfirmationProofs.Weak.Safety.WeakConfirmedSupporter
public import FastConfirmationProofs.Weak.Selection.WeakAncestryEndpoint

@[expose] public section

/-!
# Spec / Proof / WeakConfirmedDissemination

Stage 5 of the weak-synchrony migration: confirmed-block knownness and
ancestry at *all* honest endpoints, derived from an observer's store without
the observer being honest.

`MinimalSelectedDomain.lean`'s `mem_of_known_honest_past_descendant_minimal`
(`:419`), `ancestry_of_known_honest_past_descendant_minimal` (`:484`),
`confirmed_known_at_all_honest_endpoints_minimal` (`:589`) and
`confirmed_ancestry_at_all_honest_endpoints_minimal` (`:615`) all route the
observer's own store into the honest supporter's store through
`NextSlotSynchronyPremises.block_relay` with the *observer* as receiver
(`... v hv n hHn ...`), so that the ancestor walk computed at the observer can
be replayed into the supporter's store via `BlockAgreement`-style containment
congruence. That relay direction is unavailable here: the observer `v` need
not be honest.

This file rebuilds both conclusions with the observer-honesty relay replaced
by the containment-free machinery of `WeakAncestryTransport.lean` /
`WeakAncestryEndpoint.lean`, which only needs the transported node to be
*known already* at both endpoints of the transport — never a relay into the
observer.

## Route

1. `Execution.honestSupporter_of_confirmed_known_at_observer`
   (`WeakConfirmedSupporter.lean`) turns `is_one_confirmed` at the observer's
   store into an honest supporter `i` with a recorded message `lm` whose
   supported node descends from `b` in the observer's own store — driven by
   `hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)` instead
   of observer honesty.
2. `past_descendant_known_at_observer` (below, a local variant of
   `MinimalSelectedDomain.past_descendant_of_honest_supporter_known_minimal`)
   upgrades that recorded message to a *known-at-both-ends* witness: `i`'s
   vote-casting second `nu` (via `HonestBehavior.votes_head`, exactly as the
   strong original computes it) puts `lm.root` in `i`'s own store, and
   `Execution.latestMessageProvenance`, applied directly to `hlm`, puts
   `lm.root` in the observer's store as well — the same
   `LatestMessageProvenance` fact the strong original already computes
   internally as `hlmKnown`, just exposed instead of discarded. The strong
   original's conclusion is an opaque `∃ u nu d, ...`; nothing in it lets a
   caller recover `d = lm.root` or `u = i`, so the observer-side membership
   fact cannot be attached to it after the fact. This local variant avoids
   that by working with `i`/`lm.root` throughout instead of re-existentializing
   them (flagged in the final report as a deviation from "call `:345`
   as-is").
3. `Execution.is_ancestor_transport_closed` (`WeakAncestryTransport.lean`)
   transports `b` from the observer's store into `i`'s store, using `lm.root`
   as the doubly-known witness (known at the observer via step 2's
   `latestMessageProvenance` call, known at `i` via step 2's `votes_head`
   computation) and `Execution.store_anchor_min_slot` for the anchor-slot
   bound `is_ancestor_transport_closed` needs.
4. `NextSlotSynchronyPremises.block_relay`, now from the *honest supporter* `i` as
   sender (never touching the observer), disseminates `b` to every honest
   `(w, m)` past the vote slot — the same slot-gate arithmetic the strong
   original uses, since `i`'s vote slot is `< E.slot_at cfg n ≤ E.slot_at cfg
   m`.
5. For the ancestry conclusion, `b` is *also* already known at the observer
   (hypothesis `hb`), so once deliverable 1 places `b` at `(w, m)` too,
   `Execution.is_ancestor_transport_closed` / `Execution.is_ancestor_replay_closed`
   apply *directly* between the observer's store and `(w, m)` with `b` itself
   as the doubly-known witness — no second trip through `i`'s store is
   needed, unlike the strong original's two-hop (`v ↔ u` then `u ↔ w`)
   replay.

Both new theorems drop the strong originals' `hv : v ∈ E.honest` hypothesis
and add `hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)`
(consumed by `honestSupporter_of_confirmed_known_at_observer`); every other
hypothesis and the conclusions are identical to `:589` / `:615`. The
anchor-shape fact the transport lemmas need is already bundled in
`hA.genesis` (`SelectedMarginAssumptions.genesis`), so no further explicit
hypothesis is required.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Local observer/supporter-known variant of `past_descendant_of_honest_
supporter_known_minimal`

`MinimalSelectedDomain.lean:345`'s theorem needs no observer honesty (verified
above) and is reused for that fact as documented, but its conclusion is an
opaque `∃ u nu d, ...`: nothing in the existential lets a caller recover that
`u` is the very `i` passed in, or that `d` is `lm.root` — both true of the
underlying proof term, but erased by the `Prop`-valued `∃`. The observer-side
knownness this file needs (`lm.root` known *at the observer's store*, not
just at `i`'s) is exactly the `LatestMessageProvenance` fact
(`Provenance.lean:360`'s `hlmKnown` component) the strong original already
computes internally and discards. Recomputing it needs only the one extra
`E.latestMessageProvenance` call already present verbatim in the strong
proof; every other line below is that proof unchanged, with `u`/`d` written
as `i`/`lm.root` throughout instead of re-existentializing them. -/
private theorem past_descendant_known_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ) (b : Root)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext v)
    (hH : E.WithinHorizon cfg n)
    (i : ValidatorIndex) (hi : i ∈ E.honest) (lm : LatestMessage Root)
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext v n)
      (get_supported_node (E.store cfg ext v n) lm) (get_node_for_root b) = true) :
    ∃ nu : ℕ,
      E.WithinHorizon cfg nu ∧
      E.slot_at cfg nu < E.slot_at cfg n ∧
      lm.root ∈ (E.store cfg ext i nu).block_roots ∧
      lm.root ∈ (E.store cfg ext v n).block_roots ∧
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root lm.root) (get_node_for_root b) = true ∧
      nu ≤ E.slot_start cfg (E.slot_at cfg nu) +
        get_attestation_due_ms cfg / 1000 ∧
      (get_head cfg (E.store cfg ext i nu)).root = lm.root := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  obtain ⟨a', sender, sentAt, ifb, hsched, hiatt, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen0 v n i lm hlm
  obtain ⟨voteAt, own, _hcausal, hvote, hdata⟩ :=
    hA.honest_behavior.no_forgery sender sentAt a' ifb hsched i hi hiatt
  set s := a'.data.slot
  have hcomm : i ∈ E.committee s :=
    hA.honest_behavior.votes_assigned i hi s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨ap, _hiap, _htarget, _hbbrap, hapEpoch, hapBound, hapComm,
      hlmKnown, hlmSlot⟩ :=
    E.latestMessageProvenance_of_observer_validity cfg ext hA.wellFormed
      v hvalid hgen0 n i lm hlm
  have hepoch : compute_epoch_at_slot cfg s =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, hapEpoch]
  have hsap : s = ap.data.slot :=
    hA.externals_coherence.committee_assignment_unique i s ap.data.slot
      hcomm hapComm hepoch
  have hslt : s < E.slot_at cfg n := by
    rw [hsap]
    exact Nat.lt_of_succ_le hapBound
  have hanchorle : ablk.message.slot ≤
      ((E.store cfg ext v n).blocks lm.root).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hroot v n lm.root hlmKnown
  have hs0 : E.slot_at cfg 0 ≤ s := by
    rw [hcur0, hsap]
    exact hanchorle.trans hlmSlot.1
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hslt) hH
  obtain ⟨nu, index, hHnu, hnu, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi s hcomm hsH hs0
  rw [hvoteHead] at hvote
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote
  obtain ⟨_, hown⟩ := hvote
  have hrootEq : own.data.beacon_block_root = lm.root := by
    rw [← hdata]
    exact hbbr
  have hhead : (get_head cfg (E.store cfg ext i nu)).root = lm.root := by
    rw [← hrootEq, ← hown]
    rfl
  have hd : lm.root ∈ (E.store cfg ext i nu).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i nu) with hmem | heq
    · rw [← hhead]
      exact hmem
    · rw [← hhead, heq]
      exact hA.domain.justified_root_known i hi nu hHnu
  refine ⟨nu, hHnu, ?_, hd, hlmKnown, ?_, ?_, hhead⟩
  · rw [hnu]
    exact hslt
  · simpa only [is_ancestor_supported_pending, get_node_for_root] using hsupp
  · rw [hnu]
    exact (hA.honest_behavior.vote_deadline i hi s nu _ hvoteHead).2

/-! ## Deliverable 1 — confirmed knownness at all honest endpoints -/

/-- A concretely confirmed candidate, read at an arbitrary (not necessarily
honest) observer's store, is known at every honest endpoint whose slot is not
before the arbitrary selecting slot. Verbatim conclusion match for
`MinimalSelectedDomain.confirmed_known_at_all_honest_endpoints_minimal`
(`:589`), with `hv : v ∈ E.honest` replaced by
`hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)`. -/
theorem confirmed_known_at_all_honest_endpoints_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext v)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_observer cfg ext hA v n hvalid hcomm
      fcrStore hstore b hHn hb hparent hconf
  obtain ⟨nu, hHnu, hslt, hd_i, hd_v, hanc, hdue, hhead⟩ :=
    E.past_descendant_known_at_observer cfg ext hA v n b hvalid hHn i hi lm hlm hsupp
  have hanchor : ablk.message.slot ≤ ((E.store cfg ext v n).blocks b).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne v n b hb
  have hbi : b ∈ (E.store cfg ext i nu).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne hanchor hd_v hd_i hb hanc
  have hanc_i : is_ancestor (E.store cfg ext i nu)
      (get_node_for_root lm.root) (get_node_for_root b) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne hanchor hd_v hd_i hb hanc
  rw [← hhead] at hanc_i
  have hslot_lt : E.slot_at cfg nu < E.slot_at cfg m :=
    hslt.trans_le hnm
  exact E.honest_head_ancestor_known_at_endpoint_weak cfg ext hA hi hw
    hHnu hHm hdue hbi hanc_i hslot_lt

/-! ## Deliverable 2 — confirmed ancestry at all honest endpoints -/

/-- The same observer-honesty-free transport preserves a known
selected/base ancestry pair, not merely selected-root membership. Verbatim
conclusion match for `MinimalSelectedDomain.confirmed_ancestry_at_all_honest_
endpoints_minimal` (`:615`), with `hv : v ∈ E.honest` replaced by
`hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n)`. Unlike the
strong original's two-hop replay (observer store ↔ supporter's store, then
supporter's store ↔ endpoint), this proof replays directly between the
observer's store and the endpoint: `b` is already known at the observer
(`hb`) and, by deliverable 1, at the endpoint too, so `b` itself is the
doubly-known witness `is_ancestor_transport_closed` /
`is_ancestor_replay_closed` need — no second trip through an honest
supporter's store is required. -/
theorem confirmed_ancestry_at_all_honest_endpoints_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext v)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b r₀ : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hr₀ : r₀ ∈ (E.store cfg ext v n).block_roots)
    (hbge : is_ancestor (E.store cfg ext v n)
      (get_node_for_root b) (get_node_for_root r₀) = true)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    r₀ ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r₀) = true := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hbw : b ∈ (E.store cfg ext w m).block_roots :=
    E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA v n hvalid hcomm
      fcrStore hstore b hHn hb hparent hconf w hw m hnm hHm
  have hanchorR : ablk.message.slot ≤ ((E.store cfg ext v n).blocks r₀).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne v n r₀ hr₀
  have hr0w : r₀ ∈ (E.store cfg ext w m).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne hanchorR hb hbw hr₀ hbge
  have hbger₀w : is_ancestor (E.store cfg ext w m)
      (get_node_for_root b) (get_node_for_root r₀) = true :=
    E.is_ancestor_replay_closed cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparentne hanchorR hb hbw hr₀ hbge
  exact ⟨hr0w, hbw, hbger₀w⟩

/-! ## Public witness — the past-descendant certificate, exposed

`past_descendant_known_at_observer` above is `private`: it is already exactly
the witness Stage J needs (an honest supporter `i`, its vote-casting second
`nu`, and its recorded root `lm.root` known at *both* `i`'s own store and the
observer's), but its two callers only ever consume it internally. This public
wrapper existentializes the same witness under the names Stage J's design
uses (`u`, `d`), additionally surfacing the `d ∈ (E.store cfg ext obs q).
block_roots` conjunct that `past_descendant_known_at_observer` already
produces internally (as `hd_v`) and that `confirmed_known_at_all_honest_
endpoints_at_observer`/`confirmed_ancestry_at_all_honest_endpoints_at_observer`
discard. -/
theorem confirmed_pastDescendant_at_observer
    (hA : SelectedMarginAssumptions cfg ext E)
    (obs : ValidatorIndex) (q : ℕ)
    (hvalid : E.ObserverIndexedAttestationValidity cfg ext obs)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext obs q) (b : Root)
    (hqH : E.WithinHorizon cfg q)
    (hb : b ∈ (E.store cfg ext obs q).block_roots)
    (hparent : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) b = true) :
    ∃ (u : ValidatorIndex) (nu : ℕ) (d : Root),
      u ∈ E.honest ∧ E.WithinHorizon cfg nu ∧ E.slot_at cfg nu < E.slot_at cfg q ∧
      d ∈ (E.store cfg ext u nu).block_roots ∧
      d ∈ (E.store cfg ext obs q).block_roots ∧
      is_ancestor (E.store cfg ext obs q) (get_node_for_root d) (get_node_for_root b) = true := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_observer cfg ext hA obs q hvalid hcomm
      query hstore b hqH hb hparent hconf
  obtain ⟨nu, hHnu, hslt, hd_i, hd_v, hanc, _, _⟩ :=
    E.past_descendant_known_at_observer cfg ext hA obs q b hvalid hqH i hi lm hlm hsupp
  exact ⟨i, nu, lm.root, hi, hHnu, hslt, hd_i, hd_v, hanc⟩

end Execution

end FastConfirmation.Spec

end
