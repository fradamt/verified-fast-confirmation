import FastConfirmation.Spec.Proof.WeakCertificateMonotone
import FastConfirmation.Spec.Proof.WeakObserverDomain
import FastConfirmation.Spec.Proof.WeakBankedJustification

/-!
# Spec / Proof / WeakSeedDissemination

Stage S3 of the `hfilter`-discharge wave (`/tmp/hfilter-wave-design.md`, §(A)):
the two raw broadcast-certificate seeds the weak selector's entry/tentative
guards carry — `fcr_store.previous_slot_head`
(`Weak.has_justification_witness_certificate`) and the fork-choice head
(`Weak.has_head_broadcast_certificate`) — disseminate to every honest endpoint
past the certificate's span, at a possibly-Byzantine observer.

## Relationship to `WeakBankedJustification.lean`

`WeakBankedJustification.lean` already proves the analogous dissemination fact
for the *banked* value the certified head installs into
`current_epoch_observed_justified_checkpoint`
(`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`), but that
lemma is specialized to the banking use: it is stated at the second `h.second`
the invariant's certificate witness was minted at (an *installation* second,
consumed with a same-slot-capable gate tailored to
`update_fast_confirmation_variables`'s epoch-start write), and its ancestry
step is the chain-intrinsic `Weak.headUnrealizedJustification_known_and_below`
rather than a general observer-known ancestor.

This file supplies the complementary **general, at-query-second** form the
S5/S7 relay sites actually need: given a certificate *literally in scope at
the query second* (not one minted at some earlier installation second), get
dissemination of the certified root itself, or of any ancestor of it that the
observer's own store already knows — via the already-proved
`Weak.certificate_chain_dissemination` (`WeakCertificateMonotone.lean`), whose
`WalkKnown` side conditions this file does *not* try to re-derive (per that
file's docstring, they are bookkeeping discharged at call sites). Nothing here
duplicates `WeakBankedJustification.lean`; the two files solve the same
`Execution.certificate_dissemination` side-condition problem for two different
callers (installation-time banking vs. query-time relay) and could not share
code beyond the pattern (`checkpoint_state_key_of_broadcast_certificate` +
`registryConstant` + `checkpoint_states_total_active_balance` for
`hval`/`htab`; `store_anchor_min_slot` for `hstart0`;
`store_blocks_slot_le_current` + the query second's own horizon membership for
`hstartH`/`hendH`) which this file's private
`certificateSideConditions_at_observer` factors out on its own account.

## What is delivered

* `Weak.certificateSideConditions_at_observer` (private) — the shared
  antecedent bundle: from the standard `SelectedMarginAssumptions` bundle, the
  query second's horizon membership, and a true certificate on a block known
  at the query second, produces the five side conditions
  `Execution.certificate_dissemination` needs beyond committee readback and
  block-knownness (`hval`, `htab`, `hstart0`, `hstartH`, `hendH`).
* `Weak.witnessSeed_known_at_all_honest_endpoints_at_observer` — a true
  `Weak.has_justification_witness_certificate` disseminates
  `fcr_store.previous_slot_head` to every honest endpoint past its span.
* `Weak.witnessSeed_ancestor_known_at_all_honest_endpoints_at_observer` — the
  chain version: any observer-known ancestor of `previous_slot_head`
  disseminates too (`Weak.certificate_chain_dissemination`).
* `Weak.headSeed_known_at_all_honest_endpoints_at_observer` — a true
  `Weak.has_head_broadcast_certificate` disseminates the fork-choice head.
* `Weak.headSeed_ancestor_known_at_all_honest_endpoints_at_observer` — its
  chain version: any observer-known ancestor of the head disseminates too.

Both certificates share the exact same span shape
(`[get_block_slot store b, get_current_slot store - 1]` for `b` the witness or
the head respectively), so one side-condition bundle serves both families; the
only difference between the two families is how the certified block itself is
shown known at the observer (`previous_slot_head`'s knownness is a caller
premise here, to be discharged by stage S5's weak twin of
`fcrStep_previousSlotHead_known`; the head's knownness is
`Execution.head_root_known_at_observer`, honesty-free, from
`WeakObserverDomain.lean`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Shared side-condition bundle -/

/-- **The shared `certificate_dissemination` side-condition bundle.** Both
`Weak.has_justification_witness_certificate` and
`Weak.has_head_broadcast_certificate` are `Weak.has_broadcast_certificate`
applied at the same span shape
`[get_block_slot store b, get_current_slot store - 1]` against
`get_current_balance_source fcrStore`; a true certificate at that shape is
exactly what this bundle consumes, so it serves both families verbatim.

* `hval`/`htab` — the certificate forces its balance source to be a keyed
  checkpoint state (`checkpoint_state_key_of_broadcast_certificate`), and a
  keyed checkpoint state's registry/total-active-balance are the ground-truth
  ones (`registryConstant` / `checkpoint_states_total_active_balance`) — the
  same route `Weak.selectedCoveredMarginSupplyAt_of_filterSupply_at_observer`
  (`WeakEndpointClasses.lean`) already uses for `is_one_confirmed`.
* `hstart0` — the certified block's slot is bounded below by the anchor's
  (`store_anchor_min_slot`, honesty-free), and the anchor's slot *is*
  `E.slot_at cfg 0` (the `hcur0` computation, verbatim from
  `WeakConfirmedDissemination.past_descendant_known_at_observer`).
* `hstartH`/`hendH` — the certified block's slot is bounded above by the
  query second's own current slot (`store_blocks_slot_le_current`), which
  equals `E.slot_at cfg q`, so both span endpoints are within the horizon by
  `hqH` (`slotWithinHorizon_of_le`); `end_slot = current_slot - 1 ≤
  current_slot` needs no extra store fact at all. -/
private theorem certificateSideConditions_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    {fcrStore : FastConfirmationStore Root}
    (hstore : fcrStore.store = E.store cfg ext obs q)
    {block_root : Root}
    (hb_obs : block_root ∈ (E.store cfg ext obs q).block_roots)
    (hcert : Weak.has_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) block_root
      (get_block_slot fcrStore.store block_root)
      (get_current_slot cfg fcrStore.store - 1) = true) :
    (get_current_balance_source fcrStore).validators = E.registry ∧
      get_total_active_balance cfg (get_current_balance_source fcrStore) =
        E.total_active cfg ∧
      E.slot_at cfg 0 ≤ get_block_slot fcrStore.store block_root ∧
      E.SlotWithinHorizon cfg (get_block_slot fcrStore.store block_root) ∧
      E.SlotWithinHorizon cfg (get_current_slot cfg fcrStore.store - 1) := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  have hgenSlot : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot := ⟨ast, ablk, hgeq, hslot⟩
  have hcertQ : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      (get_current_balance_source fcrStore) block_root
      (get_block_slot fcrStore.store block_root)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    rw [← hstore]; exact hcert
  -- `hval` / `htab`: the certificate forces a keyed checkpoint state.
  have hcertKey : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      ((E.store cfg ext obs q).checkpoint_states
        fcrStore.current_epoch_observed_justified_checkpoint) block_root
      (get_block_slot fcrStore.store block_root)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    simpa only [get_current_balance_source, hstore] using hcertQ
  have hkey : fcrStore.current_epoch_observed_justified_checkpoint ∈
      (E.store cfg ext obs q).checkpoint_state_keys :=
    Weak.checkpoint_state_key_of_broadcast_certificate cfg ext E hgenShort obs q
      fcrStore.current_epoch_observed_justified_checkpoint block_root
      (get_block_slot fcrStore.store block_root)
      (get_current_slot cfg fcrStore.store - 1) hcertKey
  have hval : (get_current_balance_source fcrStore).validators = E.registry := by
    simp only [get_current_balance_source, hstore]
    exact (E.registryConstant cfg ext hA.externals_coherence hgenShort obs q).2
      fcrStore.current_epoch_observed_justified_checkpoint hkey
  have htab : get_total_active_balance cfg (get_current_balance_source fcrStore) =
      E.total_active cfg := by
    simp only [get_current_balance_source, hstore]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q fcrStore.current_epoch_observed_justified_checkpoint
      hkey hqH (hdiv := hA.whole_seconds) (hgen := hgenShort)
  -- `hstart0`: the certified block's slot is bounded below by the anchor's.
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext obs 0
    rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  have hanchor : ablk.message.slot ≤ (fcrStore.store.blocks block_root).slot := by
    rw [hstore]
    exact E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hparent obs q block_root hb_obs
  have hstart0 : E.slot_at cfg 0 ≤ get_block_slot fcrStore.store block_root := by
    rw [hcur0]; exact hanchor
  -- `hstartH` / `hendH`: both span endpoints are bounded above by the query
  -- second's own current slot, i.e. `E.slot_at cfg q`.
  have hcurEq : get_current_slot cfg fcrStore.store = E.slot_at cfg q := by
    rw [hstore]; exact E.store_current_slot cfg ext obs q
  have hstartLe : get_block_slot fcrStore.store block_root ≤ E.slot_at cfg q := by
    rw [hstore, ← E.store_current_slot cfg ext obs q]
    exact E.store_blocks_slot_le_current cfg ext hA.whole_seconds hgenSlot obs q
      block_root hb_obs
  have hendLe : get_current_slot cfg fcrStore.store - 1 ≤ E.slot_at cfg q := by
    rw [hcurEq]; exact Nat.sub_le _ _
  exact ⟨hval, htab, hstart0, E.slotWithinHorizon_of_le cfg hstartLe hqH,
    E.slotWithinHorizon_of_le cfg hendLe hqH⟩

/-! ## Witness-certificate dissemination (`previous_slot_head`) -/

/-- **A true justification-witness certificate disseminates its witness.**
`Weak.has_justification_witness_certificate` unfolds to exactly
`Weak.has_broadcast_certificate` at `fcr_store.previous_slot_head` over
`[get_block_slot store witness, current_slot - 1]`, so
`certificateSideConditions_at_observer` supplies every antecedent
`Execution.certificate_dissemination` needs beyond committee readback and the
witness's own knownness at the query second (`hwitness_known`, a caller
premise — discharged along a real trajectory by stage S5's weak twin of
`Execution.fcrStep_previousSlotHead_known`, not re-derived here). Site 3 of
the `hfilter` design (`AcceptedEarlyPhaseSourceWiring.lean`'s
`fcrStep_previous_endpointRecentSourceSeed`) is exactly this call. -/
theorem witnessSeed_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {fcrStore : FastConfirmationStore Root}
    (hstore : fcrStore.store = E.store cfg ext obs q)
    (hwitness : Weak.has_justification_witness_certificate cfg ext fcrStore = true)
    (hwitness_known : fcrStore.previous_slot_head ∈ (E.store cfg ext obs q).block_roots)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : (get_current_slot cfg fcrStore.store - 1) + 1 ≤ E.slot_at cfg m) :
    fcrStore.previous_slot_head ∈ (E.store cfg ext w m).block_roots := by
  have hcert : Weak.has_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) fcrStore.previous_slot_head
      (get_block_slot fcrStore.store fcrStore.previous_slot_head)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    simpa only [Weak.has_justification_witness_certificate] using hwitness
  obtain ⟨hval, htab, hstart0, hstartH, hendH⟩ :=
    certificateSideConditions_at_observer cfg ext hA hqH hstore hwitness_known hcert
  have hcertQ : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      (get_current_balance_source fcrStore) fcrStore.previous_slot_head
      (get_block_slot fcrStore.store fcrStore.previous_slot_head)
      (get_current_slot cfg fcrStore.store - 1) = true := by rw [← hstore]; exact hcert
  exact E.certificate_dissemination cfg ext hA.wellFormed hA.honest_behavior hsync
    hA.externals_coherence hA.byzantine_bound hji hA.genesis obs q
    (get_current_balance_source fcrStore) fcrStore.previous_slot_head
    (get_block_slot fcrStore.store fcrStore.previous_slot_head)
    (get_current_slot cfg fcrStore.store - 1) hqH hstartH hendH hstart0 hval htab
    hcomm hwitness_known hcertQ w hw m hmH hgate

/-- **Chain version**: any observer-known ancestor of the witness disseminates
too. Thin wrapper over `Weak.certificate_chain_dissemination`
(`WeakCertificateMonotone.lean`) with the same side-condition bundle; the
`WalkKnown` premises are bookkeeping discharged at the call site, exactly as
that file's docstring records. Not currently called by any accepted-route
site (per `/tmp/hfilter-wave-design.md` §(A), no in-scope relay needs an
ancestor of the witness rather than the witness itself), but landed as the
safety net the design calls for. -/
theorem witnessSeed_ancestor_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q))
    {fcrStore : FastConfirmationStore Root}
    (hstore : fcrStore.store = E.store cfg ext obs q)
    (hwitness : Weak.has_justification_witness_certificate cfg ext fcrStore = true)
    (hwitness_known : fcrStore.previous_slot_head ∈ (E.store cfg ext obs q).block_roots)
    {anc : Root} (hanc_obs : anc ∈ (E.store cfg ext obs q).block_roots)
    (hwb : WalkKnown (E.store cfg ext obs q)
      ((E.store cfg ext obs q).blocks anc).slot fcrStore.previous_slot_head)
    (hwalk : ∀ i lm, (E.store cfg ext obs q).latest_messages i = some lm →
      is_ancestor (E.store cfg ext obs q) (get_node_for_root lm.root)
        (get_node_for_root fcrStore.previous_slot_head) = true →
      WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks anc).slot lm.root)
    (hanc : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root fcrStore.previous_slot_head) (get_node_for_root anc) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : (get_current_slot cfg fcrStore.store - 1) + 1 ≤ E.slot_at cfg m) :
    anc ∈ (E.store cfg ext w m).block_roots := by
  have hcert : Weak.has_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) fcrStore.previous_slot_head
      (get_block_slot fcrStore.store fcrStore.previous_slot_head)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    simpa only [Weak.has_justification_witness_certificate] using hwitness
  obtain ⟨hval, htab, hstart0, hstartH, hendH⟩ :=
    certificateSideConditions_at_observer cfg ext hA hqH hstore hwitness_known hcert
  have hcertQ : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      (get_current_balance_source fcrStore) fcrStore.previous_slot_head
      (get_block_slot fcrStore.store fcrStore.previous_slot_head)
      (get_current_slot cfg fcrStore.store - 1) = true := by rw [← hstore]; exact hcert
  exact Weak.certificate_chain_dissemination cfg ext E hA.wellFormed hA.honest_behavior hsync
    hA.externals_coherence hA.byzantine_bound hji hA.genesis obs q
    (get_current_balance_source fcrStore) fcrStore.previous_slot_head anc
    (get_block_slot fcrStore.store fcrStore.previous_slot_head)
    (get_current_slot cfg fcrStore.store - 1) hqH hstartH hendH hstart0 hval htab hcomm
    hwitness_known hanc_obs hcertQ hwb hwalk hanc w hw m hmH hgate

/-! ## Head-certificate dissemination (fork-choice head) -/

/-- **A true head broadcast certificate disseminates the fork-choice head.**
`Weak.has_head_broadcast_certificate` unfolds to exactly
`Weak.has_broadcast_certificate` at `(get_head store).root` over
`[get_block_slot store head, current_slot - 1]` — the same span shape as the
witness certificate — so the same side-condition bundle applies; the head's
own knownness at the query second is honesty-free
(`Execution.head_root_known_at_observer`, `WeakObserverDomain.lean`), driven
by `hcoh : E.ObserverCoherence cfg ext obs` (which also supplies the committee
readback `certificate_dissemination` needs). Sites 6 and 7 of the `hfilter`
design (`fcrStep_currentNext_endpointRecentSourceSeed`'s query-head leg, and
`previousOffStart_queryGUEpochSeed`'s `head` arm) are exactly this call. -/
theorem headSeed_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcoh : E.ObserverCoherence cfg ext obs)
    {fcrStore : FastConfirmationStore Root}
    (hstore : fcrStore.store = E.store cfg ext obs q)
    (hhead : Weak.has_head_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : (get_current_slot cfg fcrStore.store - 1) + 1 ≤ E.slot_at cfg m) :
    (get_head cfg fcrStore.store).root ∈ (E.store cfg ext w m).block_roots := by
  have hheadKnown : (get_head cfg fcrStore.store).root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hstore]
    exact E.head_root_known_at_observer cfg ext hcoh q hqH
  have hcert : Weak.has_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root
      (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    simpa only [Weak.has_head_broadcast_certificate] using hhead
  obtain ⟨hval, htab, hstart0, hstartH, hendH⟩ :=
    certificateSideConditions_at_observer cfg ext hA hqH hstore hheadKnown hcert
  have hcertQ : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root
      (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
      (get_current_slot cfg fcrStore.store - 1) = true := by rw [← hstore]; exact hcert
  exact E.certificate_dissemination cfg ext hA.wellFormed hA.honest_behavior hsync
    hA.externals_coherence hA.byzantine_bound hji hA.genesis obs q
    (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root
    (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
    (get_current_slot cfg fcrStore.store - 1) hqH hstartH hendH hstart0 hval htab
    (hcoh.committees_agree q hqH) hheadKnown hcertQ w hw m hmH hgate

/-- **Chain version**: any observer-known ancestor of the fork-choice head
disseminates too. Thin wrapper over `Weak.certificate_chain_dissemination`,
mirroring `witnessSeed_ancestor_known_at_all_honest_endpoints_at_observer`
above. This is the general form of the fact
`Weak.headUnrealizedJustification_known_and_below` /
`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`
(`WeakBankedJustification.lean`) specialize to the banking installer's own
second and its chain-intrinsic ancestor (the head's own unrealized
justification); here the second is the query second itself and the ancestor
is arbitrary, which is what a relay site with its own `WalkKnown` witness
needs. -/
theorem headSeed_ancestor_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    (hcoh : E.ObserverCoherence cfg ext obs)
    {fcrStore : FastConfirmationStore Root}
    (hstore : fcrStore.store = E.store cfg ext obs q)
    (hhead : Weak.has_head_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) = true)
    {anc : Root} (hanc_obs : anc ∈ (E.store cfg ext obs q).block_roots)
    (hwb : WalkKnown (E.store cfg ext obs q)
      ((E.store cfg ext obs q).blocks anc).slot (get_head cfg fcrStore.store).root)
    (hwalk : ∀ i lm, (E.store cfg ext obs q).latest_messages i = some lm →
      is_ancestor (E.store cfg ext obs q) (get_node_for_root lm.root)
        (get_node_for_root (get_head cfg fcrStore.store).root) = true →
      WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks anc).slot lm.root)
    (hanc : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root (get_head cfg fcrStore.store).root) (get_node_for_root anc) = true)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : (get_current_slot cfg fcrStore.store - 1) + 1 ≤ E.slot_at cfg m) :
    anc ∈ (E.store cfg ext w m).block_roots := by
  have hheadKnown : (get_head cfg fcrStore.store).root ∈
      (E.store cfg ext obs q).block_roots := by
    rw [hstore]
    exact E.head_root_known_at_observer cfg ext hcoh q hqH
  have hcert : Weak.has_broadcast_certificate cfg ext fcrStore.store
      (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root
      (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
      (get_current_slot cfg fcrStore.store - 1) = true := by
    simpa only [Weak.has_head_broadcast_certificate] using hhead
  obtain ⟨hval, htab, hstart0, hstartH, hendH⟩ :=
    certificateSideConditions_at_observer cfg ext hA hqH hstore hheadKnown hcert
  have hcertQ : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs q)
      (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root
      (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
      (get_current_slot cfg fcrStore.store - 1) = true := by rw [← hstore]; exact hcert
  exact Weak.certificate_chain_dissemination cfg ext E hA.wellFormed hA.honest_behavior hsync
    hA.externals_coherence hA.byzantine_bound hji hA.genesis obs q
    (get_current_balance_source fcrStore) (get_head cfg fcrStore.store).root anc
    (get_block_slot fcrStore.store (get_head cfg fcrStore.store).root)
    (get_current_slot cfg fcrStore.store - 1) hqH hstartH hendH hstart0 hval htab
    (hcoh.committees_agree q hqH) hheadKnown hanc_obs hcertQ hwb hwalk hanc w hw m hmH hgate

end Weak

end FastConfirmation.Spec
