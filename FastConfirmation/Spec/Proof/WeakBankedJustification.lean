import FastConfirmation.Spec.Model.WeakSynchrony
import FastConfirmation.Spec.Proof.CheckpointDomain
import FastConfirmation.Spec.Proof.WeakCertificateDissemination
import FastConfirmation.Spec.Proof.WeakAncestryTransport
import FastConfirmation.Spec.Proof.AnchorFacade
import FastConfirmation.Spec.Proof.Trajectory
import FastConfirmation.Spec.Proof.MinimalSelectedDomain
import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts
import FastConfirmation.Spec.Proof.WeakFCRCallContracts

/-!
# Spec / Proof / WeakBankedJustification

Rule delta 5's input invariant (`Weak.CertifiedBankedJustification`,
`docs/delta5-proposal.md` §2) and its consumption lemma(s), with the
Francesco amendment to §3's "residual corner": the anchor arm is handled by a
symmetric two-arm consumption, not by scoping or a side condition.

## What is delivered

* `Weak.BankedJustificationCertificate` / `Weak.CertifiedBankedJustification`
  — the certified-arm evidence package and the one-shot input invariant, per
  proposal §2.
* `Weak.has_broadcast_certificate_span_nonempty` — a true certificate forces
  a non-empty span (proposal §1's "free bonus").
* `Weak.checkpoint_state_key_of_broadcast_certificate` — a true certificate
  forces its balance source to be a keyed checkpoint state (same route as
  `Execution.checkpoint_state_key_of_one_confirmed` /
  `Execution.get_attestation_score_unkeyed_eq_zero`, `CheckpointDomain.lean`).
* `Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer` — the
  consumption lemma stated over the certificate structure directly (proposal
  §2, unchanged statement): the supplier *and* the banked root are known at
  every honest endpoint past the gate.
* `Weak.bankedRoot_known_at_all_honest_endpoints_at_observer` — the amendment:
  the same conclusion's banked-root half, stated over the *invariant*
  (`CertifiedBankedJustification`), covering **both** arms symmetrically: the
  anchor arm via genesis membership + `Execution.store_storeLE` (globally
  known by initialisation, no supplier), the certified arm by routing through
  the lemma above.

* `Weak.acceptedOriginRoot_known_at_observer` and its two instances
  `Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory` and
  `Weak.justifiedRoot_known_at_observer` — the accepted-FFG knownness facts
  restated at a possibly-Byzantine observer, copy-with-binder-dropped exactly
  as `ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`
  (`WeakOneShotSafety.lean`) was.
* `Weak.update_fcv_observed_exact`, `Weak.weakFcr_previousGreatest_succ_exact`,
  `Weak.weakFcr_previousGreatest_origin` — the weak twins of the strong
  bookkeeping rotation lemmas (`ActualResetCheckpointRealization.lean`,
  `AcceptedCandidateHistoryRecurrence.lean`), now gated-rule aware.
* `Weak.weakFcr_previousGreatest_known`, `Weak.weakFcr_observed_known`,
  `Weak.weakFcrStep_observed_known` — **`banked_known` discharged in full**
  along the actual weak trajectory, unconditionally and with no honesty
  hypothesis anywhere.
* `Weak.bankedBelowHead_of_bankedBelowJustified` — the fork-choice reduction
  of `banked_below_supplier`: the head descends from the store's justified
  root, so it suffices to place the banked root on the *justified* root's
  chain.

## Honesty audit of the installation-provenance machinery

Every component the maintenance lemmas need from the strong development is
honesty-free, either because there is no honesty binder at all
(`Execution.fcr_previousGreatest_succ_exact`,
`Execution.previousGreatest_acceptedInstallation`,
`Execution.AcceptedUJCacheInstallationAt`,
`ObservedResetCandidateInputAt.acceptedInstallation`,
`ExactPrefixAcceptedFFGSemantics.causalStoreGlobalProjection`,
`globalJustified_anchor_or_AUEvidence`,
`AcceptedSelectorAUCarrier.checkpointRoot_known`,
`AcceptedFFGTransitionCoherence.au_checkpoint_of_known` — quantified over
`E.CausalStore`, not `E.honest`) or because the binder is routed only into
node-generic store geometry (`store_causal`, `store_parentSlotLt`,
`store_walkKnownK`, `store_storeLE`, `store_anchor_block`,
`store_anchor_min_slot`). The one honesty-quantified route,
`ActualResetCheckpointRealization.lean`'s `ResetCheckpointHistoryAt` family,
uses the **legacy** `FFGTransitionCoherence.au_checkpoint_of_known`
(`∀ w ∈ E.honest, …`) and is bypassed here in favour of the accepted bundle.
So the honesty is dead, exactly as it was for
`justifiedRootKnown_of_acceptedGlobalTrajectory`.

## What is not delivered, and why it is a model-level finding

`Weak.certifiedBankedJustification_update` and
`Weak.weakFcr_certifiedBankedJustification` (proposal §2's maintenance lemmas)
are **not** included. After the work above, exactly one field of
`BankedJustificationCertificate` remains: `banked_below_supplier`. It is not
merely unproved — **as rule delta 5 is currently written it is false in
general**, so no amount of observer-side restatement can close it.

The gate installs `previous_epoch_greatest_unrealized_checkpoint`, which
`weakFcr_previousGreatest_origin` shows is `(E.store obs k)
.unrealized_justified_checkpoint` for the second `k` at the *end of the
previous epoch*. The gate certifies the fork-choice head at the *boundary*
second, and `get_head` descends from `store.justified_checkpoint.root`
(`bankedBelowHead_of_bankedBelowJustified`). Between `k` and the boundary the
store's own checkpoints can move to a different branch: `on_tick_per_slot`'s
epoch pull-up installs whatever `store.unrealized_justified_checkpoint` is at
the *tick*, and `update_unrealized_checkpoints` replaces the UJ field on any
strictly higher epoch — from any accepted carrier, on any branch. So the
observer's store can legitimately hold UJ = `C_A` (epoch `e−1`, branch A) at
second `k`, receive a branch-B block whose pulled-up state justifies `C_B` at
epoch `e`, and enter epoch `e` with `justified_checkpoint = C_B` and a head on
branch B. The gate then passes (the head *is* certified) and banks `C_A`,
which the head certificate does not cover. Placing `C_A` and `C_B` on one
chain is an FFG-safety-grade claim about conflicting certified justifications
at *different* epochs; it is not a consequence of the store definitions, and
the accepted bundle (`AcceptedGlobalUnrealizedJustifiedOrigin` = `anchor ∨
GU carrier`) does not force it. `JustificationInterface.justified_descends`
covers only the strictly-ahead case and is honest-quantified besides.

Consequence: **the gate as landed can bank a value its own certificate does
not cover**, so the banked root's dissemination to honest endpoints does not
follow. Minimal fix (statement only, for review — not applied here, since it
changes the committed rule):

```lean
    current_epoch_observed_justified_checkpoint :=
      if has_head_broadcast_certificate cfg ext store bs &&
          is_ancestor store (get_head cfg store)
            (get_node_for_root
              fcr_store.previous_epoch_greatest_unrealized_checkpoint.root) then
        fcr_store.previous_epoch_greatest_unrealized_checkpoint
      else fcr_store.current_epoch_observed_justified_checkpoint
```

i.e. one extra executable conjunct, still strictly stricter than the strong
rule and so still safety-free by the same monotonicity argument, and still
liveness-costing at most one epoch of freshness (§4's accounting gains a
fourth "inert" case: a boundary head that switched branches). With it,
`banked_below_supplier` is the conjunct verbatim, `banked_known` is the
theorems above, `second_pos` is the call's slot advance, and the two
maintenance lemmas close. `bankedBelowHead_of_bankedBelowJustified` shows the
cheaper justified-root form of the conjunct suffices.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Free bonus: a true certificate has a non-empty span -/

/-- **A true broadcast certificate has a non-empty span.** If
`start_slot > end_slot`, `Finset.Icc start_slot end_slot` is empty, so the
certificate's support is the empty sum `0`, and `0 > budget` is false for any
`budget : ℕ` — contradicting the certificate. (Proposal §1's "free bonus":
composed with `end_slot = get_current_slot store - 1` at
`has_head_broadcast_certificate` and a within-horizon call second, this is
what makes the certified head a pre-boundary block.) -/
theorem has_broadcast_certificate_span_nonempty {store : Store Root}
    {balance_source : BeaconState Root} {block_root : Root} {start_slot end_slot : Slot}
    (hcert : Weak.has_broadcast_certificate cfg ext store balance_source block_root
      start_slot end_slot = true) :
    start_slot ≤ end_slot := by
  by_contra hlt
  have hempty : Finset.Icc start_slot end_slot = (∅ : Finset Slot) :=
    Finset.Icc_eq_empty hlt
  have hsupp0 : Weak.get_broadcast_certificate_support cfg ext store balance_source
      block_root start_slot end_slot = 0 := by
    simp [Weak.get_broadcast_certificate_support, hempty]
  rw [Weak.has_broadcast_certificate, hsupp0] at hcert
  simp only [gt_iff_lt, decide_eq_true_eq] at hcert
  exact absurd hcert (Nat.not_lt_zero _)

/-! ## An unkeyed balance source cannot carry a true certificate -/

/-- **A true broadcast certificate forces its balance source to be keyed.**
An unkeyed checkpoint state is the default `BeaconState`, whose empty
validator registry makes every candidate inactive (`exit_epoch = 0`, so
`is_active_validator` is false for every epoch), hence the certificate's
support is the empty sum `0` — contradicting a true certificate exactly as
`Execution.checkpoint_state_key_of_one_confirmed` contradicts a true
`is_one_confirmed` call (`CheckpointDomain.lean`). -/
theorem checkpoint_state_key_of_broadcast_certificate (E : Execution Root)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (c : Checkpoint Root) (block_root : Root)
    (start_slot end_slot : Slot)
    (hcert : Weak.has_broadcast_certificate cfg ext (E.store cfg ext v n)
      ((E.store cfg ext v n).checkpoint_states c) block_root start_slot end_slot = true) :
    c ∈ (E.store cfg ext v n).checkpoint_state_keys := by
  by_contra hc
  have hz : (E.store cfg ext v n).checkpoint_states c = (default : BeaconState Root) :=
    E.checkpointStatesExact cfg ext hgen v n c hc
  rw [hz] at hcert
  have hnoactive : ∀ i : ValidatorIndex,
      is_active_validator ((default : BeaconState Root).validators.getD i default)
        (get_current_epoch cfg (default : BeaconState Root)) = false := by
    intro i
    change is_active_validator (default : Validator)
      (get_current_epoch cfg (default : BeaconState Root)) = false
    simp only [is_active_validator, decide_eq_false_iff_not]
    rintro ⟨-, hlt⟩
    exact absurd hlt (Nat.not_lt_zero _)
  have hsupp0 : Weak.get_broadcast_certificate_support cfg ext (E.store cfg ext v n)
      (default : BeaconState Root) block_root start_slot end_slot = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exfalso
    simp only [Finset.mem_filter, Bool.and_eq_true] at hi
    rw [hnoactive i] at hi
    exact absurd hi.1.2.2 (by decide)
  rw [Weak.has_broadcast_certificate, hsupp0] at hcert
  simp only [gt_iff_lt, decide_eq_true_eq] at hcert
  exact absurd hcert (Nat.not_lt_zero _)

/-! ## The input invariant -/

/-- Certificate evidence for the banked observed justified checkpoint (rule
delta 5's input invariant, certified arm). Exactly the package
`Execution.certificate_dissemination` consumes, plus the ancestry that lets
the banked root's own dissemination be established from the supplier's.
Field names mirror `Execution.AcceptedUJCacheInstallationAt`
(`second`/`second_le` for `originSecond`/`origin_le`) so the weak Lemma-22
history can consume both uniformly.

**Fill beyond proposal §2**: `second_pos`. The consumption lemma's timing
gate is stated as `E.slot_at cfg second ≤ E.slot_at cfg m` ("same-slot
capable", per the proposal) and needs
`get_current_slot (E.store obs second) - 1 + 1 = get_current_slot (E.store obs
second)`, which needs `get_current_slot (E.store obs second) ≥ 1` — false in
general for `ℕ` truncated subtraction when the store's current slot is `0`
(e.g. the certificate is, in principle, satisfiable at genesis's own slot).
Every certificate actually produced by a real trajectory has this for free
(`second` is only ever reached via a genuine slot advance, so the previous
second's slot bounds it below), but the bare structure does not encode that
provenance, so it is recorded as an explicit field. -/
structure BankedJustificationCertificate (E : Execution Root)
    (obs : ValidatorIndex) (n : ℕ) (fcr_store : FastConfirmationStore Root) where
  /-- the second whose gated epoch-start rotation banked the value -/
  second : ℕ
  second_le : second ≤ n
  second_within : E.WithinHorizon cfg second
  /-- fill (see docstring): the store's clock has advanced past slot `0` at
  `second`, needed for the consumption lemma's same-slot-capable timing. -/
  second_pos : 1 ≤ get_current_slot cfg (E.store cfg ext obs second)
  /-- the supplier of the justification: the fork-choice head at that second -/
  supplier : Root
  supplier_eq_head : supplier = (get_head cfg (E.store cfg ext obs second)).root
  supplier_known : supplier ∈ (E.store cfg ext obs second).block_roots
  /-- the banked root is on the supplier's chain: certificate ancestor
  monotonicity carries dissemination from the supplier down to it -/
  banked_known :
    fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext obs second).block_roots
  banked_below_supplier :
    is_ancestor (E.store cfg ext obs second) (get_node_for_root supplier)
      (get_node_for_root
        fcr_store.current_epoch_observed_justified_checkpoint.root) = true
  /-- the balance source the gate was evaluated against, with the two economic
  facts `certificate_dissemination` requires (produced, not assumed: the gate
  being true forces its key to be keyed, then `registryConstant` /
  `checkpoint_states_total_active_balance` apply) -/
  balance_source : BeaconState Root
  balance_registry : balance_source.validators = E.registry
  balance_total :
    get_total_active_balance cfg balance_source = E.total_active cfg
  /-- the gate itself, verbatim -/
  certificate :
    has_head_broadcast_certificate cfg ext (E.store cfg ext obs second)
      balance_source = true
  /-- the span side conditions, discharged once here rather than at each use -/
  start_anchor :
    E.slot_at cfg 0 ≤ get_block_slot (E.store cfg ext obs second) supplier
  start_within : E.SlotWithinHorizon cfg
    (get_block_slot (E.store cfg ext obs second) supplier)
  end_within : E.SlotWithinHorizon cfg
    (get_current_slot cfg (E.store cfg ext obs second) - 1)

/-- **The one-shot input invariant.** `fcr_store`'s banked observed justified
checkpoint is either the trusted anchor/initialisation value — globally
known, hence disseminated for free by `Execution.store_storeLE` — or it was
installed by a gate-passing rotation whose supplier carries a broadcast
certificate. Two arms, mirroring `AcceptedUJCacheInstallationAt.
accepted_origin`. -/
def CertifiedBankedJustification (E : Execution Root) (obs : ValidatorIndex)
    (n : ℕ) (fcr_store : FastConfirmationStore Root) : Prop :=
  fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      E.genesis_store.block_roots ∨
    Nonempty (BankedJustificationCertificate cfg ext E obs n fcr_store)

/-! ## Consumption -/

/-- **The consumption lemma, certified arm** (proposal §2, statement
unchanged): the banked twin of
`Execution.confirmed_known_at_all_honest_endpoints_at_observer`. The supplier
disseminates directly (`Execution.certificate_dissemination`, obligation 2,
applied at the supplier itself after unfolding `has_head_broadcast_certificate`
along `supplier_eq_head`); the banked root then transports along
`banked_below_supplier` via `Execution.is_ancestor_transport_closed`, using
the supplier's freshly-established endpoint membership as the doubly-known
witness — no second trip through an honest supporter's store, and no
`WalkKnown` side hypotheses, are needed (unlike
`Weak.certificate_chain_dissemination`, which this lemma deliberately avoids
calling: its extra `WalkKnown` premises are not derivable from the
certificate's own fields, whereas `is_ancestor_transport_closed`'s
anchor-min-slot premise is). The `hgate`/timing arithmetic is "same-slot
capable" (`E.slot_at cfg second ≤ E.slot_at cfg m`, equality not required)
via `second_pos` and `has_broadcast_certificate_span_nonempty`. -/
theorem bankedSupplier_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    h.supplier ∈ (E.store cfg ext w m).block_roots ∧
      fcr_store.current_epoch_observed_justified_checkpoint.root ∈
        (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  -- Unfold the gate to a plain certificate on the supplier.
  have hcert' : Weak.has_broadcast_certificate cfg ext (E.store cfg ext obs h.second)
      h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1) = true := by
    have hc := h.certificate
    simp only [Weak.has_head_broadcast_certificate, ← h.supplier_eq_head] at hc
    exact hc
  -- Same-slot-capable timing: end_slot + 1 = current_slot = E.slot_at second ≤ E.slot_at m.
  have hend1 : get_current_slot cfg (E.store cfg ext obs h.second) - 1 + 1 =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    Nat.sub_add_cancel h.second_pos
  have hslotEq : E.slot_at cfg h.second =
      get_current_slot cfg (E.store cfg ext obs h.second) :=
    (E.store_current_slot cfg ext obs h.second).symm
  have htiming : (get_current_slot cfg (E.store cfg ext obs h.second) - 1) + 1 ≤
      E.slot_at cfg m := by
    rw [hend1, ← hslotEq]; exact hgate
  have hsupplier : h.supplier ∈ (E.store cfg ext w m).block_roots :=
    E.certificate_dissemination cfg ext hA.wellFormed hA.honest_behavior hsync
      hA.externals_coherence hA.byzantine_bound hji ⟨ast, ablk, hgeq, hslot, hparent⟩
      obs h.second h.balance_source h.supplier
      (get_block_slot (E.store cfg ext obs h.second) h.supplier)
      (get_current_slot cfg (E.store cfg ext obs h.second) - 1)
      h.second_within h.start_within h.end_within h.start_anchor
      h.balance_registry h.balance_total (hcomm h.second h.second_within)
      h.supplier_known hcert' w hw m hmH htiming
  have hanchorBanked : ablk.message.slot ≤
      ((E.store cfg ext obs h.second).blocks
        fcr_store.current_epoch_observed_justified_checkpoint.root).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence hgeq hslot hparent
      obs h.second fcr_store.current_epoch_observed_justified_checkpoint.root h.banked_known
  have hbanked : fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.is_ancestor_transport_closed cfg ext hA.wellFormed hA.externals_coherence hgeq hslot
      hparent hanchorBanked h.supplier_known hsupplier h.banked_known h.banked_below_supplier
  exact ⟨hsupplier, hbanked⟩

/-- **The consumption lemma, both arms** (Francesco's amendment to proposal
§3's "residual corner"): the banked root is known at every honest endpoint
past the gate whether it is the trusted anchor or a certified installation —
no scoping and no side condition on the anchor arm. The anchor arm needs only
`Execution.store_storeLE` from genesis; the certified arm routes through
`bankedSupplier_known_at_all_honest_endpoints_at_observer` above (there is no
supplier in the anchor arm, so only the banked-root conjunct is stated here,
universally over whichever certificate witnesses the invariant's second
disjunct). -/
theorem bankedRoot_known_at_all_honest_endpoints_at_observer
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hsync : PaperSafetySynchrony cfg ext E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s)
    {n : ℕ} {fcr_store : FastConfirmationStore Root}
    (hinv : Weak.CertifiedBankedJustification cfg ext E obs n fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ} (hmH : E.WithinHorizon cfg m)
    (hgate : ∀ h : Weak.BankedJustificationCertificate cfg ext E obs n fcr_store,
      E.slot_at cfg h.second ≤ E.slot_at cfg m) :
    fcr_store.current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  rcases hinv with hanchor | hne
  · exact (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchor
  · obtain ⟨h⟩ := hne
    exact (Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer cfg ext hA hsync hji
      hgen hcomm h hw hmH (hgate h)).2

/-! ## Maintenance along the actual-call trajectory

The two maintenance lemmas of proposal §2 (`certifiedBankedJustification_update`,
`weakFcr_certifiedBankedJustification`) need two facts about the value rule
delta 5 installs at a gate-passing epoch-start rotation — namely the
`banked_known` and `banked_below_supplier` fields of
`BankedJustificationCertificate` at `second := n + 1`.

This section discharges **`banked_known` in full**, unconditionally along the
weak trajectory and with no honesty anywhere: the honesty binders in the
strong development's installation-provenance machinery
(`Execution.previousGreatest_acceptedInstallation`,
`Execution.AcceptedUJCacheInstallationAt`,
`ExactPrefixAcceptedFFGSemantics.causalStoreGlobalProjection`,
`AcceptedSelectorAUCarrier.checkpointRoot_known`) are either absent outright or
route only into node-generic store geometry (`store_causal`,
`store_parentSlotLt`, `store_walkKnownK`, `store_storeLE`, `store_anchor_block`),
exactly as for `justifiedRootKnown_of_acceptedGlobalTrajectory`.  The one
honesty-quantified route (`ActualResetCheckpointRealization`'s
`ResetCheckpointHistoryAt`) is the *legacy* `FFGTransitionCoherence`
(`au_checkpoint_of_known : ∀ w ∈ E.honest, …`) and is bypassed here in favour
of the accepted bundle's causal-store-quantified
`AcceptedFFGTransitionCoherence.au_checkpoint_of_known`.

`banked_below_supplier` is **not** discharged, and is not discharge*able* as
rule delta 5 is currently written — see the module docstring's finding. -/

/-! ### Observer-side accepted unrealized-justified-root knownness -/

/-- Unrealized-justified twin of
`AcceptedFFGGlobalCheckpointOrigins.justified_anchor_or_AUEvidence`
(`AcceptedFFGGlobalCheckpointTrajectory.lean` exports the justified and
finalized accessors only; the `unrealized_justified` field has the same
`anchor ∨ GU carrier` shape). -/
private theorem unrealizedJustified_anchor_or_AUEvidence {E : Execution Root}
    {anchor : Checkpoint Root} {S : AcceptedChainFFGState cfg ext E anchor}
    {store : Store Root} (h : AcceptedFFGGlobalCheckpointOrigins S store) :
    store.unrealized_justified_checkpoint = anchor ∨
      AcceptedSelectorAUEvidence S store store.unrealized_justified_checkpoint := by
  rcases h.unrealized_justified with hanchor | ⟨r, hr, hgu⟩
  · exact Or.inl hanchor
  · right
    apply AcceptedSelectorAUEvidence.of_AU hr
    rw [hgu]
    exact S.gu_AU cfg ext hr.acceptedRoot

/-- **Accepted-origin checkpoint roots are known in the observer's own store.**
The observer-side restatement of the knownness half of
`AcceptedCurrentTargetLowerContracts.justifiedRootKnown_of_acceptedGlobalTrajectory`,
generalized from the store's justified checkpoint to *any* checkpoint with an
accepted origin at that store.  Like
`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`
(`WeakOneShotSafety.lean`), this is a *copy with the honesty binder dropped*
rather than an application of the strong lemma: every step it takes
(`store_storeLE`, `store_anchor_block`, `store_parentSlotLt`,
`store_walkKnownK`, `store_causal`,
`ExactPrefixAcceptedFFGSemantics.causalStoreGlobalProjection`,
`AcceptedSelectorAUCarrier.checkpointRoot_known`) is proved for an arbitrary
node — the accepted bundle's `au_checkpoint_of_known` is quantified over
`E.CausalStore`, not over `E.honest`, unlike the legacy
`FFGTransitionCoherence` one that `ActualResetCheckpointRealization.lean`
uses — but the strong lemma still takes `_hw : w ∈ E.honest` as a required
explicit argument, which a possibly-Byzantine `obs` cannot supply. -/
theorem acceptedOriginRoot_known_at_observer
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {c : Checkpoint Root}
    (horigin : c = B.anchor ∨
      AcceptedSelectorAUEvidence B.state (E.store cfg ext obs n) c) :
    c.root ∈ (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hanchorRoot : B.anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorMem0 : B.anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorMem : B.anchor.root ∈ (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [Execution.TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  rcases horigin with hcAnchor | hevidence
  · rw [hcAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hincluded⟩ := carrier.formed_evidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor c :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
          B.state.includedAttestations) hincluded
    have hanchorEpochLe : B.anchor.epoch ≤ c.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg c.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
        ((E.store cfg ext obs n).blocks B.anchor.root).slot carrier.tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
        B.anchor.root hanchorMem carrier.tip carrier.tip_carrier.known
    have hwalk : WalkKnown (E.store cfg ext obs n)
        (compute_start_slot_at_epoch cfg c.epoch) carrier.tip := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots hwalk

/-- **The observer's own unrealized-justified root is known in its own store.**
`acceptedOriginRoot_known_at_observer` at the store-global unrealized-justified
field, whose accepted origin is `unrealizedJustified_anchor_or_AUEvidence`.
This is `banked_known`'s ultimate source. -/
theorem unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).unrealized_justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis
  exact Weak.acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (unrealizedJustified_anchor_or_AUEvidence cfg ext
      ((B.causalStoreGlobalProjection ⟨ast, ablk, hgenEq, hslot⟩ hanchor
        (E.store_causal cfg ext obs n)).storeGlobal))

/-- **The observer's own justified root is known in its own store.**
`acceptedOriginRoot_known_at_observer` at the store-global justified field.
This is `ObserverCoherence.justified_root_known` again, obtained here as an
instance of the shared observer-side restatement rather than a second copy of
the same forty lines; it is what feeds the fork-choice reduction below. -/
theorem justifiedRoot_known_at_observer
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hT.genesis
  exact Weak.acceptedOriginRoot_known_at_observer cfg ext B hT hanchor hboundary obs n
    (B.globalJustified_anchor_or_AUEvidence ⟨ast, ablk, hgenEq, hslot⟩ hanchor
      (E.store_causal cfg ext obs n))

/-! ### The ancestry leg, reduced to the store's justified root -/

/-- **`banked_below_supplier` reduces to `is_ancestor store justified banked`.**
`get_head` starts its GHOST descent at `store.justified_checkpoint.root` and
only ever steps into the filtered block tree rooted there, so any block on the
justified root's chain is on the head's chain
(`E5Filter.head_ge_of_justified_ge_K`).  All three of that lemma's domain
conditions are node-generic and hold at the (possibly Byzantine) observer:
`store_parentSlotLt`, `store_walkKnownK`, and `justifiedRoot_known_at_observer`
above.

This lemma is the exact residual of rule delta 5's maintenance obligation: it
converts `BankedJustificationCertificate.banked_below_supplier` into a fact
about the *justified* checkpoint, which is where the obligation genuinely
fails — see this module's docstring. -/
theorem bankedBelowHead_of_bankedBelowJustified
    {E : Execution Root} (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) {b : Root}
    (hb : b ∈ (E.store cfg ext obs n).block_roots)
    (hjb : is_ancestor (E.store cfg ext obs n)
      (get_node_for_root (E.store cfg ext obs n).justified_checkpoint.root)
      (get_node_for_root b) = true) :
    is_ancestor (E.store cfg ext obs n)
      (get_head cfg (E.store cfg ext obs n)) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis
  exact head_ge_of_justified_ge_K cfg
    (E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n)
    (E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n)
    (Weak.justifiedRoot_known_at_observer cfg ext B hT hanchor hboundary obs n)
    hb hjb

/-! ### Exact rotation of the two weak FCR checkpoint fields -/

/-- Weak twin of `update_fcv_observed_exact` (`ActualResetCheckpointRealization
.lean`): exact source selected for the observed checkpoint, including rule
delta 5's certificate gate and the ordered write through the possibly
just-updated greatest-unrealized field. -/
theorem update_fcv_observed_exact (fcr_store : FastConfirmationStore Root) :
    (Weak.update_fast_confirmation_variables cfg ext
        fcr_store).current_epoch_observed_justified_checkpoint =
      if is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store) ∧
          has_head_broadcast_certificate cfg ext fcr_store.store
            (get_current_balance_source fcr_store) = true then
        (if is_start_slot_at_epoch cfg (get_current_slot cfg fcr_store.store + 1) then
          fcr_store.store.unrealized_justified_checkpoint
        else fcr_store.previous_epoch_greatest_unrealized_checkpoint)
      else fcr_store.current_epoch_observed_justified_checkpoint := by
  simp only [Weak.update_fast_confirmation_variables]
  split_ifs <;> simp_all

/-- Weak twin of `Execution.fcr_previousGreatest_succ_exact`: the carried
greatest-unrealized field is refreshed at a real slot advance exactly when the
*next* slot starts an epoch, and rule delta 5 leaves that (ungated) write
alone. -/
theorem weakFcr_previousGreatest_succ_exact {E : Execution Root}
    (v : ValidatorIndex) (n : ℕ)
    (hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    (E.weakFcr cfg ext v (n + 1)).previous_epoch_greatest_unrealized_checkpoint =
      if is_start_slot_at_epoch cfg
          (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) then
        (E.store cfg ext v (n + 1)).unrealized_justified_checkpoint
      else
        (E.weakFcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint := by
  simp only [Execution.weakFcr]
  rw [if_pos hadv]
  change FastConfirmationStore.previous_epoch_greatest_unrealized_checkpoint
    (Weak.on_fast_confirmation cfg ext
      { E.weakFcr cfg ext v n with store := E.store cfg ext v (n + 1) }) = _
  simp only [Weak.on_fast_confirmation, Weak.update_fast_confirmation_variables]
  split_ifs <;> rfl

/-- **Exact provenance of the weak carried greatest-unrealized field.** It is
always some earlier second's store-global unrealized-justified checkpoint — the
weak counterpart of `Execution.AcceptedUJCacheInstallationAt.field_eq`, stated
without the accepted bundle because only the exact field identity is needed
here.  No honesty, no call predicate: the recurrence is driven by the raw slot
advance that `E.weakFcr` itself branches on. -/
theorem weakFcr_previousGreatest_origin {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) :
    ∀ n : ℕ, ∃ k ≤ n,
      (E.weakFcr cfg ext v n).previous_epoch_greatest_unrealized_checkpoint =
        (E.store cfg ext v k).unrealized_justified_checkpoint := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      obtain ⟨ast, ablk, hgenEq⟩ := hgen
      change E.genesis_store.finalized_checkpoint =
        E.genesis_store.unrealized_justified_checkpoint
      rw [hgenEq]
      simp only [get_forkchoice_store]
  | succ n ih =>
      obtain ⟨k, hk, hfield⟩ := ih
      by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · rw [Weak.weakFcr_previousGreatest_succ_exact cfg ext v n hadv]
        by_cases hrot : is_start_slot_at_epoch cfg
            (get_current_slot cfg (E.store cfg ext v (n + 1)) + 1) = true
        · rw [if_pos hrot]
          exact ⟨n + 1, Nat.le_refl _, rfl⟩
        · rw [if_neg hrot]
          exact ⟨k, hk.trans (Nat.le_succ n), hfield⟩
      · refine ⟨k, hk.trans (Nat.le_succ n), ?_⟩
        have hstep : (E.weakFcr cfg ext v (n + 1)
            ).previous_epoch_greatest_unrealized_checkpoint =
            (E.weakFcr cfg ext v n
              ).previous_epoch_greatest_unrealized_checkpoint := by
          simp only [Execution.weakFcr, if_neg hadv]
        exact hstep.trans hfield

/-! ### `banked_known`, discharged -/

/-- The weak carried greatest-unrealized root is a known block in the
observer's own store at every later second. -/
theorem weakFcr_previousGreatest_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) {n m : ℕ} (hnm : n ≤ m) :
    ((E.weakFcr cfg ext obs n
        ).previous_epoch_greatest_unrealized_checkpoint).root ∈
      (E.store cfg ext obs m).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis
  obtain ⟨k, hk, hfield⟩ :=
    Weak.weakFcr_previousGreatest_origin cfg ext ⟨ast, ablk, hgenEq⟩ obs n
  rw [hfield]
  exact (E.store_storeLE cfg ext obs (hk.trans hnm)).1
    (Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary obs k)

/-- **`banked_known`, discharged for the whole weak trajectory.** Whatever rule
delta 5 has banked in `current_epoch_observed_justified_checkpoint` at any
second is a known block in the observer's own store at that second — the
initialisation value is the trusted anchor, and every later value is either
carried (`store_storeLE`) or a gate-passing installation of the
greatest-unrealized field, which `weakFcr_previousGreatest_known` covers.  This
is the `banked_known` field of `BankedJustificationCertificate` at
`second := n`, proved outright and with no honesty hypothesis anywhere. -/
theorem weakFcr_observed_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ,
      ((E.weakFcr cfg ext obs n
          ).current_epoch_observed_justified_checkpoint).root ∈
        (E.store cfg ext obs n).block_roots := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis
  intro n
  induction n with
  | zero =>
      change E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots
      rw [hgenEq]
      simp only [get_forkchoice_store, List.mem_singleton]
  | succ n ih =>
      by_cases hadv : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (Weak.update_fast_confirmation_variables cfg ext
              { E.weakFcr cfg ext obs n with
                store := E.store cfg ext obs (n + 1) }
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_pos hadv, Weak.on_fast_confirmation]
        rw [hstep, Weak.update_fcv_observed_exact]
        split_ifs
        · exact Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory cfg ext B
            hT hanchor hboundary obs (n + 1)
        · exact Weak.weakFcr_previousGreatest_known cfg ext B hT hanchor hboundary
            obs (Nat.le_succ n)
        · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih
      · have hstep : (E.weakFcr cfg ext obs (n + 1)
            ).current_epoch_observed_justified_checkpoint =
            (E.weakFcr cfg ext obs n
              ).current_epoch_observed_justified_checkpoint := by
          simp only [Execution.weakFcr, if_neg hadv]
        rw [hstep]
        exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 ih

/-- `banked_known` at the speculative query store `E.weakFcrStep`, the shape
the maintenance lemma of proposal §2 needs at `second := n + 1`. -/
theorem weakFcrStep_observed_known {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) (n : ℕ) :
    ((E.weakFcrStep cfg ext obs n
        ).current_epoch_observed_justified_checkpoint).root ∈
      (E.store cfg ext obs (n + 1)).block_roots := by
  rw [Execution.weakFcrStep, Weak.update_fcv_observed_exact]
  split_ifs
  · exact Weak.unrealizedJustifiedRoot_known_of_acceptedGlobalTrajectory cfg ext B hT
      hanchor hboundary obs (n + 1)
  · exact Weak.weakFcr_previousGreatest_known cfg ext B hT hanchor hboundary
      obs (Nat.le_succ n)
  · exact (E.store_storeLE cfg ext obs (Nat.le_succ n)).1
      (Weak.weakFcr_observed_known cfg ext B hT hanchor hboundary obs n)

end Weak

end FastConfirmation.Spec
