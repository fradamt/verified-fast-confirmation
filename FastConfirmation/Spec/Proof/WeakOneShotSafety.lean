import FastConfirmation.Spec.Proof.WeakSelectorInversion
import FastConfirmation.Spec.Proof.WeakConfirmedDissemination
import FastConfirmation.Spec.Proof.CoveredMargin
import FastConfirmation.Spec.Proof.AcceptedCurrentTargetLowerContracts

/-!
# Spec / Proof / WeakOneShotSafety

Stage 7 (final assembly) of the weak-synchrony migration
(`docs/weak-synchrony.md`): the one-shot weak safety theorem. The weak
selector's output, read at an arbitrary (not necessarily honest) observer's
store, is `SafeFrom` at every honest endpoint.

## Shape of the argument

This is a line-for-line clone of the strong arbitrary-query bridge
`CoveredMargin.safeFrom_find_latest_confirmed_descendant_of_selectedCoveredMarginsAt_minimal`
(`:408`) and its two supporting lemmas
`coveredDescendStepChainSupply_of_selectedMarginsAt_minimal` (`:287`) and
`safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_minimal`
(`:333`), over `Weak.find_latest_confirmed_descendant` instead of the strong
selector, with the observer `(v, hv : v ∈ E.honest)` replaced everywhere by
`(obs, hW : E.WeakObserverMarginAssumptions cfg ext obs)`.

Two families of ingredient substitution are needed, matching the two ways the
strong proof used `v`'s honesty:

* wherever the strong proof calls a `MinimalSelectedDomain`/`ArbitraryQueryMargin`
  theorem whose *only* honesty use was `SelectedMarginDomain.justified_root_known`
  or `ExternalsCoherence.committees_agree` at `v`'s own store, the weak proof
  calls the corresponding `_weak` / `_at_observer` / `_of_prefix` twin already
  proved in `WeakSelectorInversion.lean`, `WeakConfirmedDissemination.lean`,
  `WeakConfirmedSupporter.lean` and `WeakEconomicReadback.lean`, driven by
  `hW.coherence` instead;
* the two crossing-margin producers `crossingEdge_descendStep_of_selectedInputs_minimal`
  (`MinimalSelectedDomain.lean:1171`) and
  `futureCrossing_descendStep_of_selectedInputs_minimal` (`:1074`) turned out
  to have a **genuine** residual `hv : v ∈ E.honest` dependency in their
  *signatures* (routed through `CrossingCert.crossing_hd_of_preRegion` and
  `LastAlgebra.hR4b_of_confinement`, both of which read `v`'s committee via
  `ExternalsCoherence.committees_agree`) — contrary to what a first read of
  the docstrings suggests. Both of those, and the one additional crossing
  lemma with the same dependency
  (`CrossingCert.crossing_equivocation_score_split`), have exactly the same
  shape of fix as `WeakEconomicReadback.lean`'s six clones: replace
  `hec`/`hv`/`hnH` by a single `hcomm : E.PrefixCommitteeAgreement cfg ext
  (E.store cfg ext v n)`. Sections 1–3 below perform that same substitution
  one level up the call graph (through `CrossingCert`'s and
  `FutureCrossingMargin`'s endpoint-inequality assemblers) to reach the two
  producers themselves. This is flagged explicitly since it is additional
  cloning beyond what the task's ingredient list named.

Every other ingredient the strong proof needs — `store_parentSlotLt`,
`store_walkKnownK`, `latestMessageProvenance`, `store_anchor_min_slot`,
`store_anchor_block`, `store_storeLE`, `get_head_root_mem_or`,
`store_blocks_slot_le_current`, `registryConstant`,
`checkpoint_states_total_active_balance`,
`checkpoint_state_key_of_one_confirmed`, `crossing_hbase_of_confirmed_window`,
`crossing_hMU_of_canonicalPre`, `intraEpoch_adversarial_guard`,
`crossing_fullSpan_adversarial_guard`, `reanchored_endpoint_of_fullSpan_certificate`,
`Execution.honest_not_equivocating`, `sameEpoch_descendStep_of_selectedInputsAt_minimal`,
`directWindow_descendStep_of_selectedInputsAt_minimal` — is already proved
for an arbitrary (honest or not) node's store, so it is reused unchanged.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 0 — observer coherence and the weak observer-margin bundle -/

/-- The two store-level coherence facts an arbitrary (not necessarily honest)
observer's own store must still satisfy for the confirmed-margin machinery to
run: committee readback (feeding `PrefixCommitteeAgreement`, in place of
`ExternalsCoherence.committees_agree v hv …`) and justified-root knownness
(in place of `SelectedMarginDomain.justified_root_known v hv …`). Both are
facts about the observer's own trajectory, not about the observer's honesty;
an implementation that always computes committees from its own head state and
always keeps its own justified root in its block map satisfies them whether
or not the observer is Byzantine. -/
structure ObserverCoherence (obs : ValidatorIndex) : Prop where
  committees_agree : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s
  justified_root_known : ∀ n : ℕ, E.WithinHorizon cfg n →
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots

/-- **`ObserverCoherence.justified_root_known` is derivable, not an extra
assumption**, given accepted global justified-root origins
(`ExactPrefixAcceptedFFGSemantics`) and the ordinary execution trajectory
(`ScheduledPrefixTrajectoryAssumptions`). This is exactly
`AcceptedCurrentTargetLowerContracts.justifiedRootKnown_of_acceptedGlobalTrajectory`
restated at an arbitrary `obs` — that theorem's honesty premise `_hw : w ∈
E.honest` is already unused in its proof (every lemma it calls,
`store_storeLE`, `store_anchor_block`, `store_parentSlotLt`,
`store_walkKnownK`, `store_causal`, is proved for an arbitrary node), but the
premise is still a required explicit argument, so it cannot be *applied*
here without first producing a (nonexistent, since `obs` need not be honest)
membership proof. The body is therefore copied verbatim with the honesty
binder dropped, rather than routed through the original via `apply`.

This is the *supplier* of `ObserverCoherence.justified_root_known` everywhere
in the weak development: no statement that carries the accepted-FFG package
takes that fact as a premise. The caller-facing bundle
`WeakObserverAssumptions` carries only `committees_agree`, and the top-level
theorems — which all already carry `B`, `hT`, `hanchor`, `hboundary` —
promote it to the internal `WeakObserverMarginAssumptions` with
`WeakObserverAssumptions.toMarginAssumptions`, discharging
`justified_root_known` here. -/
theorem ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      (E.store cfg ext obs n).justified_checkpoint.root ∈
        (E.store cfg ext obs n).block_roots := by
  intro n _hHn
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
  have hanchorMem : B.anchor.root ∈
      (E.store cfg ext obs n).block_roots :=
    (E.store_storeLE cfg ext obs (Nat.zero_le n)).1 hanchorMem0
  have hanchorBlock :
      (E.store cfg ext obs n).blocks B.anchor.root = ablk.message := by
    rw [hanchorRoot]
    exact E.store_anchor_block cfg ext hT.wellFormed hgenEq obs n
      (hanchorRoot ▸ hanchorMem)
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg B.anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hstore : E.CausalStore cfg ext (E.store cfg ext obs n) :=
    E.store_causal cfg ext obs n
  have hparentSlots : ParentSlotLt (E.store cfg ext obs n) :=
    E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hT.wellFormed.anchor_parent_unscheduled obs n
  rcases B.globalJustified_anchor_or_AUEvidence hgenShort hanchor hstore with
    hjustAnchor | hevidence
  · rw [hjustAnchor]
    exact hanchorMem
  · obtain ⟨carrier⟩ := hevidence
    obtain ⟨hincluded⟩ := carrier.formed_evidence.certified
    have hcertified : CertifiedJustified cfg E B.anchor
        (E.store cfg ext obs n).justified_checkpoint :=
      IncludedCertifiedJustified.toCertifiedJustified
        (cfg := cfg)
        (Execution.AcceptedIncludedAttestationRelation.relation cfg ext E
          B.state.includedAttestations) hincluded
    have hanchorEpochLe : B.anchor.epoch ≤
        (E.store cfg ext obs n).justified_checkpoint.epoch :=
      CertifiedJustified.anchor_epoch_le (cfg := cfg) hcertified
    have hstartLe : compute_start_slot_at_epoch cfg B.anchor.epoch ≤
        compute_start_slot_at_epoch cfg
          (E.store cfg ext obs n).justified_checkpoint.epoch :=
      Nat.mul_le_mul_right cfg.slots_per_epoch hanchorEpochLe
    have hwalkAnchor : WalkKnown (E.store cfg ext obs n)
        ((E.store cfg ext obs n).blocks B.anchor.root).slot carrier.tip :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩ obs n
        B.anchor.root hanchorMem carrier.tip carrier.tip_carrier.known
    have hwalk : WalkKnown (E.store cfg ext obs n)
        (compute_start_slot_at_epoch cfg
          (E.store cfg ext obs n).justified_checkpoint.epoch) carrier.tip := by
      apply hwalkAnchor.mono
      rw [hanchorBlock]
      exact hboundary'.trans hstartLe
    exact carrier.checkpointRoot_known B.coherence hstore hparentSlots hwalk

/-- Given the accepted global justified-root origin, constructing
`ObserverCoherence` reduces to supplying `committees_agree` alone:
`justified_root_known` is always derivable
(`justified_root_known_of_acceptedGlobalTrajectory` above), so it is not an
independent premise on top of the accepted FFG semantics bundle. -/
def ObserverCoherence.of_acceptedTrajectory
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    (obs : ValidatorIndex)
    (hcomm : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
      E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s) :
    E.ObserverCoherence cfg ext obs where
  committees_agree := hcomm
  justified_root_known :=
    ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory
      cfg ext E B hT hanchor hboundary obs

/-- The **internal** assumption bundle the margin machinery runs on: the usual
`SelectedMarginAssumptions` and the observer's own store coherence. The
observer `obs` is completely arbitrary — it **may** be honest; the model simply
grants it nothing. (Non-honesty was never used by any proof, so it is not a
field: carrying it would only narrow the statements.)

This record is *not* the premise surface of the weak development's top-level
statements: `coherence.justified_root_known` is a derived fact, never a
caller-supplied one. Callers hand in `WeakObserverAssumptions` below, whose
only observer-store field is `committees_agree`, and every statement carrying
the accepted-FFG package (`B`, `hT`, `hanchor`, `hboundary`) — the folds, the
closed call theorems, and the finalized-base corollaries — builds this bundle
internally with `WeakObserverAssumptions.toMarginAssumptions`. Only the
`hmargin`/`hfilter`-carrying one-shot floor forms
(`weak_safeFrom_find_latest_confirmed_descendant`, `…_discharged` and their
endpoint forms), which carry no `B` at all and so have nothing to derive
`justified_root_known` from, still take this bundle directly. -/
structure WeakObserverMarginAssumptions (obs : ValidatorIndex) : Prop where
  base : SelectedMarginAssumptions cfg ext E
  coherence : E.ObserverCoherence cfg ext obs

/-- **The observer premise surface of the weak development.** Everything a
caller must supply about the observer `obs`, and nothing that is derivable:

* `base` — the ordinary (observer-independent) `SelectedMarginAssumptions`;
* `committees_agree` — the one genuinely free observer-store fact: the
  observer reads back the scheduled committees from its own store.

The observer `obs` is arbitrary and **may** be honest: the weak development's
point is that nothing is assumed *in the observer's favour* (no delivery, no
honest behaviour), not that the observer is dishonest. Non-honesty was never
used by any proof, so it is not a field — carrying it would only narrow every
weak statement.

`ObserverCoherence.justified_root_known` is deliberately absent: it is a
theorem about any node's trajectory
(`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`), and
every top-level weak statement carries the accepted-FFG/trajectory premises
that prove it, so it is derived rather than assumed. -/
structure WeakObserverAssumptions (obs : ValidatorIndex) : Prop where
  base : SelectedMarginAssumptions cfg ext E
  committees_agree : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s

/-- Promotion of the caller-facing premise bundle to the internal one: the
missing field, `ObserverCoherence.justified_root_known`, is *derived* from the
accepted global justified-root origin and the ordinary execution trajectory
via `ObserverCoherence.of_acceptedTrajectory`. Every top-level weak theorem
already carries `B`, `hT`, `hanchor`, `hboundary`, so this promotion is always
available there and `justified_root_known` never reaches a premise list. -/
def WeakObserverAssumptions.toMarginAssumptions {obs : ValidatorIndex}
    (hW : E.WeakObserverAssumptions cfg ext obs)
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor)) :
    E.WeakObserverMarginAssumptions cfg ext obs where
  base := hW.base
  coherence :=
    ObserverCoherence.of_acceptedTrajectory cfg ext E B hT hanchor hboundary obs
      hW.committees_agree

/-! ## Section 1 — the three `_of_prefix` crossing-arithmetic clones

`WeakEconomicReadback.lean` already supplies `support_discount_le_parent_stuck
_of_prefix` and `Execution.get_equivocation_score_eq_weight_of_prefix`
(`CurrentTargetPrefixAccounting.lean`). The three lemmas below thread those
through one more layer of the crossing-certificate call graph — exactly the
pattern `WeakConfirmedSupporter.honestSupporter_of_confirmed_known_at_observer`
already uses one layer down. -/

/-- `_of_prefix` clone of `CrossingCert.crossing_hd_of_preRegion`: the only use
of `hv : v ∈ E.honest` (via `hec`) fed `support_discount_le_parent_stuck`,
replaced here by its `_of_prefix` twin driven by `hcomm`. -/
private theorem crossing_hd_of_preRegion_of_prefix
    (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    (mid es : Slot) :
    get_support_discount cfg ext (E.store cfg ext v n) bs b
      ≤ E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
        + E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b mid es) := by
  have hd := support_discount_le_parent_stuck_of_prefix (b := b) cfg ext hbb hcomm hval
    hstartH hbH htab hne
  have hdiff :
      ParentStuck cfg E (E.store cfg ext v n) bs b \
          (ParentStuck cfg E (E.store cfg ext v n) bs b ∩ E.span_committee mid es)
        = ParentStuck cfg E (E.store cfg ext v n) bs b \ E.span_committee mid es := by
    ext i
    simp
  have hsplit := E.weight_add_sdiff
    (Finset.inter_subset_left :
      ParentStuck cfg E (E.store cfg ext v n) bs b ∩ E.span_committee mid es
        ⊆ ParentStuck cfg E (E.store cfg ext v n) bs b)
  rw [hdiff] at hsplit
  calc
    get_support_discount cfg ext (E.store cfg ext v n) bs b
        ≤ E.weight (ParentStuck cfg E (E.store cfg ext v n) bs b) := hd
    _ = E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b mid es) := by
            simpa only [crossingParentPre, crossingParentSub, add_comm] using hsplit.symm

/-- `_of_prefix` clone of `LastAlgebra.hR4b_of_confinement`: the only use of
`hv`/`hnH` (via `hec`) fed `get_equivocation_score_eq_weight`, replaced here by
`Execution.get_equivocation_score_eq_weight_of_prefix` driven by `hcomm`. -/
private theorem hR4b_of_confinement_of_prefix
    {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    (hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest)
    {sa es : Slot}
    (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es ≤ E.Bval sa es := by
  rw [byz_score_eq_weight cfg hval,
    E.get_equivocation_score_eq_weight_of_prefix cfg ext hcomm hval sa es hesH]
  simp only [Execution.Bval, Execution.Bwin]
  refine E.weight_add_le ?_ ?_ ?_
  · rw [Finset.disjoint_left]
    intro i hiBS hiEA
    simp only [List.mem_toFinset, List.mem_filter] at hiBS
    obtain ⟨lm, _, hnoteq, _⟩ := mem_AttSupporters cfg hiBS.1
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hiEA
    exact hnoteq hiEA.1.2
  · intro i hi
    simp only [List.mem_toFinset, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  · intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.1, hne i hi.1.2⟩

/-- `_of_prefix` clone of `CrossingCert.crossing_equivocation_score_split`: the
only use of `hv`/`hnH` (via `hec`) fed two `get_equivocation_score_eq_weight`
calls, replaced here by `Execution.get_equivocation_score_eq_weight_of_prefix`
driven by `hcomm`. -/
private theorem crossing_equivocation_score_split_of_prefix
    {v : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {sa mid es : Slot} (hsa : sa ≤ mid)
    (hesH : E.SlotWithinHorizon cfg es) :
    get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
        + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es)
      = get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es := by
  rw [E.get_equivocation_score_eq_weight_of_prefix cfg ext hcomm hval mid es hesH,
    E.get_equivocation_score_eq_weight_of_prefix cfg ext hcomm hval sa es hesH]
  have hsub : EquivActive cfg E (E.store cfg ext v n) bs mid es ⊆
      EquivActive cfg E (E.store cfg ext v n) bs sa es := by
    intro i hi
    simp only [EquivActive, Finset.mem_filter, Finset.mem_inter] at hi ⊢
    exact ⟨⟨span_committee_mono_lo hsa hi.1.1, hi.1.2⟩, hi.2⟩
  simpa only [crossingEquivPre] using E.weight_add_sdiff hsub

/-! ## Section 2 — the two `_of_prefix` endpoint-inequality assemblers

Verbatim clones of `FutureCrossingMargin.intraEpochFuture_endpoint_
inequality_of_confirmed_window` and `crossingEdgeFuture_endpoint_inequality_
of_confirmed_window`, with `hec`/`hv`/`hnH` replaced by `hcomm` and every
internal call to `crossing_hd_of_preRegion` / `hR4b_of_confinement` /
`crossing_equivocation_score_split` replaced by the Section 1 `_of_prefix`
twins. Every other line, including the `hne` derivation (which only needs
`Execution.honest_not_equivocating`, already honesty-free at an arbitrary
node — see `WeakEconomicReadback.lean`'s docstring), is unchanged. -/

/-- Local restatement of `FutureCrossingMargin.lean`'s file-private
`fullSpan_base_transport_arith` (pure `ℕ` arithmetic, no honesty content). -/
private theorem fullSpan_base_transport_arith_weak
    {sq se B d MU boost A : Nat}
    (hbase : 2 * sq + 2 * B + d ≥ MU + boost + 2 * A + 1)
    (hS : sq ≤ se) :
    2 * se + 2 * B + d ≥ MU + boost + 2 * A + 1 := by
  omega

/-- `_of_prefix` clone of `intraEpochFuture_endpoint_inequality_of_confirmed_window`. -/
theorem intraEpochFuture_endpoint_inequality_of_confirmed_window_of_prefix
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈
          (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
        (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hbcur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n))
    (hdom : E.WindowRecordedEpochMax cfg ext v n
      ((E.store cfg ext v n).blocks b).slot es)
    (hintra : get_block_epoch cfg (E.store cfg ext v n) b =
      get_block_epoch cfg (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).parent_root)
    (hesSigma : es ≤ sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} {m : ℕ}
    (hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSbase : E.Sval cfg ext v n b ((E.store cfg ext v n).blocks b).slot es ≤
      E.Sval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hHsub : E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b
        ((E.store cfg ext v n).blocks b).slot es) ≤
      E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
        ≤ E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma ≤
      E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.Xval cfg ext w m b mid sigma
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext v n).blocks
    ((E.store cfg ext v n).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext v n).blocks b).slot
  have hlo : lo ≤ mid := hslotlt
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hnH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext v n))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hmidH
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest :=
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost] at hbaseQ
  rw [← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith_weak hbaseQ hSbase
  have hMUQ := E.crossing_hMU_of_canonicalPre cfg ext hbb htab hes hslotlt hbcur
    hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext v n b mid es + E.Aval cfg ext v n b mid es
        + E.Xval cfg ext v n b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext v n b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hd := E.crossing_hd_of_preRegion_of_prefix (b := b) cfg ext hbb hcomm hval
    hloH hmidH htab hne mid es
  have hguard := E.intraEpoch_adversarial_guard cfg ext hbb htab hintra hes hmidH hesH
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := E.hR4b_of_confinement_of_prefix cfg ext hcomm hval hne hesH hspan
  have hbyzfull : E.Bval mid es ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [htab]
    exact hbb.span_bound mid es hmidH hesH
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es) + 0 + 0
        ≤ 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_zero] using hguard.1
  have hAguard : estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
          * cfg.confirmation_byzantine_threshold
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es + 0 := by
    simpa only [Nat.add_zero] using hguard.2
  have hend := E.reanchored_endpoint_of_fullSpan_certificate
    (v₀ := w) (n₀ := m) (b' := b) (lo := mid) (es := es) (σ := sigma)
    (Bsup := (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
      (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum)
    (eqSub := get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es)
    (eqExtra := 0) (HAextra := 0) (Bextra := 0)
    (A := get_adversarial_weight cfg ext (E.store cfg ext v n) bs b)
    (d := get_support_discount cfg ext (E.store cfg ext v n) bs b)
    (MU := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) lo es)
    (qFull := estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg bs) mid es / 100)
    (Hpre := E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es))
    (Hsub := E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b mid es))
    (xP := E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es))
    (Bpre := E.weight (E.crossingByzPre lo mid es))
    (boost := get_proposer_score cfg (E.store cfg ext w m))
    cfg ext hbb hesSigma hmidH hSigmaH hbase hMU hd hHsub hAguard hdomFull
      (Nat.zero_le _) (Nat.zero_le _) hbyzsub (by simpa using hbyzfull) hAX hxS
  simpa only [Nat.sub_zero] using hend

/-- `_of_prefix` clone of `crossingEdgeFuture_endpoint_inequality_of_confirmed_window`. -/
theorem crossingEdgeFuture_endpoint_inequality_of_confirmed_window_of_prefix
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext v n))
    (hwf : ParentSlotLt (E.store cfg ext v n))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
        (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root)
    {es sigma : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hslotlt : ((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot <
      ((E.store cfg ext v n).blocks b).slot)
    (hbcur : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n))
    (hdom : E.WindowRecordedEpochMax cfg ext v n
      ((E.store cfg ext v n).blocks b).slot es)
    (hcross : get_block_epoch cfg (E.store cfg ext v n) b >
      get_block_epoch cfg (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).parent_root)
    (hesSigma : es ≤ sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} {m : ℕ}
    (hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSbase : E.Sval cfg ext v n b ((E.store cfg ext v n).blocks b).slot es ≤
      E.Sval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hHsub : E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b
        ((E.store cfg ext v n).blocks b).slot es) ≤
      E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
        ≤ E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma ≤
      E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    let sa := compute_start_slot_at_epoch cfg
      (get_block_epoch cfg (E.store cfg ext v n) b)
    E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.Xval cfg ext w m b mid sigma
        + (E.weight (E.crossingByzPre lo mid es)
          - E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es))
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext v n).blocks
    ((E.store cfg ext v n).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext v n).blocks b).slot
  let sa := compute_start_slot_at_epoch cfg
    (get_block_epoch cfg (E.store cfg ext v n) b)
  have hlo : lo ≤ sa := parent_slot_succ_le_crossing_start (Root := Root) cfg hcross
  have hsa : sa ≤ mid := start_slot_at_block_epoch_le cfg (E.store cfg ext v n) b
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact E.slotWithinHorizon_of_le cfg (le_refl _) hnH
  have hesH : E.SlotWithinHorizon cfg es := by
    apply E.slotWithinHorizon_mono cfg (b := get_current_slot cfg (E.store cfg ext v n))
      (by rw [hes]; exact Nat.sub_le _ _)
    exact hcurH
  have hmidH : E.SlotWithinHorizon cfg mid :=
    E.slotWithinHorizon_mono cfg hbcur hcurH
  have hsaH : E.SlotWithinHorizon cfg sa :=
    E.slotWithinHorizon_mono cfg hsa hmidH
  have hloH : E.SlotWithinHorizon cfg lo :=
    E.slotWithinHorizon_mono cfg hlo hsaH
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices, i ∉ E.honest :=
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost, ← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith_weak hbaseQ hSbase
  have hMUQ := E.crossing_hMU_of_canonicalPre cfg ext hbb htab hes hslotlt hbcur
    hloH hesH
  dsimp only at hMUQ
  have hpart : E.Sval cfg ext v n b mid es + E.Aval cfg ext v n b mid es
        + E.Xval cfg ext v n b mid es =
      E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
        + E.Xval cfg ext w m b mid es := by
    calc
      _ = E.Jspec mid es := (E.weight_partition cfg ext v n b mid es).symm
      _ = _ := E.weight_partition cfg ext w m b mid es
  have hMU :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + (E.weight (E.crossingParentPre cfg (E.store cfg ext v n) bs b mid es)
          + E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
          + E.weight (E.crossingByzPre lo mid es))
        ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hd := E.crossing_hd_of_preRegion_of_prefix (b := b) cfg ext hbb hcomm hval
    hloH hmidH htab hne mid es
  have hguard := E.crossing_fullSpan_adversarial_guard cfg ext hbb htab hcross hes
    hsaH hesH
  have hBextra : E.weight (E.crossingByzPre sa mid es) ≤
      E.weight (E.crossingByzPre lo mid es) :=
    E.weight_mono (E.crossingByzPre_mono_lo hlo)
  have heqExtra :
      E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es) ≤
        E.weight (E.crossingByzPre sa mid es) :=
    E.weight_mono (E.crossing_equivPre_subset_byzPre cfg hne)
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := E.hR4b_of_confinement_of_prefix cfg ext hcomm hval hne hesH hspan
  have hbyzfull : E.Bval mid es + E.weight (E.crossingByzPre sa mid es) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [E.crossing_fullSpan_Bval_split hsa, htab]
    exact hbb.span_bound sa es hsaH hesH
  have heqsplit := E.crossing_equivocation_score_split_of_prefix (n := n) (es := es)
    cfg ext hcomm hval hsa hesH
  have hAguard : estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
          * cfg.confirmation_byzantine_threshold
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
        + get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
        + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es) := by
    calc
      _ ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
          + get_equivocation_score cfg ext (E.store cfg ext v n) bs sa es := hguard.2
      _ = get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
          + (get_equivocation_score cfg ext (E.store cfg ext v n) bs mid es
            + E.weight (E.crossingEquivPre cfg (E.store cfg ext v n) bs sa mid es)) := by
              rw [heqsplit]
      _ = _ := (Nat.add_assoc _ _ _).symm
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es)
        + E.weight (E.crossingHonestPre sa mid es)
        + E.weight (E.crossingByzPre sa mid es)
      ≤ 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_assoc] using
      (Eq.trans_le (E.crossing_fullSpan_mass_split hsa) hguard.1)
  exact E.reanchored_endpoint_of_fullSpan_certificate cfg ext hbb hesSigma hmidH hSigmaH
    hbase hMU hd hHsub hAguard hdomFull hBextra heqExtra hbyzsub hbyzfull hAX hxS

/-! ## Section 3 — the two `_at_observer` crossing-margin producers

Verbatim clones of `MinimalSelectedDomain.futureCrossing_descendStep_of_
selectedInputs_minimal` (`:1074`) and `crossingEdge_descendStep_of_
selectedInputs_minimal` (`:1171`), with `(v, hv : v ∈ E.honest)` replaced by
`(obs, hW : E.WeakObserverMarginAssumptions cfg ext obs)` and the single
internal call to the (honesty-dependent) endpoint-inequality assembler
replaced by its Section 2 `_of_prefix` twin, `hcomm` supplied by
`hW.coherence`. Every other line — including `E.registryConstant`,
`E.checkpoint_states_total_active_balance`, `E.checkpoint_state_key_of_one_
confirmed`, `E.store_parentSlotLt`, `E.latestMessageProvenance`,
`E.store_walkKnownK`, `E.store_blocks_slot_le_current`,
`E.hval_of_selectedMarginDomain` and `hA.domain.justified_checkpoint_cached`
(both read at the *endpoint* `w`, which stays honest, via `hW.base.domain`),
`E.classes_base_transport_honest`, `E.hgrowAX_of_committee_support`,
`E.hgrowX_of_committee_support`, `recorded_bside_ge`,
`E.crossing_ledger_descendStep` — is honesty-free already and hence
unchanged. -/

/-- `_at_observer` clone of `futureCrossing_descendStep_of_selectedInputs_minimal`. -/
theorem futureCrossing_descendStep_of_selectedInputs_at_observer
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    {glc a b : Root} {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.FutureCrossingSelectedMarginInputs cfg ext glc a b obs q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen obs q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hin.block_known
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hSbase := (E.classes_base_transport_honest cfg ext obs w q m b
    ((E.store cfg ext obs q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hend := E.intraEpochFuture_endpoint_inequality_of_confirmed_window_of_prefix cfg ext
    hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hqH hcomm
    hwf hval htab hprov hconf hwalk hin.cutoff_eq hslotlt hbcur
    hin.recorded_epoch_max hin.edge_same_epoch hin.es_le_sigma hin.sigma_horizon
    hboost hSbase (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hbside hend
    hin.sibling_score

/-- `_at_observer` clone of `crossingEdge_descendStep_of_selectedInputs_minimal`. -/
theorem crossingEdge_descendStep_of_selectedInputs_at_observer
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    {glc a b : Root} {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.CrossingEdgeSelectedMarginInputs cfg ext glc a b obs q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext obs q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext obs q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext obs q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen obs q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      obs q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence obs q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen obs q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen obs q
  rw [← E.store_current_slot cfg ext obs q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ obs q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext obs q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext obs q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext obs q) ((E.store cfg ext obs q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot <
      ((E.store cfg ext obs q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext obs q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ obs q b hin.block_known
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hSbase := (E.classes_base_transport_honest cfg ext obs w q m b
    ((E.store cfg ext obs q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext obs q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hend := E.crossingEdgeFuture_endpoint_inequality_of_confirmed_window_of_prefix cfg ext
    hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hqH hcomm
    hwf hval htab hprov hconf hwalk hin.cutoff_eq hslotlt hbcur
    hin.recorded_epoch_max hin.edge_crosses hin.es_le_sigma hin.sigma_horizon
    hboost hSbase (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hbside hend
    hin.sibling_score

/-! ## Section 4 — the weak-observer covered chain-supply

Clone of `CoveredMargin.coveredDescendStepChainSupply_of_selectedMarginsAt_
minimal` (`:287`), over `(obs, hW)`. Unlike Sections 5–6 below, this lemma
never mentions the selector function at all — it turns an already-selected
candidate `glc` into the coverage-aware chain functional — so no selector
substitution is needed here, only the observer substitution: `confirmed_
known_at_all_honest_endpoints_minimal` becomes `_at_observer` (`hcomm` from
`hW.coherence`), and the two crossing-margin branches become the Section 3
`_at_observer` producers. The `sameEpoch` and `directWindow` branches are
already honesty-free and are reused verbatim with `v := obs`. -/

theorem coveredDescendStepChainSupply_of_selectedMarginsAt_weak
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    {glc r₀ : Root} {q : ℕ}
    (hqH : E.WithinHorizon cfg q) (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext obs q)
    (hglc : glc ∈ (E.store cfg ext obs q).block_roots)
    (hparent : ((E.store cfg ext obs q).blocks glc).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hconf : is_one_confirmed cfg ext query.store
      (get_current_balance_source query) glc = true)
    (hsupply : E.SelectedCoveredMarginSupplyAt cfg ext glc r₀ obs q query) :
    E.CoveredDescendStepChainSupply cfg ext glc r₀
      (E.slot_start cfg (E.slot_at cfg q)) := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  obtain ⟨_hsq, _hsH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  intro w hw m hm hHm hIH a c ha hc hlink hscope hscopeR₀ hcne
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotStart]
    exact E.slot_at_mono cfg hm
  have hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots := by
    intro w' hw' m' hm' hHm'
    have hslotQM' : E.slot_at cfg q ≤ E.slot_at cfg m' := by
      rw [← hslotStart]
      exact E.slot_at_mono cfg hm'
    exact E.confirmed_known_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hstore glc hqH hglc hparent hconf
      w' hw' m' hslotQM' hHm'
  rcases hsupply w hw m hslotQM hHm hIH
      a c ha hc hlink hscope hscopeR₀ hcne with hcovered | hmargin
  · exact Or.inl hcovered
  · right
    rcases hmargin with
      ⟨lo, es, σ, hsame⟩ | ⟨es, σ, querySlot, hcross⟩ |
        ⟨es, σ, querySlot, hfuture⟩ | ⟨lo, es, hdirect⟩
    · exact E.sameEpoch_descendStep_of_selectedInputsAt_minimal cfg ext hA
        hw hHm hc hscope hglcKnown hIH hsame
    · exact E.crossingEdge_descendStep_of_selectedInputs_at_observer cfg ext hW
        hqH hw hHm hcross
    · exact E.futureCrossing_descendStep_of_selectedInputs_at_observer cfg ext hW
        hqH hw hHm hfuture
    · exact E.directWindow_descendStep_of_selectedInputsAt_minimal cfg ext hdirect

/-! ## Section 5 — the weak-observer slot-start bridge

Clone of `CoveredMargin.safeFrom_find_latest_confirmed_descendant_covered_at_
slotStart_minimal` (`:333`), over `Weak.find_latest_confirmed_descendant` and
`(obs, hW)`. The selector inversion call becomes `WeakSelectorInversion
.find_latest_confirmed_descendant_selected_minimal_weak`, whose two-way
conclusion (unchanged / confirmed-with-guard-evidence) is first stripped down
to the same two-way shape the strong original's `rcases` consumes (`hkey`
below) — the weak witness and guard-evidence disjunct are never needed
downstream, only the strong `is_one_confirmed` witness and membership facts,
per the module's own docstring. The two `store_domainK_of_selectedMarginDomain`
uses at the *observer* `(obs, q)` are inlined by hand, since that helper's
third component is exactly `SelectedMarginDomain.justified_root_known`, which
`hW.coherence.justified_root_known` replaces directly; the two uses at the
*endpoint* `(w, m)` (still honest) are untouched, reusing `hA.domain`. The
anchoring fact `find_latest_confirmed_descendant_ge` becomes `WeakSelectorInversion
.weak_find_latest_confirmed_descendant_ge`, and `confirmed_ancestry_at_all_
honest_endpoints_minimal` becomes `WeakConfirmedDissemination.confirmed_
ancestry_at_all_honest_endpoints_at_observer` (`hcomm` from `hW.coherence`).
`head_ge_of_safe_covered_terminal` (`CoveredMargin.lean`) needs no honesty and
is reused unchanged. -/

theorem safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak
    {obs : ValidatorIndex} (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (q : ℕ)
    (hqH : E.WithinHorizon cfg q)
    (query : FastConfirmationStore Root)
    (hstore : query.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ query.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr
      (E.slot_start cfg (E.slot_at cfg q)))
    (hchain :
      Weak.find_latest_confirmed_descendant cfg ext query lcr ≠ lcr →
        E.CoveredDescendStepChainSupply cfg ext
          (Weak.find_latest_confirmed_descendant cfg ext query lcr) lcr
          (E.slot_start cfg (E.slot_at cfg q))) :
    E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext query lcr)
      (E.slot_start cfg (E.slot_at cfg q)) := by
  have hA := hW.base
  have hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs q) :=
    hW.coherence.committees_agree q hqH
  have hjrk : (E.store cfg ext obs q).justified_checkpoint.root ∈
      (E.store cfg ext obs q).block_roots :=
    hW.coherence.justified_root_known q hqH
  by_cases hsame : Weak.find_latest_confirmed_descendant cfg ext query lcr = lcr
  · rw [hsame]
    exact hbase
  have hkey : Weak.find_latest_confirmed_descendant cfg ext query lcr = lcr ∨
      (is_one_confirmed cfg ext query.store (get_current_balance_source query)
          (Weak.find_latest_confirmed_descendant cfg ext query lcr) = true ∧
        Weak.find_latest_confirmed_descendant cfg ext query lcr ∈
          query.store.block_roots ∧
        (query.store.blocks
            (Weak.find_latest_confirmed_descendant cfg ext query lcr)).parent_root ∈
          query.store.block_roots) := by
    rcases E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext hA
        obs q hqH hjrk query hstore lcr hlcr with
      heq | ⟨hc, _hwc, hb, hp, _hguard⟩
    · exact Or.inl heq
    · exact Or.inr ⟨hc, hb, hp⟩
  rcases hkey with heq | ⟨hconf, hbSelected, hpSelected⟩
  · exact absurd heq hsame
  have hbConfirm : Weak.find_latest_confirmed_descendant cfg ext query lcr ∈
      (E.store cfg ext obs q).block_roots := by
    simpa only [hstore] using hbSelected
  have hpConfirm : ((E.store cfg ext obs q).blocks
        (Weak.find_latest_confirmed_descendant cfg ext query lcr)).parent_root ∈
      (E.store cfg ext obs q).block_roots := by
    simpa only [hstore] using hpSelected
  have hlcrConfirm : lcr ∈ (E.store cfg ext obs q).block_roots := by
    simpa only [hstore] using hlcr
  have hsupply := hchain hsame
  obtain ⟨_hsq, _hsH, hslotStart, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  refine E.safeFrom_of_headStep_at cfg ext ?_
  intro w hw m hm hHm hIH
  have hwfConfirm : ParentSlotLt (E.store cfg ext obs q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hA.genesis
      hA.wellFormed.anchor_parent_unscheduled obs q
  have hwalkConfirm := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hA.genesis obs q
  have hheadConfirm : (get_head cfg (E.store cfg ext obs q)).root ∈
      (E.store cfg ext obs q).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext obs q) with h | h
    · exact h
    · rw [h]
      exact hjrk
  have hbgeConfirm : is_ancestor (E.store cfg ext obs q)
      (get_node_for_root
        (Weak.find_latest_confirmed_descendant cfg ext query lcr))
      (get_node_for_root lcr) = true := by
    have hge := (weak_find_latest_confirmed_descendant_ge cfg ext query
      (by simpa only [hstore] using hwfConfirm)
      (by simpa only [hstore] using hwalkConfirm)
      (by simpa only [hstore] using hheadConfirm) lcr hlcr).1
    simpa only [hstore] using hge
  have hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m := by
    rw [← hslotStart]
    exact E.slot_at_mono cfg hm
  obtain ⟨hlcrEndpoint, hbEndpoint, hbgeEndpoint⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints_at_observer cfg ext hA
      obs q hcomm query hstore _ lcr hqH hbConfirm hpConfirm hlcrConfirm
        hbgeConfirm hconf w hw m hslotQM hHm
  have hheadLcr : is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m)) (get_node_for_root lcr) = true :=
    hbase w hw m hm hHm
  obtain ⟨hwfEndpoint, hwalkEndpoint, hjcEndpoint⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  exact head_ge_of_safe_covered_terminal cfg hwfEndpoint
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjcEndpoint)
    hwalkEndpoint hjcEndpoint hlcrEndpoint hbEndpoint hheadLcr hbgeEndpoint
    (fun a c ha hc hlink hbc hclcr hcne =>
      hsupply w hw m hm hHm hIH a c ha hc hlink hbc hclcr hcne)

/-! ## Section 6 — the one-shot weak safety theorem

Clone of `CoveredMargin.safeFrom_find_latest_confirmed_descendant_of_
selectedCoveredMarginsAt_minimal` (`:408`), over `Weak.find_latest_confirmed_
descendant` and `(obs, hW)`. The inner selector-inversion call again produces
its two-way disjunction, stripped to the shape needed exactly as in
Section 5. -/

/-- **The one-shot weak safety theorem.** The weak selector's output, read at
an arbitrary (not necessarily honest) observer's own store, is `SafeFrom` at
the actual query second — matching the strong original's exact hypothesis
list (`SafeFrom` base at the slot boundary, `SelectedCoveredMarginSupplyAt`
margin supply) with `(v, hv : v ∈ E.honest)` replaced everywhere by
`(obs, hW : E.WeakObserverMarginAssumptions cfg ext obs)`. No further
hypothesis is added or dropped relative to `:408`. -/
theorem weak_safeFrom_find_latest_confirmed_descendant
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hmargin : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
        E.SelectedCoveredMarginSupplyAt cfg ext
          (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
          fcr_store) :
    E.SafeFrom cfg ext (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) q := by
  have hA := hW.base
  have hjrk : (E.store cfg ext obs q).justified_checkpoint.root ∈
      (E.store cfg ext obs q).block_roots :=
    hW.coherence.justified_root_known q hqH
  have hslotSafety : E.SafeFrom cfg ext
      (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)
      (E.slot_start cfg (E.slot_at cfg q)) :=
    E.safeFrom_find_latest_confirmed_descendant_covered_at_slotStart_weak
      cfg ext hW q hqH fcr_store hstore lcr hlcr hbase (by
        intro hne
        have hkey : is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store)
            (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) = true ∧
          Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
            fcr_store.store.block_roots ∧
          (fcr_store.store.blocks
              (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)).parent_root ∈
            fcr_store.store.block_roots := by
          rcases E.find_latest_confirmed_descendant_selected_minimal_weak cfg ext hA
              obs q hqH hjrk fcr_store hstore lcr hlcr with
            heq | ⟨hc, _hwc, hb, hp, _hguard⟩
          · exact absurd heq hne
          · exact ⟨hc, hb, hp⟩
        obtain ⟨hconf, hb, hp⟩ := hkey
        have hb' : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ∈
            (E.store cfg ext obs q).block_roots := by
          simpa only [hstore] using hb
        have hp' : ((E.store cfg ext obs q).blocks
              (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr)).parent_root ∈
            (E.store cfg ext obs q).block_roots := by
          simpa only [hstore] using hp
        exact E.coveredDescendStepChainSupply_of_selectedMarginsAt_weak
          cfg ext hW hqH fcr_store hstore hb' hp' hconf (hmargin hne))
  obtain ⟨hstart, _hstartH, _hslot, _hgate⟩ :=
    E.query_slot_start_facts_minimal cfg ext hA q hqH
  exact hslotSafety.mono cfg ext E hstart

/-! ## Section 7 — endpoint corollary

Unfolds `SafeFrom` (`L4Fold.lean:60`) at the actual query second, matching the
pattern of existing endpoint corollaries such as `confirmed_head_of_
acceptedActualFCRFold_nextSlot` (`AcceptedActualFCRNextSlotSafetyFold.lean`). -/

/-- Endpoint form of the one-shot weak safety theorem: the weak selector's
output, read at an arbitrary (not necessarily honest) observer's store, is
canonical at every honest endpoint at or after the query second. -/
theorem weak_confirmed_head
    {E : Execution Root} {obs : ValidatorIndex}
    (hW : E.WeakObserverMarginAssumptions cfg ext obs)
    (q : ℕ) (hqH : E.WithinHorizon cfg q)
    (fcr_store : FastConfirmationStore Root)
    (hstore : fcr_store.store = E.store cfg ext obs q)
    (lcr : Root) (hlcr : lcr ∈ fcr_store.store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (E.slot_start cfg (E.slot_at cfg q)))
    (hmargin : Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr ≠ lcr →
        E.SelectedCoveredMarginSupplyAt cfg ext
          (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr) lcr obs q
          fcr_store)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hqm : q ≤ m) (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (Weak.find_latest_confirmed_descendant cfg ext fcr_store lcr))
      = true :=
  weak_safeFrom_find_latest_confirmed_descendant cfg ext hW q hqH fcr_store hstore
    lcr hlcr hbase hmargin w hw m hqm hHm

end Execution

end FastConfirmation.Spec
