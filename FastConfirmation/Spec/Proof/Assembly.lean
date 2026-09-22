module
public import FastConfirmation.Spec.Proof.Dominance
public import FastConfirmation.Spec.Proof.Bridge
public import FastConfirmation.Spec.Proof.Engine
public import FastConfirmation.Spec.Proof.Registry
public import FastConfirmation.Spec.Proof.EdgeDynamics
public import FastConfirmation.Spec.Proof.Endpoint

@[expose] public section

/-!
# Spec / Proof / Assembly: the `descendStep_of_confirmMargin` input assembly

`Dominance.descendStep_of_confirmMargin` is the per-fork `DescendStep`
producer from the **plain** confirm-margin strip (no arms disjunction, no
min-reserve `INVstar`, no `hBb`). Its inputs, per confirmed-chain edge:

* `hstrip0` — the confirm-margin strip at the confirming anchor
  (`Bridge.weak_base_discharged`), in the exact `descendStep` shape (boost
  reconciled from `compute_proposer_score cfg bs` to
  `get_proposer_score cfg (store w m)`);
* `hgrowS`/`hgrowX`/`hbudget` — the three aggregate growth facts over `[es, σ]`;
* `hSt`/`hAt` — the `es`-vote transports `(v₀, n₀) → (w, m)` in the
  `SupportsDesc`/`AncestorOrVoteless` shapes (`EdgeDynamics.htS_of_walk` /
  `htA_of_walk` instantiated);
* `hchild`/`hbside`/`hsib` — the endpoint fork data.

The remaining engine assumptions are bundled as an explicit `Prop`.

## Section 0 — the boost reconciliation (hstrip0's boost half)

`weak_base_discharged` produces the strip at boost `compute_proposer_score cfg bs`
(`bs` = the confirming anchor's balance source, registry-constant). The
`descendStep` interface fixes boost = `get_proposer_score cfg (store w m)` (the
endpoint's justified proposer score). These agree by `compute_proposer_score`
congruence: both balance sources carry `validators = E.registry` (`hval` and
`EdgeDynamics.hval_of_interface`) with activity constant across epochs
(`StaticValidatorSet.registry_activity_constant`).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

/-- **Boost reconciliation.** A registry-constant balance source `bs` and the
endpoint's justified proposer-boost state agree on `compute_proposer_score`; hence
`compute_proposer_score cfg bs = get_proposer_score cfg (store w m)`. This turns
`Bridge.weak_base_discharged`'s boost into the `descendStep_of_confirmMargin`
interface boost. -/
theorem boost_reconcile (hsv : StaticValidatorSet cfg E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hji : JustificationInterface cfg ext E)
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hHm : E.WithinHorizon cfg m) :
    get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon →
    compute_proposer_score cfg bs = get_proposer_score cfg (E.store cfg ext w m) := by
  intro hEstH
  have hEst : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_interface cfg ext hec hgen hji w hw m hHm
  simp only [get_proposer_score]
  refine compute_proposer_score_congr cfg (hval.trans hEst.symm) ?_
  intro i
  rw [hval, hEst]
  exact hsv.registry_activity_constant i _ _ hbsH hEstH

/-! ## Section 1 — `hstrip0` in the `descendStep_of_confirmMargin` shape

`Bridge.weak_base_discharged` produces the confirm-margin strip at the confirming
anchor `(v₀, n₀)` with boost `compute_proposer_score cfg bs`; `boost_reconcile`
rewrites it to the interface boost `get_proposer_score cfg (store w m)`. The strip's
own inputs — the standard assumption package, the confirmation fact `hconf`, the
three chain-geometry facts about `b'` (`hslotlt`/`hb'cur`/`hb'anc`), the walk-domain
condition `hwalk`, and the ubiquity domination `hdom` (`RecordedEpochMax`) — are the
L4-fold / shell supplies, threaded verbatim. -/

/-- **`hstrip0`, assembled.** The plain confirm-margin strip at the confirming anchor
`(v₀, n₀)` over `[lo, es]`, in the exact shape `descendStep_of_confirmMargin` consumes
(boost = `get_proposer_score cfg (store w m)`). `Bridge.weak_base_discharged` supplies
the strip at boost `compute_proposer_score cfg bs`; `boost_reconcile` reconciles the
boost to the endpoint's proposer score. **No** arms disjunction, **no** min-reserve
`INVstar`. -/
theorem hstrip0_of_confirmed
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E) (hsv : StaticValidatorSet cfg E)
    (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv : v₀ ∈ E.honest) {n₀ : ℕ}
    (hn₀H : E.WithinHorizon cfg n₀)
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈ (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    {bs : BeaconState Root} {b' : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v₀ n₀) bs b' = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    (hslotlt : ((E.store cfg ext v₀ n₀).blocks
        ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot <
      ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hb'cur : ((E.store cfg ext v₀ n₀).blocks b').slot ≤
      get_current_slot cfg (E.store cfg ext v₀ n₀))
    (hb'anc : is_ancestor (E.store cfg ext v₀ n₀) (get_node_for_root b')
      (get_node_for_root ((E.store cfg ext v₀ n₀).blocks b').parent_root) = true)
    (hdom : E.RecordedEpochMax cfg ext v₀ n₀ es)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ) (hHm : E.WithinHorizon cfg m) :
    get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon →
    E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es := by
  intro hEstH
  have hstrip := E.weak_base_discharged cfg ext hhb hec hbb hgen hv hn₀H hwf hbH
    hval htab hprov hconf hwalk lo es hlo hes hloH hesH hslotlt hb'cur hb'anc hdom
  rwa [E.boost_reconcile cfg ext hsv hec hgen hji hval hbsH hw m hHm hEstH] at hstrip

/-! ## Section 2 — the `es`-vote transports `hSt` / `hAt`

`descendStep_of_confirmMargin` moves the honest `Sclass`/`Aclass` classes from the
confirming anchor `(v₀, n₀)` to the endpoint `(w, m)` through the two vote-class
transports. Both `SupportsDesc` and `AncestorOrVoteless` carry a single
store-dependent conjunct — an `is_ancestor` fact at `(v₀, n₀)` — with the vote
witnesses `(t, k, a)` store-independent. So the transports unpack the class,
move the `is_ancestor` fact by `EdgeDynamics.htS_of_walk` / `htA_of_walk` (block
relay containment + the per-root `WalkKnown` domain functions), and re-pack. The
block relay containment `hsub` is `EdgeDynamics.blockRoots_subset_of_relay` (from
`Synchrony.block_relay`); the walk-domain functions `hdomS`/`hdomA` are the
per-root residuals the shell supplies. -/

/-- **`hSt`, assembled.** The `SupportsDesc` (honest `b'`-support) class transports
`(v₀, n₀) → (w, m)`: unpack the vote witnesses (store-independent) and move the
`bbr ⪯ b'` fact with `EdgeDynamics.htS_of_walk`. Exactly `descendStep_of_confirmMargin`'s
`hSt` argument. -/
theorem hSt_of_walk (hwf : WellFormedExecution E)
    {v₀ w : ValidatorIndex} {n₀ m : ℕ} {b' : Root} {es : Slot}
    (hsub : (E.store cfg ext v₀ n₀).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb' : b' ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hdomS : ∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root r) (get_node_for_root b') = true →
      r ∈ (E.store cfg ext v₀ n₀).block_roots ∧
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot r) :
    ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i := by
  intro i hi
  obtain ⟨t, k, a, hle, hvote, hno, hanc⟩ := hi
  exact ⟨t, k, a, hle, hvote, hno,
    E.htS_of_walk cfg ext hwf hsub hb' hdomS _ hanc⟩

/-- **`hAt`, assembled.** The `AncestorOrVoteless` (backs-no-sibling) class
transports `(v₀, n₀) → (w, m)`: the voteless disjunct is store-independent; the
ancestor-voting disjunct unpacks the vote witnesses and moves the `b' ⪯ bbr` fact
with `EdgeDynamics.htA_of_walk`. Exactly `descendStep_of_confirmMargin`'s `hAt`
argument. -/
theorem hAt_of_walk (hwf : WellFormedExecution E)
    {v₀ w : ValidatorIndex} {n₀ m : ℕ} {b' : Root} {es : Slot}
    (hsub : (E.store cfg ext v₀ n₀).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb' : b' ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hdomA : ∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root b') (get_node_for_root r) = true →
      r ∈ (E.store cfg ext v₀ n₀).block_roots ∧
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks r).slot b') :
    ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i := by
  intro i hi
  rcases hi with hvoteless | ⟨t, k, a, hle, hvote, hno, hanc⟩
  · exact Or.inl hvoteless
  · exact Or.inr ⟨t, k, a, hle, hvote, hno,
      E.htA_of_walk cfg ext hwf hsub hb' hdomA _ hanc⟩

/-! ## Section 3 — the endpoint fork data `hbside` / `hsib`

`hbside` is `Endpoint.recorded_bside_ge` at the endpoint store with the justified
balance source (registry-constant by `hval_of_interface`); its `hSmem` — every
`Sclass` member records a `c`-supporting message that lands it in `AttSupporters` —
is the `hrec`-family recorded-support transport (`Cruxes.hrec_crux` +
`EngineTransport.HS0_in_AttSupporters`), taken as a residual. `hsib` is
`Endpoint.recorded_sibling_le` per competing sibling; its two confinements — honest
sibling supporters `⊆ Xclass` (`Confinement`), byz sibling supporters `⊆ Bwin`
(`ByzVpre`) — are taken as residuals. -/

/-- **The per-fork `DescendStep`, assembled from the enumerated residuals.** Wires the
mechanizable inputs into `Dominance.descendStep_of_confirmMargin`:

* `hSt`/`hAt` from the transport sub-inputs (`hwf`/`hsub`/`hb'`/`hdomS`/`hdomA`) via
  `hSt_of_walk`/`hAt_of_walk`;
* `hbside` from `Endpoint.recorded_bside_ge` (`hval` via `hval_of_interface`, `hSmem`
  the recorded-support transport residual);
* `hsib` from `Endpoint.recorded_sibling_le` per sibling (`hHon`/`hByz` the sibling
  confinement residuals).

The genuinely-open engine residuals stay as explicit hypotheses: `hstrip0` (the
confirm-margin strip, assembled by `hstrip0_of_confirmed`), the three growth facts
`hgrowS`/`hgrowX`/`hbudget`, the child membership `hchild`, the walk-domain functions
`hdomS`/`hdomA`, the recorded-support transport `hSmem`, and the sibling confinements
`hHon`/`hByz`. -/
theorem descendStep_of_assemblyResidual
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hji : JustificationInterface cfg ext E) (hwf : WellFormedExecution E)
    {v₀ w : ValidatorIndex} {n₀ : ℕ} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    {b' h c : Root} {lo es σ : Slot}
    (hsub : (E.store cfg ext v₀ n₀).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb' : b' ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hdomS : ∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root r) (get_node_for_root b') = true →
      r ∈ (E.store cfg ext v₀ n₀).block_roots ∧
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot r)
    (hdomA : ∀ r : Root, is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root b') (get_node_for_root r) = true →
      r ∈ (E.store cfg ext v₀ n₀).block_roots ∧
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks r).slot b')
    (hstrip0 : E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hgrowS : E.Sval cfg ext w m b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b' lo σ)
    (hgrowX : E.Xval cfg ext w m b' lo σ ≤ E.Xval cfg ext w m b' lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
      ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es))
    (hchild : ForkChoiceNode.mk c ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h))
    (hSmem : ∀ i ∈ E.Sclass cfg ext w m b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint))
    (hHon : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∈ E.honest → i ∈ E.Xclass cfg ext w m b' lo σ)
    (hByz : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
      c' ≠ c →
      ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
        i ∉ E.honest → i ∈ E.Bwin lo σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h c := by
  have hval_end : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_interface cfg ext hec hgen hji w hw m hHm
  refine E.descendStep_of_confirmMargin cfg ext v₀ w n₀ m lo es σ
    (fun i _ _ => E.hSt_of_walk cfg ext hwf hsub hb' hdomS i)
    (fun i _ _ => E.hAt_of_walk cfg ext hwf hsub hb' hdomA i)
    hstrip0 hgrowS hgrowX hbudget hchild
    (recorded_bside_ge cfg ext hval_end hSmem)
    (fun c' hc' hne => recorded_sibling_le cfg ext hval_end
      (hHon c' hc' hne) (hByz c' hc' hne))

end Execution

end FastConfirmation.Spec

end
