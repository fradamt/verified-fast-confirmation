module
public import FastConfirmation.Spec.Proof.HeadSafetyEngine
public import FastConfirmation.Spec.Proof.DynamicsClosure
public import FastConfirmation.Spec.Proof.CrossingCert
public import FastConfirmation.Spec.Proof.CrossEpochDynamics

@[expose] public section

/-!
# Spec / Proof / FutureCrossingMargin: intra-edge future-crossing margins

The edge and its later contest window have three relevant geometric regimes.
This module treats the case where:

* the selected edge itself stays in one epoch; but
* the later contest window `[lo, sigma]` crosses an epoch boundary.

The producer below uses only the sound part of the v2 ledger route.  In
particular it:

* starts `INV2` directly at the consuming endpoint, so it never assumes the
  false cross-store movement `BbadVal(endpoint) <= BbadVal(query)`;
* iterates the checked `INV2_step` / saturation composition;
* exposes the exact cross-epoch migration partition needed by that step;
* names the direct bounded committee-support input required when the
  confirmation query is made after some current-slot validators have already
  voted.

Two small arithmetic witnesses at the end show why the two exposed inputs
cannot be replaced by weaker shortcuts. Selective Byzantine
delivery can change `BbadVal` while leaving the honest class movements fixed,
and an already-supporting honest recurrer contributes to the next slot's
committee without funding any of `Unrec`, `X -> S`, `A -> S`, or fresh window
growth.  The latter is the precise `rho` obstruction to deriving the pre-step
functional from `committee_assignment_unique` alone across an epoch seam.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## 1. Exhaustive edge/window geometry -/

/-- The three mutually covering geometric cases for a real selected edge and
its later contest window.  The third constructor covers an intra-epoch edge
whose later contest window crosses an epoch boundary. -/
inductive SelectedEdgeWindowRegime
    (parentSlot childSlot lo sigma : Slot) : Prop where
  | sameWindow
      (h : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg sigma) :
      SelectedEdgeWindowRegime parentSlot childSlot lo sigma
  | edgeCrossing
      (h : compute_epoch_at_slot cfg parentSlot <
        compute_epoch_at_slot cfg childSlot) :
      SelectedEdgeWindowRegime parentSlot childSlot lo sigma
  | intraEdgeFutureCrossing
      (hedge : compute_epoch_at_slot cfg parentSlot =
        compute_epoch_at_slot cfg childSlot)
      (hwindow : compute_epoch_at_slot cfg lo <
        compute_epoch_at_slot cfg sigma) :
      SelectedEdgeWindowRegime parentSlot childSlot lo sigma

omit [LinearOrder Root] [Inhabited Root] in
/-- A real parent edge (`parentSlot < childSlot`) and an ordered contest window
(`lo <= sigma`) always lie in exactly one of the three covering cases above.
No protocol or accounting premise is used. -/
theorem selectedEdgeWindowRegime_exhaustive
    {parentSlot childSlot lo sigma : Slot}
    (hedge : parentSlot < childSlot) (hwindow : lo <= sigma) :
    SelectedEdgeWindowRegime cfg parentSlot childSlot lo sigma := by
  by_cases hsame : compute_epoch_at_slot cfg lo = compute_epoch_at_slot cfg sigma
  · exact .sameWindow hsame
  · have hedge_le : compute_epoch_at_slot cfg parentSlot <=
        compute_epoch_at_slot cfg childSlot :=
      Nat.div_le_div_right (Nat.le_of_lt hedge)
    have hwindow_le : compute_epoch_at_slot cfg lo <=
        compute_epoch_at_slot cfg sigma :=
      Nat.div_le_div_right hwindow
    rcases lt_or_eq_of_le hedge_le with hcross | hintra
    · exact .edgeCrossing hcross
    · exact .intraEdgeFutureCrossing hintra (lt_of_le_of_ne hwindow_le hsame)

namespace Execution

variable (E : Execution Root)

/-! ## 2. A sound endpoint base with an explicit tax-arm premise -/

/-- The tax arm of the confirmed-instance base at an anchor. -/
def ConfirmTaxArm (v : ValidatorIndex) (q : Nat) (b : Root)
    (lo es : Slot) (boost : Nat) : Prop :=
  E.Xval cfg ext v q b lo es + E.BbadVal cfg ext v q b lo es + (boost + 1)
      + cfg.confirmation_byzantine_threshold * E.Sval cfg ext v q b lo es /
          (100 - cfg.confirmation_byzantine_threshold)
    <= E.Sval cfg ext v q b lo es

/-- The member-cap arm of the confirmed-instance base at an anchor.  This arm
is store-independent apart from the two honest classes and therefore does
transport using only `S` growth and `X` shrinkage. -/
def ConfirmMemberArm (v : ValidatorIndex) (q : Nat) (b : Root)
    (lo es : Slot) (boost : Nat) : Prop :=
  E.Xval cfg ext v q b lo es + (boost + 1)
      + cfg.confirmation_byzantine_threshold * E.Jspec lo es /
          (100 - cfg.confirmation_byzantine_threshold)
    <= E.Sval cfg ext v q b lo es

/-- Actual `is_one_confirmed` must produce one of the two floored base arms.
The existing `Arms.arms_of_confirmed` / `EconomicCore` accounting pipeline has
this shape; keeping it as a function of the concrete Boolean fact prevents an
unrelated arm certificate from being substituted for the queried block. -/
def ConfirmedArmSupply (queryStore : Store Root) (bs : BeaconState Root)
    (b : Root) (v : ValidatorIndex) (q : Nat) (lo es : Slot) (boost : Nat) : Prop :=
  is_one_confirmed cfg ext queryStore bs b = true ->
    E.ConfirmTaxArm cfg ext v q b lo es boost \/
      E.ConfirmMemberArm cfg ext v q b lo es boost

omit [LinearOrder Root] [Inhabited Root] in
private theorem member_arm_transport_arith
    {Xq Xe Sq Se reserve boost : Nat}
    (harm : Xq + (boost + 1) + reserve <= Sq)
    (hS : Sq <= Se) (hX : Xe <= Xq) :
    Xe + (boost + 1) + reserve <= Se := by
  omega

/-- Build `INV2(es)` directly at the consuming endpoint.

The member arm transports from the query anchor with only the two honest class
movements.  For the tax arm, the caller supplies the exact endpoint tax arm.
This is intentionally narrower than `hBb`: it is required only if the concrete
confirmation actually lands in the tax branch, and it does not assert a false
set/weight ordering between two Byzantine message views. -/
theorem endpoint_INV2_base_of_confirmed_arms
    (hbb : ByzantineBound cfg E)
    {queryStore : Store Root} {bs : BeaconState Root}
    {b : Root} {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat} {lo es : Slot} {boost : Nat}
    (hloH : E.SlotWithinHorizon cfg lo)
    (hesH : E.SlotWithinHorizon cfg es)
    (hconf : is_one_confirmed cfg ext queryStore bs b = true)
    (harms : E.ConfirmedArmSupply cfg ext queryStore bs b v q lo es boost)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v q b es i -> E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v q b es i ->
        E.AncestorOrVoteless cfg ext w m b es i)
    (htax : E.ConfirmTaxArm cfg ext v q b lo es boost ->
      E.ConfirmTaxArm cfg ext w m b lo es boost) :
    E.INV2 cfg ext w m b lo es es boost := by
  obtain htaxQuery | hmemberQuery := harms hconf
  · exact E.INV2_base_of_arms cfg ext hbb w m b lo es boost hloH hesH
      (Or.inl (htax htaxQuery))
  · obtain ⟨hS, hX⟩ :=
      E.classes_base_transport_honest cfg ext v w q m b lo es hSt hAt
    apply E.INV2_base_of_arms cfg ext hbb w m b lo es boost hloH hesH
    right
    exact member_arm_transport_arith hmemberQuery hS hX

/-! ## 3. The exact cross-epoch recurrence and saturation inputs -/

/-- The sound pre-saturation class-migration input.  Unlike the strict
same-epoch `rho0_same_epoch` shortcut, this permits real `X -> S` and `A -> S`
migrants and requires the full committee funding inequality explicitly. -/
def FutureCrossingDeltas (w : ValidatorIndex) (m : Nat) (b : Root)
    (lo es : Slot) : Prop :=
  ∀ sigma' : Slot, es <= sigma' ->
    E.SlotWithinHorizon cfg sigma' -> E.SlotWithinHorizon cfg (sigma' + 1) ->
    compute_epoch_at_slot cfg (sigma' + 1) < compute_epoch_at_slot cfg es + 2 ->
    ∃ xi alpha : Nat,
      (E.Sval cfg ext w m b lo sigma' + xi + alpha +
          E.weight ((E.span_committee lo (sigma' + 1) \
            E.span_committee lo sigma').filter (fun i => i ∈ E.honest))
        <= E.Sval cfg ext w m b lo (sigma' + 1)) /\
      (E.Xval cfg ext w m b lo (sigma' + 1) + xi <=
        E.Xval cfg ext w m b lo sigma') /\
      (E.weight ((E.span_committee (sigma' + 1) (sigma' + 1)).filter
          (fun i => i ∈ E.honest)) <=
        E.weight (E.Unrec cfg ext w m b lo es sigma' \
          E.Unrec cfg ext w m b lo es (sigma' + 1)) + xi + alpha +
        E.weight ((E.span_committee lo (sigma' + 1) \
          E.span_committee lo sigma').filter (fun i => i ∈ E.honest)))

/-- The post-saturation honest-majority input used by
`DynamicsClosure.hsat_functional`. -/
def FutureCrossingSaturatedMajority (w : ValidatorIndex) (m : Nat) (b : Root)
    (lo es : Slot) (boost : Nat) : Prop :=
  ∀ sigma' : Slot, es <= sigma' ->
    compute_epoch_at_slot cfg es + 2 <= compute_epoch_at_slot cfg sigma' ->
    E.SlotWithinHorizon cfg sigma' ->
    E.Xval cfg ext w m b lo sigma'
        + cfg.confirmation_byzantine_threshold * E.Jspec lo sigma' /
            (100 - cfg.confirmation_byzantine_threshold)
        + boost + 1 <= E.Sval cfg ext w m b lo sigma'

/-- The third-regime producer boundary.  Every field after the endpoint base is
an input to the already-checked `INV2` recurrence/saturation and v2 endpoint
assembly.  The dynamics are supplied directly over the bounded interval,
making late in-slot query timing explicit. -/
structure FutureCrossingINV2Inputs
    (glc a b : Root) (v : ValidatorIndex) (q : Nat)
    (w : ValidatorIndex) (m : Nat) (bs : BeaconState Root) (queryStore : Store Root)
    (lo es sigma querySlot : Slot) : Prop where
  query_store_eq : queryStore = E.store cfg ext v q
  confirmation : is_one_confirmed cfg ext queryStore bs b = true
  lo_le_es : lo <= es
  es_le_sigma : es <= sigma
  lo_horizon : E.SlotWithinHorizon cfg lo
  es_horizon : E.SlotWithinHorizon cfg es
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  edge_same_epoch : get_block_epoch cfg queryStore a =
    get_block_epoch cfg queryStore b
  future_window_crosses : compute_epoch_at_slot cfg lo <
    compute_epoch_at_slot cfg sigma
  base_arms : E.ConfirmedArmSupply cfg ext queryStore bs b v q lo es
    (get_proposer_score cfg (E.store cfg ext w m))
  support_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.SupportsDesc cfg ext v q b es i -> E.SupportsDesc cfg ext w m b es i
  ancestor_transport : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
    E.AncestorOrVoteless cfg ext v q b es i ->
      E.AncestorOrVoteless cfg ext w m b es i
  tax_endpoint : E.ConfirmTaxArm cfg ext v q b lo es
      (get_proposer_score cfg (E.store cfg ext w m)) ->
    E.ConfirmTaxArm cfg ext w m b lo es
      (get_proposer_score cfg (E.store cfg ext w m))
  deltas : E.FutureCrossingDeltas cfg ext w m b lo es
  saturated_majority : E.FutureCrossingSaturatedMajority cfg ext w m b lo es
    (get_proposer_score cfg (E.store cfg ext w m))
  balance_source_registry : ((E.store cfg ext w m).checkpoint_states
    (E.store cfg ext w m).justified_checkpoint).validators = E.registry
  child_filtered : ForkChoiceNode.mk b .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)))
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m b lo sigma,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  honest_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) -> c' ≠ b ->
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∈ E.honest -> i ∈ E.Xclass cfg ext w m b lo sigma
  byzantine_sibling_confinement : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) -> c' ≠ b ->
    ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint),
      i ∉ E.honest ->
        i ∈ E.BbadSet cfg ext w m b lo es \/ i ∈ E.SpentSet es sigma

/-- A selected intra-epoch edge whose later window crosses epochs yields one
`DescendStep`, provided the sound endpoint base, cross-epoch deltas, saturation,
and endpoint recording inputs above are supplied. -/
theorem futureCrossing_descendStep_of_INV2Inputs
    (hbb : ByzantineBound cfg E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    {glc a b : Root} {v : ValidatorIndex} {q : Nat}
    {w : ValidatorIndex} {m : Nat} {bs : BeaconState Root} {queryStore : Store Root}
    {lo es sigma querySlot : Slot}
    (hin : E.FutureCrossingINV2Inputs cfg ext glc a b v q w m bs queryStore
      lo es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  have hbase : E.INV2 cfg ext w m b lo es es
      (get_proposer_score cfg (E.store cfg ext w m)) :=
    E.endpoint_INV2_base_of_confirmed_arms cfg ext hbb hin.lo_horizon hin.es_horizon
      hin.confirmation hin.base_arms hin.support_transport hin.ancestor_transport
      hin.tax_endpoint
  have hdeltas := hin.deltas
  have hpre : ∀ sigma' : Slot, es <= sigma' ->
      E.SlotWithinHorizon cfg sigma' -> E.SlotWithinHorizon cfg (sigma' + 1) ->
      compute_epoch_at_slot cfg (sigma' + 1) < compute_epoch_at_slot cfg es + 2 ->
      E.INV2 cfg ext w m b lo es sigma'
          (get_proposer_score cfg (E.store cfg ext w m)) ->
        E.INV2 cfg ext w m b lo es (sigma' + 1)
          (get_proposer_score cfg (E.store cfg ext w m)) := by
    intro sigma' hes' hsigH hsig1H hpreT1 hinv
    obtain ⟨xi, alpha, hS, hX, hfund⟩ := hdeltas sigma' hes' hsigH hsig1H hpreT1
    exact E.INV2_pre_step_of_deltas cfg ext hbb w m b lo es sigma'
      (get_proposer_score cfg (E.store cfg ext w m)) xi alpha
      hin.lo_horizon hsigH hsig1H (le_trans hin.lo_le_es (Nat.le_succ es))
      hes' hS hX hfund hinv
  have hmajority := hin.saturated_majority
  have hsat := E.hsat_functional cfg ext hbb w m b lo es
    (get_proposer_score cfg (E.store cfg ext w m)) hin.lo_horizon
    (le_trans hin.lo_le_es (Nat.le_succ es)) hmajority
  have hinv : E.INV2 cfg ext w m b lo es sigma
      (get_proposer_score cfg (E.store cfg ext w m)) :=
    E.INV2_maintained_same_epoch cfg ext hec hsv w m b lo es
      (get_proposer_score cfg (E.store cfg ext w m)) hbase hpre hsat
      sigma hin.es_le_sigma hin.sigma_horizon
  exact descendStep_of_ledgerStepV2 cfg ext
    (inv2_ledgerStepV2 cfg ext hin.balance_source_registry rfl hinv
      hin.child_filtered hin.selected_recording
      hin.honest_sibling_confinement hin.byzantine_sibling_confinement)

/-! ## 4. Endpoint-anchored full-span producer

The recurrence above gives an exact conditional boundary, but it is not
the strongest producer for this regime.  `Reanchor`'s full-span arithmetic
needs no per-slot `rho` partition at all.  The important anchoring correction is
to keep the future `S/A/X` classes at the consuming endpoint `(w,m)`: future
vote roots need not be known in the earlier query store `(v,n)`.

The theorem below derives every confirmation-side accounting atom from the
actual Boolean confirmation.  Only two base facts cross stores: confirmed
honest support grows into the endpoint support class, and the overlap part of
the empty-slot discount is already counted by the endpoint ancestor class.
Future `A+X` and `X` antitonicity are also endpoint facts; the concrete wrapper
after it derives them from `CommitteeSupportsAt`, including recurring
validators across epoch seams. -/

omit [LinearOrder Root] [Inhabited Root] in
private theorem fullSpan_base_transport_arith
    {sq se B d MU boost A : Nat}
    (hbase : 2 * sq + 2 * B + d >= MU + boost + 2 * A + 1)
    (hS : sq <= se) :
    2 * se + 2 * B + d >= MU + boost + 2 * A + 1 := by
  omega

/-- Same-epoch blocks use their own slot as the adversarial-span start.  This
is the non-crossing counterpart of `crossing_fullSpan_adversarial_guard`. -/
theorem intraEpoch_adversarial_guard (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hintra : get_block_epoch cfg store b =
      get_block_epoch cfg store (store.blocks b).parent_root)
    (hes : es = get_current_slot cfg store - 1)
    (hmidH : E.SlotWithinHorizon cfg (store.blocks b).slot)
    (hesH : E.SlotWithinHorizon cfg es) :
    E.Jspec (store.blocks b).slot es + E.Bval (store.blocks b).slot es <=
        100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) (store.blocks b).slot es / 100) /\
      estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) (store.blocks b).slot es / 100
          * cfg.confirmation_byzantine_threshold
        <= get_adversarial_weight cfg ext store bs b
          + get_equivocation_score cfg ext store bs (store.blocks b).slot es := by
  subst es
  have hnot : ¬ (get_block_epoch cfg store b >
      get_block_epoch cfg store (store.blocks b).parent_root) := by
    intro hgt
    rw [hintra] at hgt
    exact (Nat.lt_irrefl _ hgt)
  constructor
  · rw [E.Jspec_add_Bval_eq_weight_span]
    exact E.weight_span_le_estimate cfg hbb htab _ _ hmidH hesH
  · have hguard := qV_le_get_adversarial_add_eqV (cfg := cfg) (ext := ext)
      (store := store) (bs := bs) (b := b)
    simpa only [if_neg hnot] using hguard

/-- A concrete intra-edge/future-crossing endpoint inequality.

All confirmation-rule quantities (`Bsup`, discount, maximum support,
adversarial weight, equivocation score, and the full-window estimate) are read
at the actual query store.  All future honest classes are read at the endpoint.
This is why the result remains valid when future vote blocks were not yet known
at the query. -/
theorem intraEpochFuture_endpoint_inequality_of_confirmed_window
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
    (hbcur : ((E.store cfg ext v n).blocks b).slot <=
      get_current_slot cfg (E.store cfg ext v n))
    (hdom : E.WindowRecordedEpochMax cfg ext v n
      ((E.store cfg ext v n).blocks b).slot es)
    (hintra : get_block_epoch cfg (E.store cfg ext v n) b =
      get_block_epoch cfg (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).parent_root)
    (hesSigma : es <= sigma) (hSigmaH : E.SlotWithinHorizon cfg sigma)
    {w : ValidatorIndex} {m : ℕ}
    (hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m))
    (hSbase : E.Sval cfg ext v n b ((E.store cfg ext v n).blocks b).slot es <=
      E.Sval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hHsub : E.weight (E.crossingParentSub cfg (E.store cfg ext v n) bs b
        ((E.store cfg ext v n).blocks b).slot es) <=
      E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hAX : E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma
        <= E.Aval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es
          + E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es)
    (hxS : E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot sigma <=
      E.Xval cfg ext w m b ((E.store cfg ext v n).blocks b).slot es) :
    let lo := ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext v n).blocks b).slot
    E.weight (E.crossingXPre cfg (E.store cfg ext v n) bs b lo mid es)
        + E.Xval cfg ext w m b mid sigma
        + E.weight (E.crossingByzPre lo mid es)
        + E.Bval mid sigma + get_proposer_score cfg (E.store cfg ext w m) + 1
      <= E.Sval cfg ext w m b mid sigma := by
  dsimp only
  let lo := ((E.store cfg ext v n).blocks
    ((E.store cfg ext v n).blocks b).parent_root).slot + 1
  let mid := ((E.store cfg ext v n).blocks b).slot
  have hlo : lo <= mid := hslotlt
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
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n (by assumption) (by assumption)) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost] at hbaseQ
  rw [← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith hbaseQ hSbase
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
        <= estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
    rw [← hpart]
    exact hMUQ
  have hd := E.crossing_hd_of_preRegion (b := b) cfg ext hec hbb hv hnH hval
    hloH hmidH htab hne mid es
  have hguard := E.intraEpoch_adversarial_guard cfg ext hbb htab hintra hes hmidH hesH
  have hspan : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, i ∉ E.honest → i ∈ E.span_committee mid es := by
    intro i hi _
    rw [hes]
    exact supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) (le_refl _)
  have hbyzsub := E.hR4b_of_confinement cfg ext hec hv hnH hval hne hesH hspan
  have hbyzfull : E.Bval mid es <=
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [htab]
    exact hbb.span_bound mid es hmidH hesH
  have hdomFull :
      (E.Sval cfg ext w m b mid es + E.Aval cfg ext w m b mid es
          + E.Xval cfg ext w m b mid es + E.Bval mid es) + 0 + 0
        <= 100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100) := by
    rw [← E.weight_partition cfg ext w m b mid es]
    simpa only [Nat.add_zero] using hguard.1
  have hAguard : estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) mid es / 100
          * cfg.confirmation_byzantine_threshold
      <= get_adversarial_weight cfg ext (E.store cfg ext v n) bs b
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

/-- Compatibility wrapper for the legacy all-validator recorded-epoch
domination premise. -/
theorem intraEpochFuture_endpoint_inequality_of_confirmed
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
    (hdom : E.RecordedEpochMax cfg ext v n es)
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
  exact E.intraEpochFuture_endpoint_inequality_of_confirmed_window cfg ext
    hhb hec hbb hgen hv hnH hwf hval htab hprov hconf hwalk hes hslotlt hbcur
    (hdom.toWindow cfg ext) hintra hesSigma hSigmaH hboost hSbase hHsub hAX hxS

/-- Endpoint-anchored version of the full-span crossing-edge certificate.
This corrects the historical crossing wrapper, whose future classes were read
at the query store even though future vote roots need not be known there. -/
theorem crossingEdgeFuture_endpoint_inequality_of_confirmed_window
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
    fun i hi hih => (Execution.honest_not_equivocating cfg ext hhb hec hgen hih v n (by assumption) (by assumption)) hi
  have hbaseQ := E.crossing_hbase_of_confirmed_window cfg ext hhb hec hgen hwf hval hprov
    hconf hwalk es hes hdom
  rw [hboost, ← hes] at hbaseQ
  have hbase := fullSpan_base_transport_arith hbaseQ hSbase
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
  have hd := E.crossing_hd_of_preRegion (b := b) cfg ext hec hbb hv hnH hval
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
  have hbyzsub := E.hR4b_of_confinement cfg ext hec hv hnH hval hne hesH hspan
  have hbyzfull : E.Bval mid es + E.weight (E.crossingByzPre sa mid es) ≤
      estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100
            * cfg.confirmation_byzantine_threshold := by
    rw [E.crossing_fullSpan_Bval_split hsa, htab]
    exact hbb.span_bound sa es hsaH hesH
  have heqsplit := E.crossing_equivocation_score_split (n := n) (es := es)
    cfg ext hec hv hnH hval hsa hesH
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

/-- Compatibility wrapper for the legacy all-validator recorded-epoch
domination premise. -/
theorem crossingEdgeFuture_endpoint_inequality_of_confirmed
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
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
    (hdom : E.RecordedEpochMax cfg ext v n es)
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
  exact E.crossingEdgeFuture_endpoint_inequality_of_confirmed_window cfg ext
    hhb hec hbb hgen hv hnH hwf hval htab hprov hconf hwalk hes hslotlt hbcur
    (hdom.toWindow cfg ext) hcross hesSigma hSigmaH hboost hSbase hHsub hAX hxS

/-- Concrete third-regime inputs at an arbitrary permitted query second.

The query is represented by its real `FastConfirmationStore`, so a successful
Boolean confirmation also proves that its balance checkpoint is keyed.  The
registry, total-active, provenance, block-order, discount, adversarial, and
endpoint-balance facts are consequently derived by the producer below.

`committee_support` is the exact bounded dynamics fact consumed by the endpoint
proof.  At the slot-start bootstrap one chooses `sigma = es`, making it
vacuous; after that bootstrap it is derived from the slot-start safety
induction hypothesis. -/
structure FutureCrossingSelectedMarginInputs
    (glc a b : Root) (v : ValidatorIndex) (q : ℕ)
    (w : ValidatorIndex) (m : ℕ) (query : FastConfirmationStore Root)
    (es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext v q
  confirmation : is_one_confirmed cfg ext query.store
    (get_current_balance_source query) b = true
  block_known : b ∈ (E.store cfg ext v q).block_roots
  parent_known : ((E.store cfg ext v q).blocks b).parent_root ∈
    (E.store cfg ext v q).block_roots
  cutoff_eq : es = get_current_slot cfg (E.store cfg ext v q) - 1
  query_slot_eq : querySlot = get_current_slot cfg (E.store cfg ext v q)
  es_le_sigma : es ≤ sigma
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  edge_same_epoch : get_block_epoch cfg (E.store cfg ext v q) b =
    get_block_epoch cfg (E.store cfg ext v q)
      ((E.store cfg ext v q).blocks b).parent_root
  future_window_crosses : compute_epoch_at_slot cfg
      ((E.store cfg ext v q).blocks b).slot < compute_epoch_at_slot cfg sigma
  recorded_epoch_max : E.WindowRecordedEpochMax cfg ext v q
    ((E.store cfg ext v q).blocks b).slot es
  support_transport : ∀ i, i ∈ E.honest →
    i ∈ E.span_committee ((E.store cfg ext v q).blocks b).slot es →
    E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i
  ancestor_transport : ∀ i, i ∈ E.honest →
    i ∈ E.span_committee ((E.store cfg ext v q).blocks b).slot es →
    E.AncestorOrVoteless cfg ext v q b es i →
      E.AncestorOrVoteless cfg ext w m b es i
  parent_sub_endpoint : E.weight (E.crossingParentSub cfg
      (E.store cfg ext v q) (get_current_balance_source query) b
      ((E.store cfg ext v q).blocks b).slot es) ≤
    E.Aval cfg ext w m b ((E.store cfg ext v q).blocks b).slot es
  committee_support : ∀ t : Slot, es < t → t ≤ sigma →
    E.CommitteeSupportsAt cfg ext w m b t
  child_filtered : ForkChoiceNode.mk b .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)))
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m b
      ((E.store cfg ext v q).blocks b).slot sigma,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)
      ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q)
            (get_current_balance_source query) b
            (((E.store cfg ext v q).blocks
              ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
            ((E.store cfg ext v q).blocks b).slot es)
        + E.Xval cfg ext w m b ((E.store cfg ext v q).blocks b).slot sigma
        + E.weight (E.crossingByzPre
            (((E.store cfg ext v q).blocks
              ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
            ((E.store cfg ext v q).blocks b).slot es)
        + E.Bval ((E.store cfg ext v q).blocks b).slot sigma

/-- The concrete third producer.  It derives the full-span accounting from the
actual query confirmation, transports only the base honest support to the
endpoint, derives cross-epoch endpoint `A+X`/`X` antitonicity from committee
support, and then performs the ordinary endpoint GHOST comparison. -/
theorem futureCrossing_descendStep_of_selectedInputs
    (hSA : SpecAssumptions cfg ext E)
    {glc a b : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.FutureCrossingSelectedMarginInputs cfg ext glc a b v q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  obtain ⟨hgenFull, hwfE, hdiv, hhb, _hsync, hec, hsv, hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgenFull
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hec hgen v hv q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hsv hec v hv q cp hkey hqH
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hdiv hec hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hwfE hec
      ⟨ast, ablk, hgeq, hslot, hparent⟩ hwfE.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hwfE hec hgen v q (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec
    ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q) ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩
      v q b hin.block_known
  have hEstH := E.justified_balance_source_epoch_lt_horizon cfg ext hec hji hdiv hgen
    w hw m hmH
  have hSbase := (E.classes_base_transport_honest cfg ext v w q m b
    ((E.store cfg ext v q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hhb w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hhb w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hboost := E.boost_reconcile cfg ext hsv hec hgen hji hval hbsH hw m hmH hEstH
  have hend := E.intraEpochFuture_endpoint_inequality_of_confirmed_window cfg ext
    hhb hec hbb hgen hv hqH hwf hval htab hprov hconf hwalk
    hin.cutoff_eq hslotlt hbcur hin.recorded_epoch_max hin.edge_same_epoch
    hin.es_le_sigma hin.sigma_horizon hboost hSbase
    (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hvalEnd : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_interface cfg ext hec hgen hji w hw m hmH
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hbside hend
    hin.sibling_score

/-- Endpoint-anchored inputs for an edge that itself crosses an epoch.  All
store-dependent fields are stated at the consuming endpoint. -/
structure CrossingEdgeSelectedMarginInputs
    (glc a b : Root) (v : ValidatorIndex) (q : ℕ)
    (w : ValidatorIndex) (m : ℕ) (query : FastConfirmationStore Root)
    (es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext v q
  confirmation : is_one_confirmed cfg ext query.store
    (get_current_balance_source query) b = true
  block_known : b ∈ (E.store cfg ext v q).block_roots
  parent_known : ((E.store cfg ext v q).blocks b).parent_root ∈
    (E.store cfg ext v q).block_roots
  cutoff_eq : es = get_current_slot cfg (E.store cfg ext v q) - 1
  query_slot_eq : querySlot = get_current_slot cfg (E.store cfg ext v q)
  es_le_sigma : es ≤ sigma
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  edge_crosses : get_block_epoch cfg (E.store cfg ext v q) b >
    get_block_epoch cfg (E.store cfg ext v q)
      ((E.store cfg ext v q).blocks b).parent_root
  recorded_epoch_max : E.WindowRecordedEpochMax cfg ext v q
    ((E.store cfg ext v q).blocks b).slot es
  support_transport : ∀ i, i ∈ E.honest →
    i ∈ E.span_committee ((E.store cfg ext v q).blocks b).slot es →
    E.SupportsDesc cfg ext v q b es i → E.SupportsDesc cfg ext w m b es i
  ancestor_transport : ∀ i, i ∈ E.honest →
    i ∈ E.span_committee ((E.store cfg ext v q).blocks b).slot es →
    E.AncestorOrVoteless cfg ext v q b es i →
      E.AncestorOrVoteless cfg ext w m b es i
  parent_sub_endpoint : E.weight (E.crossingParentSub cfg
      (E.store cfg ext v q) (get_current_balance_source query) b
      ((E.store cfg ext v q).blocks b).slot es) ≤
    E.Aval cfg ext w m b ((E.store cfg ext v q).blocks b).slot es
  committee_support : ∀ t : Slot, es < t → t ≤ sigma →
    E.CommitteeSupportsAt cfg ext w m b t
  child_filtered : ForkChoiceNode.mk b .pending ∈
    get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b)))
  selected_recording : ∀ i ∈ E.Sclass cfg ext w m b
      ((E.store cfg ext v q).blocks b).slot sigma,
    i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root b)
      ((E.store cfg ext w m).checkpoint_states
        (E.store cfg ext w m).justified_checkpoint)
  sibling_score : ∀ c' : Root,
    ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
      (ForkChoiceNode.mk a (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks b))) → c' ≠ b →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint)
      ≤ E.weight (E.crossingXPre cfg (E.store cfg ext v q)
            (get_current_balance_source query) b
            (((E.store cfg ext v q).blocks
              ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
            ((E.store cfg ext v q).blocks b).slot es)
        + E.Xval cfg ext w m b ((E.store cfg ext v q).blocks b).slot sigma
        + (E.weight (E.crossingByzPre
              (((E.store cfg ext v q).blocks
                ((E.store cfg ext v q).blocks b).parent_root).slot + 1)
              ((E.store cfg ext v q).blocks b).slot es)
          - E.weight (E.crossingEquivPre cfg (E.store cfg ext v q)
              (get_current_balance_source query)
              (compute_start_slot_at_epoch cfg
                (get_block_epoch cfg (E.store cfg ext v q) b))
              ((E.store cfg ext v q).blocks b).slot es))
        + E.Bval ((E.store cfg ext v q).blocks b).slot sigma

/-- Concrete endpoint-anchored producer for a selected edge that crosses an
epoch boundary. -/
theorem crossingEdge_descendStep_of_selectedInputs
    (hSA : SpecAssumptions cfg ext E)
    {glc a b : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.CrossingEdgeSelectedMarginInputs cfg ext glc a b v q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  obtain ⟨hgenFull, hwfE, hdiv, hhb, _hsync, hec, hsv, hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgenFull
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hec hgen v hv q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hsv hec v hv q cp hkey hqH
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hdiv hec hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hwfE hec
      ⟨ast, ablk, hgeq, hslot, hparent⟩ hwfE.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hwfE hec hgen v q (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec
    ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q) ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩
      v q b hin.block_known
  have hEstH := E.justified_balance_source_epoch_lt_horizon cfg ext hec hji hdiv hgen
    w hw m hmH
  have hboost := E.boost_reconcile cfg ext hsv hec hgen hji hval hbsH hw m hmH hEstH
  have hSbase := (E.classes_base_transport_honest cfg ext v w q m b
    ((E.store cfg ext v q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hhb w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hhb w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hend := E.crossingEdgeFuture_endpoint_inequality_of_confirmed_window cfg ext
    hhb hec hbb hgen hv hqH hwf hval htab hprov hconf hwalk hin.cutoff_eq
    hslotlt hbcur hin.recorded_epoch_max hin.edge_crosses hin.es_le_sigma
    hin.sigma_horizon hboost hSbase
    (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hvalEnd : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
    E.hval_of_interface cfg ext hec hgen hji w hw m hmH
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered hbside hend
    hin.sibling_score

/-! ## 5. Machine-checked obstruction witnesses -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Honest `S`/`X` movements do not transport the tax arm when the endpoint has
a different selectively delivered Byzantine view.  The concrete values are a
scaled-down form of the discount-funded configuration: the query tax arm holds
with `Bbad = 0`, while the same `S = 26`, `X = 0` at an endpoint with
`Bbad = 18` fails by one. -/
theorem tax_arm_not_transportable_from_honest_legs :
    (0 + 0 + (0 + 1) + 25 * 26 / (100 - 25) <= 26) /\
    (26 <= 26) /\ (0 <= 0) /\
    ¬ (0 + 18 + (0 + 1) + 25 * 26 / (100 - 25) <= 26) := by
  norm_num

omit [LinearOrder Root] [Inhabited Root] in
/-- An already-supporting honest recurrer makes the cross-epoch `rho = 0`
partition impossible.  Here a weight-100 honest committee recurs, while `S`,
`X`, `Unrec`, and the union window are unchanged; no migrant witnesses can
satisfy all three delta inequalities. -/
theorem recurring_supporter_breaks_preStep_partition :
    ¬ (∃ xi alpha : Nat,
      100 + xi + alpha + 0 <= 100 /\
      0 + xi <= 0 /\
      100 <= 0 + xi + alpha + 0) := by
  omega

end Execution

end FastConfirmation.Spec

end
