module
public import FastConfirmationProofs.FFG.Certificates.FFGCertificates
public import FastConfirmationProofs.Discount.EconomicRounding
public import FastConfirmationProofs.Execution.Delivery.Registry

@[expose] public section

/-!
# Spec / Proof / FFGAccountability

Discharge the economic side of the concrete FFG certificates.  Full-epoch
committee coverage identifies every horizon-bounded target epoch's committee
union with the static anchor active set.  Consequently any two two-thirds link
certificates, even at different target epochs, intersect in an honest validator.
Together with `Proof/FFGCertificates`, this derives same-epoch uniqueness and
the Casper no-surround/finalized-prefix consequences rather than assuming them
as arbitrary store-level ancestry laws.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The exact execution assumptions used by concrete Casper accountability.
In particular this bundle contains no `JustificationInterface` field and no
store-level justified/finalized ancestry or fork-choice-head conclusion. -/
structure FFGAccountabilityAssumptions (E : Execution Root) : Prop where
  genesis_store : ∃ (anchor_state : BeaconState Root)
      (anchor_block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block
  whole_seconds : 1000 ∣ cfg.slot_duration_ms
  honest_behavior : HonestBehavior cfg ext E
  externals_coherence : BeaconExternalsPremises cfg ext E
  static_validator_set : StaticValidatorSet cfg E
  byzantine_bound : ByzantineWeightPremises cfg E

omit [LinearOrder Root] [Inhabited Root] in
private theorem mem_active_of_active_local {bs : BeaconState Root}
    {i : ValidatorIndex} {e : Epoch}
    (hact : is_active_validator (bs.validators.getD i default) e = true) :
    i ∈ get_active_validator_indices bs e := by
  simp only [get_active_validator_indices, List.mem_filter, List.mem_range]
  refine ⟨?_, hact⟩
  by_contra hge
  rw [not_lt] at hge
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none] at hact
  simp only [is_active_validator, decide_eq_true_eq] at hact
  have hbad := hact.2
  change e < 0 at hbad
  exact (Nat.not_lt_zero e) hbad

namespace Execution

variable (E : Execution Root)

private def anchorActive : Finset ValidatorIndex :=
  (get_active_validator_indices E.anchor_state
    (get_current_epoch cfg E.anchor_state)).toFinset

private theorem anchor_epoch_within (hA : FFGAccountabilityAssumptions cfg ext E) :
    get_current_epoch cfg E.anchor_state < E.verification_horizon := by
  have hslot := E.anchor_state_slot_le cfg hA.whole_seconds hA.genesis_store
  have hepoch : get_current_epoch cfg E.anchor_state ≤
      compute_epoch_at_slot cfg (E.slot_at cfg 0) := by
    simpa only [get_current_epoch] using Nat.div_le_div_right hslot
  exact lt_of_le_of_lt hepoch
    hA.static_validator_set.genesis_within_horizon.2.2

private theorem span_subset_anchorActive
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {lo hi : Slot} (hhi : E.SlotWithinHorizon cfg hi) :
    E.span_committee lo hi ⊆ E.anchorActive cfg := by
  have hanchorH := E.anchor_epoch_within cfg ext hA
  intro i hiSpan
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hiSpan
  obtain ⟨s, hs, hiCommittee⟩ := hiSpan
  have hsH : E.SlotWithinHorizon cfg s :=
    ⟨le_trans hs.2 hhi.1,
      lt_of_le_of_lt (Nat.div_le_div_right hs.2) hhi.2⟩
  have hactiveS := hA.externals_coherence.committee_members_active i s hsH hiCommittee
  have hactiveAnchor : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    rw [← hA.static_validator_set.activity_constant i (compute_epoch_at_slot cfg s)
      (get_current_epoch cfg E.anchor_state) hsH.2 hanchorH]
    exact hactiveS
  rw [anchorActive, List.mem_toFinset]
  apply mem_active_of_active_local
  simpa only [Execution.registry] using hactiveAnchor

private theorem anchorActive_subset_epoch_span
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {e : Epoch} (heH : e < E.verification_horizon) :
    E.anchorActive cfg ⊆
      E.span_committee (e * cfg.slots_per_epoch)
        (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) := by
  have hanchorH := E.anchor_epoch_within cfg ext hA
  intro i hiActive
  rw [anchorActive, List.mem_toFinset] at hiActive
  have hactiveAnchor : is_active_validator
      (E.anchor_state.validators.getD i default)
      (get_current_epoch cfg E.anchor_state) = true :=
    (List.mem_filter.mp hiActive).2
  have hactiveGround : is_active_validator (E.registry.getD i default)
      (get_current_epoch cfg E.anchor_state) = true := by
    simpa only [Execution.registry] using hactiveAnchor
  have hactiveE : is_active_validator (E.registry.getD i default) e = true := by
    rw [← hA.static_validator_set.activity_constant i
      (get_current_epoch cfg E.anchor_state) e
      hanchorH heH]
    exact hactiveGround
  obtain ⟨s, _hsH, hse, hiCommittee⟩ :=
    hA.externals_coherence.committee_coverage i e heH hactiveE
  have hdiv : s / cfg.slots_per_epoch = e := by
    simpa only [compute_epoch_at_slot] using hse
  have hlo : e * cfg.slots_per_epoch ≤ s := by
    have h := Nat.div_mul_le_self s cfg.slots_per_epoch
    rw [hdiv] at h
    exact h
  have hlt : s < e * cfg.slots_per_epoch + cfg.slots_per_epoch := by
    have h := Nat.lt_mul_div_succ s cfg.slots_per_epoch_pos
    rw [hdiv, Nat.mul_add] at h
    simpa [Nat.mul_comm, Nat.add_comm] using h
  have hhi : s ≤ e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1) := by
    have hpred := Nat.le_pred_of_lt hlt
    rw [Nat.pred_eq_sub_one,
      Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt cfg.slots_per_epoch_pos))] at hpred
    exact hpred
  simp only [Execution.span_committee, Finset.mem_biUnion]
  exact ⟨s, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hiCommittee⟩

private theorem epoch_span_eq_anchorActive
    (hA : FFGAccountabilityAssumptions cfg ext E)
    {e : Epoch}
    (heH : e < E.verification_horizon)
    (hspan : E.SlotWithinHorizon cfg
      (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))) :
    E.span_committee (e * cfg.slots_per_epoch)
        (e * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1)) =
      E.anchorActive cfg := by
  apply Finset.Subset.antisymm
  · exact E.span_subset_anchorActive cfg ext hA hspan
  · exact E.anchorActive_subset_epoch_span cfg ext hA heH

private theorem anchorActive_weight_le_total :
    E.weight (E.anchorActive cfg) ≤ E.total_active cfg := by
  simp only [anchorActive, Execution.weight, Execution.weight_of,
    Execution.total_active, get_total_active_balance, get_total_balance,
    Execution.registry]
  exact Nat.le_max_right _ _

/-- Any two concrete supermajority links in the verified horizon intersect in
an honest signer, even when their targets belong to different epochs. -/
theorem links_intersect_honest (hA : FFGAccountabilityAssumptions cfg ext E)
    {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink cfg E s t)
    (L' : SupermajorityLink cfg E s' t') :
    ∃ i ∈ L.signers, i ∈ L'.signers ∧ i ∈ E.honest := by
  let U := E.anchorActive cfg
  have hLU : L.signers ⊆ U :=
    fun _ hi => E.span_subset_anchorActive cfg ext hA L.target_span_within.2
      (L.signers_in_epoch hi)
  have hL'U : L'.signers ⊆ U :=
    fun _ hi => E.span_subset_anchorActive cfg ext hA L'.target_span_within.2
      (L'.signers_in_epoch hi)
  have hspanEq := E.epoch_span_eq_anchorActive cfg ext hA
    L.target_epoch_within L.target_span_within.2
  have hfrac : 100 * E.weight (U.filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold * E.weight U := by
    change 100 * E.weight ((E.anchorActive cfg).filter (fun i => i ∉ E.honest)) ≤
      cfg.confirmation_byzantine_threshold * E.weight (E.anchorActive cfg)
    rw [← hspanEq]
    exact hA.byzantine_bound.span_fraction _ _
      L.target_span_within.1 L.target_span_within.2
  exact two_quorums_intersect_honest E (E.total_active_pos cfg)
    hLU hL'U (E.anchorActive_weight_le_total cfg) hfrac
    cfg.confirmation_byzantine_threshold_le L.supermajority L'.supermajority

/-- Certified justification is unique per epoch, now as a theorem from the
concrete link evidence and the execution assumptions. -/
theorem certified_justified_unique (hA : FFGAccountabilityAssumptions cfg ext E)
    {anchor c c' : Checkpoint Root}
    (hc : CertifiedJustified cfg E anchor c)
    (hc' : CertifiedJustified cfg E anchor c')
    (hepoch : c.epoch = c'.epoch) : c.root = c'.root := by
  cases hc with
  | anchor =>
      cases hc' with
      | anchor => rfl
      | @link source target hsource link =>
          have hge := CertifiedJustified.anchor_epoch_le (cfg := cfg) hsource
          exfalso
          exact (Nat.ne_of_lt (lt_of_le_of_lt hge link.source_before_target)) hepoch
  | @link source target hsource link =>
      cases hc' with
      | anchor =>
          have hge := CertifiedJustified.anchor_epoch_le (cfg := cfg) hsource
          exfalso
          exact (Nat.ne_of_lt (lt_of_le_of_lt hge link.source_before_target)) hepoch.symm
      | @link source' target' hsource' link' =>
          have hspanEq := E.epoch_span_eq_anchorActive cfg ext hA
            link.target_epoch_within link.target_span_within.2
          have hspanTotal : E.weight
              (E.span_committee (c.epoch * cfg.slots_per_epoch)
                (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))) ≤
              E.total_active cfg := by
            rw [hspanEq]
            exact E.anchorActive_weight_le_total cfg
          have hfrac := hA.byzantine_bound.span_fraction
            (c.epoch * cfg.slots_per_epoch)
            (c.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
            link.target_span_within.1 link.target_span_within.2
          exact SupermajorityLink.root_eq_of_same_epoch cfg ext
            hA.honest_behavior link link'
            hepoch (E.total_active_pos cfg) hspanTotal hfrac

/-- The no-surround half of Casper accountable safety, derived for any two
certificate links in the execution prefix. -/
theorem certified_links_not_surround (hA : FFGAccountabilityAssumptions cfg ext E)
    {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink cfg E s t)
    (L' : SupermajorityLink cfg E s' t') :
    ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch) := by
  have hinter := E.links_intersect_honest cfg ext hA L L'
  exact SupermajorityLink.not_surround_of_honest_intersection cfg ext
    hA.honest_behavior L L' hinter

/-- A finalized certified checkpoint is a prefix of every weakly newer
certified justified checkpoint. -/
theorem certified_finalized_prefix (hA : FFGAccountabilityAssumptions cfg ext E)
    {anchor finalized justified : Checkpoint Root}
    (hf : CertifiedFinalized cfg E anchor finalized)
    (hj : CertifiedJustified cfg E anchor justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    E.RootDescends justified.root finalized.root :=
  CertifiedFinalized.prefix_of_accountable cfg
    (fun hx hy he => E.certified_justified_unique cfg ext hA hx hy he)
    (fun L L' => E.certified_links_not_surround cfg ext hA L L')
    hf hj hepoch

end Execution

end FastConfirmation.Spec

end
