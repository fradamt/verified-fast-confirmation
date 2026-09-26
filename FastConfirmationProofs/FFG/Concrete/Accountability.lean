module
public import FastConfirmationProofs.FFG.Concrete.FinalizationSoundness

@[expose] public section

/-! Proves quantitative accountability for concrete FFG certificates. Two
supermajority links of the fixed registry share signers with at least one
third of the fixed total active balance. Conflicting targets of one epoch, or
a surrounding pair of links, therefore make that weight of validators
slashable among included, target-matching body votes. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### The fixed active universe -/

/-- The fixed active universe: registry validators active at the first scope
epoch. -/
def _root_.FastConfirmation.Spec.FixedFFGScope.activeSet (scope : FixedFFGScope) :
    Finset ValidatorIndex :=
  ((List.range scope.validators.length).filter fun i =>
    is_active_validator (scope.validators.getD i default) scope.first_epoch).toFinset

theorem _root_.FastConfirmation.Spec.FixedFFGScope.weight_activeSet (scope : FixedFFGScope) :
    scope.weight scope.activeSet = scope.activeBalance := by
  unfold FixedFFGScope.weight FixedFFGScope.activeSet FixedFFGScope.activeBalance
  exact List.sum_toFinset _ ((List.nodup_range).filter _)

/-- A weight of signers inside the fixed active universe is at most the fixed
total active balance. -/
theorem _root_.FastConfirmation.Spec.FixedFFGScope.weight_le_activeBalance (scope : FixedFFGScope)
    {signers : Finset ValidatorIndex} (h : signers ⊆ scope.activeSet) :
    scope.weight signers ≤ scope.activeBalance := by
  rw [← scope.weight_activeSet]
  exact Finset.sum_le_sum_of_subset h

/-- The signers of an in-horizon link are in the fixed active universe. -/
theorem SupermajorityLink.signers_subset {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {source target : Checkpoint Root}
    (L : SupermajorityLink S votes source target)
    (ht : target.epoch ≤ S.scope.last_epoch) :
    L.signers ⊆ S.scope.activeSet := by
  intro i hi
  obtain ⟨hlt, hact⟩ := L.signer_active i hi
  have hfixed := S.scope.activity_fixed ⟨i, hlt⟩ target.epoch
    (by rw [hS.scope_from_genesis]; exact Nat.zero_le _) ht
  have hget : S.scope.validators.getD i default = S.scope.validators[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  unfold FixedFFGScope.activeSet
  rw [List.mem_toFinset, List.mem_filter, List.mem_range]
  refine ⟨hlt, ?_⟩
  rw [hget] at hact ⊢
  exact hfixed.symm.trans hact

/-- **Quorum intersection.** Two in-horizon supermajority links share signers
with at least one third of the fixed total active balance. -/
theorem SupermajorityLink.intersection_weight {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink S votes s t) (L' : SupermajorityLink S votes s' t')
    (ht : t.epoch ≤ S.scope.last_epoch) (ht' : t'.epoch ≤ S.scope.last_epoch) :
    S.scope.activeBalance ≤ 3 * S.scope.weight (L.signers ∩ L'.signers) := by
  have hunion : S.scope.weight (L.signers ∪ L'.signers) ≤ S.scope.activeBalance :=
    S.scope.weight_le_activeBalance
      (Finset.union_subset (L.signers_subset hS ht) (L'.signers_subset hS ht'))
  have hsum := Finset.sum_union_inter (s₁ := L.signers) (s₂ := L'.signers)
    (f := fun i => (S.scope.validators.getD i default).effective_balance)
  change S.scope.weight (L.signers ∪ L'.signers) + S.scope.weight (L.signers ∩ L'.signers) =
    S.scope.weight L.signers + S.scope.weight L'.signers at hsum
  have h1 := L.supermajority
  have h2 := L'.supermajority
  beacon_omega

/-! ### Slashable quorums -/

/-- Two links whose vote data is slashable give a slashable quorum. -/
theorem slashableQuorum_of_links {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink S votes s t) (L' : SupermajorityLink S votes s' t')
    (ht : t.epoch ≤ S.scope.last_epoch) (ht' : t'.epoch ≤ S.scope.last_epoch)
    (hslash : ∀ d d' : AttestationData Root, d.source = s → d.target = t →
      d'.source = s' → d'.target = t' → is_slashable_attestation_data d d' = true) :
    SlashableQuorum S votes := by
  refine ⟨L.signers ∩ L'.signers, L.intersection_weight hS L' ht ht', ?_⟩
  intro i hi
  obtain ⟨r, hr, hri, hrs, hrt⟩ := L.signer_vote i (Finset.mem_inter.mp hi).1
  obtain ⟨r', hr', hri', hrs', hrt'⟩ := L'.signer_vote i (Finset.mem_inter.mp hi).2
  exact ⟨r, r', hr, hr', hri, hri', hslash _ _ hrs hrt hrs' hrt'⟩

/-- **Double vote.** Two in-horizon links to distinct targets of one epoch
make signers with one third of the active balance slashable. -/
theorem slashableQuorum_of_double {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink S votes s t) (L' : SupermajorityLink S votes s' t')
    (ht : t.epoch ≤ S.scope.last_epoch) (hepoch : t.epoch = t'.epoch) (hne : t ≠ t') :
    SlashableQuorum S votes := by
  refine slashableQuorum_of_links hS L L' ht (hepoch ▸ ht) ?_
  intro d d' _ hdt _ hdt'
  unfold is_slashable_attestation_data
  refine decide_eq_true (Or.inl ⟨fun hdd => hne ?_, ?_⟩)
  · rw [← hdt, ← hdt', hdd]
  · rw [hdt, hdt']; exact hepoch

/-- **Surround vote.** An in-horizon link that surrounds another link makes
signers with one third of the active balance slashable. -/
theorem slashableQuorum_of_surround {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {s t s' t' : Checkpoint Root}
    (L : SupermajorityLink S votes s t) (L' : SupermajorityLink S votes s' t')
    (ht : t.epoch ≤ S.scope.last_epoch) (hs : s.epoch < s'.epoch) (hts : t'.epoch < t.epoch) :
    SlashableQuorum S votes := by
  refine slashableQuorum_of_links hS L L' ht (by beacon_omega) ?_
  intro d d' hds hdt hds' hdt'
  unfold is_slashable_attestation_data
  refine decide_eq_true (Or.inr ⟨?_, ?_⟩)
  · rw [hds, hds']; exact hs
  · rw [hdt, hdt']; exact hts

omit [DecidableEq Root] in
/-- A justified checkpoint of epoch 0 is the genesis stub. -/
theorem Justified.eq_stub_of_epoch_zero [BEq Root] {S : FFGSetup Root}
    {votes : List (IncludedVote Root)} {c : Checkpoint Root} (h : Justified S votes c)
    (h0 : c.epoch = 0) : c = S.stub := by
  cases h with
  | anchor => rfl
  | link _ L =>
    have := L.source_before_target
    beacon_omega

/-- **Justification uniqueness or slashing.** Two justified checkpoints of one
in-horizon epoch are equal, or signers with one third of the active balance
are slashable. -/
theorem justified_eq_or_slashable {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {x y : Checkpoint Root}
    (hx : Justified S votes x) (hy : Justified S votes y)
    (hlast : x.epoch ≤ S.scope.last_epoch) (hepoch : x.epoch = y.epoch) :
    x = y ∨ SlashableQuorum S votes := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  right
  cases hx with
  | anchor =>
    exact absurd (hy.eq_stub_of_epoch_zero hepoch.symm).symm hxy
  | link hs L =>
    cases hy with
    | anchor => exact absurd (Justified.eq_stub_of_epoch_zero (.link hs L) hepoch) hxy
    | link _ L' => exact slashableQuorum_of_double hS L L' hlast hepoch hxy

/-- **Concrete certificate accountability.** Without a slashable quorum, the
two certificate laws of the exact-prefix argument hold. -/
theorem ConcreteCertificateAccountability.of_not_slashableQuorum {S : FFGSetup Root}
    (hS : S.Admissible) {votes : List (IncludedVote Root)}
    (h : ¬ SlashableQuorum S votes) : ConcreteCertificateAccountability S votes where
  justified_unique := fun hx hy hlast hepoch => by
    rcases justified_eq_or_slashable hS hx hy hlast hepoch with hxy | hq
    · rw [hxy]
    · exact absurd hq h
  links_not_surround := fun L L' ht ⟨hs, hts⟩ =>
    h (slashableQuorum_of_surround hS L L' ht hs hts)

/-- Slashable signers inside a set of less than one third of the active
balance exclude a slashable quorum. With honest validators that never sign
slashable pairs, the set is the Byzantine set. -/
theorem not_slashableQuorum_of_weight_lt {S : FFGSetup Root}
    {votes : List (IncludedVote Root)} {faulty : Finset ValidatorIndex}
    (hfaulty : ∀ i, SlashableSigner S votes i → i ∈ faulty)
    (hweight : 3 * S.scope.weight faulty < S.scope.activeBalance) :
    ¬ SlashableQuorum S votes := by
  rintro ⟨signers, hq, hs⟩
  have hsub : signers ⊆ faulty := fun i hi => hfaulty i (hs i hi)
  have : S.scope.weight signers ≤ S.scope.weight faulty := Finset.sum_le_sum_of_subset hsub
  beacon_omega

end FastConfirmation.Spec.ConcreteFFG

end
