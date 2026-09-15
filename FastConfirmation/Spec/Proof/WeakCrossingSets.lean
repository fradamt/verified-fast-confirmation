import FastConfirmation.Spec.Proof.WeakEndpointClasses
import FastConfirmation.Spec.Proof.CrossingCert
import FastConfirmation.Spec.Proof.FutureCrossingMargin
import FastConfirmation.Spec.Proof.Reanchor

/-!
# Spec / Proof / WeakCrossingSets

Margin-discharge wave, Stage I-a/I-b (`docs/weak-synchrony.md` rule delta 3):
the weak crossing-set geometry and the two endpoint-inequality assemblers that
retire `hdom`/`WindowRecordedEpochMax` from the crossing/sibling arms.

`Weak.crossingParentPre`/`crossingParentSub`/`crossingXPre` are the exact
`CrossingCert.lean` set geometry over `Weak.FreshParentStuck` instead of the
strong `ParentStuck`; every arithmetic consumer (`crossing_hMU_of_canonicalPre`,
`crossing_hd_of_preRegion_of_prefix`) is the corresponding strong lemma's proof
verbatim, over the fresh sets.

**F3 (crossing-edge subtractive arm collapses).** `Weak.compute_adversarial_weight`
has no equivocation subtraction (rule delta 1), so `Weak.adversarial_guard_intra`
and `Weak.adversarial_guard_crossing` are *equalities* dressed as inequalities
with the `eqSub = eqExtra = 0` padding that `reanchored_endpoint_of_fullSpan_certificate`
expects. Consequently both weak endpoint-inequality assemblers below share the
same **non-subtractive** conclusion shape — the crossing-edge arm's
`crossingEquivPre`/`hR4b_of_confinement`-based subtractive route never
appears on this path.

The base charge (`Weak.crossing_hbase_of_confirmed_at_observer`,
`WeakEndpointClasses.lean`) is already read at the honest endpoint `(w, m)`,
so unlike the strong `_of_prefix` clones in `WeakOneShotSafety.lean` §2, no
`hSbase`/`fullSpan_base_transport_arith` step is needed here.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## 1. The weak crossing sets -/

/-- Fresh parent-stuck honest validators not already counted in the
sub-window. Weak twin of `Execution.crossingParentPre`, over
`Weak.FreshParentStuck`. -/
def crossingParentPre (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) (mid es : Slot) : Finset ValidatorIndex :=
  FreshParentStuck cfg E store bs b \ E.span_committee mid es

/-- Fresh parent-stuck honest validators that recur in, and are therefore
already counted by, the sub-window. Weak twin of `Execution.crossingParentSub`. -/
def crossingParentSub (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) (mid es : Slot) : Finset ValidatorIndex :=
  FreshParentStuck cfg E store bs b ∩ E.span_committee mid es

/-- The canonical old-sibling honest pre mass, over the weak parent-pre set.
Weak twin of `Execution.crossingXPre`. -/
def crossingXPre (E : Execution Root) (store : Store Root) (bs : BeaconState Root)
    (b : Root) (lo mid es : Slot) : Finset ValidatorIndex :=
  E.crossingHonestPre lo mid es \ crossingParentPre cfg E store bs b mid es

/-- The weak (fresh) crossing pre-region is a subset of the strong one:
dropping the freshness conjunct only shrinks `FreshParentStuck` inside
`ParentStuck`. -/
theorem crossingParentPre_subset_strong {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} {mid es : Slot} :
    crossingParentPre cfg E store bs b mid es ⊆ E.crossingParentPre cfg store bs b mid es :=
  Finset.sdiff_subset_sdiff (FreshParentStuck_subset_ParentStuck cfg) (Finset.Subset.refl _)

/-- Dually, the strong old-sibling pre mass is a subset of the weak one:
subtracting a smaller set (the weak parent-pre) leaves a bigger difference. -/
theorem crossingXPre_superset_strong {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} {lo mid es : Slot} :
    E.crossingXPre cfg store bs b lo mid es ⊆ crossingXPre cfg E store bs b lo mid es :=
  Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (crossingParentPre_subset_strong cfg)

/-- Weak twin of `CrossingCert.crossing_parentPre_subset_honestPre`, over
`Weak.FreshParentStuck`/`mem_FreshParentSupport`. -/
theorem crossing_parentPre_subset_honestPre {E : Execution Root}
    {obs : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root} {es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext obs n) - 1)
    (hbcur : ((E.store cfg ext obs n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs n)) :
    crossingParentPre cfg E (E.store cfg ext obs n) bs b
        ((E.store cfg ext obs n).blocks b).slot es
      ⊆ E.crossingHonestPre
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es := by
  intro i hi
  have hi' : i ∈ FreshParentStuck cfg E (E.store cfg ext obs n) bs b \
      E.span_committee ((E.store cfg ext obs n).blocks b).slot es := by
    simpa only [crossingParentPre] using hi
  obtain ⟨hiP, hiNotSub⟩ := Finset.mem_sdiff.mp hi'
  have hiRaw := (mem_FreshParentSupport cfg (Finset.mem_filter.mp hiP).1).1
  have hhigh : ((E.store cfg ext obs n).blocks b).slot - 1 ≤ es := by
    rw [hes]
    exact Nat.sub_le_sub_right hbcur 1
  have hiFull := E.span_committee_mono
    (((E.store cfg ext obs n).blocks
      ((E.store cfg ext obs n).blocks b).parent_root).slot + 1) hhigh hiRaw
  simp only [Execution.crossingHonestPre, Execution.crossingPreRegion, Finset.mem_filter,
    Finset.mem_sdiff]
  exact ⟨⟨hiFull, hiNotSub⟩, (Finset.mem_filter.mp hiP).2⟩

/-- Weak twin of `CrossingCert.crossing_hMU_of_canonicalPre`: the sub-window
ledger partition plus `Weak.crossingParentPre`, `Weak.crossingXPre`, and
`crossingByzPre` is exactly the full-window committee union, over the fresh
parent-pre geometry. -/
theorem crossing_hMU_of_canonicalPre {E : Execution Root} (hbb : ByzantineBound cfg E)
    {obs : ValidatorIndex} {n : ℕ} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hes : es = get_current_slot cfg (E.store cfg ext obs n) - 1)
    (hslotlt : ((E.store cfg ext obs n).blocks
        ((E.store cfg ext obs n).blocks b).parent_root).slot <
      ((E.store cfg ext obs n).blocks b).slot)
    (hbcur : ((E.store cfg ext obs n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext obs n))
    (hloH : E.SlotWithinHorizon cfg
      (((E.store cfg ext obs n).blocks
        ((E.store cfg ext obs n).blocks b).parent_root).slot + 1))
    (hesH : E.SlotWithinHorizon cfg es) :
    let lo := ((E.store cfg ext obs n).blocks
      ((E.store cfg ext obs n).blocks b).parent_root).slot + 1
    let mid := ((E.store cfg ext obs n).blocks b).slot
    (E.Sval cfg ext obs n b mid es + E.Aval cfg ext obs n b mid es
        + E.Xval cfg ext obs n b mid es + E.Bval mid es)
      + (E.weight (crossingParentPre cfg E (E.store cfg ext obs n) bs b mid es)
        + E.weight (crossingXPre cfg E (E.store cfg ext obs n) bs b lo mid es)
        + E.weight (E.crossingByzPre lo mid es))
      ≤ estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) lo es := by
  dsimp only
  have hparent := crossing_parentPre_subset_honestPre (bs := bs) cfg ext hes hbcur
  have hhonest := E.weight_add_sdiff hparent
  have hpre := E.weight_split_honest (E.crossingPreRegion
    (((E.store cfg ext obs n).blocks
      ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
    ((E.store cfg ext obs n).blocks b).slot es)
  have hlo : ((E.store cfg ext obs n).blocks
      ((E.store cfg ext obs n).blocks b).parent_root).slot + 1
      ≤ ((E.store cfg ext obs n).blocks b).slot := hslotlt
  rw [← E.weight_partition cfg ext obs n b
    ((E.store cfg ext obs n).blocks b).slot es]
  rw [show E.weight (crossingParentPre cfg E (E.store cfg ext obs n) bs b
          ((E.store cfg ext obs n).blocks b).slot es)
        + E.weight (crossingXPre cfg E (E.store cfg ext obs n) bs b
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es)
      = E.weight (E.crossingHonestPre
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es) by
        simpa only [crossingXPre] using hhonest]
  rw [show E.weight (E.crossingHonestPre
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es)
        + E.weight (E.crossingByzPre
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es)
      = E.weight (E.crossingPreRegion
          (((E.store cfg ext obs n).blocks
            ((E.store cfg ext obs n).blocks b).parent_root).slot + 1)
          ((E.store cfg ext obs n).blocks b).slot es) by
        simpa only [Execution.crossingHonestPre, Execution.crossingByzPre] using hpre.symm]
  exact E.crossing_hMU_of_preRegion cfg hbb htab hlo hloH hesH

/-- Weak twin of `CrossingCert.crossing_hd_of_preRegion`, driven by
`Weak.support_discount_le_fresh_parent_stuck_of_prefix` — no `hne`
(no-honest-equivocator) premise, since the weak discount already has no
equivocation apparatus. Replaces `crossing_hd_of_preRegion_of_prefix`. -/
theorem crossing_hd_of_preRegion_of_prefix {E : Execution Root}
    (hbb : ByzantineBound cfg E)
    {obs : ValidatorIndex} {n : ℕ}
    (hcomm : E.PrefixCommitteeAgreement cfg ext (E.store cfg ext obs n))
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext obs n).blocks
        ((E.store cfg ext obs n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext obs n).blocks b).slot)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (mid es : Slot) :
    Weak.get_support_discount cfg ext (E.store cfg ext obs n) bs b
      ≤ E.weight (crossingParentPre cfg E (E.store cfg ext obs n) bs b mid es)
        + E.weight (crossingParentSub cfg E (E.store cfg ext obs n) bs b mid es) := by
  have hd := support_discount_le_fresh_parent_stuck_of_prefix cfg ext hbb hcomm hval
    hstartH hbH htab
  have hdiff :
      FreshParentStuck cfg E (E.store cfg ext obs n) bs b \
          (FreshParentStuck cfg E (E.store cfg ext obs n) bs b ∩ E.span_committee mid es)
        = FreshParentStuck cfg E (E.store cfg ext obs n) bs b \ E.span_committee mid es := by
    ext i
    simp
  have hsplit := E.weight_add_sdiff
    (Finset.inter_subset_left :
      FreshParentStuck cfg E (E.store cfg ext obs n) bs b ∩ E.span_committee mid es
        ⊆ FreshParentStuck cfg E (E.store cfg ext obs n) bs b)
  rw [hdiff] at hsplit
  calc
    Weak.get_support_discount cfg ext (E.store cfg ext obs n) bs b
        ≤ E.weight (FreshParentStuck cfg E (E.store cfg ext obs n) bs b) := hd
    _ = E.weight (crossingParentPre cfg E (E.store cfg ext obs n) bs b mid es)
          + E.weight (crossingParentSub cfg E (E.store cfg ext obs n) bs b mid es) := by
            simpa only [crossingParentPre, crossingParentSub, add_comm] using hsplit.symm

/-- **Replaces `hR4b_of_confinement(_of_prefix)`.** With `eqSub := 0` this is a
pure subset argument: fresh byz supporters are non-honest span members. -/
theorem freshByzSupporters_le_Bval {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {b : Root} (hval : bs.validators = E.registry)
    {mid es : Slot}
    (hspan : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee mid es) :
    (((FreshAttSupporters cfg store (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum + 0
      ≤ E.Bval mid es := by
  rw [Nat.add_zero, fresh_byz_score_eq_weight cfg hval]
  simp only [Execution.Bval, Execution.Bwin]
  apply E.weight_mono
  intro i hi
  rw [List.mem_toFinset, List.mem_filter] at hi
  have hnh : i ∉ E.honest := of_decide_eq_true hi.2
  exact Finset.mem_filter.mpr ⟨hspan i (mem_AttSupporters_of_mem_fresh cfg hi.1) hnh, hnh⟩

/-! ## 2. The full-span weak adversarial guard (both regimes collapse to an
equality, `F3`) -/

/-- **Both regimes at once: the weak budget equals the raw span estimate, so
`hAguard` is an equality with `eqSub = eqExtra = 0`.** Intra-epoch case. -/
theorem adversarial_guard_intra {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hintra : get_block_epoch cfg store b =
      get_block_epoch cfg store (store.blocks b).parent_root)
    (hes : es = get_current_slot cfg store - 1)
    (hmidH : E.SlotWithinHorizon cfg (store.blocks b).slot)
    (hesH : E.SlotWithinHorizon cfg es) :
    E.Jspec (store.blocks b).slot es + E.Bval (store.blocks b).slot es ≤
        100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) (store.blocks b).slot es / 100) ∧
      estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) (store.blocks b).slot es / 100
          * cfg.confirmation_byzantine_threshold
        ≤ Weak.get_adversarial_weight cfg store bs b + 0 + 0 := by
  subst es
  have hnot : ¬ (get_block_epoch cfg store b >
      get_block_epoch cfg store (store.blocks b).parent_root) := by
    intro hgt
    rw [hintra] at hgt
    exact (Nat.lt_irrefl _ hgt)
  constructor
  · rw [E.Jspec_add_Bval_eq_weight_span]
    exact E.weight_span_le_estimate cfg hbb htab _ _ hmidH hesH
  · rw [Weak.get_adversarial_weight_eq, if_neg hnot, Weak.compute_adversarial_weight_eq]
    simp

/-- Crossing-branch counterpart of `adversarial_guard_intra`, over
`sa := compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)`. -/
theorem adversarial_guard_crossing {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {es : Slot}
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hcross : get_block_epoch cfg store b >
      get_block_epoch cfg store (store.blocks b).parent_root)
    (hes : es = get_current_slot cfg store - 1)
    (hsaH : E.SlotWithinHorizon cfg
      (compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)))
    (hesH : E.SlotWithinHorizon cfg es) :
    let sa := compute_start_slot_at_epoch cfg (get_block_epoch cfg store b)
    E.Jspec sa es + E.Bval sa es ≤
        100 * (estimate_committee_weight_between_slots cfg
          (get_total_active_balance cfg bs) sa es / 100) ∧
      estimate_committee_weight_between_slots cfg
            (get_total_active_balance cfg bs) sa es / 100
          * cfg.confirmation_byzantine_threshold
        ≤ Weak.get_adversarial_weight cfg store bs b + 0 + 0 := by
  subst es
  dsimp only
  constructor
  · rw [E.Jspec_add_Bval_eq_weight_span]
    exact E.weight_span_le_estimate cfg hbb htab _ _ hsaH hesH
  · rw [Weak.get_adversarial_weight_eq, if_pos hcross, Weak.compute_adversarial_weight_eq]
    simp

/-! ## 3. The overlap-part discount charge, at the honest endpoint -/

/-- The endpoint form of `crossingParentSub_le_endpoint_Aval_minimal`, over
the fresh parent-stuck set: the overlap part of the weak confirmation discount
is already present in the endpoint ancestor class. The proof does not
transport a generic `Aclass` membership (invalid across `lo`); instead it
places the member into `Aclass w m b (parent.slot+1) es`
(`Weak.freshParentStuck_subset_endpoint_Aclass`) and swaps in the sharper span
membership `crossingParentSub` already supplies at `mid`, since `SupportsDesc`/
`AncestorOrVoteless` do not depend on the lower window bound. -/
private theorem crossingParentSub_le_endpoint_Aval {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} (hqH : E.WithinHorizon cfg q)
    {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hbQ : b ∈ (E.store cfg ext obs q).block_roots)
    (hpQ : ((E.store cfg ext obs q).blocks b).parent_root ∈
      (E.store cfg ext obs q).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext obs q)) (E.store cfg ext obs q))
    (hsched : SchedLMProv E cfg (E.store cfg ext obs q))
    {es : Slot}
    (hes : es = get_current_slot cfg (E.store cfg ext obs q) - 1)
    (hesq : es < E.slot_at cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (haM : ((E.store cfg ext obs q).blocks b).parent_root ∈ (E.store cfg ext w m).block_roots)
    (hbM : b ∈ (E.store cfg ext w m).block_roots)
    (hparentM : ((E.store cfg ext w m).blocks b).parent_root =
      ((E.store cfg ext obs q).blocks b).parent_root) :
    E.weight (crossingParentSub cfg E (E.store cfg ext obs q) bs b
        ((E.store cfg ext obs q).blocks b).slot es)
      ≤ E.Aval cfg ext w m b ((E.store cfg ext obs q).blocks b).slot es := by
  obtain ⟨ast, ablk, hgeq, hslot, hparentne⟩ := hA.genesis
  have hlo0 : E.slot_at cfg 0 ≤ ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks b).parent_root).slot + 1 := by
    have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
      have ht := E.store_current_slot cfg ext obs 0
      rw [show E.store cfg ext obs 0 = E.genesis_store from rfl, hgeq,
        get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
      rw [← ht, hslot]
    have hanchorP : ablk.message.slot ≤ ((E.store cfg ext obs q).blocks
        ((E.store cfg ext obs q).blocks b).parent_root).slot :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hslot hparentne obs q _ hpQ
    rw [hcur0]
    exact hanchorP.trans (Nat.le_succ _)
  have hAclassLo := freshParentStuck_subset_endpoint_Aclass cfg ext hA hqH
    (a := ((E.store cfg ext obs q).blocks b).parent_root) hval hpQ hbQ rfl hprov hsched
    hlo0 (le_refl _) hes hesq hw hmH hslotQM haM hbM hparentM
  rw [Execution.Aval]
  apply E.weight_mono
  intro i hi
  have hi' : i ∈ FreshParentStuck cfg E (E.store cfg ext obs q) bs b ∩
      E.span_committee ((E.store cfg ext obs q).blocks b).slot es := by
    simpa only [crossingParentSub] using hi
  obtain ⟨hiP, hiS⟩ := Finset.mem_inter.mp hi'
  have hia := hAclassLo hiP
  simp only [Execution.Aclass, Finset.mem_filter] at hia ⊢
  exact ⟨⟨hiS, hia.1.2⟩, hia.2⟩

end Weak

end FastConfirmation.Spec
