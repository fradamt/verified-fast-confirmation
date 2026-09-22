module
public import FastConfirmation.Spec.Proof.Ledger
public import FastConfirmation.Spec.Proof.EngineStore
public import FastConfirmation.Spec.Proof.Bridge
public import FastConfirmation.Spec.Proof.Forks

@[expose] public section

/-!
# Spec / Proof / Endpoint: ledger inequality ⟹ head descent at `(w, m)`

This module consumes the per-`σ` ledger inequality

  `E.Xval + E.Bval + get_proposer_score store + 1 ≤ E.Sval`

(the `Ledger.lean` ground-class accessors for the certificate block `b′` over its
window `[lo, σ]`; the shell derives it from `INVstar` by stripping the `(100−C)`
factor and the `min`, and from `Base.weak_base_discharged` / boost congruence) and
produces the fork-choice head descent at every honest store `(w, m)`.

The endpoint uses the following components:

* **`recorded_bside_ge`** — the `b′`-side child's recorded
  attestation score at `(w, m)` is at least `Sval`, via
  `MajorityPersists.recorded_support_lower` with `HS := Sclass`. The
  ground-class → `AttSupporters` membership is the transport fact
  (`EngineTransport.HS0_in_AttSupporters` / `NewVoters_in_AttSupporters` shape),
  taken as a hypothesis the shell supplies.
* **`recorded_sibling_le`** — a sibling's recorded score is at
  most `Xval + Bval`, via `MajorityPersists.attestation_score_eq_weight` +
  `weight_union_le`. The honest confinement (recorded supporters of a sibling are
  in `Xclass` — `Bridge` + `Forks.siblings_incompatible`) and the byz confinement
  (`Bwin` window membership) are taken as hypotheses (store-dynamics; shell).
* **`pending_status_selected_of_margin`** — the payload-status score margin
  selects the child bid's resolved parent, using the Gloas tie breaker when
  both previous-slot payload decisions have zero weight.
* **`ghost_step_dominates`** — the ledger plus the two recorded
  bounds give `get_weight (c̃) < get_weight (c)` for every sibling, via
  `MajorityPersists.fork_weight_lt`; `ledger_descendStep` packages this into an
  `EngineStore.DescendStep`.
* **`head_descends_of_ledger`** — an `EngineStore.DescendStep`
  chain from the justified root down to `b` (each fork's step built from a
  per-`b′` `ledger_descendStep`) forces the head to descend from `b` under the
  filter-containment hypotheses of `EngineStore.is_ancestor_get_head_of_chain`.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The `b′`-side child's recorded score dominates `Sval`

Set-weight subadditivity over a union (`EngineWindows.weight_union_le`, reused for
the sibling bound below) and the recorded-support machinery of `MajorityPersists`
are the only ingredients. -/

/-- **Recorded `b′`-side lower bound.** At a registry-constant balance source `bs`,
the fork child `c`'s attestation score at `store` is at least `Sval σ` — the
ground weight of the honest window members whose newest vote supports
`subtree(b′)` — provided every such member records a `c`-supporting latest message
at `store` (`hSmem`, the transport fact the shell supplies via
`EngineTransport.HS0_in_AttSupporters` / `NewVoters_in_AttSupporters`). Direct
`MajorityPersists.recorded_support_lower` with `HS := Sclass`. -/
theorem recorded_bside_ge {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c : Root} {lo σ : Slot}
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs) :
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c) bs := by
  rw [Execution.Sval]
  exact recorded_support_lower cfg hval (E.Sclass cfg ext v₀ n₀ b' lo σ) hSmem

/-! ## A sibling's recorded score is at most `Xval + Bval` -/

/-- **Recorded sibling upper bound.** At a registry-constant balance source `bs`,
the recorded attestation score of a sibling `cc` (of `parent(b′)`, `cc ≠` the
`b′`-side child) is at most `Xval σ + Bval σ`. Its supporter set splits into an
honest part confined to `Xclass` (recorded supporters of a sibling neither support
`subtree(b′)` nor are `b′`-ancestors — `Bridge` + `Forks.siblings_incompatible`,
supplied as `hHon`) and a byz part confined to the window enemy set `Bwin`
(window confinement, supplied as `hByz`);
`MajorityPersists.attestation_score_eq_weight` turns the score into that supporter
set's weight and `weight_union_le` weighs the confinement. -/
theorem recorded_sibling_le {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' cc : Root} {lo σ : Slot}
    (hHon : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∉ E.honest → i ∈ E.Bwin lo σ) :
    get_attestation_score cfg store (get_node_for_root cc) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ := by
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Bval]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  intro i hi
  rw [List.mem_toFinset] at hi
  rw [Finset.mem_union]
  by_cases hh : i ∈ E.honest
  · exact Or.inl (hHon i hi hh)
  · exact Or.inr (hByz i hi hh)

/-! ## The ancestor slice of the opposite payload branch -/

/-- Honest ancestor-class voters recorded for the opposite resolved payload
status. Intersecting with `Aclass` keeps this class disjoint from `Xclass`;
opposite-status votes below a sibling belong to `Xclass` already. -/
noncomputable def OppositeAncestorClass (E : Execution Root)
    (store : Store Root) (bs : BeaconState Root)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' h : Root) (lo σ : Slot)
    (other : PayloadStatus) : Finset ValidatorIndex :=
  (E.Aclass cfg ext v₀ n₀ b' lo σ) ∩
    (AttSupporters cfg store (ForkChoiceNode.mk h other) bs).toFinset

/-- The missing payload class is disjoint from the root-ledger's sibling class. -/
theorem oppositeAncestorClass_disjoint_Xclass {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo σ : Slot}
    {other : PayloadStatus} :
    Disjoint (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other)
      (E.Xclass cfg ext v₀ n₀ b' lo σ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hiO hiX
  have hiA : i ∈ E.Aclass cfg ext v₀ n₀ b' lo σ :=
    (Finset.mem_inter.mp hiO).1
  simp only [Execution.Aclass, Execution.Xclass, Finset.mem_filter] at hiA hiX
  exact hiX.2.2 hiA.2.2

/-- At the confirming store, opposite ancestor votes and matching parent
votes consume separate parts of the ancestor-class weight. -/
theorem oppositeAncestorClass_plus_matching_le_Aval {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo σ : Slot}
    {other : PayloadStatus} {G : Finset ValidatorIndex}
    (hG : G ⊆ E.Aclass cfg ext v₀ n₀ b' lo σ)
    (hdisj : Disjoint G
      (AttSupporters cfg store (ForkChoiceNode.mk h other) bs).toFinset) :
    E.weight G +
        E.weight (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other)
      ≤ E.Aval cfg ext v₀ n₀ b' lo σ := by
  classical
  have hO : OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other
      ⊆ E.Aclass cfg ext v₀ n₀ b' lo σ := Finset.inter_subset_left
  have hGO : Disjoint G
      (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other) :=
    hdisj.mono_right Finset.inter_subset_right
  rw [Execution.Aval]
  change (∑ i ∈ G, E.weight_of i) +
      (∑ i ∈ OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other,
        E.weight_of i) ≤
      E.weight (E.Aclass cfg ext v₀ n₀ b' lo σ)
  rw [← Finset.sum_union hGO]
  exact E.weight_mono (Finset.union_subset hG hO)

private theorem opposite_weight_add_sdiff {E : Execution Root}
    {A B : Finset ValidatorIndex} (h : A ⊆ B) :
    E.weight A + E.weight (B \ A) = E.weight B := by
  simp only [Execution.weight]
  rw [add_comm]
  exact Finset.sum_sdiff h

/-- Split the source opposite ancestor slice at the V-region boundary. The
pre-region part and the matching-parent discount class are disjoint parts of
the remaining ancestor weight. -/
theorem oppositeAncestorClass_region_split {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo sa es : Slot}
    {other : PayloadStatus} {G : Finset ValidatorIndex}
    (hlo : lo ≤ sa)
    (hG : G ⊆ E.Aclass cfg ext v₀ n₀ b' lo es \
      E.Aclass cfg ext v₀ n₀ b' sa es)
    (hdisj : Disjoint G
      (AttSupporters cfg store (ForkChoiceNode.mk h other) bs).toFinset) :
    let O := OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo es other
    let V := E.Aclass cfg ext v₀ n₀ b' sa es
    let P := E.Aclass cfg ext v₀ n₀ b' lo es \ V
    E.weight (O ∩ V) + E.weight (O ∩ P) = E.weight O ∧
    E.weight (V \ O) + E.weight (O ∩ V) = E.Aval cfg ext v₀ n₀ b' sa es ∧
    E.weight G + E.weight (O ∩ P) + E.weight (P \ (G ∪ (O ∩ P))) = E.weight P := by
  classical
  dsimp
  let O := OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo es other
  let V := E.Aclass cfg ext v₀ n₀ b' sa es
  let A := E.Aclass cfg ext v₀ n₀ b' lo es
  let P := A \ V
  have hspan : E.span_committee sa es ⊆ E.span_committee lo es := by
    intro i hi
    simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hi ⊢
    obtain ⟨t, ⟨ht, hte⟩, hit⟩ := hi
    exact ⟨t, ⟨le_trans hlo ht, hte⟩, hit⟩
  have hVA : V ⊆ A := by
    simp only [V, A, Execution.Aclass]
    exact Finset.filter_subset_filter _ (Finset.filter_subset_filter _ hspan)
  have hOA : O ⊆ A := Finset.inter_subset_left
  have hOP : O ∩ P ⊆ P := Finset.inter_subset_right
  have hOV : O ∩ V ⊆ V := Finset.inter_subset_right
  have hGO : Disjoint G O := hdisj.mono_right Finset.inter_subset_right
  have hGP : G ⊆ P := hG
  have hPdisj : Disjoint G (O ∩ P) := hGO.mono_right Finset.inter_subset_left
  have hsplit : O ∩ V ∪ O ∩ P = O := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hiO, _⟩ | ⟨hiO, _⟩) <;> exact hiO
    · intro hiO
      by_cases hiV : i ∈ V
      · exact Or.inl ⟨hiO, hiV⟩
      · exact Or.inr ⟨hiO, Finset.mem_sdiff.mpr ⟨hOA hiO, hiV⟩⟩
  have hOVP : Disjoint (O ∩ V) (O ∩ P) := by
    apply Finset.disjoint_left.mpr
    intro i hiV hiP
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hiP).2).2 (Finset.mem_inter.mp hiV).2
  constructor
  · simp only [Execution.weight]
    rw [← Finset.sum_union hOVP, hsplit]
  constructor
  · have hdiff : V \ (O ∩ V) = V \ O := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have h := opposite_weight_add_sdiff (E := E) hOV
    simpa only [hdiff, add_comm, Execution.Aval] using h
  · have hU : G ∪ (O ∩ P) ⊆ P := Finset.union_subset hGP hOP
    have hsplitP := opposite_weight_add_sdiff (E := E) hU
    have hsum : E.weight (G ∪ (O ∩ P)) =
        E.weight G + E.weight (O ∩ P) := by
      simp only [Execution.weight]
      exact Finset.sum_union hPdisj
    rw [hsum] at hsplitP
    exact hsplitP

/-- Confirmation arithmetic with the ancestor class charged once. The
matching-parent discount funds `G`; the remaining ancestor weight funds the
opposite branch's ancestor votes. -/
theorem confirmed_ancestor_strip_arith
    {M P H d S A X B G O : ℕ}
    (hconf : M + P + 1 ≤ 2 * H + d)
    (hchild : H ≤ S)
    (hdiscount : d ≤ G)
    (hancestor : G + O ≤ A)
    (hpartition : S + A + X + B ≤ M) :
    X + B + P + O + 1 ≤ S := by omega

/-- The root-ledger partition and the complete Byzantine window fit inside
the spec's committee estimate. -/
theorem ledger_partition_le_estimate {E : Execution Root}
    (hbb : ByzantineBound cfg E) {lo σ : Slot}
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} :
    E.Sval cfg ext v₀ n₀ b' lo σ +
        E.Aval cfg ext v₀ n₀ b' lo σ +
        E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ ≤
      estimate_committee_weight_between_slots cfg (E.total_active cfg) lo σ := by
  have hsplit : E.Jspec lo σ + E.Bval lo σ = E.weight (E.span_committee lo σ) := by
    simp only [Execution.Jspec, Execution.Bval, Execution.Bwin, Execution.weight]
    exact Finset.sum_filter_add_sum_filter_not (E.span_committee lo σ)
      (fun i => i ∈ E.honest) E.weight_of
  rw [← E.weight_partition cfg ext v₀ n₀ b' lo σ]
  rw [hsplit]
  exact hbb.estimate_sound lo σ hloH hσH

/-- The corrected source-store strip. Its `G` class is the honest matching
parent support and its `O` class is only the ancestor slice of the complete
opposite score. Every remaining opposite supporter is paid by `X` or `B`. -/
theorem confirmed_ancestor_strip_at_source {E : Execution Root}
    (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo σ : Slot}
    {other : PayloadStatus} {G : Finset ValidatorIndex}
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hmajor :
      estimate_committee_weight_between_slots cfg (E.total_active cfg) lo σ +
        compute_proposer_score cfg bs + 1 ≤
          2 * (((AttSupporters cfg store (get_node_for_root b') bs).filter
            (fun i => i ∈ E.honest)).map
              (fun i => (bs.validators.getD i default).effective_balance)).sum +
          get_support_discount cfg ext store bs b')
    (hchild :
      (((AttSupporters cfg store (get_node_for_root b') bs).filter
        (fun i => i ∈ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
        E.Sval cfg ext v₀ n₀ b' lo σ)
    (hdiscount : get_support_discount cfg ext store bs b' ≤ E.weight G)
    (hG : G ⊆ E.Aclass cfg ext v₀ n₀ b' lo σ)
    (hdisj : Disjoint G
      (AttSupporters cfg store (ForkChoiceNode.mk h other) bs).toFinset) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ +
        compute_proposer_score cfg bs +
        E.weight (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other) + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hA := oppositeAncestorClass_plus_matching_le_Aval cfg ext hG hdisj
  have hpartition := ledger_partition_le_estimate cfg ext hbb hloH hσH
    (v₀ := v₀) (n₀ := n₀) (b' := b')
  exact confirmed_ancestor_strip_arith hmajor hchild hdiscount hA hpartition

/-- The actual confirmation fact supplies the corrected ancestor strip at
the confirming store. The child and matching-parent inclusions are the
existing `Bridge` ground-vote lemmas. -/
theorem confirmed_ancestor_strip_of_rule {E : Execution Root}
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {c : Root} (other : PayloadStatus)
    (hval : bs.validators = E.registry)
    (hloH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks c).parent_root).slot + 1))
    (hcH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks c).slot)
    (hesH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1))
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hneEquiv : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest)
    (hbyz : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root c) bs).filter
        (fun i => i ∉ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs c)
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs c = true)
    (hother : other ≠ .pending)
    (hneStatus : other ≠ get_parent_payload_status
      (E.store cfg ext v n) ((E.store cfg ext v n).blocks c))
    (hchild :
      (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root c) bs).filter
        (fun i => i ∈ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
        E.Sval cfg ext v n c
          (((E.store cfg ext v n).blocks
            ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v n) - 1))
    (hG : ParentPayloadStuck cfg E (E.store cfg ext v n) bs c ⊆
      E.Aclass cfg ext v n c
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1)) :
    E.Xval cfg ext v n c
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) +
      E.Bval
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) +
      compute_proposer_score cfg bs +
      E.weight (OppositeAncestorClass cfg ext E (E.store cfg ext v n) bs v n c
        ((E.store cfg ext v n).blocks c).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) other) + 1 ≤
      E.Sval cfg ext v n c
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) := by
  have hmajor := honest_support_majority_of_byz_le cfg ext hconf hbyz
  rw [htab] at hmajor
  have hdiscount := support_discount_le_matching_parent_stuck cfg ext
    hec hbb hv hnH hval hloH hcH htab hneEquiv
  have hdisj := parentPayloadStuck_disjoint_oppositeStatus cfg E
    (E.store cfg ext v n) bs c other hother hneStatus
  exact confirmed_ancestor_strip_at_source cfg ext hbb hloH hesH
    hmajor hchild hdiscount hG hdisj

/-- The corrected source strip with both ground-vote inclusions discharged.
The same provenance and vote domination facts already used by the root ledger
place honest child supporters in `Sclass` and matching parent voters in
`Aclass`. -/
theorem confirmed_ancestor_strip_from_execution {E : Execution Root}
    (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {c : Root} (other : PayloadStatus)
    (hval : bs.validators = E.registry)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈
        (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    (hc : c ∈ (E.store cfg ext v n).block_roots)
    (hp : ((E.store cfg ext v n).blocks c).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root c) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks c).slot lm.root)
    (hdom : E.RecordedEpochMax cfg ext v n
      (get_current_slot cfg (E.store cfg ext v n) - 1))
    (hloH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks c).parent_root).slot + 1))
    (hcH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks c).slot)
    (hesH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1))
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hneEquiv : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest)
    (hbyz : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root c) bs).filter
        (fun i => i ∉ E.honest)).map
          (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs c)
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs c = true)
    (hother : other ≠ .pending)
    (hneStatus : other ≠ get_parent_payload_status
      (E.store cfg ext v n) ((E.store cfg ext v n).blocks c)) :
    E.Xval cfg ext v n c
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) +
      E.Bval
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) +
      compute_proposer_score cfg bs +
      E.weight (OppositeAncestorClass cfg ext E (E.store cfg ext v n) bs v n c
        ((E.store cfg ext v n).blocks c).parent_root
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) other) + 1 ≤
      E.Sval cfg ext v n c
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks c).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) := by
  let store := E.store cfg ext v n
  let lo := (store.blocks (store.blocks c).parent_root).slot + 1
  let es := get_current_slot cfg store - 1
  have hslotlt := hwf c hc hp
  have hcutoff := confirmed_block_slot_le_cutoff cfg ext hwf hprov hwalk hconf
  have hcur : (store.blocks c).slot ≤ get_current_slot cfg store := by
    change (store.blocks c).slot ≤ es at hcutoff
    exact hcutoff.trans (Nat.sub_le _ _)
  have hanc : is_ancestor store (get_node_for_root c)
      (get_node_for_root (store.blocks c).parent_root) = true :=
    is_ancestor_of_parent hwf hc hp rfl
  have hchild := E.honest_supporters_sum_le_Sval cfg ext hhb hec hgen
    hwf hprov hval (lo := lo) (es := es) rfl rfl hslotlt hwalk hdom
  have hParent := E.ParentStuck_subset_Aclass cfg ext hhb hec hgen
    hprov (bs := bs) (lo := lo) (es := es) rfl rfl hslotlt hcur hanc hdom
  have hG : ParentPayloadStuck cfg E store bs c ⊆
      E.Aclass cfg ext v n c lo es := by
    apply Finset.Subset.trans ?_ hParent
    intro i hi
    simp only [ParentPayloadStuck, ParentPayloadSupport,
      ParentStuck, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1.1, hi.2⟩
  exact confirmed_ancestor_strip_of_rule cfg ext hec hbb hv hnH other
    hval hloH hcH hesH htab hneEquiv hbyz hconf hother hneStatus hchild hG

/-- A supporter of the opposite resolved parent cannot also support its child
when the child's supporters select the required resolved parent. -/
theorem opposite_supporter_excludes_child {store : Store Root} {bs : BeaconState Root}
    {h c : Root} {selected other : PayloadStatus} {i : ValidatorIndex}
    {lm : LatestMessage Root}
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected)
    (hopp : i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs)
    (hlm : store.latest_messages i = some lm)
    (hc : is_ancestor store (get_supported_node store lm)
      (get_node_for_root c) = true)
    (hchildSubset : (AttSupporters cfg store (get_node_for_root c) bs).toFinset ⊆
      (AttSupporters cfg store (ForkChoiceNode.mk h selected) bs).toFinset) :
    False := by
  have hiC : i ∈ AttSupporters cfg store (get_node_for_root c) bs :=
    mem_AttSupporters_of cfg (AttSupporters_active cfg hopp)
      (AttSupporters_unslashed cfg hopp) hlm (mem_AttSupporters cfg hopp).choose_spec.2.1 hc
  have hiSel := List.mem_toFinset.mp
    (hchildSubset (List.mem_toFinset.mpr hiC))
  obtain ⟨lmS, hlmS, _, hs⟩ := mem_AttSupporters cfg hiSel
  obtain ⟨lmO, hlmO, _, ho⟩ := mem_AttSupporters cfg hopp
  have hS : lmS = lm := Option.some.inj (hlmS.symm.trans hlm)
  have hO : lmO = lm := Option.some.inj (hlmO.symm.trans hlm)
  subst lmS
  subst lmO
  exact not_ancestor_two_resolved_statuses store
    (get_supported_node store lm) h selected other hselected hother hne ⟨hs, ho⟩

/-- Every opposite-status supporter is paid by the old sibling class, the
non-honest window, or the ancestor slice. -/
theorem recorded_opposite_status_le {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo σ : Slot}
    {other : PayloadStatus}
    (hHon : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ ∨
          i ∈ E.Aclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∉ E.honest → i ∈ E.Bwin lo σ) :
    get_attestation_score cfg store (ForkChoiceNode.mk h other) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ +
        E.weight (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other) := by
  classical
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Bval]
  have hsub : (AttSupporters cfg store (ForkChoiceNode.mk h other) bs).toFinset ⊆
      (E.Xclass cfg ext v₀ n₀ b' lo σ ∪ E.Bwin lo σ) ∪
        OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other := by
    intro i hi
    have hi' := List.mem_toFinset.mp hi
    by_cases hh : i ∈ E.honest
    · rcases hHon i hi' hh with hX | hA
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hX)))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hA, hi⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr (hByz i hi' hh))))
  exact (E.weight_mono hsub).trans
    ((weight_union_le _ _).trans
      (Nat.add_le_add_right (weight_union_le _ _) _))

/-- The opposite-score bound follows from the recorded child bridge and the
payload-aware parent ancestry bridge. It needs only window confinement for
the opposite voters; all honest class geometry is proved here. -/
theorem recorded_opposite_status_le_of_child {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root}
    (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot}
    {selected other : PayloadStatus}
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected)
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs)
    (hchildSubset : (AttSupporters cfg store (get_node_for_root c) bs).toFinset ⊆
      (AttSupporters cfg store (ForkChoiceNode.mk h selected) bs).toFinset)
    (hspan : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∈ E.honest → i ∈ E.span_committee lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∉ E.honest → i ∈ E.Bwin lo σ) :
    get_attestation_score cfg store (ForkChoiceNode.mk h other) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ +
        E.weight (OppositeAncestorClass cfg ext E store bs v₀ n₀ b' h lo σ other) := by
  have hHon : ∀ i ∈ AttSupporters cfg store (ForkChoiceNode.mk h other) bs,
      i ∈ E.honest →
        i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ ∨
          i ∈ E.Aclass cfg ext v₀ n₀ b' lo σ := by
    intro i hiOpp hiHon
    have hnotS : i ∉ E.Sclass cfg ext v₀ n₀ b' lo σ := by
      intro hiS
      have hiSelected := List.mem_toFinset.mp
        (hchildSubset (List.mem_toFinset.mpr (hSmem i hiS)))
      obtain ⟨lm, hlm, _, hs⟩ := mem_AttSupporters cfg hiSelected
      obtain ⟨lm', hlm', _, ho⟩ := mem_AttSupporters cfg hiOpp
      have heq : lm = lm' := Option.some.inj (hlm.symm.trans hlm')
      cases heq
      exact not_ancestor_two_resolved_statuses store
        (get_supported_node store lm) h selected other hselected hother hne
        ⟨hs, ho⟩
    have hiSpan := hspan i hiOpp hiHon
    have hnotDesc : ¬ E.SupportsDesc cfg ext v₀ n₀ b' σ i := by
      intro hDesc
      apply hnotS
      simp only [Execution.Sclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hiHon⟩, hDesc⟩
    by_cases hAnc : E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i
    · right
      simp only [Execution.Aclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hiHon⟩, hnotDesc, hAnc⟩
    · left
      simp only [Execution.Xclass, Finset.mem_filter]
      exact ⟨⟨hiSpan, hiHon⟩, hnotDesc, hAnc⟩
  exact recorded_opposite_status_le cfg ext hval hHon hByz

/-! ## The GHOST step favours the `b′`-side child -/

/-- Pure-ℕ core of the GHOST step (`Gwei` weights are opaque to `omega`, so the
linear arithmetic is discharged over plain ℕ and `exact`-ed). -/
private theorem ghost_arith {sc scc X B P S : ℕ}
    (hbside : S ≤ sc) (hledger : X + B + P + 1 ≤ S) (hsib : scc ≤ X + B) :
    scc + P < sc := by omega

private theorem ancestor_margin_arith {X B P O S Q R : ℕ}
    (hstrip : X + B + P + O + 1 ≤ S)
    (ho : Q ≤ X + B + O) (hs : S ≤ R) : Q + P < R := by omega

/-- Arithmetic form of the payload contest at confirmation. `d` is paid only
by matching parent votes `G`; `O` contains the opposing payload's recorded
votes, including opposite-status parent votes. The window budget bounds the
disjoint selected, matching-parent, and opposing groups, with `A` available
for non-honest votes. This is the strict branch margin required later. -/
theorem confirmation_payload_margin_arith
    {S d M P A G O : ℕ}
    (hconf : M + P + 2 * A + 1 ≤ 2 * S + d)
    (hdiscount : d ≤ G)
    (hpartition : O + S + G ≤ M + A) :
    O + P < S + G := by omega

/-- The status budget in the form produced by the actual confirmation rule.
`H` is honest child support at confirmation, after the rule's `2 * A` has
paid for Byzantine child support.  `O` is the complete opposite-status score
at the endpoint.  The old selected and matching-parent voters are disjoint
from it, while newly recorded Byzantine votes cost `Bnew`; honest new votes
of at least that weight increase the selected score. -/
theorem confirmed_payload_margin_transport_arith
    {H d M P G O Bnew Hnew selectedScore : ℕ}
    (hconf : M + P + 1 ≤ 2 * H + d)
    (hdiscount : d ≤ G)
    (hbudget : O + H + G ≤ M + Bnew)
    (hnew : Bnew ≤ Hnew)
    (hselected : H + Hnew ≤ selectedScore) :
    O + P < selectedScore := by omega

/-- The confirmation-store form after Byzantine child support is paid by the
rule's adversarial term.  The three disjoint status sets fit in the old
window, so the complete opposite score plus proposer score is below honest
child support even before adding matching parent support. -/
theorem confirmed_payload_source_arith
    {H d M P G O : ℕ}
    (hconf : M + P + 1 ≤ 2 * H + d)
    (hdiscount : d ≤ G)
    (hbudget : O + H + G ≤ M) :
    O + P < H := by omega

/-- The actual Boolean confirmation implies a strict source-store payload
score margin over the opposite resolved status.  Set geometry is supplied by
`recorded_payload_status_budget_le_estimate`; the discount only charges
honest matching-parent votes. -/
theorem confirmed_payload_score_margin_at_source {E : Execution Root}
    (hec : ExternalsCoherence cfg ext E) (hbb : ByzantineBound cfg E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hnH : E.WithinHorizon cfg n)
    {bs : BeaconState Root} {b : Root} (other : PayloadStatus)
    (hval : bs.validators = E.registry)
    (hwf : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈
        (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hp : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hother : other ≠ .pending)
    (hneStatus : other ≠ get_parent_payload_status
      (E.store cfg ext v n) ((E.store cfg ext v n).blocks b))
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hwalk : ∀ i lm, (E.store cfg ext v n).latest_messages i = some lm →
      WalkKnown (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot lm.root ∧
      WalkKnown (E.store cfg ext v n)
        ((E.store cfg ext v n).blocks b).slot lm.root)
    (hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1))
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v n).blocks b).slot)
    (hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1))
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hneEquiv : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest)
    (hbyz : (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext (E.store cfg ext v n) bs b)
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true) :
    get_attestation_score cfg (E.store cfg ext v n)
        (ForkChoiceNode.mk ((E.store cfg ext v n).blocks b).parent_root other) bs
      + compute_proposer_score cfg bs <
      (((AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum := by
  have hmajor := honest_support_majority_of_byz_le cfg ext hconf hbyz
  have hdiscount := support_discount_le_matching_parent_stuck cfg ext
    hec hbb hv hnH hval hstartH hbH htab hneEquiv
  have hbudget := recorded_payload_status_budget_le_estimate cfg ext hbb other
    hwf hb hp hother hneStatus hprov hwalk hstartH hendH htab hconf
  rw [E.honest_score_eq_weight cfg hval] at hmajor ⊢
  rw [attestation_score_eq_weight cfg hval]
  exact confirmed_payload_source_arith hmajor hdiscount hbudget

/-- The resolved parent status selected by a child receives every vote that
supports the child's pending node.  This is a score lower bound at the same
store, with Gloas payload ancestry preserved. -/
theorem selected_parent_score_ge_child_score {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root b) bs →
        WalkKnown store (store.blocks (store.blocks b).parent_root).slot lm.root) :
    get_attestation_score cfg store (get_node_for_root b) bs ≤
      get_attestation_score cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root
          (get_parent_payload_status store (store.blocks b))) bs := by
  rw [attestation_score_eq_weight cfg hval,
    attestation_score_eq_weight cfg hval]
  apply E.weight_mono
  exact attSupporters_subset_resolved_ancestor cfg hwf
    (child_pending_descends_required_parent_status hwf hb hp) hwalk
    (WalkKnown.step hb (hwf b hb hp) (WalkKnown.stop hp (le_refl _)))

/-- The pending parent's payload contest. A strict margin pays the complete
proposer score. If Gloas gives both previous-slot payload decisions zero
weight, the status tie breaker supplies the second route. -/
def PendingStatusMargin (store : Store Root) (blocks : List Root)
    (h : Root) (status : PayloadStatus) : Prop :=
  let selected := ForkChoiceNode.mk h status
  selected ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending) ∧
  ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
    other ≠ selected →
    (get_attestation_score cfg store other
          (store.checkpoint_states store.justified_checkpoint) +
          get_proposer_score cfg store <
        get_attestation_score cfg store selected
          (store.checkpoint_states store.justified_checkpoint) ∧
      is_previous_slot_payload_decision cfg store selected = false) ∨
      (get_weight cfg store other = get_weight cfg store selected ∧
        get_payload_status_tiebreaker cfg store other <
          get_payload_status_tiebreaker cfg store selected)

/-- The corrected ledger strip implies the pending-parent margin once the
opposite score is confined to `X + B + Oanc` and child supporters have been
lifted to the required parent status. -/
theorem pendingStatusMargin_of_ancestor_strip {E : Execution Root}
    {store : Store Root} {blocks : List Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h : Root} {lo σ : Slot}
    {status : PayloadStatus}
    (hmem : ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending))
    (hnotPrev : is_previous_slot_payload_decision cfg store
      (ForkChoiceNode.mk h status) = false)
    (hselected : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (ForkChoiceNode.mk h status)
        (store.checkpoint_states store.justified_checkpoint))
    {O : ℕ}
    (hstrip : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ +
      get_proposer_score cfg store + O + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hopp : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ ForkChoiceNode.mk h status →
      get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) ≤
          E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + O) :
    PendingStatusMargin cfg store blocks h status := by
  refine ⟨hmem, ?_⟩
  intro other hm hne
  left
  constructor
  · have ho := hopp other hm hne
    change get_attestation_score cfg store other
        (store.checkpoint_states store.justified_checkpoint) +
        get_proposer_score cfg store <
      get_attestation_score cfg store (ForkChoiceNode.mk h status)
        (store.checkpoint_states store.justified_checkpoint)
    exact ancestor_margin_arith hstrip ho hselected
  · exact hnotPrev

/-- The payload ledger margin selects the required status with Gloas's full
weight, root, and payload-status key. -/
theorem pending_status_selected_of_margin {store : Store Root} {blocks : List Root}
    {h : Root} {status : PayloadStatus}
    (hmargin : PendingStatusMargin cfg store blocks h status) :
    (get_node_children store blocks (ForkChoiceNode.mk h .pending)).argmax
      (fun child => toLex (get_weight cfg store child,
        toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
      some (ForkChoiceNode.mk h status) := by
  let selected := ForkChoiceNode.mk h status
  have hmem := hmargin.1
  have hkey : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ selected →
      (toLex (get_weight cfg store other,
        toLex (other.root, get_payload_status_tiebreaker cfg store other)) :
          Gwei ×ₗ (Root ×ₗ ℕ)) <
      toLex (get_weight cfg store selected,
        toLex (selected.root, get_payload_status_tiebreaker cfg store selected)) := by
    intro other hm hne
    rcases hmargin.2 other hm hne with ⟨hscore, hnotrecent⟩ | ⟨heq, htie⟩
    · rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (lt_of_le_of_lt (get_weight_le cfg store other)
        (lt_of_lt_of_le hscore
          (get_weight_ge_of_not_payload_decision cfg store selected hnotrecent)))
    · have hroot : other.root = h := ((mem_get_node_children_pending rfl).mp hm).1
      rw [Prod.Lex.toLex_lt_toLex]
      right
      constructor
      · exact heq
      · rw [Prod.Lex.toLex_lt_toLex]
        right
        exact ⟨hroot, htie⟩
  rw [List.argmax_eq_some_iff]
  refine ⟨hmem, fun other hm => ?_, fun other hm hle => ?_⟩
  · by_cases hsame : other = selected
    · subst hsame; exact le_refl _
    · exact le_of_lt (hkey other hm hsame)
  · by_cases hsame : other = selected
    · subst hsame; exact le_refl _
    · exact absurd (lt_of_lt_of_le (hkey other hm hsame) hle) (lt_irrefl _)

/-- **The GHOST step dominates.** From the ledger inequality
`Xval + Bval + get_proposer_score + 1 ≤ Sval`, the `b′`-side lower bound `hbside`
and a sibling upper bound `hsib`, the sibling `cc`
loses to the `b′`-side child `c` in `get_weight` — the boost is charged to the
sibling in full (`MajorityPersists.fork_weight_lt`) yet the winner's bare score
already exceeds sibling-plus-boost. -/
theorem ghost_step_dominates {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo σ : Slot}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    get_weight cfg store (ForkChoiceNode.mk cc .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (ghost_arith hbside hledger hsib)

/-- **A ledger certificate builds one `DescendStep`.** At a fork with parent `h`,
the status margin selects the payload status required by `c`. Within that
resolved branch the ledger inequality, selected lower bound, and every sibling
upper bound select `c`. The shell must derive `hstatus` from confirmation. -/
theorem ledger_descendStep {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot}
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
    (hstatus : PendingStatusMargin cfg store (get_filtered_block_tree cfg store)
      h (get_parent_payload_status store (store.blocks c)))
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c :=
  descendStep_of_dom cfg hchild
    (fun c' hc' hne => ghost_step_dominates cfg ext hbside hledger (hsib c' hc' hne))
    (pending_status_selected_of_margin cfg hstatus)

/-! ## The head descends from `b` along the confirmed chain -/

/-- **Head descent from the ledger chain.** A `DescendStep` chain from the
justified checkpoint root down to `b` (each fork's step built by
`ledger_descendStep` from that block's ledger certificate)
forces the fork-choice head to descend from `b`. Thin composition over
`EngineStore.is_ancestor_get_head_of_chain`; `hwf` (`parent_slot_lt`) and `hsub`
(filtered ⊆ known) are the usual domain conditions and `hnd` the path
distinctness. -/
theorem head_descends_of_ledger {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  is_ancestor_get_head_of_chain cfg hwf hsub hb hnd hchain hlast

/-! ## The per-fork ledger certificate and the chain fold

`head_descends_of_ledger` consumes a pre-built `DescendStep` chain. The bundle
below expresses each fork's step as its ledger *certificate* — the raw inequalities
`ledger_descendStep` consumes, with the fork's `(v₀, n₀, b′, lo, σ)` existentially
packaged — so the shell can present the confirmed chain as a `List.IsChain` of
certificates, and `head_descends_of_ledger_chain` folds it to head descent. -/

/-- One fork's ledger certificate: the required payload status wins the
pending-parent contest, and the ledger selects `c` among children of that
resolved parent. Exactly the hypotheses of `ledger_descendStep`, packaged per
fork. -/
def LedgerStep (E : Execution Root) (store : Store Root) (h c : Root) : Prop :=
  ∃ (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot),
    ForkChoiceNode.mk c .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) ∧
    PendingStatusMargin cfg store (get_filtered_block_tree cfg store)
      h (get_parent_payload_status store (store.blocks c)) ∧
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
        get_attestation_score cfg store (get_node_for_root c)
          (store.checkpoint_states store.justified_checkpoint) ∧
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
        ≤ E.Sval cfg ext v₀ n₀ b' lo σ ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children store (get_filtered_block_tree cfg store)
            (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ)

/-- A ledger certificate yields a `DescendStep` (unpack the certificate, apply
`ledger_descendStep`). -/
theorem descendStep_of_ledgerStep {E : Execution Root} {store : Store Root} {h c : Root}
    (hstep : LedgerStep cfg ext E store h c) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c := by
  obtain ⟨v₀, n₀, b', lo, σ, hchild, hstatus, hbside, hledger, hsib⟩ := hstep
  exact ledger_descendStep cfg ext hchild hstatus hbside hledger hsib

/-- **Head descent from a certificate chain.** A `List.IsChain` of per-fork ledger
certificates from the justified checkpoint root down to `b` forces the fork-choice
head to descend from `b`: each certificate lifts to a `DescendStep`
(`descendStep_of_ledgerStep`), and `head_descends_of_ledger` closes the chain.
This is the confirmed-chain fold — one `b′` certificate per fork — the head-safety
engine shell instantiates from the L4 chain of confirmed blocks. -/
theorem head_descends_of_ledger_chain {E : Execution Root} {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (LedgerStep cfg ext E store)
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  head_descends_of_ledger cfg hwf hsub hb hnd
    (hchain.imp (fun _ _ hab => descendStep_of_ledgerStep cfg ext hab)) hlast

end FastConfirmation.Spec

end
