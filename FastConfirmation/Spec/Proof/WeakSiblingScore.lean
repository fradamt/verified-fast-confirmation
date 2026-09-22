module
public import FastConfirmation.Spec.Proof.WeakCrossingSets
public import FastConfirmation.Spec.Proof.FutureSiblingScore

@[expose] public section

/-!
# Spec / Proof / WeakSiblingScore

Margin-discharge wave, Stage I-c: the weak sibling-score bound at the honest
endpoint.

Weak twin of `FutureSiblingScore.futureCrossing_sibling_score_of_endpointLedger_minimal`,
with the query-side `Xclass` confinement premise (`hSt`/`hAt`/`hmaxQuery`)
replaced by an *endpoint*-indexed one, `hparentA`, taken as an explicit
hypothesis rather than re-derived: it is exactly
`Weak.freshParentStuck_subset_endpoint_Aclass` (`WeakEndpointClasses.lean`) at
the caller. This single lemma serves **both** crossing regimes — the
subtractive `crossingEdge_sibling_score_of_endpointLedger_minimal` variant is
retired on the weak path (`F3`: `Weak.compute_adversarial_weight` has no
equivocation subtraction, so there is no `crossingEquivPre` to sharpen the
Byzantine pre-term with).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- Weak twin of `mem_crossingXPre_of_query_Xclass_not_mid`, with the query
`Xclass` premise replaced by the endpoint one and `hparentA` the
endpoint-indexed fresh-parent-stuck inclusion. -/
theorem mem_crossingXPre_of_endpoint_Xclass_not_mid {E : Execution Root}
    {obs : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {b : Root} {lo mid es : Slot} {i : ValidatorIndex}
    (hparentA : FreshParentStuck cfg ext E (E.store cfg ext obs q) bs b
      ⊆ E.Aclass cfg ext w m b lo es)
    (hiX : i ∈ E.Xclass cfg ext w m b lo es)
    (hiNotMid : i ∉ E.span_committee mid es) :
    i ∈ crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es := by
  have hiX' := hiX
  simp only [Execution.Xclass, Finset.mem_filter] at hiX'
  rw [crossingXPre, Finset.mem_sdiff]
  constructor
  · simp only [Execution.crossingHonestPre, Execution.crossingPreRegion, Finset.mem_filter,
      Finset.mem_sdiff]
    exact ⟨⟨hiX'.1.1, hiNotMid⟩, hiX'.1.2⟩
  · intro hiParentPre
    have hiParent : i ∈ FreshParentStuck cfg ext E (E.store cfg ext obs q) bs b :=
      (Finset.mem_sdiff.mp hiParentPre).1
    have hiA := hparentA hiParent
    simp only [Execution.Aclass, Finset.mem_filter] at hiA
    exact hiX'.2.2 hiA.2.2

/-- **Weak twin of `futureCrossing_sibling_score_of_endpointLedger_minimal`,
used for BOTH crossing regimes** (the subtractive crossing-edge variant is
retired, `F3`). `hmaxQuery`, `hSt`, `hAt`, `hv`, `hrelaySlot` are all gone:
the endpoint `Aclass` placement is supplied directly by the caller (typically
`Weak.freshParentStuck_subset_endpoint_Aclass`) rather than re-derived from a
query-indexed `WindowRecordedEpochMax` transport. -/
theorem crossing_sibling_score_of_endpointLedger {E : Execution Root}
    (hA : SelectedMarginAssumptions cfg ext E)
    {obs : ValidatorIndex} {q : ℕ} {w : ValidatorIndex} {m : ℕ}
    {bs : BeaconState Root} {a b : Root} {lo mid es sigma : Slot}
    (hparentA : FreshParentStuck cfg ext E (E.store cfg ext obs q) bs b
      ⊆ E.Aclass cfg ext w m b lo es)
    (hmidEs : mid ≤ es) (hesSigma : es ≤ sigma)
    (hcommittee : ∀ t : Slot, es < t → t ≤ sigma → E.CommitteeSupportsAt cfg ext w m b t)
    (hledger : E.EndpointLedgerFields cfg ext w m a b lo sigma) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk a) → c' ≠ b →
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es)
          + E.Xval cfg ext w m b mid sigma
          + E.weight (E.crossingByzPre lo mid es)
          + E.Bval mid sigma := by
  classical
  have hXback : E.Xclass cfg ext w m b lo sigma ⊆
      E.Xclass cfg ext w m b lo es :=
    E.Xclass_subset_of_committee_support cfg ext hA.honest_behavior
      w m b lo hesSigma hcommittee
  have hXsplit : E.Xclass cfg ext w m b lo sigma ⊆
      crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es ∪
        E.Xclass cfg ext w m b mid sigma := by
    intro i hi
    by_cases hiMid : i ∈ E.span_committee mid sigma
    · apply Finset.mem_union_right
      have hi' := hi
      simp only [Execution.Xclass, Finset.mem_filter] at hi' ⊢
      exact ⟨⟨hiMid, hi'.1.2⟩, hi'.2⟩
    · apply Finset.mem_union_left
      have hiEndEs := hXback hi
      have hiNotMidEs : i ∉ E.span_committee mid es := by
        intro hiMidEs
        exact hiMid (E.span_committee_mono mid hesSigma hiMidEs)
      exact mem_crossingXPre_of_endpoint_Xclass_not_mid (E := E) cfg ext hparentA
        hiEndEs hiNotMidEs
  have hXweight : E.Xval cfg ext w m b lo sigma ≤
      E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es) +
        E.Xval cfg ext w m b mid sigma := by
    calc
      E.Xval cfg ext w m b lo sigma =
          E.weight (E.Xclass cfg ext w m b lo sigma) := rfl
      _ ≤ E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es ∪
          E.Xclass cfg ext w m b mid sigma) := E.weight_mono hXsplit
      _ ≤ E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es) +
          E.weight (E.Xclass cfg ext w m b mid sigma) :=
        weight_union_le _ _
      _ = E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma := rfl
  have hBsplit : E.Bwin lo sigma ⊆
      E.crossingByzPre lo mid es ∪ E.Bwin mid sigma :=
    Execution.Bwin_subset_crossingByzPre_union (E := E) (lo := lo)
      hmidEs hesSigma
  have hBweight : E.Bval lo sigma ≤
      E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma := by
    calc
      E.Bval lo sigma = E.weight (E.Bwin lo sigma) := rfl
      _ ≤ E.weight (E.crossingByzPre lo mid es ∪ E.Bwin mid sigma) :=
        E.weight_mono hBsplit
      _ ≤ E.weight (E.crossingByzPre lo mid es) + E.weight (E.Bwin mid sigma) :=
        weight_union_le _ _
      _ = E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma := rfl
  intro c' hchild hne
  have hsibling := hledger.sibling_score c' hchild hne
  calc
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
          ((E.store cfg ext w m).checkpoint_states
            (E.store cfg ext w m).justified_checkpoint)
        ≤ E.Xval cfg ext w m b lo sigma + E.Bval lo sigma := hsibling
    _ ≤ (E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma) +
        (E.weight (E.crossingByzPre lo mid es) + E.Bval mid sigma) :=
      Nat.add_le_add hXweight hBweight
    _ = E.weight (crossingXPre cfg ext E (E.store cfg ext obs q) bs b lo mid es) +
          E.Xval cfg ext w m b mid sigma
          + E.weight (E.crossingByzPre lo mid es)
          + E.Bval mid sigma := by
      simp only [Nat.add_assoc]

end Weak

end FastConfirmation.Spec

end
