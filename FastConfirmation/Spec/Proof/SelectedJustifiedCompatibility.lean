module
public import FastConfirmation.Spec.Proof.CausalCheckpointCompatibility

@[expose] public section

/-!
# Selected-result compatibility with an endpoint justification

This module separates the two checkpoint-compatibility rungs used by the
coupled selected-result induction.

* `InitialSelectedJustifiedCompatibilityAt` is the narrow low/equal-epoch
  SIR/Gasper boundary: it states only ancestry comparability of the selected
  result and the endpoint justified checkpoint.  It says nothing about heads,
  filters, tips, voting sources, or future placement.
* `EndpointJustificationCausalityAt` is the high-epoch realization boundary:
  a strictly newer endpoint justification supplies a timely honest ground
  vote targeting that checkpoint.  Its conclusion is independent of the
  selected result.

Together with the earlier-slot head-safety induction, ordinary store domain,
and the selected chain `glc ⩾c c`, these two interfaces yield the exact
non-covered orientation `c ⩾c endpoint.JC`, and hence `glc ⩾c endpoint.JC`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- A causal honest target witness for the realized justified checkpoint at
endpoint `(w,m)`.  These are exactly the witness premises consumed by
`endpoint_justified_ancestor_of_causal_honest_target_minimal`: the vote is
honest, is cast no earlier than the query slot and strictly before the
endpoint, lies in the verified slot horizon, is an actual ground vote, and
targets the endpoint checkpoint.

No selected result, chain block, filter, or fork-choice conclusion occurs in
this predicate.
-/
def CausalHonestTargetAt (q : ℕ) (w : ValidatorIndex) (m : ℕ) : Prop :=
  ∃ i ∈ E.honest, ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
    E.slot_at cfg q ≤ s ∧
    s < E.slot_at cfg m ∧
    E.SlotWithinHorizon cfg s ∧
    E.vote i s = some (k, a) ∧
    a.data.target = (E.store cfg ext w m).justified_checkpoint

/-- Causal origin of an endpoint justification, without classifying the vote
relative to the selected query yet.  The vote must be an actual honest ground
vote cast after the trusted execution anchor and strictly before the endpoint
slot.  The anchor cutoff is essential because `Execution.vote` intentionally
contains no protocol semantics for pre-anchor history. -/
def HonestTargetBeforeEndpointAt (w : ValidatorIndex) (m : ℕ) : Prop :=
  ∃ i ∈ E.honest, ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
    E.slot_at cfg 0 ≤ s ∧
    s < E.slot_at cfg m ∧
    E.SlotWithinHorizon cfg s ∧
    E.vote i s = some (k, a) ∧
    a.data.target = (E.store cfg ext w m).justified_checkpoint

/-- A realized endpoint justification is either the trusted anchor or has a
causal honest target vote before the endpoint.  This is the time-indexed
replacement for a timeless endpoint certificate. -/
def EndpointJustificationOriginAt (anchor : Checkpoint Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  (E.store cfg ext w m).justified_checkpoint = anchor ∨
    E.HonestTargetBeforeEndpointAt cfg ext w m

/-- The part of an endpoint-justification origin which predates the selected
query slot.  Same-slot endpoints necessarily enter this branch. -/
def PreQueryTargetOriginAt (anchor : Checkpoint Root) (q : ℕ)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  (E.store cfg ext w m).justified_checkpoint = anchor ∨
    ∃ i ∈ E.honest, ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
      E.slot_at cfg 0 ≤ s ∧
      s < E.slot_at cfg q ∧
      s < E.slot_at cfg m ∧
      E.SlotWithinHorizon cfg s ∧
      E.vote i s = some (k, a) ∧
      a.data.target = (E.store cfg ext w m).justified_checkpoint

/-- Narrow pre-query SIR/base boundary.  It is invoked only for the trusted
anchor or for a causally realized justification whose honest target vote was
cast before the selected query slot.  Post-query votes are handled by the
coupled head induction and do not enter this premise. -/
def PreQuerySelectedJustifiedCompatibilityAt
    (anchor : Checkpoint Root) (q : ℕ) (glc : Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  E.PreQueryTargetOriginAt cfg ext anchor q w m →
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∨
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root glc) = true

/-- Low/equal-query-epoch compatibility boundary.

This is the precise SIR/base fact suggested by the paper's Gasper argument:
when the endpoint justified checkpoint is not newer than the query store's
current epoch, it is ancestry-comparable with the selected result.  This is a
deliberately narrow semantic interface.  In particular it does **not** assert
which orientation holds, any head descent, retained placement, filter
membership, tip existence, source freshness, or future-global property.
-/
def InitialSelectedJustifiedCompatibilityAt
    (query : FastConfirmationStore Root) (glc : Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  (E.store cfg ext w m).justified_checkpoint.epoch ≤
      get_current_store_epoch cfg query.store →
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∨
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root glc) = true

/-- Strictly-newer endpoint-justification realization boundary.

If the endpoint's justified epoch is newer than the query store's current
epoch, the endpoint exposes a causal honest vote targeting that checkpoint.
The interface is intentionally result-independent: it mentions neither
`glc` nor any selected edge, so it cannot assume the desired branch result.
-/
def EndpointJustificationCausalityAt
    (q : ℕ) (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : ℕ) : Prop :=
  get_current_store_epoch cfg query.store <
      (E.store cfg ext w m).justified_checkpoint.epoch →
    E.CausalHonestTargetAt cfg ext q w m

/-- The two epoch interfaces close the selected-result/justification
compatibility rung.

In the low/equal epoch case, base comparability plus the excluded direct-
coverage orientation forces `glc ⩾c JC`; comparability of `c` and `JC` below
that common descendant then forces `c ⩾c JC`.  In the high epoch case,
`EndpointJustificationCausalityAt` supplies the result-independent causal vote
consumed by `endpoint_justified_ancestor_of_causal_honest_target_minimal`.
Finally, `glc ⩾c c ⩾c JC` gives the result-level orientation in both cases.
-/
theorem selected_result_and_child_ancestor_of_endpoint_justified_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {q : ℕ} (query : FastConfirmationStore Root)
    {glc c : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    (hinitial : E.InitialSelectedJustifiedCompatibilityAt cfg ext
      query glc w m)
    (hcausal : E.EndpointJustificationCausalityAt cfg ext
      q query w m)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root c)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let J := (E.store cfg ext w m).justified_checkpoint
  have hstartM : E.slot_start cfg (E.slot_at cfg q) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hglcM : glc ∈ (E.store cfg ext w m).block_roots :=
    hglcKnown w hw m hstartM hHm
  obtain ⟨hwfM, hwalkM, hJM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  by_cases hlow : J.epoch ≤ get_current_store_epoch cfg query.store
  · rcases hinitial (by simpa only [J] using hlow) with hglcJ | hJglc
    · have hglcJ' : is_ancestor (E.store cfg ext w m)
          (get_node_for_root glc) (get_node_for_root J.root) = true := by
        simpa only [J] using hglcJ
      rcases is_ancestor_comparable hwfM
          (hwalkM J.root hJM glc hglcM)
          (hwalkM c hcM glc hglcM)
          hglcJ' hglcC_M with hcJ | hJc
      · exact ⟨by simpa only [J] using hcJ, by simpa only [J] using hglcJ'⟩
      · exact False.elim (hnotCovered (by simpa only [J] using hJc))
    · have hJglc' : is_ancestor (E.store cfg ext w m)
          (get_node_for_root J.root) (get_node_for_root glc) = true := by
        simpa only [J] using hJglc
      have hJc : is_ancestor (E.store cfg ext w m)
          (get_node_for_root J.root) (get_node_for_root c) = true :=
        is_ancestor_trans (a := get_node_for_root J.root) (b := get_node_for_root glc)
            (c := get_node_for_root c) hwfM
          (hwalkM c hcM J.root hJM) (hwalkM c hcM glc hglcM)
          hJglc' hglcC_M
      exact False.elim (hnotCovered (by simpa only [J] using hJc))
  · have hhigh : get_current_store_epoch cfg query.store < J.epoch :=
      Nat.lt_of_not_ge hlow
    obtain ⟨i, hi, s, k, a, hqs, hsm, hsH, hvote, htarget⟩ :=
      hcausal (by simpa only [J] using hhigh)
    have hcJ : is_ancestor (E.store cfg ext w m)
        (get_node_for_root c) (get_node_for_root J.root) = true := by
      apply E.endpoint_justified_ancestor_of_causal_honest_target_minimal
        cfg ext hA hwalkDomain hw hHm hcM hglcC_M hglcKnown hIH
        hi hqs hsm hsH hvote
      · simpa only [J] using htarget
      · simpa only [J] using hnotCovered
    have hglcJ : is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc) (get_node_for_root J.root) = true :=
      is_ancestor_trans (a := get_node_for_root glc) (b := get_node_for_root c)
          (c := get_node_for_root J.root) hwfM
        (hwalkM J.root hJM glc hglcM) (hwalkM J.root hJM c hcM)
        hglcC_M hcJ
    exact ⟨by simpa only [J] using hcJ, by simpa only [J] using hglcJ⟩

/-- Causal-time version of checkpoint compatibility.

Every endpoint justification first exposes its origin.  A target vote at or
after the selected query slot is discharged by the actual earlier-slot head
induction.  Only an anchor/pre-query origin is sent to the narrow SIR base.
This avoids classifying a query-current-epoch justification as "initial" merely
because of its epoch number. -/
theorem selected_result_and_child_ancestor_of_endpoint_justified_causal_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext)
    {anchor : Checkpoint Root}
    {q : ℕ}
    {glc c : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (hslotQM : E.slot_at cfg q ≤ E.slot_at cfg m)
    (hcM : c ∈ (E.store cfg ext w m).block_roots)
    (hglcC_M : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.WithinHorizon cfg m' →
      glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ,
      E.slot_start cfg (E.slot_at cfg q) ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
      E.WithinHorizon cfg m' →
      is_ancestor (E.store cfg ext w' m')
        (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root glc) = true)
    (hpre : E.PreQuerySelectedJustifiedCompatibilityAt cfg ext
      anchor q glc w m)
    (horigin : E.EndpointJustificationOriginAt cfg ext anchor w m)
    (hnotCovered : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root c) ≠ true) :
    is_ancestor (E.store cfg ext w m)
        (get_node_for_root c)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root glc)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root) = true := by
  let J := (E.store cfg ext w m).justified_checkpoint
  have hstartM : E.slot_start cfg (E.slot_at cfg q) ≤ m :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA hslotQM
  have hglcM : glc ∈ (E.store cfg ext w m).block_roots :=
    hglcKnown w hw m hstartM hHm
  obtain ⟨hwfM, hwalkM, hJM⟩ :=
    E.store_domainK_of_selectedMarginDomain cfg ext hA.wellFormed
      hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have finish :
      (is_ancestor (E.store cfg ext w m)
          (get_node_for_root glc) (get_node_for_root J.root) = true ∨
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root J.root) (get_node_for_root glc) = true) →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root c) (get_node_for_root J.root) = true ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root glc) (get_node_for_root J.root) = true := by
    intro hcomp
    rcases hcomp with hglcJ | hJglc
    · rcases is_ancestor_comparable hwfM
          (hwalkM J.root hJM glc hglcM)
          (hwalkM c hcM glc hglcM)
          hglcJ hglcC_M with hcJ | hJc
      · exact ⟨hcJ, hglcJ⟩
      · exact False.elim (hnotCovered (by simpa only [J] using hJc))
    · have hJc : is_ancestor (E.store cfg ext w m)
          (get_node_for_root J.root) (get_node_for_root c) = true :=
        is_ancestor_trans (a := get_node_for_root J.root) (b := get_node_for_root glc)
            (c := get_node_for_root c) hwfM
          (hwalkM c hcM J.root hJM) (hwalkM c hcM glc hglcM)
          hJglc hglcC_M
      exact False.elim (hnotCovered (by simpa only [J] using hJc))
  rcases horigin with hanchor | htarget
  · apply finish
    simpa only [J] using hpre (Or.inl hanchor)
  · obtain ⟨i, hi, s, k, a, hs0, hsm, hsH, hvote, htargetEq⟩ := htarget
    by_cases hqs : E.slot_at cfg q ≤ s
    · have hcJ : is_ancestor (E.store cfg ext w m)
          (get_node_for_root c) (get_node_for_root J.root) = true := by
        apply E.endpoint_justified_ancestor_of_causal_honest_target_minimal
          cfg ext hA hwalkDomain hw hHm hcM hglcC_M hglcKnown hIH
          hi hqs hsm hsH hvote
        · simpa only [J] using htargetEq
        · simpa only [J] using hnotCovered
      have hglcJ : is_ancestor (E.store cfg ext w m)
          (get_node_for_root glc) (get_node_for_root J.root) = true :=
        is_ancestor_trans (a := get_node_for_root glc) (b := get_node_for_root c)
            (c := get_node_for_root J.root) hwfM
          (hwalkM J.root hJM glc hglcM) (hwalkM J.root hJM c hcM)
          hglcC_M hcJ
      exact ⟨by simpa only [J] using hcJ, by simpa only [J] using hglcJ⟩
    · apply finish
      have hsQ : s < E.slot_at cfg q := Nat.lt_of_not_ge hqs
      simpa only [J] using hpre (Or.inr
        ⟨i, hi, s, k, a, hs0, hsQ, hsm, hsH, hvote, htargetEq⟩)

end Execution

end FastConfirmation.Spec

end
