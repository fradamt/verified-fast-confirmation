module
public import FastConfirmationProofs.Discount.ArbitraryQueryMargin

@[expose] public section

/-!
# Committee support from the arbitrary-query slot-start induction

The crossing-margin dynamics use `CommitteeSupportsAt` rather than the
same-epoch fresh-seat recurrence.  This file constructs that semantic input
directly from the slot-start head-safety induction: every honest member of an
intervening committee votes its own head, the induction puts that head below
the selected result, and the selected chain plus synchrony transports the vote
below the edge child at the fixed endpoint.

Unlike `FreshEngineInputs`, the result covers recurring committee members as
well as fresh ones.  The newest-through-`t` witness is simply the validator's
vote at `t` itself.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- Every honest member of an intervening committee supports the selected
edge child at the endpoint.  The lower induction bound is the first second of
the real query slot, so this remains valid when the query itself occurs later
in that slot. -/
theorem committeeSupportsAt_of_slotStart_IH_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {q : ℕ} {glc c : Root}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    {t : Slot}
    (hqt : E.slot_at cfg q ≤ t)
    (htm : t < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hchain : is_ancestor (E.store cfg ext w m)
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
    (ht0 : E.slot_at cfg 0 ≤ t) :
    E.CommitteeSupportsAt cfg ext w m c t := by
  intro i hi hcomm
  have htH : E.SlotWithinHorizon cfg t :=
    E.slotWithinHorizon_of_le cfg (Nat.le_of_lt htm) hHm
  obtain ⟨nᵢ, index, hHnᵢ, hnᵢSlot, hvote⟩ :=
    hA.honest_behavior.votes_head i hi t hcomm htH ht0
  have hnᵢLower : E.slot_start cfg (E.slot_at cfg q) ≤ nᵢ :=
    E.query_slot_start_le_of_slot_ge_minimal cfg ext hA (by
      rw [hnᵢSlot]
      exact hqt)
  have hnᵢSlotLt : E.slot_at cfg nᵢ < E.slot_at cfg m := by
    rw [hnᵢSlot]
    exact htm
  have hnᵢLt : nᵢ < m := by
    apply Nat.lt_of_not_ge
    intro hmnᵢ
    exact (Nat.not_le_of_gt hnᵢSlotLt) (E.slot_at_mono cfg hmnᵢ)
  have hheadGlc : is_ancestor (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ))
      (get_node_for_root glc) = true :=
    hIH i hi nᵢ hnᵢLower hnᵢSlotLt hHnᵢ
  have hglcᵢ : glc ∈ (E.store cfg ext i nᵢ).block_roots :=
    hglcKnown i hi nᵢ hnᵢLower hHnᵢ
  have hdue : nᵢ ≤ E.slot_start cfg (E.slot_at cfg nᵢ) +
      get_attestation_due_ms cfg / 1000 := by
    simpa only [hnᵢSlot] using
      (hA.honest_behavior.vote_deadline i hi t nᵢ _ hvote).2
  have hheadM := E.honest_head_known_at_later_slot_minimal cfg ext hA
    hi hw hHnᵢ hHm hdue hnᵢSlotLt
  have hhead := E.head_root_known_of_selectedMarginDomain cfg ext hA.domain
    hi nᵢ hHnᵢ
  obtain ⟨hglcM, hheadGlcM⟩ := E.ancestor_at_common_descendant_minimal cfg ext hA
    hhead hheadM hglcᵢ (by rwa [is_ancestor_node_root] at hheadGlc)
  obtain ⟨hparentM, hwalkM, _⟩ := E.store_domainK_of_selectedMarginDomain cfg ext
    hA.wellFormed hA.externals_coherence hA.genesis hA.domain w hw m hHm
  have hheadCEnd : is_ancestor (E.store cfg ext w m)
      (get_node_for_root (get_head cfg (E.store cfg ext i nᵢ)).root)
      (get_node_for_root c) = true :=
    is_ancestor_trans (b := get_node_for_root glc) hparentM (hwalkM c hc _ hheadM)
      (hwalkM c hc glc hglcM) hheadGlcM hchain
  refine ⟨t, nᵢ,
    honest_attestation cfg ext (E.store cfg ext i nᵢ) t index i,
    le_refl _, hvote, ?_, ?_⟩
  · intro t' htt' ht't
    exact False.elim ((Nat.not_lt_of_ge ht't) htt')
  · have hbbr :
        (honest_attestation cfg ext (E.store cfg ext i nᵢ) t index i).data.beacon_block_root =
          (get_head cfg (E.store cfg ext i nᵢ)).root := by
      rw [honest_attestation_data_eq]
      exact honest_attestation_data_beacon_block_root cfg ext
        (E.store cfg ext i nᵢ) t index
    rw [hbbr]
    exact hheadCEnd

end Execution

end FastConfirmation.Spec

end
