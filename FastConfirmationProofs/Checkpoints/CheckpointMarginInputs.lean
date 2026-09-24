module
public import FastConfirmationProofs.Discount.EconomicSupport
public import FastConfirmationProofs.FFG.SourceHistory.LaterStoreSupport
public import FastConfirmationProofs.FFG.Certificates.VoteLanding

@[expose] public section

/-!
# Spec / Proof / Remainder: the mechanical remainder

This module assembles economic and trajectory inputs used by `EconomicCore`,
`IHMechanize`, and `VoteLanding`. It combines
`VoteLanding.honest_committee_vote`, `EngineTransport.is_ancestor_transport`, and
the head-safety induction hypothesis in `HeadSafetyEngine.LedgerChainInput`'s shape to
derive the fresh-voter and migration-monotonicity inputs.

## Section 1 — `hfresh`: fresh-voter support

`EconomicCore.hSmono_of_fresh` / `hXmono_of_fresh` reduce the pre-`T1` migration
monotonicities to `hfresh`: a **fresh** honest committee member of slot
`σ'+1` enters `Sclass (σ'+1)` (i.e. `SupportsDesc … (σ'+1)`). This section proves exactly
that from the head-safety induction hypothesis, `votes_head`, and the cross-store
`is_ancestor` transport.

The chain is:

* a fresh window member (`i ∈ span lo (σ'+1) \ span lo σ'`) is assigned **only** at
  `σ'+1` (`committee_assignment` slot-splitting) — `mem_committee_of_fresh`;
* an honest committee member of `σ'+1` casts, at some voting second `nᵢ` with
  `slot_at nᵢ = σ'+1`, its own head vote (`honest_committee_vote` = `votes_head`), whose
  block is `(get_head (store i nᵢ)).root` (`honest_attestation` structure);
* the head-safety IH at the voting store `(i, nᵢ)` gives
  `head ≽ b'` there; `is_ancestor_transport` carries it to the anchor store `(v₀, n₀)`;
* the vote is trivially `i`'s newest through `σ'+1` (the endpoint) — so `SupportsDesc`.

When `σ'+1 = slot_at m`, the IH does not apply because the voter's slot is not
strictly earlier than the anchor slot; this case is supplied by the explicit
same-slot availability premise.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hfresh` -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **A fresh window member is assigned only at `σ'+1`.** If `i ∈ span lo (σ'+1)` but
`i ∉ span lo σ'`, then the assignment slot witnessing `i`'s window membership must be
`σ'+1` itself — every earlier assignment would already place `i` in `span lo σ'`. Hence
`i ∈ E.committee (σ'+1)`. (No same-epoch hypothesis needed: this is a pure slot split.) -/
theorem mem_committee_of_fresh {i : ValidatorIndex} {lo σ' : Slot}
    (hi : i ∈ E.span_committee lo (σ' + 1)) (hni : i ∉ E.span_committee lo σ') :
    i ∈ E.committee (σ' + 1) := by
  simp only [Execution.span_committee, Finset.mem_biUnion, Finset.mem_Icc] at hi hni
  obtain ⟨s, ⟨hslo, hshi⟩, hcomm⟩ := hi
  have hseq : s = σ' + 1 := by
    by_contra hne
    have hsle : s ≤ σ' := Nat.lt_succ_iff.mp (lt_of_le_of_ne hshi hne)
    exact hni ⟨s, ⟨hslo, hsle⟩, hcomm⟩
  exact hseq ▸ hcomm

/-- A fresh honest member supports the selected descendant at the endpoint.
The caller transports the actual recorded vote head with its deadline.
No unrelated source roots need to occur at the receiver. -/
theorem supportsDesc_fresh (hhb : HonestBehavior cfg ext E) (hwf : WellFormedExecution E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo σ' : Slot}
    (hσ1H : E.SlotWithinHorizon cfg (σ' + 1))
    (hs0 : E.slot_at cfg 0 ≤ σ' + 1)
    {i : ValidatorIndex}
    (hi : i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
      (fun i => i ∈ E.honest))
    (htransport : ∀ nᵢ idx, E.slot_at cfg nᵢ = σ' + 1 →
      E.vote i (σ' + 1) = some (nᵢ,
        honest_attestation cfg ext (E.store cfg ext i nᵢ) (σ' + 1) idx i) →
      is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root (get_head cfg (E.store cfg ext i nᵢ)).root)
        (get_node_for_root b') = true) :
    E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i := by
  rw [Finset.mem_filter, Finset.mem_sdiff] at hi
  obtain ⟨⟨hmem1, hnmem0⟩, hih⟩ := hi
  have hcomm : i ∈ E.committee (σ' + 1) := E.mem_committee_of_fresh hmem1 hnmem0
  obtain ⟨nᵢ, idx, hslot, hvote⟩ :=
    E.honest_committee_vote cfg ext hhb hih hcomm hσ1H hs0
  refine ⟨σ' + 1, nᵢ, honest_attestation cfg ext (E.store cfg ext i nᵢ) (σ' + 1) idx i,
    le_refl _, hvote, ?_, ?_⟩
  · intro t' ht' ht'le; exact absurd (lt_of_lt_of_le ht' ht'le) (lt_irrefl _)
  · exact htransport nᵢ idx hslot hvote

/-! ## Migration monotonicity from the actual fresh vote -/

/-- Endpoint ancestry for each actual recorded fresh vote. The producer uses
its vote deadline, G4, and the earlier-slot head-safety induction. -/
def FreshEngineInputs (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot) : Prop :=
  ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter (fun i => i ∈ E.honest),
    ∀ nᵢ idx, E.slot_at cfg nᵢ = σ' + 1 →
      E.vote i (σ' + 1) = some (nᵢ,
        honest_attestation cfg ext (E.store cfg ext i nᵢ) (σ' + 1) idx i) →
      is_ancestor (E.store cfg ext v₀ n₀)
        (get_node_for_root (get_head cfg (E.store cfg ext i nᵢ)).root)
        (get_node_for_root b') = true

/-- **`hfresh` over the whole fresh growth set** from the engine inputs. -/
theorem hfresh_of_engine (hhb : HonestBehavior cfg ext E) (hwf : WellFormedExecution E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo σ' : Slot}
    (hσ1H : E.SlotWithinHorizon cfg (σ' + 1))
    (hs0 : E.slot_at cfg 0 ≤ σ' + 1)
    (hin : E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    ∀ i ∈ (E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
        (fun i => i ∈ E.honest),
      E.SupportsDesc cfg ext v₀ n₀ b' (σ' + 1) i :=
  fun i hi => E.supportsDesc_fresh cfg ext hhb hwf hσ1H hs0 hi (hin i hi)

/-- **`hSmono` from the engine inputs** — `EconomicCore.hSmono_of_fresh` composed with
`hfresh_of_engine`. Closes the pre-`T1` honest-support growth to the head-safety IH and
the block-relay domain conditions. -/
theorem hSmono_of_engine (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hwf : WellFormedExecution E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hσ1H : E.SlotWithinHorizon cfg (σ' + 1))
    (hs0 : E.slot_at cfg 0 ≤ σ' + 1)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hin : E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    E.Sval cfg ext v₀ n₀ b' lo σ' +
        E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ' + 1) :=
  E.hSmono_of_fresh cfg ext hhb hec v₀ n₀ b' lo σ' hsame
    (E.hfresh_of_engine cfg ext hhb hwf hσ1H hs0 hin)

/-- **`hXmono` from the engine inputs** — `EconomicCore.hXmono_of_fresh` composed with
`hfresh_of_engine`. Closes the pre-`T1` sibling-stuck antitonicity, `Xclass`-exit leg
included. -/
theorem hXmono_of_engine (hhb : HonestBehavior cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hwf : WellFormedExecution E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ' : Slot)
    (hσ1H : E.SlotWithinHorizon cfg (σ' + 1))
    (hs0 : E.slot_at cfg 0 ≤ σ' + 1)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ' →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg (σ' + 1))
    (hin : E.FreshEngineInputs cfg ext v₀ n₀ b' lo σ') :
    E.Xval cfg ext v₀ n₀ b' lo (σ' + 1) ≤ E.Xval cfg ext v₀ n₀ b' lo σ' :=
  E.hXmono_of_fresh cfg ext hhb hec v₀ n₀ b' lo σ' hsame
    (E.hfresh_of_engine cfg ext hhb hwf hσ1H hs0 hin)




end Execution

end FastConfirmation.Spec

end
