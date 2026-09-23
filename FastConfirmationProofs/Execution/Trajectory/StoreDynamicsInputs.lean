module
public import FastConfirmationProofs.Handlers.HandlerVoteClasses

@[expose] public section

/-!
# Spec / Proof / DynamicsClosure

This module contains `hSmem_of_recorded` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)


















/-- **Family 6 — `hSmem` from per-member recorded `c`-support.** For each `Sclass`
member `i`, given a recorded latest message at `(w, m)` that supports
`get_node_for_root c` (`hrec`, the `recorded_supports_c_of_IH` output), `i` sits in
`AttSupporters cfg (store w m) (get_node_for_root c) bs` for the registry-constant
justified source `bs`. Honest-ness and committee assignment come from
`Sclass ⊆ span_committee` + the honest filter; active/unslashed/non-equivocation are
internal to `mem_AttSupporters_of_honest_committee`. This is `hSmem`. -/
theorem hSmem_of_recorded (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (m : ℕ) {bs : BeaconState Root}
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' c : Root) (lo σ : Slot)
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hrec : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bs := by
  intro i hi
  have hi' := hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi'
  obtain ⟨t, ht, hcomm⟩ := Finset.mem_biUnion.mp hi'.1.1
  have htle : t ≤ σ := (Finset.mem_Icc.mp ht).2
  have htH : E.SlotWithinHorizon cfg t :=
    ⟨htle.trans hσH.1,
      lt_of_le_of_lt (Nat.div_le_div_right htle) hσH.2⟩
  obtain ⟨lm, hlm, hsupp⟩ := hrec i hi
  exact mem_AttSupporters_of_honest_committee cfg ext (hw := hw) (hmH := hmH) hhb hec hsv hgen hval hbsH
    hi'.1.2 htH hcomm hlm hsupp

end Execution

end FastConfirmation.Spec

end
