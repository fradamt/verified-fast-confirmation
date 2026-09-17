import FastConfirmation.Spec.Proof.AnchorFacade
import FastConfirmation.Spec.Proof.ResidualMechanicalII
import FastConfirmation.Spec.Proof.AheadFacade
import FastConfirmation.Spec.Proof.ExportWiring
import FastConfirmation.Spec.Proof.FinalWiring
import FastConfirmation.Spec.Proof.Remainder

/-!
# Strong-prefix safety interfaces (retired)

This module held the conditional reductions for `Spec_Safety`, the statement that quantifies
over every later completed whole-second execution state, including later states inside the same
slot. The accepted public result is `acceptedSpec_safety_next_slot`, exported by
`FastConfirmation.Spec.ProvenTheorems`, and is unaffected by anything here.

All of it belonged to the legacy `SpecAssumptions` observed-anchor cone and is deleted (P-6):
`shellResiduals_of_strongPrefixSafetyInputs`, `Spec_Safety_of_strongPrefix_inputs`,
`Spec_Safety_of_sameSlot_inputs` and the two `Spec_Monotonicity_of_strongPrefix_inputs*`
companions routed the observed anchor through `AheadFacade`'s ahead-regime head-tracking
premise, which nothing in the development ever produced and no audited witness reached; the
vocabulary that only fed them (`StrongPrefixSafetyInputs`, `SameSlotFinalizedRootKnown` and its
non-genesis variant, `hkc_of_confirmed_known`, `spec_monotonicity_of_safety`) went with them in
the orphan sweep. See the section notes below and `docs/p6-justified-descends-derivation.md` §8.

What remains are the two ancestor-comparability lemmas, which are general `get_ancestor`
composition facts with no connection to the ahead regime.
-/
namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Deleted: the strong-prefix reduction and its vocabulary

Everything this module used to state stood here and immediately below the `end Execution` that
followed it:

* `StrongPrefixSafetyInputs`, the three-field input record;
* `shellResiduals_of_strongPrefixSafetyInputs`, which assembled
  `ShellInstantiation.ShellResiduals` from it — wiring the observed-anchor leg through
  `ExportWiring.observedFilterResiduals_of_interface` and carrying the ahead-regime
  head-tracking premise `htracks` explicitly;
* `SameSlotFinalizedRootKnown` / `SameSlotFinalizedRootKnownNonGenesis` and the genesis
  reduction between them;
* the conditional theorems `Spec_Safety_of_strongPrefix_inputs` /
  `Spec_Safety_of_sameSlot_inputs` and the companions
  `Spec_Monotonicity_of_strongPrefix_inputs` /
  `Spec_Monotonicity_of_strongPrefix_inputs_of_confirmed_known`;
* `hkc_of_confirmed_known` and `spec_monotonicity_of_safety`, the safety-to-monotonicity
  bridge — whose conclusion `Spec_Monotonicity` is itself deleted (`TheoremStatements.lean`).

The conditional theorems are part of the legacy `SpecAssumptions` observed-anchor cone (P-6);
the rest are the orphans that cascaded from them. Nothing ever produced the ahead-regime
premise, and the audited route does not need it: `AcceptedObservedRestartDynamicSafety` proves
`obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, so the observed anchor never enters the
ahead regime and `E5Filter.head_ge_of_justified_ge_K` closes its `SafeFrom` on its own. See
`docs/p6-justified-descends-derivation.md` §8 and `docs/plumbing-spec-citations.md` P-6. -/

end Execution

/-! ## Ancestor comparability

Two ancestors of a common node are ancestry-ordered. This was the engine of the deleted
safety-to-monotonicity bridge; it is a general `get_ancestor` composition law and is kept. -/

omit [Inhabited Root] in
/-- **Two ancestors of a common node, the lower slot below.** If `a` and `b` are both
ancestors of `x` and `(blocks a).slot ≤ (blocks b).slot`, then `a` is an ancestor of `b`
(`b ⪰ a`). The walk from `x` down to `b`'s slot lands on `b` (`hb`); continuing it to `a`'s
slot lands on `a` (`ha`) by walk composition (`get_ancestor_comp`) — so the walk from `b` to
`a`'s slot is `a`. Purely the `get_ancestor` composition law; the `WalkKnown` witness is the
walk of `x` down to `a`'s slot. -/
theorem ancestor_comparable_of_common {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a b : Root} (hle : (store.blocks a).slot ≤ (store.blocks b).slot)
    (hwa : WalkKnown store (store.blocks a).slot x)
    (ha : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk a) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk b) = true) :
    is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk a) = true := by
  simp only [is_ancestor, decide_eq_true_eq] at ha hb ⊢
  have hcomp := get_ancestor_comp hwf hle hwa
  rw [hb, ha] at hcomp
  exact hcomp

omit [Inhabited Root] in
/-- **Ancestor comparability.** Two ancestors `a`, `b` of a common node `x` are
ancestry-ordered (`b ⪰ a` or `a ⪰ b`) — the confirmed-root chain is linear. Symmetric
wrapper over `ancestor_comparable_of_common`, dispatching on which slot is lower. -/
theorem ancestor_comparable {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a b : Root}
    (hwa : WalkKnown store (store.blocks a).slot x)
    (hwb : WalkKnown store (store.blocks b).slot x)
    (ha : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk a) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk b) = true) :
    is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk a) = true ∨
    is_ancestor store (ForkChoiceNode.mk a) (ForkChoiceNode.mk b) = true := by
  rcases le_total (store.blocks a).slot (store.blocks b).slot with hle | hle
  · exact Or.inl (ancestor_comparable_of_common hwf hle hwa ha hb)
  · exact Or.inr (ancestor_comparable_of_common hwf hle hwb hb ha)

end FastConfirmation.Spec
