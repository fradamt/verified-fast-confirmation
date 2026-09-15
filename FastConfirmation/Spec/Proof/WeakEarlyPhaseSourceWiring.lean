import FastConfirmation.Spec.Proof.WeakSeedDissemination
import FastConfirmation.Spec.Proof.WeakSelectedTrace
import FastConfirmation.Spec.Proof.WeakSelectorInversion
import FastConfirmation.Spec.Proof.AcceptedPhaseSourceSupply

/-!
# Spec / Proof / WeakEarlyPhaseSourceWiring

Stage S5 of the `hfilter`-discharge wave (`/tmp/hfilter-wave-design.md`): weak
twins of `AcceptedEarlyPhaseSourceWiring.lean`'s executable head-cache
knownness lemmas and of `AcceptedPhaseSourceSupply.lean`'s two actual-call
source-supply theorems (sites 3 and 6 of the wave's site inventory), all
re-indexed over `E.weakFcrStep` / `E.weakFcr` (`WeakFCRCallContracts.lean`),
per `/tmp/delta5-proposal.md` §5.

## What is delivered so far

* `Weak.weakFcr_currentSlotHead_known` / `Weak.weakFcrStep_previousSlotHead_known`
  — weak twins of `Execution.fcr_currentSlotHead_known` /
  `Execution.fcrStep_previousSlotHead_known`. The strong
  `head_root_known_of_selectedMarginDomain cfg ext hdomain hv` call is replaced
  by the honesty-free `Execution.head_root_known_at_observer`
  (`WeakObserverDomain.lean`), driven by `hcoh : E.ObserverCoherence cfg ext
  obs`; `SelectedMarginDomain` is dropped entirely from the signature (it fed
  nothing else in either strong proof).

Sites 3 and 6 land in subsequent commits.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-! ## Executable weak FCR head-cache knownness -/

/-- Weak twin of `Execution.fcr_currentSlotHead_known`. -/
theorem weakFcr_currentSlotHead_known
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) (n : Nat)
    (hH : E.WithinHorizon cfg n) :
    (E.weakFcr cfg ext obs n).current_slot_head ∈
      (E.store cfg ext obs n).block_roots := by
  induction n with
  | zero =>
      obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hgen
      change (E.genesis_store.finalized_checkpoint.root ∈
        E.genesis_store.block_roots)
      rw [hgenEq]
      simp [get_forkchoice_store]
  | succ n ih =>
      have hnH : E.WithinHorizon cfg n :=
        E.withinHorizon_mono cfg (Nat.le_succ n) hH
      have hknownN := ih hnH
      by_cases hcall : get_current_slot cfg (E.store cfg ext obs (n + 1)) >
          get_current_slot cfg (E.store cfg ext obs n)
      · have hhead := E.head_root_known_at_observer cfg ext hcoh (n + 1) hH
        simp only [Execution.weakFcr, hcall, if_true, Weak.on_fast_confirmation,
          Weak.update_fast_confirmation_variables]
        split_ifs <;> exact hhead
      · have hcarry :=
          (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
        simpa only [Execution.weakFcr, hcall, if_false] using hcarry

/-- Weak twin of `Execution.fcrStep_previousSlotHead_known`. -/
theorem weakFcrStep_previousSlotHead_known
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
        ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs) (n : Nat)
    (hH : E.WithinHorizon cfg (n + 1)) :
    (E.weakFcrStep cfg ext obs n).previous_slot_head ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots := by
  have hnH : E.WithinHorizon cfg n :=
    E.withinHorizon_mono cfg (Nat.le_succ n) hH
  have hknownN := weakFcr_currentSlotHead_known cfg ext hgen hcoh n hnH
  have hknownN1 :=
    (E.store_storeLE cfg ext obs (Nat.le_succ n)).1 hknownN
  simp only [Execution.weakFcrStep, Weak.update_fast_confirmation_variables]
  split_ifs <;> exact hknownN1

end Weak

end FastConfirmation.Spec
