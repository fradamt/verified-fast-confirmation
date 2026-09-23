module
public import FastConfirmationModel.Weak.WeakSynchrony
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-! Weak certificate obligations used by the safety proof. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak

/-! ## Proof obligations

The two dissemination facts the weak-model safety proof must establish,
stated as named `Prop`s so the migration target is pinned without proof placeholders.
The proof plan lives in `docs/weak-synchrony.md`. -/

/-- **Obligation 1 — certificate surplus is honest.** In any store within the
horizon (in particular the observer's), a broadcast certificate implies some
*honest* validator cast a counted vote: a vote at its assigned slot in the
span, for `block_root` or a descendant. Follows from the certificate
inequality once the economic bound ties the counted non-honest weight to the
weak adversarial budget (the `ByzantineWeightPremises`/committee-estimation soundness
package, undiscounted).

Instance-specific premises: the balance source reads the ground registry
(`registryConstant`/`checkpoint_states_total_active_balance` discharge these at
the rule's actual balance sources, at every node), and the store-computed slot
committees read back the ground-truth assignment
(`Execution.PrefixCommitteeAgreement`; cf. `ObserverContext` — the honest-only
`BeaconExternalsPremises.committees_agree` is unusable at the observer). -/
def CertificateHonestSupporter (E : Execution Root) : Prop :=
  ∀ (v : ValidatorIndex) (n : ℕ) (balance_source : BeaconState Root)
    (block_root : Root) (start_slot end_slot : Slot),
    E.WithinHorizon cfg n →
    E.SlotWithinHorizon cfg start_slot →
    E.SlotWithinHorizon cfg end_slot →
    balance_source.validators = E.registry →
    get_total_active_balance cfg balance_source = E.total_active cfg →
    (∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s) →
    has_broadcast_certificate cfg ext (E.store cfg ext v n) balance_source block_root
      start_slot end_slot = true →
    ∃ w ∈ E.honest, ∃ s : Slot, start_slot ≤ s ∧ s ≤ end_slot ∧
      w ∈ E.committee s ∧
      ∃ (nw : ℕ) (a : Attestation Root), E.vote w s = some (nw, a) ∧
        a.data.slot = s ∧
        a.data.beacon_block_root ∈ (E.store cfg ext v n).block_roots ∧
        is_ancestor (E.store cfg ext v n) (get_node_for_root a.data.beacon_block_root)
          (get_node_for_root block_root) = true

/-- **Obligation 2 — certificates disseminate.** A broadcast certificate over
`[start_slot, end_slot]` observed in any store within the horizon implies
every honest validator holds `block_root` from slot `end_slot + 1` onward.
This is the weak-model replacement for applying `Synchrony.block_relay` to the
observer as holder: the honest supporter of Obligation 1 held the chain by its
vote's slot (honest votes are computed from the voter's own store), and
`block_relay` applies to *that* validator.

Beyond Obligation 1's premises: the span starts at or after the execution's
first slot (`votes_head`'s scope), and `block_root` is known to the observing
store — carried instead of a genesis-start anchor hypothesis, which is strictly
stronger and would not survive checkpoint sync (intended call sites discharge
this knownness from `is_one_confirmed`, cf. `hbconf_of_genesisStart`). -/
def CertificateDissemination (E : Execution Root) : Prop :=
  ∀ (v : ValidatorIndex) (n : ℕ) (balance_source : BeaconState Root)
    (block_root : Root) (start_slot end_slot : Slot),
    E.WithinHorizon cfg n →
    E.SlotWithinHorizon cfg start_slot →
    E.SlotWithinHorizon cfg end_slot →
    E.slot_at cfg 0 ≤ start_slot →
    balance_source.validators = E.registry →
    get_total_active_balance cfg balance_source = E.total_active cfg →
    (∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s) →
    block_root ∈ (E.store cfg ext v n).block_roots →
    has_broadcast_certificate cfg ext (E.store cfg ext v n) balance_source block_root
      start_slot end_slot = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
      end_slot + 1 ≤ E.slot_at cfg m →
      block_root ∈ (E.store cfg ext w m).block_roots

end Weak
end FastConfirmation.Spec

end
