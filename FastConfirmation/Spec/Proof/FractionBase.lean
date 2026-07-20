import FastConfirmation.Spec.Proof.Fraction
import FastConfirmation.Spec.Proof.HonestWeight
import FastConfirmation.Spec.Proof.EngineInduction

/-!
# Spec / Proof / FractionBase (the base conversion)

The confirmation-time identifications the fraction/ledger engine consumes:
turning L2's honest-support term (`honest_support_majority` / `AttSupporters`
list-sums, `HonestWeight` + `QuorumAccounting`) into ground-truth `Finset`
weights and, once supporters are confined to the span committee, into
`Fraction.Hspec` — so the fraction/ledger numerator `H₀` *is* L2's
honest-support term. (The denominator `J₀ = Jspec a b` is definitionally the
honest committee weight — no lemma needed.)

**`ByzantineBound` revision.** The former endpoint-base results — honest-committee
positivity `Jspec_pos` and the `strong_base_unprovable_witness` β-mismatch
analysis — are **removed**: they served `Fraction.lean`'s deleted
absolute-margin endpoint (`Hmargin_of_fraction`), calibrated at a committee
Byzantine fraction `β = 1/3` that mismatched the confirmation's own
`β = CONFIRMATION_BYZANTINE_THRESHOLD/100 ≤ 1/4` reservation. The INV\* ledger
(`Proof/Ledger.lean`, `Proof/Base.lean`) supersedes that endpoint with a single
min-potential invariant consuming `ByzantineBound.span_fraction` directly. What
remains — and what INV\*'s base still uses — is the registry identification of
the honest-supporter list-sum with `E.Hspec`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Registry identifications: the confirmation list-sums are `Hspec`

`honest_support_majority` (`HonestWeight`) states the honest-support term as a
`List.sum` of the balance source's effective balances over the honest slice of
`AttSupporters`. Registry constancy (`hval`) turns those into ground-truth
weights and the supporter list's `Nodup` identifies the list-sum with a `Finset`
weight (`E.weight`); supporter confinement (`hspan`, discharged by
`QuorumAccounting.supporter_mem_span_committee`) then rewrites that `Finset` as
the `Hspec` filter set. So the fraction/ledger numerator `H₀` *is*
`honest_support_majority`'s honest term. -/

omit [Inhabited Root] in
/-- The honest-supporter list-sum equals the ground-truth weight of the honest
supporters as a `Finset` (mirror of `byz_score_eq_weight` for the honest slice). -/
theorem honest_score_eq_weight {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry) :
    (((AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum =
      E.weight (((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).toFinset) := by
  have hLnodup : ((AttSupporters cfg store (get_node_for_root b) bs).filter
      (fun i => i ∈ E.honest)).Nodup := (AttSupporters_nodup cfg store _ bs).filter _
  have hmap : ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map (fun i => (bs.validators.getD i default).effective_balance)
      = ((AttSupporters cfg store (get_node_for_root b) bs).filter
        (fun i => i ∈ E.honest)).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [hmap]
  exact (List.sum_toFinset E.weight_of hLnodup).symm

omit [Inhabited Root] in
/-- The honest supporters (as a `Finset`), once confined to the span committee
`[a, b_slot]` (`hspan`), coincide with the `Hspec` filter set for the "is a
supporter" predicate. Hence the honest-support list-sum *is* `E.Hspec` for that
predicate: the fraction/ledger numerator `H₀` at the confirming store. -/
theorem honest_supporter_weight_eq_Hspec {store : Store Root} {bs : BeaconState Root}
    {b : Root} {a b_slot : Slot} (hval : bs.validators = E.registry)
    (hspan : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs, i ∈ E.honest →
      i ∈ E.span_committee a b_slot) :
    (((AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      = E.Hspec a b_slot
          (fun i => i ∈ (AttSupporters cfg store (get_node_for_root b) bs).toFinset) := by
  rw [honest_score_eq_weight cfg E hval]
  simp only [Execution.Hspec]
  congr 1
  ext i
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hiA, hih⟩
    exact ⟨hspan i hiA hih, hih, hiA⟩
  · rintro ⟨_, hih, hiA⟩
    exact ⟨hiA, hih⟩

end Execution

end FastConfirmation.Spec
