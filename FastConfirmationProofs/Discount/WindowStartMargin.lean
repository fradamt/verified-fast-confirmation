module
public import FastConfirmationProofs.Handlers.SupportClasses
public import FastConfirmationProofs.Discount.SupportDiscount
public import FastConfirmationProofs.Gloas.Payload.MajorityPersists
public import FastConfirmationProofs.FFG.Certificates.Quorum

@[expose] public section

/-!
# Spec / Proof / Base

This module contains `base_min_of_tax`, `base_min_of_R`, `weak_base_arith` and related declarations.
-/

namespace FastConfirmation.Spec

/-! ## Section 1 — the pure-ℕ ledger base arithmetic (the min collapse)

All quantities are pre-scaled by `C := confirmation_byzantine_threshold` or
`100 − C`; `s`, `x`, `B`, `J` read as `Sval`, `Xval`, `Bval`, `Jspec` at `es`.
The two branch hypotheses are the confirmed-instance obligations; the assembly
bounds `min` by whichever holds. Truncation-free additive form so `omega` never
needs to reason about `ℕ` subtraction. -/

/-- **Tax branch.** The confirmed instance's recurrence-tax funded base — bounds
`min` by its left arm `C·s`: `(100−C)·(x+B+boost+1) + C·s ≤ (100−C)·s`
(equivalently `(★): (100−2C)·s ≥ (100−C)·(x+B+boost+1)`). Corner-3 (`a₀`-heavy)
lands here. -/
private theorem base_min_of_tax {C s x B J boost : ℕ}
    (htax : (100 - C) * (x + B + boost + 1) + C * s ≤ (100 - C) * s) :
    (100 - C) * (x + B + boost + 1) + min (C * s) (C * J - (100 - C) * B) ≤ (100 - C) * s :=
  le_trans (by gcongr; exact min_le_left _ _) htax

/-- **R branch.** The confirmed instance's F3-capacity base — bounds `min` by its
right arm `C·J − (100−C)·B` (the remaining window byz capacity, un-truncated by
`Rterm_nonneg`): `(100−C)·(x+B+boost+1) + (C·J − (100−C)·B) ≤ (100−C)·s`.
Corner-1 (byz at cap, `R = 0`) lands here. -/
private theorem base_min_of_R {C s x B J boost : ℕ}
    (hR : (100 - C) * (x + B + boost + 1) + (C * J - (100 - C) * B) ≤ (100 - C) * s) :
    (100 - C) * (x + B + boost + 1) + min (C * s) (C * J - (100 - C) * B) ≤ (100 - C) * s :=
  le_trans (by gcongr; exact min_le_right _ _) hR



/-- Pure-ℕ core of the weak base. From the rule `2·Hsup + d ≥ MS + boost + 1`,
the estimate domination `J + B ≤ MS`, the honest partition `J = s + a + x`, and
the two recorded-slice bridges `Hsup ≤ s`, `d ≤ a`, the endpoint-form margin
`s ≥ x + B + boost + 1` follows (the `a` and the extra `Hsup` on the rule's
majority side cancel the partition's `a`, leaving the bare margin). -/
private theorem weak_base_arith {Hsup d MS boost s a x B J : ℕ}
    (hsm : 2 * Hsup + d ≥ MS + boost + 1)
    (hHsup : Hsup ≤ s) (hdisc : d ≤ a) (hMS : J + B ≤ MS) (hpart : J = s + a + x) :
    x + B + boost + 1 ≤ s := by omega

/-! ## Section 1′ — machine-checked corner coverage

Both corners are `C = 25`. Each satisfies exactly one branch and fails the
other, confirming the `min` assembly needs the disjunction. The `example`s
instantiate the branch lemmas at the corner numbers and check the assembled
INV\*(es) inequality (with the concrete `min`) elaborates. -/

/-- **Corner 3** (`a₀`-heavy tax branch): `J₀ = 9000`, `x₀ = 249`,
`B₀ = 1000`, `s₀ = 2751`, `boost = 584` — the `(★)` tax base is tight
(`50·2751 = 75·1834 = 137550`) and funds the left `min` arm `C·s₀ = 68775`
(< the R arm `150000`). The R branch fails here. -/
example :
    (100 - 25) * (249 + 1000 + 584 + 1)
        + min (25 * 2751) (25 * 9000 - (100 - 25) * 1000)
      ≤ (100 - 25) * 2751 :=
  @base_min_of_tax 25 2751 249 1000 9000 584 (by norm_num)

/-- **Corner 1** (Byzantine weight at cap, `R = 0`): `J₀ = 75`, `B₀ = 25`, `s₀ = 74`,
`x₀ = 0`, `boost = 48` — the F3 capacity `R = 25·75 − 75·25 = 0` is the right
`min` arm and the R base is tight (`75·74 = 5550`). The `(★)` tax base fails here
(`50·74 = 3700 < 75·74 = 5550`). -/
example :
    (100 - 25) * (0 + 25 + 48 + 1)
        + min (25 * 74) (25 * 75 - (100 - 25) * 25)
      ≤ (100 - 25) * 74 :=
  @base_min_of_R 25 74 0 25 75 48 (by norm_num)

namespace Execution

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
variable (E : Execution Root)

/-! ## Section 2 — `U(es) = s₀`

At the window start the not-yet-recurred set is all of `Sclass es`: the filter
"no committee assignment in `(es, es]`" is vacuous (`es < t ∧ t ≤ es` is
unsatisfiable). -/


/-! ## Section 3 — INV\*(es) from the branch disjunction

The min-assembly over the ledger accessor values: given the confirmed instance's
branch disjunction on `s₀`/`x₀`/`B(es)`/`J₀`, INV\* holds at `σ = es`. -/


/-! ## Section 4 — the weak base from the confirmation rule

`honest_support_majority` at the confirming node `(v₀, n₀)` gives
`2·Hsup + d ≥ MS + boost + 1`. Two internal identifications close the
endpoint-form weak base `s₀ ≥ x₀ + B(es) + boost + 1`:

* `MS ≥ J₀ + B(es)` — `ByzantineBound.estimate_sound` on the window
  `[lo, es] = [parent+1, current−1]` (the rule's own `maximum_support` span),
  split honest/non-honest by `weight_split_honest`;
* `J₀ = s₀ + a₀ + x₀` — `Ledger.weight_partition`.

The two store-dynamics facts are explicit hypotheses (the reverse
Provenance/Delivery bridge — recorded latest messages imply ground-truth newest
votes, mirroring `EngineSupport.mem_AttSupporters_honest` in the opposite
direction):

* `hHsup` — the recorded honest supporters are `Sclass es` members, so their
  weight `Hsup ≤ s₀`;
* `hdisc` — the discount `d ≤ a₀` (`Discount.support_discount_le_parent_stuck`
  + `ParentStuck ⊆ Aclass es`: recorded `lm = parent ⇒` newest vote's block
  `= parent`, an ancestor of `b′`, so `Aclass`). -/

/-- **The weak base** `s₀ ≥ x₀ + B(es) + boost + 1` from `honest_support_majority`.
`lo := parent(b′).slot + 1`, `es := current_slot − 1`, `boost :=
compute_proposer_score`. The `maximum_support` estimate dominates the honest
committee-union plus enemy weight, and the honest supporters/discount are the
`Sclass`/`Aclass` recorded slices (`hHsup`/`hdisc`). This is the endpoint-form
margin; the branch-selection premise funds it into `(★)`/`(★R)`. -/
theorem weak_base_of_rule
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ : ValidatorIndex} (hv : v₀ ∈ E.honest) {n₀ : ℕ}
    (hnH : E.WithinHorizon cfg n₀)
    (hwf : ∀ r ∈ (E.store cfg ext v₀ n₀).block_roots,
      ((E.store cfg ext v₀ n₀).blocks r).parent_root ∈ (E.store cfg ext v₀ n₀).block_roots →
        ((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks r).parent_root).slot <
          ((E.store cfg ext v₀ n₀).blocks r).slot)
    {bs : BeaconState Root} {b' : Root}
    (hbH : E.SlotWithinHorizon cfg ((E.store cfg ext v₀ n₀).blocks b').slot)
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext v₀ n₀))
      (E.store cfg ext v₀ n₀))
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v₀ n₀) bs b' = true)
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs, ∀ lm,
      (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v₀ n₀) ((E.store cfg ext v₀ n₀).blocks b').slot lm.root)
    (lo es : Slot)
    (hlo : lo = ((E.store cfg ext v₀ n₀).blocks
      ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (hes : es = get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    (hHsup : (((AttSupporters cfg (E.store cfg ext v₀ n₀) (get_node_for_root b') bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hdisc : get_support_discount cfg ext (E.store cfg ext v₀ n₀) bs b'
      ≤ E.Aval cfg ext v₀ n₀ b' lo es) :
    E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es + compute_proposer_score cfg bs + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es := by
  subst hlo hes
  have hsm := honest_support_majority cfg ext hhb hec hbb hgen hv hnH hwf hbH
    hval htab hprov hconf hwalk
  have hpart := E.weight_partition cfg ext v₀ n₀ b'
    (((E.store cfg ext v₀ n₀).blocks ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
  have hsplit : E.weight (E.span_committee
        (((E.store cfg ext v₀ n₀).blocks ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1))
      = E.Jspec
          (((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1)
        + E.Bval
          (((E.store cfg ext v₀ n₀).blocks
            ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
          (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1) := by
    rw [Execution.Jspec, Execution.Bval, Execution.Bwin]; exact E.weight_split_honest _
  have hMS := hbb.estimate_sound
    (((E.store cfg ext v₀ n₀).blocks ((E.store cfg ext v₀ n₀).blocks b').parent_root).slot + 1)
    (get_current_slot cfg (E.store cfg ext v₀ n₀) - 1) hloH hesH
  rw [hsplit] at hMS
  rw [htab] at hsm
  exact weak_base_arith hsm hHsup hdisc hMS hpart

end Execution

end FastConfirmation.Spec

end
