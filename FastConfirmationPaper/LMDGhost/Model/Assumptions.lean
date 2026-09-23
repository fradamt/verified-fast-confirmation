module
public import FastConfirmationPaper.LMDGhost.Model.Weights

@[expose] public section

/-!
# LMDGhost / Model / Assumptions

The genuine **environmental / economic assumptions** of §3 (Assumptions 1, 2),
as opposed to the network model (`Synchrony`) and the honest voting protocol
(`HonestBehavior`). These are hypotheses of the theorems, discharged by the
deployment's economics, not properties we prove.
-/

namespace FastConfirmation.LMDGhost

open scoped Block

variable {n : ℕ} {P : Type}

/-- **Assumption 2.** Over every committee union (at anchor `A`), honest weight is at
    least `(1 - β)` of the total. This is the bridge from the all-voter `Q`-threshold
    (Def 8) to an honest majority (Lemmas 3–4); `β < 1/3` alone is not enough. -/
def CommitteeHonestMajority (fm : FaultModel n) (cm : Committees n) (A : Anchor n) : Prop :=
  ∀ lo hi : Slot,
    (1 - fm.β) * totalWeight A (committeeUnion cm lo hi)
      ≤ totalWeight A ((committeeUnion cm lo hi).filter (fun i => i ∈ fm.honest))

/-- **Single-slot committee minority** (an ADDED committee-size assumption, at anchor `A`). The
    committee assigned to any *single* slot controls strictly less than `(2/3 − β)` of the total
    stake. **This is a genuine added hypothesis, NOT a consequence of the model's existing
    assumptions:** the paper's committee *partition* (the `⊔`, i.e. disjointness across the
    `slotsPerEpoch` slots) and `CommitteeHonestMajority` / Assumption 2 (an honest-*fraction* lower
    bound over committee *unions*) do **not** bound a single slot's *total* weight from above — that
    requires this size/spread condition. It is true of real Ethereum (committees
    ≈ `W / slotsPerEpoch` per slot, far below `(2/3 − β)·W`), and is the slot-level counterpart of
    `CommitteeHonestMajority`, but it is a real premise. It is what makes "no checkpoint of the
    *current* epoch can be justified
    at that epoch's *first* slot" hold (a single slot's votes cannot reach a `2/3` target): see
    `justified_epoch_le_of_firstSlot`
    (`FastConfirmation/Paper/HFC/Proof/Certificate.lean`), which the previous-epoch base
    case consumes to bound the witness voting source's epoch. -/
def SlotCommitteeMinority (fm : FaultModel n) (cm : Committees n) (A : Anchor n) : Prop :=
  ∀ s : Slot, totalWeight A (cm.member s) < (2 / 3 - fm.β) * totalWeight A Finset.univ

/-- **Assumption 1** (static balances). Every anchor produced by `gj` assigns the same
    balance to each validator — the validator set and balances are static (except
    slashing). This implies the GJ-weight-non-increase condition of Lemma 6. -/
def StaticBalances (gj : ViewFamily n P → Validator n → Time → Anchor n)
    (𝒱 : ViewFamily n P) : Prop :=
  ∀ (v : Validator n) (t : Time) (v' : Validator n) (t' : Time) (i : Validator n),
    (gj 𝒱 v t).bal i = (gj 𝒱 v' t').bal i

/-- **Assumption 1 corollary** (static validator set ⇒ full-epoch coverage), at the
    *operative epoch* `e`. The committees of epoch `e` — the slots `[fslot e, lslot e]` —
    together cover the *whole* validator set. Because the validator set is static
    (Assumption 1, no joins or exits), every validator is assigned to some committee in
    epoch `e`. The paper uses this verbatim in Lemma 8
    (`lem:canonical-for-an-epoch-implies-q-satisfied`): over a full epoch the committee
    union has total weight `W_t`. It delivers two facts the crux needs: (i)
    `W_{b'}^{slot(t')-1} = totalWeight univ` (so `Wp / W_{b'} = pb`), and (ii) every honest
    validator votes at some slot of epoch `e`, where head-safety holds — so `H = J`. Taking
    the epoch as a parameter (rather than `∀ e`) matches the paper, which only needs
    coverage of the single epoch the monotonicity step operates over. -/
def CommitteeCoversEpoch (τ : Timing) (cm : Committees n) (e : Epoch) : Prop :=
  committeeUnion cm (τ.fslot e) (τ.lslot e) = Finset.univ

/-- **Anchor-coincidence premise** (the §3.1 specialization of Lemma 6 hypothesis (4)).
    Every honest validator's greatest-justified anchor (read at any slot's start view)
    coincides with the engine anchor `C`. This is *strictly implied* by `StaticBalances`
    together with `C := gj 𝒱 v t` (all `gj`-anchors then assign identical balances, so as
    `Stakes` they are the same balance source — see `AnchorsCoincide_of_StaticBalances`).
    It pins honest voters' fork-choice anchor to `C`, so an honest vote for *its own*
    `gj`-head is a vote for the `C`-head the induction reasons about. -/
def AnchorsCoincide (gj : ViewFamily n P → Validator n → Time → Anchor n)
    (𝒱 : ViewFamily n P) (fm : FaultModel n) (τ : Timing) (C : Anchor n) : Prop :=
  ∀ ⦃j : Validator n⦄, j ∈ fm.honest → ∀ (kk : Slot), gj 𝒱 j (τ.st kk) = C

end FastConfirmation.LMDGhost

end
