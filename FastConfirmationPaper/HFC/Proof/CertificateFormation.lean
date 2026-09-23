module
public import FastConfirmationPaper.HFC.Proof.Justification
public import FastConfirmationPaper.LMDGhost.Proof.Support
public import FastConfirmationPaper.LMDGhost.Model.Assumptions

@[expose] public section

/-!
# HFC / Proof / Formation

**Certificate formation** — the forward FFG argument of §4.1 (arXiv:2405.00549,
Lemma 13 / SIR.3): the §4 layer no longer *assumes* that the FFG certificate for the
canonical checkpoint exists; it **proves** the checkpoint becomes `Justified` from honest
voting behaviour, the committee honest-majority, `β < 1/3`, and **Assumption 3** (FFG
inclusion). This is the missing *forward* direction (`CrossEpoch.lean` is its backward
inverse: `Justified ⇒ honest voter ⇒ target pinned`).

The keystone is `checkpoint_justified_of_canonical`: if every honest epoch-`e` committee
member's FFG vote is pinned to a common source `S` and a common target `T`
(`= C(B,e)` when `B` is canonical — the inductive invariants the joint canonical/justified
induction maintains), then `T` is justified in **every** honest view once epoch `e`'s votes
are delivered. **No new economic/environmental assumption is introduced** — FFG-vote
*existence* is free from the GHOST primitive `HonestBehavior.votesHead` (its witnessing
message is an `HonestCast`, whose `.extra` payload `HonestFFGNoEquivocation` pins), and
delivery is exactly `Assumption3`. The honest weight `≥ 2/3` is `CommitteeHonestMajority`
(`(1−β)`) closed under `β < 1/3` (so `3(1−β) ≥ 2`).
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- A slot in the range `[fslot e, lslot e]` lies in epoch `e`. -/
theorem epochOf_of_mem_epoch (τ : Timing) {e : Epoch} {s : Slot}
    (hlo : τ.fslot e ≤ s) (hhi : s ≤ τ.lslot e) : τ.epochOf s = e := by
  have hpos := τ.hSlotsPerEpoch
  have hlo' : e * τ.slotsPerEpoch ≤ s := hlo
  have hhi' : s ≤ e * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) := hhi
  have hub : s < (e + 1) * τ.slotsPerEpoch := by
    have h1 : e * τ.slotsPerEpoch + τ.slotsPerEpoch = (e + 1) * τ.slotsPerEpoch := by ring
    have h2 : τ.slotsPerEpoch - 1 < τ.slotsPerEpoch := Nat.sub_lt hpos one_pos
    calc s ≤ e * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) := hhi'
      _ < e * τ.slotsPerEpoch + τ.slotsPerEpoch := Nat.add_lt_add_left h2 _
      _ = (e + 1) * τ.slotsPerEpoch := h1
  change s / τ.slotsPerEpoch = e
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpos).mpr hub)
  · exact (Nat.le_div_iff_mul_le hpos).mpr hlo'


end FastConfirmation.HFC

end
