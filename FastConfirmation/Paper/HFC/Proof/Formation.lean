module
public import FastConfirmation.Paper.HFC.Proof.Justification
public import FastConfirmation.Paper.LMDGhost.Proof.Support
public import FastConfirmation.Paper.LMDGhost.Model.Assumptions

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

/-- **§4.1 certificate formation** (arXiv:2405.00549 Lemma 13 / SIR.3) — the FFG
    certificate for the canonical epoch-`e` checkpoint `T` is **proved**, not assumed.

    Given that every honest epoch-`e` committee member's prescribed FFG vote has a common
    source `S` (`hsrc`) and a common target `T` (`htgt`) — the inductive invariants of the
    joint canonical/justified induction, which hold with `T = C(B,e)` and `S` the previous
    epoch's justified checkpoint while `B` is canonical — and that `S` is justified in every
    honest view after delivery (`hSjust`), the target `T` is `Justified` in **every** honest
    view at every time after epoch `e`'s votes are delivered (`st(lslot e + 1)` on).

    The proof: each honest committee member casts its vote (`votesHead`), that message is an
    `HonestCast` whose FFG payload is pinned `S → T` (`HonestFFGNoEquivocation`); `Assumption3`
    (`hA3`) delivers it to every honest view; so the `S → T` link weight in any honest view
    dominates the honest committee weight, which is `≥ (1−β)·W > (2/3)·W` (`CommitteeHonestMajority`
    + `CommitteeCoversEpoch` + `β < 1/3`); `Justified.link` from the justified source closes it. -/
theorem checkpoint_justified_of_canonical (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    {e : Epoch} {S T : Checkpoint n}
    (hMono : ViewsMonotone 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hA3 : Assumption3 τ fm 𝒱)
    (hcm : CommitteeHonestMajority fm cm bal₀)
    (hcover : CommitteeCoversEpoch τ cm e)
    (hgst : τ.AfterGST (τ.st (τ.lslot e)))
    (htgt : ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.epochOf s = e → v ∈ cm.member s →
      checkpointOf τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 v (τ.st s)) boost pb (ffgFilter bal₀ τ)
        (𝒱 v (τ.st s)) (τ.st s)) e = T)
    (hsrc : ∀ ⦃v : Validator n⦄, v ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.epochOf s = e → v ∈ cm.member s →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 v (τ.st s)) boost pb
        (ffgFilter bal₀ τ) (𝒱 v (τ.st s)) (τ.st s)) (τ.st s) = S)
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot e + 1) ≤ t' → Justified bal₀ (𝒱 w t') S) :
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot e + 1) ≤ t' → Justified bal₀ (𝒱 w t') T := by
  intro w hw t' ht'
  -- Step 1: every honest validator's pinned `S → T` vote is delivered into `𝒱 w t'`.
  have hsign : ∀ i ∈ fm.honest, ∃ m ∈ (𝒱 w t').msgs,
      m.ghost.validator = i ∧ m.extra.source = S ∧ m.extra.target = T := by
    intro i hi
    -- `i` lies in the epoch-`e` committee union (= `univ`), so it votes at some slot `s` of `e`.
    have hiU : i ∈ committeeUnion cm (τ.fslot e) (τ.lslot e) := by
      rw [hcover]; exact Finset.mem_univ i
    rw [committeeUnion, Finset.mem_biUnion] at hiU
    obtain ⟨s, hsIcc, hmem⟩ := hiU
    rw [Finset.mem_Icc] at hsIcc
    have hes : τ.epochOf s = e := epochOf_of_mem_epoch τ hsIcc.1 hsIcc.2
    -- `votesHead` gives `i`'s GHOST vote message in its own view at `st s`.
    obtain ⟨gv, hgvmem, hgvslot, _hgvblock⟩ := hHB.votesHead hi hmem
    rw [View.votesOf, Finset.mem_filter] at hgvmem
    obtain ⟨hgvg, hgvval⟩ := hgvmem
    obtain ⟨m, hmmsg, _hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hgvg
    have hmval : m.ghost.validator = i := by rw [hmg]; exact hgvval
    have hmslot : m.ghost.slot = s := by rw [hmg]; exact hgvslot
    -- That message is an `HonestCast`, so `HonestFFGNoEquivocation` pins its FFG payload.
    have hcast : HonestCast fm 𝒱 τ m := by
      refine ⟨by rw [hmval]; exact hi, ?_⟩
      rw [hmval, hmslot]; exact hmmsg
    obtain ⟨htg, hsr⟩ := hnoequiv hcast
    rw [hmval, hmslot, hes] at htg
    rw [hmval, hmslot] at hsr
    have htgT : m.extra.target = T := htg.trans (htgt hi hes hmem)
    have hsrS : m.extra.source = S := hsr.trans (hsrc hi hes hmem)
    -- `Assumption3` delivers `m` to `w`'s view by `st(lslot e + 1)`, then monotonicity to `t'`.
    have hdeliv : m ∈ (𝒱 w (τ.st (τ.lslot e + 1))).msgs :=
      hA3 hw hcast (by rw [hmslot]; exact hsIcc.2) hgst
    exact ⟨m, (hMono w _ _ ht').1 hdeliv, hmval, hsrS, htgT⟩
  -- Step 2: the `S → T` link weight dominates the honest committee weight.
  have hlinkge : totalWeight bal₀ fm.honest ≤ linkWeight bal₀ (𝒱 w t') S T := by
    unfold linkWeight
    refine totalWeight_mono bal₀ ?_
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hsign i hi⟩
  -- Step 3: honest committee weight `≥ (1−β)·W` (cover + honest majority).
  have hcmW : (1 - fm.β) * totalWeight bal₀ Finset.univ ≤ totalWeight bal₀ fm.honest := by
    have h := hcm (τ.fslot e) (τ.lslot e)
    rw [hcover] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    ext i
    simp
  -- Step 4: `3·linkWeight ≥ 2·W` (since `β < 1/3 ⇒ 3(1−β) ≥ 2`).
  have hW0 : 0 ≤ totalWeight bal₀ Finset.univ := by
    unfold totalWeight; exact Finset.sum_nonneg (fun i _ => (bal₀.hpos i).le)
  have hbound : 3 * linkWeight bal₀ (𝒱 w t') S T ≥ 2 * totalWeight bal₀ Finset.univ := by
    nlinarith [hlinkge, hcmW, hW0,
      mul_nonneg (show (0:ℚ) ≤ 1 - 3 * fm.β by linarith [fm.hβ]) hW0]
  exact Justified.link (hSjust hw ht') hbound

end FastConfirmation.HFC

end
