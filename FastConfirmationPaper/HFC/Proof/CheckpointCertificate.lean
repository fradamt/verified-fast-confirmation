module
public import FastConfirmationPaper.HFC.Proof.CertificateFormation
public import FastConfirmationPaper.HFC.Proof.CrossEpoch
public import FastConfirmationPaper.HFC.Model.AnchorRule

@[expose] public section

/-!
# HFC / Proof / Certificate — `willChkpBeJustified ⇒ C(b,e) justified` (paper Lemma 13)

The §4.1 certificate lemma (arXiv:2405.00549 `lem:sufficient-condition-for-justification`,
l.2843), **proved** — not assumed — in our gossip-justification model. It is the
`willChkpBeJustified` analogue of the keystone `checkpoint_justified_of_canonical`
(`FastConfirmationPaper/HFC/Proof/CertificateFormation.lean`): the keystone needs the *whole* epoch committee canonical, which fails for the
early-confirmation-epoch voters (slots `< slot(t)`, before `b` is safe). Here the weight is split
exactly as the local rule's reservation does:

* the **observed** part `linkWeightUpTo (𝒱 v t) S T (slot(t)-1)` — FFG votes for `S → T` *already
  seen* in the confirming honest view `𝒱 v t` (committee slots `≤ slot(t)-1`, of any provenance);
* the **honest-future** part `(1-β)·committee[slot(t), lslot e]` — the honest fraction of the rest
  of the epoch's committee, which (canonical from `slot(t)` on) FFG-vote `S → T`.

Both halves reach *every* honest view by the epoch-end boundary via **`Synchrony.messageRelay`**
(gossip relay): the observed votes — *including adversary-authored ones* — because some honest
validator already holds them; the future honest votes because they are honest casts. The two
committee slot-ranges are **disjoint** (`hdisj`: each validator sits in one committee slot per
epoch — Ethereum's partition, the paper's `⊔`), so the seen `S → T` weight in any honest view is
`≥ observed + (1-β)·future ≥ ⅔W` by `willChkpBeJustified`; `Justified.link` from the (justified)
anchor `S` closes it. The `min(we, β·W)` slashable margin is pure slack here — relay carries the
observed Byzantine votes honestly (no on-chain inclusion limit to defend against, unlike the paper's
Assumption 5.3, which our gossip model dissolves).
-/

namespace FastConfirmation.HFC

open FastConfirmation FastConfirmation.LMDGhost
open scoped Block

variable {n : ℕ}

/-- **§4.1 certificate formation from the local reservation** (arXiv:2405.00549 Lemma 13). With `S`
    the common FFG source (the justified anchor) and `T` the common target `C(b,e)`, if the honest
    future committee `[slot(t), lslot e]` FFG-votes `S → T` (canonicity, via `htgt`/`hsrc`), the
    local
    `willChkpBeJustified` weight bound `hwill` holds in the confirming honest view `𝒱 v t`, and the
    observed/future committee ranges are disjoint (`hdisj`), then `T` is `Justified` in every honest
    view from `st(lslot e + 1)` on. Proof: gossip relay (`hRelay`) puts both the observed `S → T`
    votes and the honest future `S → T` votes into every honest view; their disjoint weight is
    `≥ observed + (1-β)·future ≥ ⅔W` (`hwill`); `Justified.link` from `hSjust`. -/
theorem checkpoint_justified_of_willChkp (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    {v : Validator n} {t : Time} {e : Epoch} {S T : Checkpoint n}
    (hv : v ∈ fm.honest)
    (hRelay : ∀ ⦃a c : Validator n⦄, a ∈ fm.honest → c ∈ fm.honest →
      ∀ ⦃tt : Time⦄ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄, m ∈ (𝒱 a tt).msgs →
        τ.slotOf tt ≤ s' → τ.AfterGST (τ.st s') → m ∈ (𝒱 c (τ.st (s' + 1))).msgs)
    (hMono : ViewsMonotone 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hcm : CommitteeHonestMajority fm cm bal₀)
    (hgst : τ.AfterGST (τ.st (τ.lslot e)))
    (hte : τ.epochOf (τ.slotOf t) = e)
    (hwe0 : 0 ≤ we)
    (hdisj : Disjoint (committeeUnion cm (τ.fslot T.epoch) (τ.slotOf t - 1))
                      (committeeUnion cm (τ.slotOf t) (τ.lslot e)))
    (hwill : linkWeightUpTo bal₀ cm τ (𝒱 v t) S T (τ.slotOf t - 1)
              + (1 - fm.β) * totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e))
              ≥ (2 / 3) * totalWeight bal₀ Finset.univ
                + min we (fm.β * totalWeight bal₀ Finset.univ))
    (htgt : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s → τ.epochOf s = e →
      i ∈ cm.member s →
      checkpointOf τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb (ffgFilter bal₀ τ)
        (𝒱 i (τ.st s)) (τ.st s)) e = T)
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s → τ.epochOf s = e →
      i ∈ cm.member s →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st s)) (τ.st s)) (τ.st s) = S)
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot e + 1) ≤ t' → Justified bal₀ (𝒱 w t') S) :
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot e + 1) ≤ t' → Justified bal₀ (𝒱 w t') T := by
  classical
  intro w hw t' ht'
  -- `fslot e ≤ slotOf t ≤ lslot e` (the confirmation slot lies in epoch `e`).
  have hfslot_le : τ.fslot e ≤ τ.slotOf t := by
    unfold Timing.fslot; rw [← hte]; unfold Timing.epochOf
    exact Nat.div_mul_le_self (τ.slotOf t) τ.slotsPerEpoch
  have hsl : τ.slotOf t ≤ τ.lslot e := by
    have := le_lslot_epochOf τ (τ.slotOf t); rwa [hte] at this
  -- The two committee sets whose `S → T` votes carry to `w`'s view.
  set ObsSet : Finset (Validator n) :=
    (committeeUnion cm (τ.fslot T.epoch) (τ.slotOf t - 1)).filter
      (fun i => ∃ m ∈ (𝒱 v t).msgs, m.ghost.validator = i ∧
        τ.fslot T.epoch ≤ m.ghost.slot ∧ m.ghost.slot ≤ τ.slotOf t - 1 ∧
        m.extra.source = S ∧ m.extra.target = T)
    with hObsSet
  set FutSet : Finset (Validator n) :=
    (committeeUnion cm (τ.slotOf t) (τ.lslot e)).filter (fun i => i ∈ fm.honest) with hFutSet
  -- Observed `S → T` votes (in `𝒱 v t`) relay into `𝒱 w t'`.
  have hObs : ∀ i ∈ ObsSet, ∃ m ∈ (𝒱 w t').msgs,
      m.ghost.validator = i ∧ m.extra.source = S ∧ m.extra.target = T := by
    intro i hi
    rw [hObsSet, Finset.mem_filter] at hi
    obtain ⟨_, m, hmmsg, hmval, _hmslotlo, _hmslotup, hmsrc, hmtgt⟩ := hi
    exact ⟨m, (hMono w _ _ ht').1 (hRelay hv hw hmmsg hsl hgst), hmval, hmsrc, hmtgt⟩
  -- Honest future committee votes `S → T` (canonical) and relays into `𝒱 w t'`.
  have hFut : ∀ i ∈ FutSet, ∃ m ∈ (𝒱 w t').msgs,
      m.ghost.validator = i ∧ m.extra.source = S ∧ m.extra.target = T := by
    intro i hi
    rw [hFutSet, Finset.mem_filter] at hi
    obtain ⟨hiU, hihon⟩ := hi
    rw [committeeUnion, Finset.mem_biUnion] at hiU
    obtain ⟨s, hsIcc, hmem⟩ := hiU
    rw [Finset.mem_Icc] at hsIcc
    have hsge : τ.slotOf t ≤ s := hsIcc.1
    have hsle : s ≤ τ.lslot e := hsIcc.2
    have hes : τ.epochOf s = e :=
      epochOf_of_mem_epoch τ (le_trans hfslot_le hsge) hsle
    obtain ⟨gv, hgvmem, hgvslot, _hgvblock⟩ := hHB.votesHead hihon hmem
    rw [View.votesOf, Finset.mem_filter] at hgvmem
    obtain ⟨hgvg, hgvval⟩ := hgvmem
    obtain ⟨m, hmmsg, _hLMD, hmg⟩ := mem_msg_of_mem_ghostVotes hgvg
    have hmval : m.ghost.validator = i := by rw [hmg]; exact hgvval
    have hmslot : m.ghost.slot = s := by rw [hmg]; exact hgvslot
    have hcast : HonestCast fm 𝒱 τ m := by
      refine ⟨by rw [hmval]; exact hihon, ?_⟩
      rw [hmval, hmslot]; exact hmmsg
    obtain ⟨htg, hsr⟩ := hnoequiv hcast
    rw [hmval, hmslot, hes] at htg
    rw [hmval, hmslot] at hsr
    have htgT : m.extra.target = T := htg.trans (htgt hihon hsge hes hmem)
    have hsrS : m.extra.source = S := hsr.trans (hsrc hihon hsge hes hmem)
    have hmview : m ∈ (𝒱 i (τ.st s)).msgs := by
      have h := hcast.2; rw [hmval, hmslot] at h; exact h
    have hdel : m ∈ (𝒱 w (τ.st (τ.lslot e + 1))).msgs :=
      hRelay hihon hw hmview (by rw [Timing.slotOf_st]; exact hsle) hgst
    exact ⟨m, (hMono w _ _ ht').1 hdel, hmval, hsrS, htgT⟩
  -- `ObsSet ∪ FutSet` ⊆ the `S → T` link set of `𝒱 w t'`, and the two are disjoint.
  have hdisj' : Disjoint ObsSet FutSet :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj)
  -- Weight chain: `⅔W ≤ observed + (1-β)·future ≤ totalWeight(Obs ∪ Fut) ≤ linkWeight`.
  have hW0 : 0 ≤ totalWeight bal₀ Finset.univ :=
    Finset.sum_nonneg (fun i _ => (bal₀.hpos i).le)
  have hmin0 : 0 ≤ min we (fm.β * totalWeight bal₀ Finset.univ) :=
    le_min hwe0 (mul_nonneg fm.hβ0 hW0)
  have hObsW : totalWeight bal₀ ObsSet = linkWeightUpTo bal₀ cm τ (𝒱 v t) S T (τ.slotOf t - 1) := by
    simp only [hObsSet, linkWeightUpTo]
  have hFutW : (1 - fm.β) * totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e))
      ≤ totalWeight bal₀ FutSet := by
    rw [hFutSet]; exact hcm (τ.slotOf t) (τ.lslot e)
  have hunion : totalWeight bal₀ (ObsSet ∪ FutSet)
      = totalWeight bal₀ ObsSet + totalWeight bal₀ FutSet := by
    unfold totalWeight; exact Finset.sum_union hdisj'
  have hmono : totalWeight bal₀ (ObsSet ∪ FutSet) ≤ linkWeight bal₀ (𝒱 w t') S T := by
    unfold linkWeight
    apply totalWeight_mono
    intro i hi
    rw [Finset.mem_union] at hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hi.elim (hObs i) (hFut i)⟩
  rw [hunion, hObsW] at hmono
  have hlink : (2 / 3) * totalWeight bal₀ Finset.univ ≤ linkWeight bal₀ (𝒱 w t') S T := by
    calc (2 / 3) * totalWeight bal₀ Finset.univ
        ≤ (2 / 3) * totalWeight bal₀ Finset.univ
            + min we (fm.β * totalWeight bal₀ Finset.univ) := le_add_of_nonneg_right hmin0
      _ ≤ linkWeightUpTo bal₀ cm τ (𝒱 v t) S T (τ.slotOf t - 1)
            + (1 - fm.β) * totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e)) := hwill
      _ ≤ linkWeightUpTo bal₀ cm τ (𝒱 v t) S T (τ.slotOf t - 1) + totalWeight bal₀ FutSet := by
          gcongr
      _ ≤ linkWeight bal₀ (𝒱 w t') S T := hmono
  exact Justified.link (hSjust hw ht') (by linarith)


/-- **The certificate, discharged from a confirmation (current-epoch).** Packages
    `checkpoint_justified_of_willChkp` for the confirmed block `b`, deriving the common-target
    premise `htgt` from head-safety (`hHeadb`: every honest head over `[slot(t), lslot e]` extends
    `b`) via `boundaryBlock_eq_of_ancestor` (prefix agreement: every such head computes the same
    `C(b,e)`). The common-**source** premise `hsrc` is the paper's `P-link`
    (`ldm-vote-for-b-is-ffg-vote-for-cb`, arXiv:2405.00549 l.2544), assumed as part of the Gasper
    interface. `hwill` is Algorithm 1's `willChkpBeJustified(b, epoch(b), t)`; `hSjust` the
    (justified) anchor `S = vs(b,t)`; `hpart` the
    committee-slot partition (the paper's `⊔`). Conclusion: `C(b,e)` is `Justified` in every honest
    view from `st(lslot e + 1)` on. -/
theorem certificate_of_confirmation (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    {v : Validator n} {b : Block n} {t : Time}
    (hv : v ∈ fm.honest)
    (hRelay : ∀ ⦃a c : Validator n⦄, a ∈ fm.honest → c ∈ fm.honest →
      ∀ ⦃tt : Time⦄ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄, m ∈ (𝒱 a tt).msgs →
        τ.slotOf tt ≤ s' → τ.AfterGST (τ.st s') → m ∈ (𝒱 c (τ.st (s' + 1))).msgs)
    (hMono : ViewsMonotone 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hcm : CommitteeHonestMajority fm cm bal₀)
    (hgst : τ.AfterGST (τ.st (τ.lslot (τ.epochOf b.slot))))
    (hte : τ.epochOf (τ.slotOf t) = τ.epochOf b.slot)
    (hwe0 : 0 ≤ we)
    (hbwf : b.WellFormed)
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf t - 1))
                      (committeeUnion cm (τ.slotOf t) (τ.lslot (τ.epochOf b.slot))))
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf b.slot) t)
    (hHeadb : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s →
      s ≤ τ.lslot (τ.epochOf b.slot) →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st s))
        (τ.st s))
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s →
      τ.epochOf s = τ.epochOf b.slot → i ∈ cm.member s →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st s)) (τ.st s)) (τ.st s)
        = ruleVotingSource bal₀ τ b t)
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (ruleVotingSource bal₀ τ b t)) :
    ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (checkpointOf τ b (τ.epochOf b.slot)) := by
  have hbfslot : τ.fslot (τ.epochOf b.slot) ≤ b.slot := by
    unfold Timing.fslot Timing.epochOf; exact Nat.div_mul_le_self b.slot τ.slotsPerEpoch
  refine checkpoint_justified_of_willChkp bal₀ (e := τ.epochOf b.slot)
    (S := ruleVotingSource bal₀ τ b t) (T := checkpointOf τ b (τ.epochOf b.slot))
    hv hRelay hMono hHB hnoequiv hcm hgst hte hwe0 hpart hwill ?_ hsrc hSjust
  -- `htgt`: every honest head over `[slot(t), lslot e]` computes the same `C(b,e)`
  -- (prefix agreement).
  intro i hi s hsge hsep hmem
  have hsle : s ≤ τ.lslot (τ.epochOf b.slot) := by rw [← hsep]; exact le_lslot_epochOf τ s
  have hbhead := hHeadb hi hsge hsle
  have hheadwf : (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb (ffgFilter bal₀ τ)
      (𝒱 i (τ.st s)) (τ.st s)).WellFormed :=
    forkChoiceHead_WellFormed (gjFFG bal₀ 𝒱 i (τ.st s)) (ffgFilter bal₀ τ) (𝒱 i (τ.st s)) (τ.st s)
  change checkpointOf τ _ (τ.epochOf b.slot) = checkpointOf τ b (τ.epochOf b.slot)
  unfold checkpointOf
  rw [boundaryBlock_eq_of_ancestor (τ.fslot (τ.epochOf b.slot)) hbhead hbwf hheadwf hbfslot]

/-- **The never-filter's comparability, from Algorithm 1 (current-epoch).** The drop-in replacement
    for `greatestRealizedJustified_on_chain`'s gate-consuming ANCESTOR call: concludes
    `block(GJ) ≼ b` with the gate replaced by `willChkpBeJustified` + the certificate machinery.
    Case B (`GJ.epoch < epoch(b)`) is the GU-anchor route; Case A (`GJ.epoch = epoch(b)`, pinned by
    `hGJub`) **derives** the certificate `C(b,epoch(b))` inline via `certificate_of_confirmation` —
    at which point realization forces `slotOf t' > lslot(epoch(b))`, so the head-safety window
    `hHead` covers `[slot(t), lslot(epoch(b))]` (giving `htgt`) and `t' ≥ st(lslot(epoch(b))+1)` (so
    the certificate fires) — then per-epoch
    uniqueness identifies `block(GJ) = C(b,epoch(b)).block ≼ b`. -/
theorem greatestRealizedJustified_on_chain_from_confirmation (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {pb : Weight} {we : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    {v : Validator n} {b : Block n} {t : Time}
    (hv : v ∈ fm.honest)
    (hRelay : ∀ ⦃a c : Validator n⦄, a ∈ fm.honest → c ∈ fm.honest →
      ∀ ⦃tt : Time⦄ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄, m ∈ (𝒱 a tt).msgs →
        τ.slotOf tt ≤ s' → τ.AfterGST (τ.st s') → m ∈ (𝒱 c (τ.st (s' + 1))).msgs)
    (hMono : ViewsMonotone 𝒱)
    (hHB : HonestBehavior τ fm cm (gjFFG bal₀) boost pb (ffgFilter bal₀ τ) 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hcm : CommitteeHonestMajority fm cm bal₀)
    (hgst : τ.AfterGST (τ.st (τ.lslot (τ.epochOf b.slot))))
    (hte : τ.epochOf (τ.slotOf t) = τ.epochOf b.slot)
    (hwe0 : 0 ≤ we) (hbwf : b.WellFormed)
    (hpart : Disjoint (committeeUnion cm (τ.fslot (τ.epochOf b.slot)) (τ.slotOf t - 1))
                      (committeeUnion cm (τ.slotOf t) (τ.lslot (τ.epochOf b.slot))))
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b (τ.epochOf b.slot) t)
    (hsrc : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s →
      τ.epochOf s = τ.epochOf b.slot → i ∈ cm.member s →
      ruleVotingSource bal₀ τ (forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb
        (ffgFilter bal₀ τ) (𝒱 i (τ.st s)) (τ.st s)) (τ.st s)
        = ruleVotingSource bal₀ τ b t)
    (hSjust : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄,
      τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' →
      Justified bal₀ (𝒱 w t') (ruleVotingSource bal₀ τ b t))
    (huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t') C₁ → Justified bal₀ (𝒱 w t') C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time}
    (hbt' : τ.epochOf b.slot ≤ τ.epochOf (τ.slotOf t'))
    (hHead : ∀ ⦃j : Slot⦄, τ.slotOf t ≤ j → j < τ.slotOf t' → ∀ ⦃i : Validator n⦄, i ∈ fm.honest →
      b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st j)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st j))
        (τ.st j))
    (hGU : ∃ GUc : Checkpoint n, Justified bal₀ (𝒱 w t') GUc ∧
      GUc.epoch = τ.epochOf b.slot - 1 ∧ GUc.block ≼ b)
    (hGJub : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ τ.epochOf b.slot) :
    (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b := by
  classical
  rcases Nat.lt_or_ge (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch (τ.epochOf b.slot)
    with hlt | hge
  · -- Case B (anchor route) — verbatim from `greatestRealizedJustified_on_chain_cert`.
    obtain ⟨GUc, hGUc, hGUcep, hGUcle⟩ := hGU
    have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
    have hGUcMem : GUc ∈ mentionedCheckpoints (𝒱 w t') :=
      justified_mem_mentioned bal₀ (𝒱 w t') hwit hGUc
    have hbpos : 0 < τ.epochOf b.slot := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hGUcReal : GUc.epoch < τ.epochOf (τ.slotOf t') := by
      rw [hGUcep]; exact lt_of_lt_of_le (Nat.sub_lt hbpos Nat.one_pos) hbt'
    have hdom : GUc.epoch ≤ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch :=
      greatestRealizedJustified_max bal₀ τ (𝒱 w t') t' hGUcMem hGUc hGUcReal
    have hle : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ GUc.epoch := by
      rw [hGUcep]; exact Nat.le_sub_one_of_lt hlt
    have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block = GUc.block :=
      huniq hw (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') hGUc
        (Nat.le_antisymm hle hdom)
    rw [hblockeq]; exact hGUcle
  · -- Case A: `GJ.epoch = epoch(b)`. Derive the certificate inline, then uniqueness.
    have hGJeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch = τ.epochOf b.slot :=
      Nat.le_antisymm hGJub hge
    by_cases hb0 : τ.epochOf b.slot = 0
    · have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block
          = genesisCheckpoint.block :=
        huniq hw (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') Justified.base
          (by rw [hGJeq, hb0]; rfl)
      rw [hblockeq]; exact genesis_ancestor _
    · have hbpos : 0 < τ.epochOf b.slot := Nat.pos_of_ne_zero hb0
      have hreal : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch < τ.epochOf (τ.slotOf t') :=
        greatestRealizedJustified_realized_of_pos bal₀ τ (𝒱 w t') t' (by rw [hGJeq]; exact hbpos)
      have hfl : τ.lslot (τ.epochOf b.slot) + 1 = τ.fslot (τ.epochOf b.slot + 1) := by
        have hE : 1 ≤ τ.slotsPerEpoch := τ.hSlotsPerEpoch
        change τ.epochOf b.slot * τ.slotsPerEpoch + (τ.slotsPerEpoch - 1) + 1
           = (τ.epochOf b.slot + 1) * τ.slotsPerEpoch
        rw [add_mul, one_mul, add_assoc, Nat.sub_add_cancel hE]
      have h1 : τ.epochOf b.slot + 1 ≤ τ.epochOf (τ.slotOf t') := by rw [← hGJeq]; exact hreal
      have h2 : τ.fslot (τ.epochOf b.slot + 1) ≤ τ.slotOf t' :=
        calc τ.fslot (τ.epochOf b.slot + 1) ≤ τ.fslot (τ.epochOf (τ.slotOf t')) := by
              unfold Timing.fslot; exact Nat.mul_le_mul_right _ h1
          _ ≤ τ.slotOf t' := by unfold Timing.fslot Timing.epochOf; exact Nat.div_mul_le_self _ _
      have hlslt : τ.lslot (τ.epochOf b.slot) < τ.slotOf t' := by
        have hle : τ.lslot (τ.epochOf b.slot) + 1 ≤ τ.slotOf t' := by rw [hfl]; exact h2
        exact hle
      have ht'cert : τ.st (τ.lslot (τ.epochOf b.slot) + 1) ≤ t' := by
        rw [hfl]
        calc τ.st (τ.fslot (τ.epochOf b.slot + 1)) ≤ τ.st (τ.slotOf t') := by
              unfold Timing.st; exact Nat.mul_le_mul_right _ h2
          _ ≤ t' := by unfold Timing.st Timing.slotOf; exact Nat.div_mul_le_self t' τ.slotDur
      -- head-safety over `[slot(t), lslot(epoch(b))]` (inside the window `[slot(t), slotOf t')`).
      have hHeadb : ∀ ⦃i : Validator n⦄, i ∈ fm.honest → ∀ ⦃s : Slot⦄, τ.slotOf t ≤ s →
          s ≤ τ.lslot (τ.epochOf b.slot) →
          b ≼ forkChoiceHead τ (gjFFG bal₀ 𝒱 i (τ.st s)) boost pb (ffgFilter bal₀ τ) (𝒱 i (τ.st s))
            (τ.st s) := fun i hi s hsge hsle => hHead hsge (Nat.lt_of_le_of_lt hsle hlslt) hi
      have hcert := certificate_of_confirmation bal₀ hv hRelay hMono hHB hnoequiv hcm hgst hte hwe0
        hbwf hpart hwill hHeadb hsrc hSjust
      have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block
          = (checkpointOf τ b (τ.epochOf b.slot)).block :=
        huniq hw (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') (hcert hw ht'cert)
          (by rw [hGJeq]; rfl)
      rw [hblockeq]; exact boundaryBlock_ancestor _ b

/-! ### Previous-epoch certificate (confirmation at the first slot of the next epoch) -/

/-- **`linkWeightUpTo ≤ linkWeight`** — the committee-slot-restricted link weight is a lower bound
    for the full-view link weight (the restricted signer filter sits inside the universal one). -/
theorem linkWeightUpTo_le_linkWeight (bal₀ : Stakes n) {τ : Timing} (cm : Committees n)
    (V : View n (FFGVote n)) (src tgt : Checkpoint n) (upTo : Slot) :
    linkWeightUpTo bal₀ cm τ V src tgt upTo ≤ linkWeight bal₀ V src tgt := by
  classical
  unfold linkWeightUpTo linkWeight
  apply totalWeight_mono
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_filter]
  obtain ⟨m, hm, hval, _hslotlo, _hslotup, hsrc, htgt⟩ := hi.2
  exact ⟨Finset.mem_univ i, m, hm, hval, hsrc, htgt⟩

/-- **Previous-epoch certificate, in the confirming validator's own view.** In the previous-epoch
    branch the confirmation slot is the first slot of the next epoch (`slotOf t = lslot e + 1`,
    where `e = epochOf(slotOf t) - 1` is the certificate epoch — which need **not** equal
    `epoch(b)`: the paper's prev-epoch case allows `epoch(b) < epoch(t)-1`, in which case `C(b, e)`
    is `b` itself labelled at the epoch-`e` boundary). The future committee `[slotOf t, lslot e]` is
    then **empty** and `willChkpBeJustified` collapses to the observed link weight alone reaching
    `⅔W` — no honest-future votes, no relay. Hence `C(b, e)` is already `Justified` in the
    confirming honest view `𝒱 v t`, given the anchor `S = vs(b, t)` is justified there (`hSjust`).
    `min(we, β·W)` is slack. -/
theorem checkpoint_justified_in_own_view_prev (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {we : Weight}
    {𝒱 : ViewFamily n (FFGVote n)} {v : Validator n} {b : Block n} {t : Time} {e : Epoch}
    (hwe0 : 0 ≤ we)
    (hempty : τ.slotOf t = τ.lslot e + 1)
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b e t)
    (hSjust : Justified bal₀ (𝒱 v t) (ruleVotingSource bal₀ τ b t)) :
    Justified bal₀ (𝒱 v t) (checkpointOf τ b e) := by
  classical
  set S := ruleVotingSource bal₀ τ b t with hS
  set T := checkpointOf τ b e with hT
  -- The future committee `[slotOf t, lslot e]` is empty: `Icc (lslot e + 1) (lslot e) = ∅`.
  have hFutEmpty : committeeUnion cm (τ.slotOf t) (τ.lslot e) = ∅ := by
    have hicc : Finset.Icc (τ.lslot e + 1) (τ.lslot e) = (∅ : Finset Slot) :=
      Finset.Icc_eq_empty (Nat.not_succ_le_self (τ.lslot e))
    rw [hempty, committeeUnion, hicc, Finset.biUnion_empty]
  have hFut0 : totalWeight bal₀ (committeeUnion cm (τ.slotOf t) (τ.lslot e)) = 0 := by
    rw [hFutEmpty]; simp [totalWeight]
  -- `willChkp` with empty future ⇒ observed `linkWeightUpTo ≥ ⅔W` ⇒ `linkWeight ≥ ⅔W`.
  have hW0 : 0 ≤ totalWeight bal₀ Finset.univ :=
    Finset.sum_nonneg (fun i _ => (bal₀.hpos i).le)
  have hmin0 : 0 ≤ min we (fm.β * totalWeight bal₀ Finset.univ) :=
    le_min hwe0 (mul_nonneg fm.hβ0 hW0)
  have hwill' : linkWeightUpTo bal₀ cm τ (𝒱 v t) S T (τ.slotOf t - 1)
      ≥ (2 / 3) * totalWeight bal₀ Finset.univ := by
    have h := hwill
    unfold willChkpBeJustified at h
    rw [← hS, ← hT] at h
    rw [hFut0, mul_zero, add_zero] at h
    linarith
  have hlink : (2 / 3) * totalWeight bal₀ Finset.univ ≤ linkWeight bal₀ (𝒱 v t) S T :=
    le_trans hwill' (linkWeightUpTo_le_linkWeight bal₀ cm (𝒱 v t) S T (τ.slotOf t - 1))
  exact Justified.link hSjust (by linarith)

/-- **The previous-epoch certificate `hTv`, DERIVED from the rule** (not assumed). At a
    confirmation at the first slot of epoch `ec+1` (`hsfirst`, `hteP`), the epoch-`ec`
    future committee `[slotOf(st s), lslot ec]` is empty (`slotOf(st s) = lslot ec + 1`),
    so the rule's previous-epoch reservation `willChkpBeJustified(b, ec, st s)` (the else
    branch of `isConfirmedNoCaching`) is entirely *observed* link weight `≥ ⅔W`, and the
    source `vs(b, st s)` is the AU selector `ruleVotingSource`, whose view-level justification is
    supplied by the block AU visibility interface. Hence
    `checkpoint_justified_in_own_view_prev` yields `C(b, ec)` justified in the confirming
    view — the `hTv` premise the prev-epoch never-filter consumes, now discharged from
    Algorithm 1's local check rather than carried as a free `Justified` premise. -/
theorem checkpoint_justified_of_confirmedNoCaching_prev (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {we : Weight}
    {𝒱 : ViewFamily n (FFGVote n)} {v : Validator n} {b : Block n} {s : Slot} {ec : Epoch}
    (hwe0 : 0 ≤ we)
    (hteP : τ.epochOf s = ec + 1)
    (hsfirst : s = τ.fslot (τ.epochOf s))
    (hwill : willChkpBeJustified bal₀ cm fm we τ 𝒱 v b ec (τ.st s))
    (hSjust : Justified bal₀ (𝒱 v (τ.st s)) (ruleVotingSource bal₀ τ b (τ.st s))) :
    Justified bal₀ (𝒱 v (τ.st s)) (checkpointOf τ b ec) := by
  have hslots : τ.slotOf (τ.st s) = s := Timing.slotOf_st τ s
  -- The epoch-`ec` future committee is empty: `slotOf(st s) = s = fslot(ec+1) = lslot ec + 1`.
  have hempty : τ.slotOf (τ.st s) = τ.lslot ec + 1 := by
    rw [hslots]
    conv_lhs => rw [hsfirst, hteP]
    unfold Timing.fslot Timing.lslot
    rw [Nat.add_assoc, Nat.sub_add_cancel τ.hSlotsPerEpoch]
    ring
  exact checkpoint_justified_in_own_view_prev bal₀ hwe0 hempty hwill hSjust

/-- **Lemma B′ — no current-epoch (or higher) checkpoint is justified at the epoch's first slot.**
    The previous-epoch analogue of the paper's
    `prop:gasper-basic:highest-justified-not-from-current-epoch` (arXiv:2405.00549 l.2565),
    specialized to the first slot of an epoch and **proven** from the committee partition (rather
    than assumed). At `s = τ.fslot (ec+1)` (the first slot of epoch `ec+1`, `hteP`/`hsfirst`), every
    checkpoint `Justified` in the confirming honest view `𝒱 v (st s)` has epoch `≤ ec` — no
    checkpoint of the *current* epoch `ec+1` (nor any higher) can yet be justified.

    **Proof.** A justified `Cpt` is either `base` (genesis, epoch `0 ≤ ec`) or a supermajority
    `link` (`3·linkWeight ≥ 2W`). Suppose, for the link, `Cpt.epoch ≥ ec+1`. Every *honest* signer
    `i` of the link has, by `HonestNoForgery` + `HonestFFGNoEquivocation`, its FFG target pinned to
    `chkp(headᵢ, epochOf(slotᵢ))`, so `Cpt.epoch = epochOf(slotᵢ)`; `noFutureMessages` gives
    `slotᵢ ≤ slotOf(st s) = s`, hence `epochOf(slotᵢ) ≤ epochOf s = ec+1`; with `Cpt.epoch ≥ ec+1`
    this forces `epochOf(slotᵢ) = ec+1`, and as `s = fslot(ec+1)` is the *first* slot of that epoch,
    `slotᵢ = s`; `ViewValid` then pins `i ∈ cm.member s`. So the honest link weight is
    `≤ totalWeight(cm.member s)` and the adversarial weight is `≤ β·W` (`GlobalByzantineBound`),
    giving `(2/3)·W ≤ linkWeight ≤ totalWeight(cm.member s) + β·W`, contradicting
    `SlotCommitteeMinority` (`totalWeight(cm.member s) < (2/3 − β)·W`). This is the realization
    bound the previous-epoch never-filter needs: the AU witness voting source
    `ruleVotingSource(b',t)` (visible as `Justified` in `𝒱 v (st s)`) has epoch `≤ ec`, so it is
    realized in later views. ∎ -/
theorem justified_epoch_le_of_firstSlot (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {cm : Committees n} {pb : Weight}
    {boost : ProposerBoost n (FFGVote n)} {𝒱 : ViewFamily n (FFGVote n)}
    {v : Validator n} {s : Slot} {ec : Epoch}
    (hVV : ViewsValid cm 𝒱) (hNF : HonestNoForgery fm τ 𝒱)
    (hnoequiv : HonestFFGNoEquivocation τ fm cm bal₀ boost pb 𝒱)
    (hByz : GlobalByzantineBound bal₀ fm)
    (hSCM : SlotCommitteeMinority fm cm bal₀)
    (hnofut : ∀ ⦃u : Validator n⦄ ⦃tt : Time⦄ ⦃m : Message n (FFGVote n)⦄,
      m ∈ (𝒱 u tt).msgs → m.ghost.slot ≤ τ.slotOf tt)
    (hv : v ∈ fm.honest)
    (hteP : τ.epochOf s = ec + 1) (hsfirst : s = τ.fslot (τ.epochOf s))
    {Cpt : Checkpoint n} (hJ : Justified bal₀ (𝒱 v (τ.st s)) Cpt) :
    Cpt.epoch ≤ ec := by
  classical
  have hs_eq : s = (ec + 1) * τ.slotsPerEpoch := by
    conv_lhs => rw [hsfirst]
    unfold Timing.fslot; rw [hteP]
  set V := 𝒱 v (τ.st s) with hVdef
  cases hJ with
  | base => exact Nat.zero_le ec
  | @link Cs _hs hsup =>
    by_contra hgt
    push Not at hgt
    set Sgn : Finset (Validator n) := Finset.univ.filter (fun i =>
      ∃ m ∈ V.msgs, m.ghost.validator = i ∧ m.extra.source = Cs ∧ m.extra.target = Cpt) with hSgn
    have hlink : linkWeight bal₀ V Cs Cpt = totalWeight bal₀ Sgn := rfl
    -- every honest signer of the `· → Cpt` link sits in slot `s`'s committee
    have hHsub : Sgn.filter (fun i => i ∈ fm.honest) ⊆ cm.member s := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiSgn, hihon⟩ := hi
      rw [hSgn, Finset.mem_filter] at hiSgn
      obtain ⟨_, m, hm, hmv, _hms, hmt⟩ := hiSgn
      have hival : m.ghost.validator ∈ fm.honest := by rw [hmv]; exact hihon
      have hcast : HonestCast fm 𝒱 τ m := hNF hv hm hival
      obtain ⟨htgt, _hsrc⟩ := hnoequiv hcast
      have hCptep : Cpt.epoch = τ.epochOf m.ghost.slot := by
        rw [← hmt, htgt]; rfl
      have hms_le : m.ghost.slot ≤ s := by
        have h := hnofut hm; rwa [Timing.slotOf_st] at h
      -- `ec < Cpt.epoch = epochOf(slotᵢ)`, so `slotᵢ ≥ fslot(ec+1) = s` (and `≤ s`) ⇒ `slotᵢ = s`.
      have hge_ep : ec + 1 ≤ τ.epochOf m.ghost.slot := hCptep ▸ hgt
      have hs_le_slot : s ≤ m.ghost.slot := by
        rw [hs_eq]
        calc (ec + 1) * τ.slotsPerEpoch
            ≤ τ.epochOf m.ghost.slot * τ.slotsPerEpoch :=
              Nat.mul_le_mul_right τ.slotsPerEpoch hge_ep
          _ ≤ m.ghost.slot := by
              unfold Timing.epochOf; exact Nat.div_mul_le_self m.ghost.slot τ.slotsPerEpoch
      have hms_eq : m.ghost.slot = s := le_antisymm hms_le hs_le_slot
      have hvv := (hVV v (τ.st s) m hm).1
      rw [← hmv, ← hms_eq]; exact hvv
    -- adversarial signer weight `≤ β·W`
    have hAdv : totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest))
        ≤ fm.β * totalWeight bal₀ Finset.univ := by
      refine le_trans (totalWeight_mono bal₀ ?_) hByz
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi.2⟩
    -- honest signer weight `≤ totalWeight(cm.member s)`
    have hHon : totalWeight bal₀ (Sgn.filter (fun i => i ∈ fm.honest))
        ≤ totalWeight bal₀ (cm.member s) := totalWeight_mono bal₀ hHsub
    have hsplit : totalWeight bal₀ Sgn
        = totalWeight bal₀ (Sgn.filter (fun i => i ∈ fm.honest))
          + totalWeight bal₀ (Sgn.filter (fun i => i ∉ fm.honest)) := by
      simp only [totalWeight]
      exact (Finset.sum_filter_add_sum_filter_not Sgn (fun i => i ∈ fm.honest) bal₀.bal).symm
    have hSCMs := hSCM s
    rw [sub_mul] at hSCMs
    have hge23 : (2 / 3) * totalWeight bal₀ Finset.univ ≤ linkWeight bal₀ V Cs Cpt := by
      linarith [hsup]
    rw [hlink] at hge23
    linarith [hHon, hAdv, hsplit, hSCMs, hge23]

/-- **`t < st(slotOf t + 1)`** — `t` lies strictly before the start of its next slot
    (`t = slotDur·(t/slotDur) + t%slotDur < slotDur·(t/slotDur) + slotDur`). -/
theorem lt_st_slotOf_succ (τ : Timing) (t : Time) : t < τ.st (τ.slotOf t + 1) := by
  unfold Timing.st Timing.slotOf
  have hqr : τ.slotDur * (t / τ.slotDur) + t % τ.slotDur = t := Nat.div_add_mod t τ.slotDur
  have hmod : t % τ.slotDur < τ.slotDur := Nat.mod_lt t τ.hSlot
  calc t = τ.slotDur * (t / τ.slotDur) + t % τ.slotDur := hqr.symm
    _ < τ.slotDur * (t / τ.slotDur) + τ.slotDur := Nat.add_lt_add_left hmod _
    _ = (t / τ.slotDur + 1) * τ.slotDur := by ring

/-- **The never-filter's comparability, from Algorithm 1 (PREVIOUS-epoch) — faithful route.**
    The previous-epoch drop-in for `greatestRealizedJustified_on_chain_from_confirmation`: concludes
    the **compatibility** `block(GJ) ~ b` (`block(GJ) ≼ b ∨ b ≼ block(GJ)`) for a realized `GJ` of
    epoch `≤ ec` (`hGJub`), at the *first slot of the next epoch*. Here `ec` is the **certificate
    epoch** `= epochOf(slotOf t) − 1` (which need not equal `epoch(b)`). Two cases on `GJ.epoch` vs
    `ec` (paper `lem:base-case-prev-epoch-for-safety-of-confirmation-ffg`, l.3475–3531):

    * **Case A `GJ.epoch = ec`** — the no-conflicting epoch-`ec` argument, faithful via the
      one-boundary gossip relay (NOT a contemporaneous certificate delivery). The realized `GJ`'s
      justification (`justified_relays`, `hRelay`) and the observed-only in-view certificate
      `C(b, ec)` (`hTv`, carried forward by `Justified_mono_time`) both hold in a *common* future
      view `𝒱 v (st(s'+1))` (`s' = max(slotOf t', slotOf t)`); per-epoch uniqueness (`huniq`) there
      gives `block(GJ) = C(b, ec).block ≼ b`.
    * **Case B `GJ.epoch < ec`** — the **witness-source** route (paper l.3513–3522). The witness's
      voting source `A = ruleVotingSource(b',t)` (`hWitV`; its **block** is `≼ b'` by the AU
      selector lemma) is
      delivered to `𝒱 w t'` **keyed at the witness `b'`** via `hdel'`, the active
      `OnChainAnchorInterface` (AU realization plus visibility) applied to the settled
      `epoch(t)-2` anchor `A`, and is *realized* there
      (`A.epoch ≤ ec < epochOf(slotOf t')`, `hWitUb`/`hbt'`), so
      `greatestRealizedJustified_max` dominates it; the rule's lower-bound recency (`hWitLo`,
      `ec ≤ A.epoch+1`) pins `GJ.epoch = A.epoch`, uniqueness gives `block(GJ) = A.block ≼ b'`, and
      `b ≼ b'` (`hbb'`) makes `block(GJ)` and `b` two ancestors of `b'`, hence **comparable**
      (`ancestor_comparable`).

    Faithful to `alg:ffg`: it needs NEITHER the (removed) source-epoch upper bound NOR the (removed)
    `vs(b',t).block ≼ b` ancestor conjunct — the realization bound `hWitUb` is *proven*
    (`justified_epoch_le_of_firstSlot`), and the conclusion is only compatibility (the paper's
    `gj-succ` is likewise only `≽`, l.3522). -/
theorem greatestRealizedJustified_on_chain_from_confirmation_prev (bal₀ : Stakes n) {τ : Timing}
    {fm : FaultModel n} {𝒱 : ViewFamily n (FFGVote n)}
    {v : Validator n} {b : Block n} {t : Time} {ec : Epoch}
    (hv : v ∈ fm.honest)
    (hRelay : ∀ ⦃a c : Validator n⦄, a ∈ fm.honest → c ∈ fm.honest →
      ∀ ⦃tt : Time⦄ ⦃m : Message n (FFGVote n)⦄ ⦃s' : Slot⦄, m ∈ (𝒱 a tt).msgs →
        τ.slotOf tt ≤ s' → τ.AfterGST (τ.st s') → m ∈ (𝒱 c (τ.st (s' + 1))).msgs)
    (hMono : ViewsMonotone 𝒱)
    (hgst : τ.AfterGST (τ.st (τ.slotOf t)))
    (hTv : Justified bal₀ (𝒱 v t) (checkpointOf τ b ec))
    {b' : Block n} (hbb' : b ≼ b')
    (hdel' : ∀ ⦃Cc : Checkpoint n⦄, Cc.block ≼ b' →
      (∃ u, u ∈ fm.honest ∧ Justified bal₀ (𝒱 u t) Cc) →
      ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄, τ.st (τ.slotOf t) ≤ t' →
        Justified bal₀ (𝒱 w t') Cc)
    (hWitV : Justified bal₀ (𝒱 v t) (ruleVotingSource bal₀ τ b' t))
    (hWitUb : (ruleVotingSource bal₀ τ b' t).epoch ≤ ec)
    (hWitLo : ec ≤ (ruleVotingSource bal₀ τ b' t).epoch + 1)
    (huniq : ∀ ⦃w : Validator n⦄, w ∈ fm.honest → ∀ ⦃t' : Time⦄ ⦃C₁ C₂ : Checkpoint n⦄,
      Justified bal₀ (𝒱 w t') C₁ → Justified bal₀ (𝒱 w t') C₂ → C₁.epoch = C₂.epoch →
        C₁.block = C₂.block)
    {w : Validator n} (hw : w ∈ fm.honest) {t' : Time}
    (ht'b : τ.st (τ.slotOf t) ≤ t')
    (hbt' : ec < τ.epochOf (τ.slotOf t'))
    (hGJub : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ ec) :
    (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b
      ∨ b ≼ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block := by
  classical
  rcases Nat.lt_or_ge (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ec with hlt | hge
  · -- Case B (witness-source route): GJ.epoch < ec.
    set A := ruleVotingSource bal₀ τ b' t with hA
    have hA_anc : A.block ≼ b' := by
      rw [hA]
      exact ruleVotingSource_block_le bal₀ τ b' t
    -- `A` (= `vs(b',t)`, on `chain(b')`) is delivered to `𝒱 w t'` keyed at the witness `b'`.
    have hA_just_w : Justified bal₀ (𝒱 w t') A := hdel' hA_anc ⟨v, hv, hWitV⟩ hw ht'b
    have hA_real : A.epoch < τ.epochOf (τ.slotOf t') := lt_of_le_of_lt hWitUb hbt'
    have hwit : (Finset.univ : Finset (Validator n)).Nonempty := ⟨w, Finset.mem_univ w⟩
    have hA_mem : A ∈ mentionedCheckpoints (𝒱 w t') :=
      justified_mem_mentioned bal₀ (𝒱 w t') hwit hA_just_w
    have hdom : A.epoch ≤ (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch :=
      greatestRealizedJustified_max bal₀ τ (𝒱 w t') t' hA_mem hA_just_w hA_real
    -- `GJ.epoch < ec ≤ A.epoch + 1` pins `GJ.epoch = A.epoch`; uniqueness identifies the blocks.
    have hle : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch ≤ A.epoch :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hWitLo)
    have hepeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch = A.epoch :=
      Nat.le_antisymm hle hdom
    have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block = A.block :=
      huniq hw (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t') hA_just_w hepeq
    have hgjCb' : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block ≼ b' := by
      rw [hblockeq]; exact hA_anc
    -- `block(GJ)` and `b` are two ancestors of `b'` ⇒ comparable.
    exact ancestor_comparable hgjCb' hbb'
  · -- Case A: GJ.epoch = ec. No-conflicting via a common future view (no certificate delivery).
    refine Or.inl ?_
    have hGJeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').epoch = ec :=
      Nat.le_antisymm hGJub hge
    set s' := max (τ.slotOf t') (τ.slotOf t) with hs'def
    have hs'_ge_t' : τ.slotOf t' ≤ s' := le_max_left _ _
    have hs'_ge_t : τ.slotOf t ≤ s' := le_max_right _ _
    have hgst' : τ.AfterGST (τ.st s') := le_trans hgst (Timing.st_le_st τ hs'_ge_t)
    -- relay the realized GJ's justification into v's common future view.
    have hGJrelay : Justified bal₀ (𝒱 v (τ.st (s' + 1)))
        (greatestRealizedJustified bal₀ τ (𝒱 w t') t') :=
      justified_relays bal₀ hRelay hw hv hs'_ge_t' hgst'
        (greatestRealizedJustified_justified bal₀ τ (𝒱 w t') t')
    -- carry the observed-only `C(b, ec)` certificate (hTv) into the same view.
    have hslot_le : τ.slotOf t + 1 ≤ s' + 1 := Nat.add_le_add_right hs'_ge_t 1
    have ht_le : t ≤ τ.st (s' + 1) :=
      le_of_lt (lt_of_lt_of_le (lt_st_slotOf_succ τ t) (Timing.st_le_st τ hslot_le))
    have hTrelay : Justified bal₀ (𝒱 v (τ.st (s' + 1))) (checkpointOf τ b ec) :=
      Justified_mono_time bal₀ hMono ht_le hTv
    have hblockeq : (greatestRealizedJustified bal₀ τ (𝒱 w t') t').block
        = (checkpointOf τ b ec).block :=
      huniq hv (t' := τ.st (s' + 1)) hGJrelay hTrelay (by simp only [checkpointOf]; exact hGJeq)
    rw [hblockeq]; exact boundaryBlock_ancestor _ b

end FastConfirmation.HFC

end
