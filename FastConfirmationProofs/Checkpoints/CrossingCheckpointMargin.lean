module
public import FastConfirmationProofs.Discount.ByzantineBudgetLedger
public import FastConfirmationProofs.Execution.Trajectory.LatestMessageProvenance

@[expose] public section

/-!
# Spec / Proof / Reanchor

Proves the margin bounds when a confirmed chain crosses an epoch checkpoint.

This module contains `reanchored_endpoint_fullSpan`, `crossing_ghost_arith`, `reanchored_endpoint_of_fullSpan_certificate` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)






end Execution

/-! ## The pure-ℕ re-anchored endpoint

The confirmed-instance atoms (all ground-truth `Gwei` weights over
`E.span_committee`), read at the crossing geometry `p(b′) [slot ps] → b′
[slot bs] → … → b`, `pre = [ps+1, bs−1]`, `V = [bs, es]` (`es = current_slot−1`),
tail `(es, σ]`:

| atom | meaning |
|---|---|
| `s0`,`aS0`,`xS0` | honest sub-window classes at `es` (`Sval`/`Aval`/`Xval` at `[bs,es]`) |
| `Bsub0` | sub-window byz at `es` (`Bval [bs,es]`) |
| `Hpar` | parent-stuck honest (pre-region; the discount source) |
| `xP`,`Bpre` | OLD-sibling pre-region honest backers / byz (`slot < bs`) |
| `Bsup`,`eqV` | byz `b′`-supporters / equivocators inside `V` |
| `A`,`qV` | `get_adversarial_weight(b′)` / `estimate(V)//100` |
| `d`,`boost`,`MU` | `get_support_discount` / `compute_proposer_score` / `maximum_support` |
| `Bsig`,`Jsig`,`ssig`,`aSsig`,`xSsig` | sub-window byz / honest-`J` / `s` / `a` / `x` at `σ` |

For every `C ∈ [0,55]`, the hypotheses below imply the endpoint inequality for
both sibling cases. Each named hypothesis contributes one of the required base,
capacity, growth, or antitonicity bounds. -/



/-! ## Full-span, k-independent crossing endpoint

The multi-seam crossing arm keeps the real adversarial span
`[start_slot(epoch b'), es]`.  `HAextra`/`Bextra`/`eqExtra` are its prefix
outside the re-anchored sub-window; they are subsets of the pre-region masses,
and prefix equivocators are removed from the old sibling's usable `Bpre`.
No seam count or per-seam fuel occurs in this statement. -/

/-- **Full-span re-anchored endpoint with combined non-supporter
antitonicity.** The full adversarial guard and estimate, full-MU
charge, overlap-safe discount split, endpoint union cap, the combined `a+x`
bound, and the separate `x` cap imply the old-sibling strip independently of
the number of epoch seams. -/
theorem reanchored_endpoint_fullSpan
    {s0 aS0 xS0 Bsub0 Hpre Hsub xP Bpre Bsup eqSub eqExtra HAextra Bextra
      A d boost MU qFull Bsig Jsig ssig aSsig xSsig C : ℕ}
    (hbase : 2 * s0 + 2 * Bsup + d ≥ MU + boost + 2 * A + 1)
    (hMU : (s0 + aS0 + xS0 + Bsub0) + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub ≤ aS0)
    (hAguard : qFull * C ≤ A + eqSub + eqExtra)
    (hdom : (s0 + aS0 + xS0 + Bsub0) + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ Bsub0)
    (hbyzfull : Bsub0 + Bextra ≤ qFull * C)
    (hcap : (100 - C) * Bsig ≤ C * Jsig)
    (hJgrow : s0 + aS0 + xS0 ≤ Jsig)
    (hsigma : ssig + aSsig + xSsig = Jsig)
    (hAX : aSsig + xSsig ≤ aS0 + xS0)
    (hxS : xSsig ≤ xS0)
    (hC : C ≤ 25) :
    xP + xSsig + (Bpre - eqExtra) + Bsig + boost + 1 ≤ ssig := by
  interval_cases C <;> omega



/-- Pure-ℕ core of the crossing GHOST step (`Gwei` weights are opaque to `omega`
across simp-rewritten atoms, so the linear arithmetic is discharged over plain ℕ
and unified via the lemma type — mirrors `Endpoint.ghost_arith`). The crossing
enemy `XB := xP + x(σ) + Bpre + B(σ)` is one ℕ atom. -/
private theorem crossing_ghost_arith {sc scc XB P S : ℕ}
    (hbside : S ≤ sc) (hend : XB + P + 1 ≤ S) (hsib : scc ≤ XB) : scc + P < sc := by omega

namespace Execution

variable (E : Execution Root)


/-- **The full-span crossing certificate over ledger accessors.**  Unlike
`reanchored_endpoint_of_certificate`, this consumer keeps the real crossing
adversarial span explicit and consumes the authorized endpoint pair: combined
antitonicity of `Aval + Xval` plus separate antitonicity of `Xval`. Prefix
equivocators `eqExtra` are removed from the pre-region enemy mass available to
an old sibling. -/
theorem reanchored_endpoint_of_fullSpan_certificate (hbb : ByzantineWeightPremises cfg E)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    {Bsup eqSub eqExtra HAextra Bextra A d MU qFull Hpre Hsub xP Bpre boost : ℕ}
    (hes : es ≤ σ) (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hbase : 2 * E.Sval cfg ext v₀ n₀ b' lo es + 2 * Bsup + d
      ≥ MU + boost + 2 * A + 1)
    (hMU : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + (Hpre + xP + Bpre) ≤ MU)
    (hd : d ≤ Hpre + Hsub)
    (hHsub : Hsub ≤ E.Aval cfg ext v₀ n₀ b' lo es)
    (hAguard : qFull * cfg.confirmation_byzantine_threshold
      ≤ A + eqSub + eqExtra)
    (hdom : (E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
        + E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es)
      + HAextra + Bextra ≤ 100 * qFull)
    (hBextra : Bextra ≤ Bpre)
    (heqExtra : eqExtra ≤ Bextra)
    (hbyzsub : Bsup + eqSub ≤ E.Bval lo es)
    (hbyzfull : E.Bval lo es + Bextra
      ≤ qFull * cfg.confirmation_byzantine_threshold)
    (hAX : E.Aval cfg ext v₀ n₀ b' lo σ + E.Xval cfg ext v₀ n₀ b' lo σ
      ≤ E.Aval cfg ext v₀ n₀ b' lo es + E.Xval cfg ext v₀ n₀ b' lo es)
    (hxS : E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es) :
    xP + E.Xval cfg ext v₀ n₀ b' lo σ + (Bpre - eqExtra) + E.Bval lo σ
        + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hJgrow : E.Sval cfg ext v₀ n₀ b' lo es + E.Aval cfg ext v₀ n₀ b' lo es
      + E.Xval cfg ext v₀ n₀ b' lo es ≤ E.Jspec lo σ := by
    rw [← E.weight_partition cfg ext v₀ n₀ b' lo es]
    exact E.Jspec_mono lo hes
  have hsigma : E.Sval cfg ext v₀ n₀ b' lo σ + E.Aval cfg ext v₀ n₀ b' lo σ
      + E.Xval cfg ext v₀ n₀ b' lo σ = E.Jspec lo σ :=
    (E.weight_partition cfg ext v₀ n₀ b' lo σ).symm
  exact reanchored_endpoint_fullSpan hbase hMU hd hHsub hAguard hdom hBextra heqExtra
    hbyzsub hbyzfull (E.Rterm_nonneg cfg hbb lo σ hloH hσH) hJgrow hsigma hAX hxS
    cfg.confirmation_byzantine_threshold_le

/-- **The crossing GHOST step dominates** (the crossing analog of
`Endpoint.ghost_step_dominates`). From the re-anchored endpoint `hend` (the
OLD-sibling recorded contest bound, supplied by the full-span consumer), the
`b′`-side child's recorded lower bound `hbside` (`Endpoint.recorded_bside_ge` at
`lo := slot(b′)`) and the crossing sibling's recorded upper bound `hsib` (its
supporters confined to the pre-region backers `xP`/`Bpre` plus the window
`Xclass`/`Bwin` at `lo`), the sibling `cc` loses to the `b′`-side child `c` in
`get_weight`. The proposer boost is charged to the sibling in full
(`MajorityPersists.fork_weight_lt`). -/
theorem crossing_ghost_step_dominates {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo σ : Slot} {xP Bpre : ℕ}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hend : xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ
        + get_proposer_score cfg store + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ) :
    get_weight cfg store (ForkChoiceNode.mk cc .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (crossing_ghost_arith hbside hend hsib)

/-- **A crossing certificate builds one `DescendStep`.** At a fork with parent `h`
and `b′`-side child `c` (a filtered-tree child), the re-anchored endpoint `hend`
plus the `b′`-side lower bound `hbside` plus an old-sibling upper bound `hsib` *for
every competing child* dominate the fork in `get_weight`, so `c` is the descent-step
choice. The crossing analog of `Endpoint.ledger_descendStep`. -/
theorem crossing_ledger_descendStep {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot} {xP Bpre : ℕ}
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
    (hstatus : PendingStatusMargin cfg store (get_filtered_block_tree cfg store)
      h (get_parent_payload_status store (store.blocks c)))
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hend : xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ
        + get_proposer_score cfg store + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
      c' ≠ c →
      get_attestation_score cfg store (get_node_for_root c')
          (store.checkpoint_states store.justified_checkpoint)
        ≤ xP + E.Xval cfg ext v₀ n₀ b' lo σ + Bpre + E.Bval lo σ) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c :=
  descendStep_of_dom cfg hchild
    (fun c' hc' hne => E.crossing_ghost_step_dominates cfg ext hbside hend (hsib c' hc' hne))
    (pending_status_selected_of_margin cfg hstatus)

end Execution

end FastConfirmation.Spec

end
