module
public import FastConfirmation.Spec.Proof.INVstarTrack

@[expose] public section

/-!
# Spec / Proof / Dominance: per-edge dominance in confirm-margin form

This module proves **per-edge dominance** at every fork along the confirmed `b`-chain,
in the **confirm-margin form**, and settles the `hdelta` (per-slot maintenance)
disposition.

## The per-ancestor confirmation insight

`get_latest_confirmed` advances only through `is_one_confirmed` blocks
(`find_latest_confirmed_descendant`: the `for … break` loop steps to a child only
when that child is `is_one_confirmed`). So **every** block `a` on the confirmed
`b`-chain — not just `b` — carries its *own* `is_one_confirmed` charge over its own
window `[parent(a).slot + 1, es]`. The paper (arXiv:2405.00549 v4 Lemma 6)
maintains a per-ancestor `P`; the spec's `is_confirmed_chain_safe` / the L4 loop
does the same, one `is_one_confirmed` per chain block. Each fork's contest is
**edge-specific** — a losing sibling `c'` of `a` draws its support from the *same*
window `[parent(a).slot + 1, es]` that funds `a`'s charge — so the whole chain of
forks is `GroundBeta`'s single-fork dominance re-instantiated per edge. Each
per-ancestor charge funds its own edge contest for `C ∈ [1,25]`.

## The `hdelta` disposition (window-uniform maintenance)

The Spec_Safety endpoint `(w, m)` sits at a *later* slot `k`, so its fork-contest
window is `[lo, σ]` with `σ = k − 1 ≥ es`. The confirm-margin strip survives to
`σ` without the per-slot
`INVstar` step:

* the **bare** strip does not survive window growth:
  the byz that entered `(es, σ]` must be funded;
* a **single aggregate growth budget** `(100−C)·(B(σ)−B(es)) ≤ C·(J(σ)−J(es))`
  closes it — the domination is **window-uniform**,
  one charge over `[lo, σ]`, *no* `σ−es`-fold per-slot iteration;
* same-epoch endpoints get that budget for free (`committee_assignment_unique`
  makes `(es, σ]` a disjoint span, so `span_fraction` on `[es+1, σ]` *is* the
  aggregate budget), and cross-epoch the recurrence is paid by the `INVstar`
  `min`-reserve `C·U` tax, carried once.

Thus `hdelta` collapses from a per-slot functional to a **single window-uniform
budget fact** (`edge_growth_budget`-shaped):
`bval_strip_window_uniform` produces the endpoint strip at `σ` directly from the
confirm-margin strip at `es` plus the aggregate budget, and
`descendStep_of_confirmMargin` packages the per-fork `DescendStep`, including
the `harm`/`hdelta`/`hbside`/`hsib` legs at any
`σ ≥ es`, mirroring `GroundBeta.bval_strip`'s `σ`-generality with no min-reserve.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — the pure-ℕ dominance cores

All ledger accessors are `Gwei = ℕ`; the linear steps are proved over plain ℕ
and `exact`-ed (variable products `D·dB` trip `omega`, so the coefficient
reduction is a separate `Nat.le_of_mul_le_mul_left`). -/

/-- **Budget reduction.** The aggregate growth budget in cross-multiplied form
`(100−C)·dB ≤ C·dJ`, with `C ≤ 100−C` (i.e. `C ≤ 50`, from `C ≤ 25`) and
`0 < 100−C`, reduces to the plain `dB ≤ dJ`. This is where `C ≤ 25` makes the
byz growth never exceed the honest-support growth. -/
private theorem budget_reduce {C D dB dJ : ℕ} (hCD : C ≤ D) (hDpos : 0 < D)
    (h : D * dB ≤ C * dJ) : dB ≤ dJ :=
  Nat.le_of_mul_le_mul_left (le_trans h (Nat.mul_le_mul hCD (le_refl dJ))) hDpos

/-- **The confirm-margin strip survives window growth (pure ℕ).** From the strip
at the base window end `es` (`x₀ + B₀ + P + 1 ≤ s₀`), the honest-support growth
`s₀ + dJ ≤ sσ` (fresh honest window members support `b`, `dJ` the honest window
growth), the sibling-stuck bound `xσ ≤ x₀` (no new honest sibling-stuck), the
enemy growth `Bσ ≤ B₀ + dB` (`Bval_mono`), and the aggregate budget `dB ≤ dJ`,
the strip holds at the later window end `σ`: `xσ + Bσ + P + 1 ≤ sσ`. `omega`. -/
private theorem strip_survives_growth
    {x0 B0 P s0 xg Bg sg dJ dB : ℕ}
    (hstrip : x0 + B0 + P + 1 ≤ s0) (hs : s0 + dJ ≤ sg)
    (hx : xg ≤ x0) (hB : Bg ≤ B0 + dB) (hbudget : dB ≤ dJ) :
    xg + Bg + P + 1 ≤ sg := by omega

/-- `a ≤ b + (a − b)` in ℕ; isolated so `omega` runs in a clean context (the
call site carries nonlinear product hypotheses `omega` cannot atomize). -/
private theorem le_add_tsub (a b : ℕ) : a ≤ b + (a - b) := by omega

namespace Execution

variable (E : Execution Root)

/-! ## Section 2 — the window-uniform endpoint strip (the `hdelta` collapse)

`EngineCore.invstar_sigma_of_deltas` takes a per-`σ'` step functional maintaining `INVstar` slot by slot
from `es` to `σ`. This collapses to a
**single** aggregate growth budget: the strip survives the whole window growth in
one step. This section delivers that collapse over the ledger accessors. -/

/-- **The confirm-margin strip survives window growth, window-uniform.** From the
endpoint strip at the base window end `es` (`Xval(es) + Bval(es) + P + 1 ≤
Sval(es)`), and the three **aggregate** growth facts over `[es, σ]`:

* `hgrowS` — honest-support growth: `Sval(es) + (J(σ) − J(es)) ≤ Sval(σ)` (every
  fresh honest window member supports `b`, `J(σ) − J(es)` the honest window
  growth; recurrers are already counted in `J(es)`/`Sval(es)`);
* `hgrowX` — no new honest sibling-stuck: `Xval(σ) ≤ Xval(es)`;
* `hbudget` — the aggregate span_fraction on the growth: `(100−C)·(B(σ) − B(es))
  ≤ C·(J(σ) − J(es))` (same-epoch: `span_fraction [es+1, σ]` directly; cross-epoch:
  the `INVstar` `C·U` tax, carried **once**),

the strip holds at the later window end `σ`: `Xval(σ) + Bval(σ) + P + 1 ≤ Sval(σ)`.
The enemy-growth split is `le_add_tsub` (truncated-subtraction safe, so `σ ≥ es`
need not even be assumed); `budget_reduce` (needs `C ≤ 25`) turns the
cross-multiplied budget into `B(σ) − B(es) ≤ J(σ) − J(es)`. **No** per-slot
iteration and **no** `min`-reserve `INVstar` — one window-uniform charge. -/
theorem bval_strip_window_uniform (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root)
    (lo es σ : Slot) (P : ℕ)
    (hstrip : E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es + P + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hgrowS : E.Sval cfg ext v₀ n₀ b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hgrowX : E.Xval cfg ext v₀ n₀ b' lo σ ≤ E.Xval cfg ext v₀ n₀ b' lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
      ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es)) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + P + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le; omega
  have hCD : cfg.confirmation_byzantine_threshold
      ≤ 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le; omega
  have hbud : E.Bval lo σ - E.Bval lo es ≤ E.Jspec lo σ - E.Jspec lo es :=
    budget_reduce hCD hDpos hbudget
  exact strip_survives_growth hstrip hgrowS hgrowX
    (le_add_tsub (E.Bval lo σ) (E.Bval lo es)) hbud

/-! ## Section 3 — the endpoint strip and the per-fork `DescendStep`

`GroundBeta.bval_endpoint_strip_of_transport` immediately **strips** the min-reserve
off `INVstar` (`INVstar_endpoint`) before transporting — only the plain strip
`Xval + Bval + boost + 1 ≤ Sval` is ever used. The min-reserve `INVstar` existed
solely to feed the per-slot `INVstar_step` maintenance (`hdelta`); once the
window-uniform growth budget (§2) replaces that per-slot iteration, the min-reserve
is dead weight. So this section takes the **plain confirm-margin strip at the
confirming anchor** — `Base.weak_base_of_rule`'s output, straight from
`is_one_confirmed`'s `honest_support_majority` charge — with **no** arms disjunction
(`harm`) and **no** min-reserve `INVstar` at all. The base enemy is the
store-independent `Bval` (§`GroundBeta`, `hBb`-free), the transport is the honest
legs only (`classes_base_transport`), and the maintenance is the single growth budget
(`bval_strip_window_uniform`). It feeds `Endpoint.ledger_descendStep` at every fork. -/

/-- **The window-uniform endpoint strip, from the plain confirm-margin strip.** From
the confirm-margin strip at the confirming anchor `(v₀, n₀)` over `[lo, es]`
(`hstrip0` — `Base.weak_base_of_rule`'s output; **no** arms disjunction, **no**
min-reserve `INVstar`), the honest descent transports `hSt`/`hAt` at `es` (past-slot
window votes, same-slot-available — `EngineTransport`/`Delivery`), and the three
aggregate growth facts over `[es, σ]`, the ground-truth-`Bval` endpoint strip holds
at `(w, m)` over `[lo, σ]`. `classes_base_transport` moves the honest classes to
`(w, m)` and `bval_strip_transport` carries the strip across nodes at `es`;
`bval_strip_window_uniform` carries it to `σ` in **one** window-uniform step. The
`hBb`-free, `INVstar`-free, `hdelta`-free replacement for
`INVstarTrack.bval_endpoint_strip_sigma ∘ INVstar_maintained`. -/
theorem bval_endpoint_strip_window_uniform (v₀ w : ValidatorIndex) (n₀ m : ℕ)
    (b' : Root) (lo es σ : Slot) (boost : ℕ)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
        E.AncestorOrVoteless cfg ext w m b' es i)
    (hstrip0 : E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hgrowS : E.Sval cfg ext w m b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b' lo σ)
    (hgrowX : E.Xval cfg ext w m b' lo σ ≤ E.Xval cfg ext w m b' lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
      ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es)) :
    E.Xval cfg ext w m b' lo σ + E.Bval lo σ + boost + 1 ≤ E.Sval cfg ext w m b' lo σ := by
  obtain ⟨hS, hX⟩ :=
    E.classes_base_transport_honest cfg ext v₀ w n₀ m b' lo es hSt hAt
  exact E.bval_strip_window_uniform cfg ext w m b' lo es σ boost
    (E.bval_strip_transport cfg ext v₀ w n₀ m b' lo es boost hstrip0 hS hX)
    hgrowS hgrowX hbudget

/-- **One `DescendStep` at a fork, confirm-margin / window-uniform.** At endpoint
`(w, m)`, from the plain confirm-margin strip at the confirming anchor `(v₀, n₀)`
over `[lo, es]` (`hstrip0` — `Base.weak_base_of_rule`, straight from
`is_one_confirmed`; **no** arms, **no** min-reserve `INVstar`), the honest descent
transports `hSt`/`hAt`, the three aggregate growth facts (`hgrowS`/`hgrowX`/`hbudget`
— the window-uniform `hdelta` replacement), and the endpoint fork data — the filtered
`b′`-side child `hchild`, its `b′`-side lower bound `hbside`, and a `Bval` sibling
upper bound `hsib` — the fork-choice head at `(w, m)` picks the `b′`-side child `c`.
Composes `bval_endpoint_strip_window_uniform` into `Endpoint.ledger_descendStep` at
`boost := get_proposer_score cfg (store)`. The drop-in for
`INVstarTrack.descendStep_of_forkEdgeGroundInputs` with the base reduced to the
confirm-margin strip and the maintenance collapsed: **no** `hBb`, **no** arms, **no**
per-slot `INVstar` step. -/
theorem descendStep_of_confirmMargin (v₀ w : ValidatorIndex) (n₀ m : ℕ)
    {b' h c : Root} (lo es σ : Slot)
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
        E.AncestorOrVoteless cfg ext w m b' es i)
    (hstrip0 : E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es
        + get_proposer_score cfg (E.store cfg ext w m) + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hgrowS : E.Sval cfg ext w m b' lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b' lo σ)
    (hgrowX : E.Xval cfg ext w m b' lo σ ≤ E.Xval cfg ext w m b' lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) * (E.Bval lo σ - E.Bval lo es)
      ≤ cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es))
    (hchild : ForkChoiceNode.mk c .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))))
    (hbside : E.Sval cfg ext w m b' lo σ ≤ get_attestation_score cfg (E.store cfg ext w m)
      (get_node_for_root c)
      ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint))
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h (get_parent_payload_status (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states
              (E.store cfg ext w m).justified_checkpoint)
          ≤ E.Xval cfg ext w m b' lo σ + E.Bval lo σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h c :=
  -- These bounds compare children within the selected payload branch.
  -- Selection of that branch remains open in `ledger_descendStep`.
  ledger_descendStep cfg ext hchild hbside
    (E.bval_endpoint_strip_window_uniform cfg ext v₀ w n₀ m b' lo es σ
      (get_proposer_score cfg (E.store cfg ext w m)) hSt hAt hstrip0 hgrowS hgrowX hbudget)
    hsib

end Execution

end FastConfirmation.Spec

end
