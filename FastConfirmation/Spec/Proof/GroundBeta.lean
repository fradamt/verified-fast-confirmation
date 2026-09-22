module
public import FastConfirmation.Spec.Proof.StepDischargeII
public import FastConfirmation.Spec.Proof.Endpoint

@[expose] public section

/-!
# Spec / Proof / GroundBeta: the ground-truth-β same-slot argument

For **discount-funded (tax-arm)**
confirmations, `hBb` (`BbadVal@(w,m) ≤ BbadVal@(vc,nc)`, `StepDischargeII.
INV2_base_transport`'s recorded-enemy transport) is un-dischargeable at
`slot(m) = slot(nc)`: the relay legs (`attester_slashing_relay` /
`recorded_conflict_slashed` / `latest_message_relay`) are end-of-slot `+1`-gated
by design (`HeadStack` §5). At the protocol level, however, a tax-arm confirmation
at `vc` and a sibling flip at any other honest `w` are mutually exclusive when
the endpoint enemy is bounded directly by the ground-truth span budget.

This module ports that argument to Lean — the **ground-truth-β route**, exactly
as paper v4's Lemma 50 / Lemma 6 / Lemma 2 do: rather than *transport* the
recorded base enemy (`hBb`, relay-gated), bound the endpoint enemy **directly**
by the uniform `ByzantineBound.span_fraction` budget at the endpoint node
(store-independent; no relay), and let the confirmation's un-cancelled `2A`
budget (the rule charges `2·get_adversarial_weight` over the *full* live window,
silent enemies or not) plus the discount `d` (covering only parent-exact-stuck
honest weight) absorb it. The confirm/flip mutual exclusion is then a **pure-ℕ**
fact, closed by `omega` — no `interval_cases C` and, crucially, **no granularity
field** is needed (see §1 note: the `//100` floor only bites the transport
route, not the domination route).

The proof has three components:

* **§1 — the pure-ℕ arithmetic core** (`taxArm_confirm_excludes_flip`): a tax-arm confirmation excludes
  the sibling flip, over ground-truth weights bounded by the rule's charged
  budgets. `omega`-closed.
* **§2 — the endpoint enemy span bound** (`BbadVal_le_budget_direct`): the
  recorded base enemy at *any* store `(w, m)` is `span_fraction`-bounded by the
  ground-truth window budget `⌊C·J(es)/D⌋` **directly** — the store-independent
  replacement for the relay-gated `hBb`.
* **§3 — the same-slot endpoint strip** (`inv2_endpoint_sameslot`): the endpoint
  inequality `Xval@(w,m) + Bval(es) + boost + 1 ≤ Sval@(w,m)` that the ledger
  endpoint consumes, from the confirmation surplus and the honest-window-vote
  bridges, expressed as typed hypotheses.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — the pure-ℕ arithmetic core

The scenario has parent `p` at slot `sp`; competing
sibling `b_sib` at `sp+1`; confirmed block `b` at `es ≥ sp+2`; current slot
`cur`; empty region `[sp+1, es−1]` (committee weight `We`, byz `Ae`), live
region `[es, cur−1]` (committee weight `Wl`, byz `Al`). All honest weights are
ground truth; the confirmation window votes are past-slot, hence delivered to
every honest node by synchrony (the same fact that makes the window agree even
at same-slot — the intra-slot residue lives only in the *latest*-second votes,
which the confirmation window `[·, cur−1]` excludes).

The arithmetic atoms are:

| quantity | Lean atom | meaning |
|---|---|---|
| `We`, `Wl` | `We`, `Wl` | empty / live committee weight |
| `Ae`, `Al` | `Ae`, `Al` | actual byz weight, `100·A ≤ C·W` (span_fraction) |
| `advE`, `advL` | `advE`, `advL` | rule's charged budget `get_adversarial_weight` |
| `He = We−Ae`, `Hl = Wl−Al` | `He`, `Hl` | honest weight |
| `pE_vc` | `pE` | byz shown parent `p` to `vc` (feeds discount) |
| `bL_vc` | `bL` | byz shown `b` to `vc` (feeds support) |
| `sibE_w`, `sibL_w` | `sE`, `sL` | byz shown sibling to `w` (feeds flip) |
| `discount = parent_support − advE` | `d` | equivocation-net discount |
| `boost` | `boost` | `compute_proposer_score` |

The rule's budgets dominate the actual byz (`hAe`,`hAl`: `Ae ≤ advE`,
`Al ≤ advL`) — this is `span_fraction` composed with `estimate_dominates`, and
is exactly where the `//100` floor is harmless: domination survives it (the
floor only *under*-counts, which cannot break `actual ≤ budget`). No
granularity hypothesis is needed. -/

/-- **Confirm excludes flip (pure ℕ).**

Hypotheses (all ground-truth ℕ weights):
* `hHe`/`hHl`: the committee splits honest + byz (`We = He + Ae`, `Wl = Hl + Al`);
* `hAe`/`hAl`: the rule's charged budgets dominate the actual byz
  (`Ae ≤ advE`, `Al ≤ advL` — `span_fraction` + `estimate_dominates`);
* `hpE`/`hbL`/`hsE`/`hsL`: each selective-disclosure allocation is bounded by the
  region's byz (`pE,sE ≤ Ae`, `bL,sL ≤ Al`);
* `hdisc`: the discount is active — `parent_support = He + pE = advE + d`, `d ≥ 1`
  (the `compute_empty_slot_support_discount` guard `parent_support > advE`);
* `hconfirm`: `is_one_confirmed` at `vc` — `2·(Hl + bL) + d ≥ We + Wl + boost
  + 2·advL + 1` (`is_one_confirmed_ineq`: `2·attestation_score + discount ≥
  estimate([sp+1, cur−1]) + proposer_score + 2·adversarial_weight + 1`, with
  `estimate = We + Wl`, `attestation_score = Hl + bL`).

Conclusion: `sE + sL ≤ Hl + boost` — the sibling's recorded support at `w`
(byz-only; honest support `b`) does **not** exceed `b`'s honest live support plus
the proposer boost, i.e. the LMD-GHOST head at `w` does **not** flip to the
sibling. `omega`.

*Two properties of the ground-truth route* (both absent from the floored
ledger's `Arms.arms_pure`): **(1)** `C` drops out entirely — the mutual exclusion
is **uniform in the byzantine threshold**, needing no `interval_cases C` (the
floored ledger needed all 26 cases because the `//100` reserve is `C`-shaped;
here the enemy is dominated *directly*). **(2)** the discount-active guard
`d ≥ 1` is **not needed** — the confirm margin already gives `Hl ≥ Ae+Al+boost+1`
whether or not the discount fires (both are dropped; the lemma is the strongest
clean form). -/
theorem taxArm_confirm_excludes_flip
    {We Wl Ae Al advE advL boost He Hl pE bL sE sL d : ℕ}
    (hHe : We = He + Ae) (hHl : Wl = Hl + Al)
    (hAe : Ae ≤ advE) (hAl : Al ≤ advL)
    (hpE : pE ≤ Ae) (hbL : bL ≤ Al) (hsE : sE ≤ Ae) (hsL : sL ≤ Al)
    (hdisc : He + pE = advE + d)
    (hconfirm : We + Wl + boost + 2 * advL + 1 ≤ 2 * (Hl + bL) + d) :
    sE + sL ≤ Hl + boost := by
  omega

/-- **The confirm-side endpoint bound (pure ℕ).** The same hypotheses (minus the
flip allocations `sE`/`sL`) yield the *positive* margin `Hl ≥ Ae + Al + boost + 1`
— `b`'s honest live support strictly dominates the whole live-window byz plus
boost. This is the confirm half in isolation; the flip half
`sE + sL ≤ Ae + Al` then contradicts a flip. Used by §3 to strip to the endpoint
inequality with the ground-truth window enemy `Bval(es)` in place of the recorded
`Enemy`. `omega`. -/
theorem taxArm_confirm_margin
    {We Wl Ae Al advE advL boost He Hl pE bL d : ℕ}
    (hHe : We = He + Ae) (hHl : Wl = Hl + Al)
    (hAe : Ae ≤ advE) (hAl : Al ≤ advL)
    (hpE : pE ≤ Ae) (hbL : bL ≤ Al)
    (hdisc : He + pE = advE + d)
    (hconfirm : We + Wl + boost + 2 * advL + 1 ≤ 2 * (Hl + bL) + d) :
    Ae + Al + boost + 1 ≤ Hl := by
  omega

namespace Execution

variable (E : Execution Root)

/-! ## Section 2 — the endpoint enemy span bound (the store-level `hBb` replacement)

`StepDischargeII.INV2_base_transport` needs `hBb : BbadVal@(w,m) ≤ BbadVal@(vc,nc)`
— the recorded enemy *shrinking* from the confirming store to the endpoint —
which the relays gate at `slot(m) ≥ slot(nc)+1`. The ground-truth-β route never
transports: the **full** window enemy `Bval(es) = weight(Bwin lo es)` is
**store-independent** (it reads only `E.span_committee`/`∉ E.honest`, no store),
so it — and *a fortiori* every store's recorded base enemy `BbadVal@(w,m) ≤
Bval(es)` — is bounded by the ground-truth budget **at the endpoint node
directly**, by `span_fraction` alone (`Ledger.Rterm_nonneg`). No relay, no
same-slot residue. This is what `Endpoint.recorded_sibling_le` already uses to
bound a sibling's flip support (`hByz`: byz supporters ⊆ `Bwin lo es`), and what
`taxArm_confirm_excludes_flip`'s `hAe`/`hAl` domination is at ground truth. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- **The full window enemy is span_fraction-budgeted (floored), store-independent.**
`Bval(es) ≤ ⌊C·J(es)/D⌋` with `C := confirmation_byzantine_threshold`,
`D := 100 − C`. Directly from `Ledger.Rterm_nonneg` (`(100−C)·B ≤ C·J`, the
cross-multiplied `span_fraction`) and `Nat.le_div_iff_mul_le` (`D > 0` from
`C ≤ 25`). Holds at every honest endpoint `(w, m)` with **no** relay — the
ground-truth replacement for the recorded transport `hBb`: where the ledger
shrank the enemy to the recorded `BbadVal` to make the base transport go through
same-slot, the full `Bval` is already under the budget everywhere. -/
theorem Bval_le_floor_capacity (hbb : ByzantineBound cfg E) (lo es : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es) :
    E.Bval lo es ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo es
        / (100 - cfg.confirmation_byzantine_threshold) := by
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le; omega
  rw [Nat.le_div_iff_mul_le hDpos, Nat.mul_comm]
  exact E.Rterm_nonneg cfg hbb lo es hloH hesH

/-- **The recorded base enemy at any endpoint is span_fraction-budgeted, no relay.**
`BbadVal@(w,m) ≤ ⌊C·J(es)/D⌋` — the store-independent budget bound applied at the
endpoint `(w, m)` itself. This is `LedgerV2.BbadVal_le_floor_capacity` at the
endpoint anchor; stated here as the explicit **`hBb`-free** enemy bound the
ground-truth route uses in place of `StepDischargeII.INV2_base_transport`'s relay
transport. Because it holds at *every* anchor, it holds at same-slot endpoints
`slot(m) = slot(nc)` where `hBb` cannot fire. -/
theorem BbadVal_endpoint_le_floor (hbb : ByzantineBound cfg E)
    (w : ValidatorIndex) (m : ℕ) (b' : Root) (lo es : Slot)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es) :
    E.BbadVal cfg ext w m b' lo es ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo es
        / (100 - cfg.confirmation_byzantine_threshold) :=
  le_trans (E.weight_mono (E.BbadSet_subset_Bwin cfg ext w m b' lo es))
    (E.Bval_le_floor_capacity cfg hbb lo es hloH hesH)

end Execution

/-! ## Section 3 — the same-slot endpoint strip, transport-free

`Endpoint.ghost_step_dominates` consumes the **ground-truth-`Bval` endpoint strip**
`hledger : Xval + Bval + get_proposer_score + 1 ≤ Sval` (not the recorded-`Enemy`
form), and `Endpoint.recorded_sibling_le` bounds the sibling with the same `Bval`.
The v2 ledger (`INV2`/`Enemy`) shrank the enemy to the recorded `BbadVal` for a
tighter base — but that made the base *store-dependent*, forcing the relay-gated
`hBb : BbadVal@(w,m) ≤ BbadVal@(vc,nc)` (`StepDischargeII.INV2_base_transport`),
which is un-dischargeable same-slot.

The ground-truth-β route uses the v1 invariant `Ledger.INVstar` (over the full
`Bval`) instead. `Bval(lo, σ)` reads only `E.span_committee`/`∉ E.honest` — it is
**store-independent**, the *same term* at both anchors — so the endpoint strip
transports across nodes with **only the honest legs** (`Sval` grows, `Xval`
shrinks; `Ledger.weight_mono` over the class transports), and **no enemy transport
`hBb` at all**. That the confirmation surplus funds the *looser* `Bval` base (not
just the shrunk `Enemy`) is exactly `taxArm_confirm_margin`:
the rule's un-cancelled `2A` covers the full window byz. Hence this leg carries
**no same-slot residue** — the residue was entirely `hBb`'s, and `hBb` is gone. -/

/-- Pure-ℕ transport of the endpoint strip (Gwei is opaque to `omega`, so the
linear step is discharged over plain ℕ and `exact`-ed). -/
private theorem strip_transport_arith {X0 Xm B boost S0 Sm : ℕ}
    (hstrip : X0 + B + boost + 1 ≤ S0) (hS : S0 ≤ Sm) (hX : Xm ≤ X0) :
    Xm + B + boost + 1 ≤ Sm := by omega

namespace Execution

variable (E : Execution Root)

/-- **The `INVstar` endpoint strip.** Dropping the nonnegative `min` reserve and
cancelling the positive factor `(100 − C)` (from `C ≤ 25`), `Ledger.INVstar` at
window end `σ` yields the plain ground-truth endpoint inequality
`Xval(σ) + Bval(σ) + boost + 1 ≤ Sval(σ)` — the `Bval` form
`Endpoint.ghost_step_dominates` consumes as `hledger`. The v1 analog of
`LedgerV2.INV2_endpoint`, with the full window enemy `Bval` in place of `Enemy`. -/
theorem INVstar_endpoint (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) (hinv : E.INVstar cfg ext v₀ n₀ b' lo es σ boost) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  simp only [Execution.INVstar] at hinv
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le; omega
  refine Nat.le_of_mul_le_mul_left (le_trans (Nat.le_add_right _ _) hinv) hDpos

/-- **The endpoint strip transports across anchors — `hBb`-free.** Given the strip
`Xval + Bval + boost + 1 ≤ Sval` at the confirming anchor `(v₀, n₀)` and the two
honest class movements (`hS : Sval@(v₀,n₀) ≤ Sval@(w,m)`, `hX : Xval@(w,m) ≤
Xval@(v₀,n₀)`), the strip holds at the endpoint `(w, m)`. `Bval(lo, es)` is
store-independent (the identical term at both anchors), so — unlike
`StepDischargeII.INV2_base_transport` — **no enemy-weight movement `hBb` is
needed**, and the leg fires at same-slot. The honest legs are exactly
`StepDischargeII.classes_base_transport`'s outputs (`weight_mono` over the
`SupportsDesc`/`AncestorOrVoteless` transports the shell supplies). -/
theorem bval_strip_transport (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root)
    (lo es : Slot) (boost : ℕ)
    (hstrip : E.Xval cfg ext v₀ n₀ b' lo es + E.Bval lo es + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo es)
    (hS : E.Sval cfg ext v₀ n₀ b' lo es ≤ E.Sval cfg ext w m b' lo es)
    (hX : E.Xval cfg ext w m b' lo es ≤ E.Xval cfg ext v₀ n₀ b' lo es) :
    E.Xval cfg ext w m b' lo es + E.Bval lo es + boost + 1
      ≤ E.Sval cfg ext w m b' lo es :=
  strip_transport_arith hstrip hS hX

/-- **The same-slot endpoint strip, composed from the raw honest transports.**
From `INVstar` at the confirming anchor and the forward descent transports
`hSt`/`hAt` (the honest window members' newest votes still support `desc(b′)` /
stay ancestor-or-voteless at `(w, m)` — supplied by the shell via `votes_head` +
delivery of the *past-slot* window votes, hence available even at same-slot), the
ground-truth-`Bval` endpoint strip holds at `(w, m)`. This is the tax-arm route
replacement for `StepDischargeII.INV2_base_transport_of_transport`: same honest
inputs `hSt`/`hAt`, but the enemy leg `hBb` is **eliminated** (store-independent
`Bval`). Directly feeds `Endpoint.ghost_step_dominates`/`ledger_descendStep`'s
`hledger` at `boost := get_proposer_score cfg (E.store cfg ext w m)`. -/
theorem bval_endpoint_strip_of_transport (v₀ w : ValidatorIndex) (n₀ m : ℕ)
    (b' : Root) (lo es : Slot) (boost : ℕ)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i)
    (hinv : E.INVstar cfg ext v₀ n₀ b' lo es es boost) :
    E.Xval cfg ext w m b' lo es + E.Bval lo es + boost + 1
      ≤ E.Sval cfg ext w m b' lo es := by
  obtain ⟨hS, hX⟩ := E.classes_base_transport cfg ext v₀ w n₀ m b' lo es hSt hAt
  exact E.bval_strip_transport cfg ext v₀ w n₀ m b' lo es boost
    (E.INVstar_endpoint cfg ext v₀ n₀ b' lo es es boost hinv) hS hX

end Execution

/-! ## Section 4 — wiring: the same-slot per-fork descent, `hBb`-free

`Endpoint.ledger_descendStep` builds one `EngineStore.DescendStep` at a fork from
the `Bval` endpoint strip (`hledger`), the `b′`-side lower bound (`hbside`,
`Endpoint.recorded_bside_ge`) and the `Bval` sibling upper bound (`hsib`,
`Endpoint.recorded_sibling_le`). §3's `bval_endpoint_strip_of_transport` supplies
`hledger` at the endpoint `(w, m)` with **no `hBb`**; the other two inputs are the
honest transport (`hbside`) and the `span_fraction`/`siblings_incompatible`
confinements (`hsib`) — all `hBb`-free. So the whole per-fork descent step closes
at **any** slot regime, same-slot included: the same-slot availability `hBb` corner is gone
from the base transport. This is the drop-in replacement for the
`ChainInput`/`INV2_base_transport_of_transport` per-edge pipeline's enemy leg. -/

/-- **One `DescendStep` at a fork, ground-truth-β / `hBb`-free.** From `INVstar` at
the confirming anchor `(v₀, n₀)` (the economic-core base — `Arms.arms_of_confirmed`
in `INVstar` form), the honest descent transports `hSt`/`hAt` (past-slot window
votes, same-slot-available), and the endpoint fork data at `(w, m)` — the filtered
`b′`-side child `hchild`, its `b′`-side lower bound `hbside`, and a `Bval` sibling
upper bound `hsib` for every competing child — the fork-choice head at `(w, m)`
picks the `b′`-side child `c`. The enemy leg is the store-independent `Bval`, so
**no `hBb`**: valid at `slot_at m = slot_at n₀`. Composes
`bval_endpoint_strip_of_transport` into `Endpoint.ledger_descendStep`. -/
theorem ledger_descendStep_groundBeta {E : Execution Root}
    (v₀ w : ValidatorIndex) (n₀ m : ℕ) {b' h c : Root} (lo es : Slot)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i)
    (hinv : E.INVstar cfg ext v₀ n₀ b' lo es es
      (get_proposer_score cfg (E.store cfg ext w m)))
    (hchild : ForkChoiceNode.mk c .pending ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m))
        (ForkChoiceNode.mk h
          (get_parent_payload_status (E.store cfg ext w m)
            ((E.store cfg ext w m).blocks c))))
    (hbside : E.Sval cfg ext w m b' lo es ≤
      get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states
          (E.store cfg ext w m).justified_checkpoint))
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈ get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states
              (E.store cfg ext w m).justified_checkpoint)
          ≤ E.Xval cfg ext w m b' lo es + E.Bval lo es) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h c :=
  ledger_descendStep cfg ext hchild hbside
    (E.bval_endpoint_strip_of_transport cfg ext v₀ w n₀ m b' lo es
      (get_proposer_score cfg (E.store cfg ext w m)) hSt hAt hinv) hsib

/-! ## Consequences of the ground-truth-β argument

The principal consequences are:

1. **The arithmetic exclusion** (§1,
   `taxArm_confirm_excludes_flip` / `taxArm_confirm_margin`): a tax-arm
   confirmation at `vc` and a sibling flip at any other honest `w` are mutually
   exclusive, over ground-truth weights bounded by the rule's charged budgets.
   `omega`.
2. **The recorded-`BbadVal` transport `hBb` is eliminated from the base
   transport** (§2–§4): the full window enemy `Bval(es)` is store-independent and
   `span_fraction`-budgeted at the endpoint directly (`Bval_le_floor_capacity`,
   no relay); the endpoint strip `Xval + Bval + boost + 1 ≤ Sval`
   (`Endpoint.ghost_step_dominates`'s `hledger`) transports across nodes with only
   the honest legs (`bval_strip_transport`/`bval_endpoint_strip_of_transport`);
   and the whole per-fork descent closes at **any** slot regime
   (`ledger_descendStep_groundBeta`), same-slot included. `hBb` — the sole
   carrier of the base-transport same-slot residue (`HeadStack` §5,
   `StepDischargeII` §1) — is gone.

No granularity hypothesis is needed. Divisibility of weights by `100` or
`EFFECTIVE_BALANCE_INCREMENT`, which would make `//100` exact, is not required for
the ground-truth route. Section 1 uses the
*domination* form `Ae ≤ advE`, `Al ≤ advL` (actual byz ≤ the rule's charged
budget), which is `span_fraction` composed with `estimate_dominates` — and
domination *survives* the `//100` floor (the floor only under-counts the budget,
which cannot break `actual ≤ budget`). Thus `span_fraction` and
`estimate_dominates` suffice, and `C` itself drops out (uniform in the byzantine threshold — no
`interval_cases C`).

The endpoint lemmas use the following explicit hypotheses, all `hBb`-free:

* `hinv : INVstar@(v₀,n₀)` — the **economic-core base** at the confirming anchor.
  This is `Arms.arms_of_confirmed` in `INVstar` form: `is_one_confirmed_ineq` +
  the `Arms` V/pre class-decomposition identities (`EconomicCore.INV2_base_bridged`
  residue / `LastAlgebra.vpreIdentities_of`).
* `hSt`/`hAt` — the honest descent transports (`SupportsDesc`/`AncestorOrVoteless`
  at `(w,m)`). The window votes are *past-slot* (`[lo, es] ⊆ [·, cur−1]`), hence
  available by synchrony even within the confirming slot, so these carry **no**
  same-slot residue (unlike the latest-second votes, which the confirmation
  window excludes). The shell supplies them via `votes_head` + delivery
  (`Delivery`/`EngineTransport`), the same honest inputs
  `StepDischargeII.classes_base_transport` already consumes.
* `hbside`/`hsib` — `Endpoint.recorded_bside_ge` / `recorded_sibling_le`'s inputs
  (honest support transport + `span_fraction`/`siblings_incompatible`
  confinements). `hBb`-free.

This argument removes `hBb` from the base transport. It does not construct the
engine base `INVstar@(v₀,n₀)`, which remains an explicit premise of these endpoint
lemmas.

`ledger_descendStep_groundBeta`
is the drop-in for the enemy leg of the `ChainInput`/`INV2_base_transport_of_transport`
per-edge pipeline that `ForkEdgeEngineSupply` (hence `Definitive.EngineOpenResiduals.
fork_edges_engine`) threads. After this lemma, that leg needs no `hBb` at any
slot. The `SameSlotFinalizedRootKnown` field
(`finalized_dom_sameslot`) is a **different** corner — the finalized-reset-anchor
*block-gossip* knownness, past `block_relay`'s `+1` gate — untouched by the
tax-arm arithmetic and not addressed here. -/

end FastConfirmation.Spec

end
