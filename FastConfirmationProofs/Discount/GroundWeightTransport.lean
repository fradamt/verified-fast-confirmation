module
public import FastConfirmationProofs.Handlers.HandlerVoteClasses
public import FastConfirmationProofs.FFG.SelectedSource.EndpointMargin

@[expose] public section

/-!
# Spec / Proof / GroundBeta

Transports ground-truth vote weights when an execution window is stripped or extended.

This module contains `strip_transport_arith`, `bval_strip_transport` and related declarations.
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



namespace Execution

variable (E : Execution Root)





end Execution



/-- Pure-ℕ transport of the endpoint strip (Gwei is opaque to `omega`, so the
linear step is discharged over plain ℕ and `exact`-ed). -/
private theorem strip_transport_arith {X0 Xm B boost S0 Sm : ℕ}
    (hstrip : X0 + B + boost + 1 ≤ S0) (hS : S0 ≤ Sm) (hX : Xm ≤ X0) :
    Xm + B + boost + 1 ≤ Sm := by omega

namespace Execution

variable (E : Execution Root)


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


end Execution






end FastConfirmation.Spec

end
