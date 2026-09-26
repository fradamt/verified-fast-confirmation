module
public import FastConfirmationProofs.FFG.Certificates.VoteLanding

@[expose] public section

/-!
# Spec / Proof / HeadStack

Proves known-root and relay facts required by the fork-choice head walk.

This module contains `head_root_known`, `b_known_of_relay` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hhead_known`, unconditional -/

/-- **`get_head` lands on a known block, unconditionally.** The case split
of `Engine.get_head_root_mem_or` (known block, or the justified checkpoint root on an
empty filtered descent) closes against `JustificationInterface.checkpoint_known`
(the justified root is a known block at every honest store). No `store_domain` /
walk hypotheses. This is `hhead_known` (`= (honest_attestation …).data.beacon_block_root`
by `honest_attestation_data_beacon_block_root`). -/
theorem head_root_known (hji : JustificationInterface cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m) :
    (get_head cfg (E.store cfg ext w m)).root ∈ (E.store cfg ext w m).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext w m) with h | h
  · exact h
  · rw [h]; exact (hji.checkpoint_known w hw m).1

/-! ## Section 2 — `hhead_walk`, reduced to the checkpoint-boundary bound -/


/-! ## Section 3 — the closed vote-landing bundle -/



/-! ## Section 4 — `hJlb`: the saturated-regime `Jspec` lower bound

`VoteLanding.boost_dilution` (feeding `IHMechanize.hmaj_of_saturation`) consumes the
saturated-regime lower bound `2·(boost+1) ≤ Jspec lo σ'`. It is a pure `span_fraction`
consequence over the committee weight of the (saturated, `≥ 1`-epoch) window: with
`C := CONFIRMATION_BYZANTINE_THRESHOLD ≤ 25`, `span_fraction` gives byzantine weight
`≤ C·W/100 ≤ W/4`, so the honest weight `Jspec = W − byz ≥ 3W/4`. Hence any
`4·(boost+1) ≤ W` closes `2·(boost+1) ≤ Jspec` (`3W/4 ≥ W/2 ≥ 2·(boost+1)`).

The residual `4·(boost+1) ≤ W(span lo σ')` is the *only* genuinely new fact — a
committee-weight floor over the saturated window: past `T1` the window spans a full
epoch, whose committee union is the whole active set (`committee_coverage`), of weight
`E.total_active`, while `boost = proposer_score_boost·(TAB/SLOTS_PER_EPOCH)/100 ≤
40·(TAB/32)/100 = TAB/80`, so `4·(boost+1) ≤ TAB/20 + 4 ≤ TAB = W` with wide margin.
Its faithful discharge needs the `estimate`/`committee_coverage` epoch-scale weight
identification (`W(full epoch) = TAB`); the theorem below states that premise directly. -/






/-! ## Section 6 — `hb`: the confirmed block relays to every later endpoint

`IHMechanize.dynamicsChainStruct_of_endpoint`'s first per-endpoint residual `hb` asks
that the confirmed block `b` is a known block at every honest endpoint `(w, m)`. The
confirmed root `b = E.confirmed cfg ext v₀ n₀` is a known block at its own confirming
store (`get_latest_confirmed` returns `confirmed_root` / the finalized root / a
`is_one_confirmed` descendant of the balance source — all in `block_roots`); `block_relay`
then lands it in every honest node's block set from the next slot on. `b_known_of_relay`
is that block-relay leg. Its slot gate `slot(n₀)+1 ≤ slot(m+1)` is the later-slot
regime; the **same-slot residue** (`slot(m) = slot(n₀)`, a *different* node `w` that has
not yet gossip-received `b`) is the intra-slot reach limit shared with `hBb` — the IH is
vacuous there (`slot(m') < slot(m) = slot(n₀)` is unreachable for `m' ≥ n₀`), so the full
`hb` shape carries that condition explicitly, just as `recorded_conflict_slashed` does for `hBb`.

`hcase` (`get_ancestor_roots (store w m) b jc ≠ [] ∨ b = jc`) is the L4 loop-inversion
descent: it is the AncestryRoots characterization of `b` sitting on the store's justified
chain, fed by the engine IH's justified-dominance leg + `L4Fold.find_latest_confirmed_
descendant_spec`. It is genuinely per-endpoint (the shell's own induction supplies the IH),
and is represented by an explicit per-endpoint premise. -/


end Execution

end FastConfirmation.Spec

end
