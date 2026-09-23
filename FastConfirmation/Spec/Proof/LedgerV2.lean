module
public import FastConfirmation.Spec.Proof.Arms
public import FastConfirmation.Spec.Proof.Endpoint

@[expose] public section

/-!
# Spec / Proof / LedgerV2

This module contains `BbadSet`, `SpentSet`, `BbadVal` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the v2 enemy sets -/

open Classical in
/-- `BbadSet` — the base enemy in **recorded** form (`recorded-base reduction` reshape): non-honest,
`(v₀, n₀)`-non-equivocating members of the window `[lo, es]` whose **recorded** latest
message at `(v₀, n₀)` is **sibling-ward** — recorded neither `b′`-supporting
(`¬ lm.root ⪰ b′`) nor a `b′`-ancestor (`¬ b′ ⪰ lm.root`). Byzantine enemies are only
knowable through the store's recorded latest message (there is no
`HonestBehavior.no_forgery` for byz, so the ground `E.vote` and the recorded message
diverge); this is the recorded analog of `Xclass es`, definitionally equal to
`ByzVpre.RecByzSibBase cfg ext v₀ n₀ b′ lo es`. It still excludes `Bsup`, `Bpar` and
the relayed equivocators, and sits inside the window byz set `Bwin lo es` (only the
`span_committee`/`∉ honest` prefix is read by the accounting). -/
noncomputable def BbadSet (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) :
    Finset ValidatorIndex :=
  ((E.span_committee lo es).filter (fun i => i ∉ E.honest)).filter
    (fun i => i ∉ (E.store cfg ext v₀ n₀).equivocating_indices ∧
      ∀ lm : LatestMessage Root, (E.store cfg ext v₀ n₀).latest_messages i = some lm →
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root lm.root) (get_node_for_root b') = true ∧
        ¬ is_ancestor (E.store cfg ext v₀ n₀)
            (get_node_for_root b') (get_node_for_root lm.root) = true)

/-- `SpentSet σ` — the byz of the tail window `(es, σ]`; their per-slot votes pay
`span_fraction` capacity. -/
def SpentSet (es σ : Slot) : Finset ValidatorIndex :=
  (E.span_committee (es + 1) σ).filter (fun i => i ∉ E.honest)



/-! ## Section 2 — weight accessors -/

/-- `Bbad` — base-enemy weight. -/
noncomputable def BbadVal (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) : Gwei :=
  E.weight (E.BbadSet cfg ext v₀ n₀ b' lo es)


/-- `Enemy(σ) := weight (BbadSet ∪ SpentSet σ)` — the v2 enemy as a **union** weight
(`LedgerV2`, §9). A validator has one latest message, so the semantic enemy is a subset of
the union; counting members **once** is what makes the capacity cap `D·Enemy ≤ C·J`
derivable (`Enemy_capacity`) — the cross-epoch double-seat problem of the sum form
vanishes. `Enemy ≤ Bbad + spent` (`Enemy_le_sum`) keeps the step's additive arrival
accounting. -/
noncomputable def Enemy (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) : Gwei :=
  E.weight (E.BbadSet cfg ext v₀ n₀ b' lo es ∪ E.SpentSet es σ)



/-! ## Section 3 — easy set-level facts -/








/-! ## Section 4 — the `span_fraction` capacity bounds on the enemy

The base enemy sits inside the window byz set, so `Rterm_nonneg`'s
`(100−C)·B(es) ≤ C·J(es)` passes to it: `D·Bbad ≤ C·J₀`, hence
`Bbad ≤ ⌊C·J₀/D⌋`. The tail byz `spent` is `span_fraction`-bounded on the tail
window directly. -/






/-! ## Section 5 — monotonicity of the tail / enemy -/




/-! ## Section 6 — the v2 invariant and the endpoint strip -/

/-- **INV2** at window end `σ` (floored, `C := confirmation_byzantine_threshold`,
`D := 100 − C`): the honest support `s(σ)` covers the sibling-stuck honest `x(σ)`,
the v2 enemy `Enemy(σ) = Bbad + spent(σ)`, the boost margin, and a floored `min`
reserve — the recurrence tax `⌊C·U(σ)/D⌋` on unrecurred base supporters and the
remaining member capacity `⌊C·J(σ)/D⌋ − Enemy(σ)`. Mirrors v1's `INVstar` with
`Bval` replaced by the smaller `Enemy` and the reserve floored. -/
def INV2 (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot)
    (boost : ℕ) : Prop :=
  E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      + min (cfg.confirmation_byzantine_threshold * E.Uval cfg ext v₀ n₀ b' lo es σ
              / (100 - cfg.confirmation_byzantine_threshold))
          (cfg.confirmation_byzantine_threshold * E.Jspec lo σ
              / (100 - cfg.confirmation_byzantine_threshold)
            - E.Enemy cfg ext v₀ n₀ b' lo es σ)
    ≤ E.Sval cfg ext v₀ n₀ b' lo σ


/-! ## Section 7 — the base `INV2(es)` from the `Arms` arms -/






/-! ## Section 8 — the v2 sibling bridge (endpoint result 5)

`Endpoint.recorded_sibling_le` bounds a sibling's recorded score by `Xval + Bval`
(the whole window byz). The v2 refinement confines the byz supporters to the
smaller v2 enemy sets `BbadSet ∪ SpentSet` (the store-dynamics fact the shell
supplies: a byz recorded as backing a sibling of `b′` at `(w, m)` is either
already sibling-recorded at `es` — in `BbadSet` — or defected/arrived after `es`,
so it has a tail assignment — in `SpentSet`; equivocators relay out and score
zero), giving the tighter `Xval + Enemy(σ)`. -/





/-! ## Section 9 — the pure-ℕ v2 step ("defections pay")

The floored ledger step: `INV2(σ) ⟹ INV2(σ')` over the per-slot class deltas the
engine shell discharges (`ξ` = `x→s` migrants, `α` = `a→s` migrants, `φ` = fresh
honest joining `s`, `β` = new tail byz, `σt` = base supporters recurring off
`Unrec`). The reserve is floored (ℕ-division), so the step relies on the floor
witnesses' two-sided bounds; the byz arrival `β` pays the per-slot `span_fraction`
capacity `D·β ≤ C·(σt+ξ+α+φ)` (F3). Enemy caps `D·E ≤ C·J` at both ends keep the
member reserve un-truncated. `interval_cases C` turns every `C`/`D` product into a
literal-coefficient linear term and `omega` closes each of the 26 cases (the `min`
is split internally). -/




/-! ## Section 10 — saturation after `T1`, consuming `committee_coverage`

Beyond `T1 := end of epoch(es) + SLOTS_PER_EPOCH`, every honest active validator
has had an assignment in `(es, σ]` (`committee_coverage`: committees partition the
active set each epoch), so it has re-voted `desc(b′)` and left `Unrec`: `U(σ) = 0`,
the recurrence tax vanishes, and `INV2` collapses to its endpoint form — which the
window cap sustains. This section derives `U(σ) = 0` from `committee_coverage` (via
the epoch arithmetic) and shows `INV2` self-maintains from the endpoint margin. -/






end Execution

end FastConfirmation.Spec

end
