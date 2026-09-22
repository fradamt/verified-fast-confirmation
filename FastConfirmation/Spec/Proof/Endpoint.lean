module
public import FastConfirmation.Spec.Proof.Ledger
public import FastConfirmation.Spec.Proof.EngineStore
public import FastConfirmation.Spec.Proof.Bridge
public import FastConfirmation.Spec.Proof.Forks

@[expose] public section

/-!
# Spec / Proof / Endpoint: ledger inequality ⟹ head descent at `(w, m)`

This module consumes the per-`σ` ledger inequality

  `E.Xval + E.Bval + get_proposer_score store + 1 ≤ E.Sval`

(the `Ledger.lean` ground-class accessors for the certificate block `b′` over its
window `[lo, σ]`; the shell derives it from `INVstar` by stripping the `(100−C)`
factor and the `min`, and from `Base.weak_base_discharged` / boost congruence) and
produces the fork-choice head descent at every honest store `(w, m)`.

The endpoint uses the following components:

* **`recorded_bside_ge`** — the `b′`-side child's recorded
  attestation score at `(w, m)` is at least `Sval`, via
  `MajorityPersists.recorded_support_lower` with `HS := Sclass`. The
  ground-class → `AttSupporters` membership is the transport fact
  (`EngineTransport.HS0_in_AttSupporters` / `NewVoters_in_AttSupporters` shape),
  taken as a hypothesis the shell supplies.
* **`recorded_sibling_le`** — a sibling's recorded score is at
  most `Xval + Bval`, via `MajorityPersists.attestation_score_eq_weight` +
  `weight_union_le`. The honest confinement (recorded supporters of a sibling are
  in `Xclass` — `Bridge` + `Forks.siblings_incompatible`) and the byz confinement
  (`Bwin` window membership) are taken as hypotheses (store-dynamics; shell).
* **`ghost_step_dominates`** — the ledger plus the two recorded
  bounds give `get_weight (c̃) < get_weight (c)` for every sibling, via
  `MajorityPersists.fork_weight_lt`; `ledger_descendStep` packages this into an
  `EngineStore.DescendStep`.
* **`head_descends_of_ledger`** — an `EngineStore.DescendStep`
  chain from the justified root down to `b` (each fork's step built from a
  per-`b′` `ledger_descendStep`) forces the head to descend from `b` under the
  filter-containment hypotheses of `EngineStore.is_ancestor_get_head_of_chain`.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The `b′`-side child's recorded score dominates `Sval`

Set-weight subadditivity over a union (`EngineWindows.weight_union_le`, reused for
the sibling bound below) and the recorded-support machinery of `MajorityPersists`
are the only ingredients. -/

/-- **Recorded `b′`-side lower bound.** At a registry-constant balance source `bs`,
the fork child `c`'s attestation score at `store` is at least `Sval σ` — the
ground weight of the honest window members whose newest vote supports
`subtree(b′)` — provided every such member records a `c`-supporting latest message
at `store` (`hSmem`, the transport fact the shell supplies via
`EngineTransport.HS0_in_AttSupporters` / `NewVoters_in_AttSupporters`). Direct
`MajorityPersists.recorded_support_lower` with `HS := Sclass`. -/
theorem recorded_bside_ge {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c : Root} {lo σ : Slot}
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs) :
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c) bs := by
  rw [Execution.Sval]
  exact recorded_support_lower cfg hval (E.Sclass cfg ext v₀ n₀ b' lo σ) hSmem

/-! ## A sibling's recorded score is at most `Xval + Bval` -/

/-- **Recorded sibling upper bound.** At a registry-constant balance source `bs`,
the recorded attestation score of a sibling `cc` (of `parent(b′)`, `cc ≠` the
`b′`-side child) is at most `Xval σ + Bval σ`. Its supporter set splits into an
honest part confined to `Xclass` (recorded supporters of a sibling neither support
`subtree(b′)` nor are `b′`-ancestors — `Bridge` + `Forks.siblings_incompatible`,
supplied as `hHon`) and a byz part confined to the window enemy set `Bwin`
(window confinement, supplied as `hByz`);
`MajorityPersists.attestation_score_eq_weight` turns the score into that supporter
set's weight and `weight_union_le` weighs the confinement. -/
theorem recorded_sibling_le {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' cc : Root} {lo σ : Slot}
    (hHon : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∉ E.honest → i ∈ E.Bwin lo σ) :
    get_attestation_score cfg store (get_node_for_root cc) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ := by
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Bval]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  intro i hi
  rw [List.mem_toFinset] at hi
  rw [Finset.mem_union]
  by_cases hh : i ∈ E.honest
  · exact Or.inl (hHon i hi hh)
  · exact Or.inr (hByz i hi hh)

/-! ## The GHOST step favours the `b′`-side child -/

/-- Pure-ℕ core of the GHOST step (`Gwei` weights are opaque to `omega`, so the
linear arithmetic is discharged over plain ℕ and `exact`-ed). -/
private theorem ghost_arith {sc scc X B P S : ℕ}
    (hbside : S ≤ sc) (hledger : X + B + P + 1 ≤ S) (hsib : scc ≤ X + B) :
    scc + P < sc := by omega

/-- **The GHOST step dominates.** From the ledger inequality
`Xval + Bval + get_proposer_score + 1 ≤ Sval`, the `b′`-side lower bound `hbside`
and a sibling upper bound `hsib`, the sibling `cc`
loses to the `b′`-side child `c` in `get_weight` — the boost is charged to the
sibling in full (`MajorityPersists.fork_weight_lt`) yet the winner's bare score
already exceeds sibling-plus-boost. -/
theorem ghost_step_dominates {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo σ : Slot}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    get_weight cfg store (ForkChoiceNode.mk cc .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (ghost_arith hbside hledger hsib)

/-- **A ledger certificate builds one `DescendStep`.** At a fork with parent `h`,
`b′`-side child `c` (a `get_node_children` member of the filtered tree — the
never-filtered / chain-in-tree fact) the ledger inequality + the `b′`-side lower
bound + a sibling upper bound *for every competing child* dominate the fork in
`get_weight`, so `c` is the descent-step choice. Wraps `ghost_step_dominates`
through `EngineStore.descendStep_of_dom`. This is the per-fork producer the shell
iterates along the confirmed chain (one `b′` certificate per fork). -/
theorem ledger_descendStep {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot}
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c :=
  -- The sibling bound covers only this resolved parent. The pending parent's
  -- selection of that status remains to be derived; `descendStep_of_dom`
  -- requires that additional fact as its final argument.
  descendStep_of_dom cfg hchild
    (fun c' hc' hne => ghost_step_dominates cfg ext hbside hledger (hsib c' hc' hne))

/-! ## The head descends from `b` along the confirmed chain -/

/-- **Head descent from the ledger chain.** A `DescendStep` chain from the
justified checkpoint root down to `b` (each fork's step built by
`ledger_descendStep` from that block's ledger certificate)
forces the fork-choice head to descend from `b`. Thin composition over
`EngineStore.is_ancestor_get_head_of_chain`; `hwf` (`parent_slot_lt`) and `hsub`
(filtered ⊆ known) are the usual domain conditions and `hnd` the path
distinctness. -/
theorem head_descends_of_ledger {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (DescendStep cfg store (get_filtered_block_tree cfg store))
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  is_ancestor_get_head_of_chain cfg hwf hsub hb hnd hchain hlast

/-! ## The per-fork ledger certificate and the chain fold

`head_descends_of_ledger` consumes a pre-built `DescendStep` chain. The bundle
below expresses each fork's step as its ledger *certificate* — the raw inequalities
`ledger_descendStep` consumes, with the fork's `(v₀, n₀, b′, lo, σ)` existentially
packaged — so the shell can present the confirmed chain as a `List.IsChain` of
certificates, and `head_descends_of_ledger_chain` folds it to head descent. -/

/-- One fork's ledger certificate: `c` is the filtered `b′`-side child of `h`, and
for some certificate `(v₀, n₀, b′, lo, σ)` the ledger inequality, the `b′`-side
lower bound and a sibling upper bound (for every competing child) hold at `store`.
Exactly the hypotheses of `ledger_descendStep`, existentially bundled per fork. -/
def LedgerStep (E : Execution Root) (store : Store Root) (h c : Root) : Prop :=
  ∃ (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo σ : Slot),
    ForkChoiceNode.mk c .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) ∧
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
        get_attestation_score cfg store (get_node_for_root c)
          (store.checkpoint_states store.justified_checkpoint) ∧
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
        ≤ E.Sval cfg ext v₀ n₀ b' lo σ ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children store (get_filtered_block_tree cfg store)
            (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ)

/-- A ledger certificate yields a `DescendStep` (unpack the certificate, apply
`ledger_descendStep`). -/
theorem descendStep_of_ledgerStep {E : Execution Root} {store : Store Root} {h c : Root}
    (hstep : LedgerStep cfg ext E store h c) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c := by
  obtain ⟨v₀, n₀, b', lo, σ, hchild, hbside, hledger, hsib⟩ := hstep
  exact ledger_descendStep cfg ext hchild hbside hledger hsib

/-- **Head descent from a certificate chain.** A `List.IsChain` of per-fork ledger
certificates from the justified checkpoint root down to `b` forces the fork-choice
head to descend from `b`: each certificate lifts to a `DescendStep`
(`descendStep_of_ledgerStep`), and `head_descends_of_ledger` closes the chain.
This is the confirmed-chain fold — one `b′` certificate per fork — the head-safety
engine shell instantiates from the L4 chain of confirmed blocks. -/
theorem head_descends_of_ledger_chain {E : Execution Root} {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (LedgerStep cfg ext E store)
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  head_descends_of_ledger cfg hwf hsub hb hnd
    (hchain.imp (fun _ _ hab => descendStep_of_ledgerStep cfg ext hab)) hlast

end FastConfirmation.Spec

end
