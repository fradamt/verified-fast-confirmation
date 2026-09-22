module
public import FastConfirmation.Spec.Proof.StepDischarge

@[expose] public section

/-!
# Spec / Proof / HeadSafetyEngine: the head-safety engine shell

This module mirrors the `head_safety_at_slot` and `head_safety_engine` construction in
`FastConfirmation/Paper/LMDGhost/Proof/HeadSafety.lean`.

This module is the **shell**: the strong induction on the cutoff slot `k` whose
predicate quantifies over *all* seconds `m` at slot `k` (`EngineInv`), assembling
`EngineInv cfg ext E b n₀ k` for every `k` from the per-store head-descent lemma.
It composes the following proved components:

* **`LedgerStepV2`** — the v2 per-fork ledger certificate (`Enemy` in place of the
  window byz `Bval` of `Endpoint.LedgerStep`): the sibling-recorded score is
  confined to the strictly smaller union enemy `weight (BbadSet ∪ SpentSet)`, so
  the descent inequality reads against `Enemy`. Its `get_weight` domination
  (`ghost_step_dominates_v2`) is `Endpoint.ghost_step_dominates`'s arithmetic with
  `Enemy` for `Bval`; the fold `head_descends_of_ledger_chain_v2` reuses
  `Endpoint.head_descends_of_ledger` verbatim on the produced `DescendStep` chain.
* **`inv2_ledgerStepV2`** — one fork's `LedgerStepV2` from `INV2` at `(w, m)` (via
  `LedgerV2.INV2_endpoint`), the recorded `b′`-side lower bound
  (`Endpoint.recorded_bside_ge`), the recorded sibling upper bound
  (`LedgerV2.recorded_sibling_le_v2`) and boost congruence. This is the INV2 ⟶
  head-descent wiring the certificate extractor instantiates per fork.
* **`INV2_maintained`** — the base-to-`σ` iteration of `LedgerV2.INV2_step`, taking
  the per-slot step transition as a functional (its class-delta hypotheses are the
  store-dynamics residue `StepDischarge` flags — outside the shell).
* **`spec_head_safety_engine`** — the headline. Strong induction on `k`; at each
  honest `(w, m)` the confirmed chain presents as a `List.IsChain LedgerStepV2`
  from the justified root to `b` (the `LedgerChainInput` functional, fed the
  induction hypothesis), folded to head descent. The functional packages the
  certificate-extraction boundary (INV2 base/step/endpoint + the recorded-support
  transport bridges + the E5 never-filtered / filter-containment inputs); per §8
  the E6 / `TipRecency`-family gates live there, not in the shell.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — the v2 per-fork ledger certificate and its head-descent fold

`Endpoint.lean` states its ledger step (`ghost_step_dominates`, `LedgerStep`,
`head_descends_of_ledger_chain`) against the whole window byz weight `E.Bval`.
The v2 accounting (`LedgerV2`) confines the enemy to the strictly smaller union
`E.Enemy = weight (BbadSet ∪ SpentSet)`; `LedgerV2.INV2_endpoint` and
`LedgerV2.recorded_sibling_le_v2` both read against `Enemy`, so the descent
inequality does too. These lemmas mirror the `Endpoint` triplet with `Enemy` for
`Bval`; the descent arithmetic and the chain fold are otherwise identical. -/

/-- Pure-ℕ core of the v2 GHOST step (`Gwei` weights are opaque to `omega`, so the
linear arithmetic is discharged over plain ℕ and `exact`-ed — the `Enemy`-analog of
`Endpoint`'s private `ghost_arith`). -/
private theorem ghost_arith_v2 {sc scc X EE P S : ℕ}
    (hbside : S ≤ sc) (hledger : X + EE + P + 1 ≤ S) (hsib : scc ≤ X + EE) :
    scc + P < sc := by omega

/-- **The GHOST step dominates (v2).** `Endpoint.ghost_step_dominates` with the v2
enemy `E.Enemy` in place of `E.Bval`: the `b′`-side lower bound (`hbside`), the v2
ledger inequality (`hledger`) and a v2 sibling upper bound (`hsib`) put the sibling
`cc` below the `b′`-side child `c` in `get_weight`. The boost is charged to the
sibling in full (`MajorityPersists.fork_weight_lt`); the winner's bare score already
clears sibling-plus-boost. -/
theorem ghost_step_dominates_v2 {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo es σ : Slot}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ
        + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ) :
    get_weight cfg store (ForkChoiceNode.mk cc) < get_weight cfg store (ForkChoiceNode.mk c) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (ghost_arith_v2 hbside hledger hsib)

/-- One fork's **v2** ledger certificate: `c` is the filtered `b′`-side child of
`h`, and for some certificate `(v₀, n₀, b′, lo, es, σ)` the v2 ledger inequality,
the `b′`-side lower bound and a v2 sibling upper bound (for every competing child)
hold at `store`. The `Enemy`-analog of `Endpoint.LedgerStep`. -/
def LedgerStepV2 (E : Execution Root) (store : Store Root) (h c : Root) : Prop :=
  ∃ (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot),
    ForkChoiceNode.mk c ∈
        get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h) ∧
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
        get_attestation_score cfg store (get_node_for_root c)
          (store.checkpoint_states store.justified_checkpoint) ∧
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ
        + get_proposer_score cfg store + 1
        ≤ E.Sval cfg ext v₀ n₀ b' lo σ ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' ∈
          get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ)

/-- A v2 ledger certificate yields a `DescendStep` (unpack, apply
`ghost_step_dominates_v2` through `EngineStore.descendStep_of_dom`). -/
theorem descendStep_of_ledgerStepV2 {E : Execution Root} {store : Store Root} {h c : Root}
    (hstep : LedgerStepV2 cfg ext E store h c) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c := by
  obtain ⟨v₀, n₀, b', lo, es, σ, hchild, hbside, hledger, hsib⟩ := hstep
  exact descendStep_of_dom cfg hchild
    (fun c' hc' hne => ghost_step_dominates_v2 cfg ext hbside hledger (hsib c' hc' hne))

/-- **Head descent from a v2 certificate chain.** A `List.IsChain LedgerStepV2`
from the justified checkpoint root down to `b` forces the fork-choice head to
descend from `b`: each certificate lifts to a `DescendStep`
(`descendStep_of_ledgerStepV2`), and `Endpoint.head_descends_of_ledger` closes the
chain. The `Enemy`-analog of `Endpoint.head_descends_of_ledger_chain` — the
confirmed-chain fold the shell instantiates at every honest `(w, m)`. -/
theorem head_descends_of_ledger_chain_v2 {E : Execution Root} {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hsub : ∀ r ∈ get_filtered_block_tree cfg store, r ∈ store.block_roots)
    {b : Root} {ds : List Root}
    (hb : b ∈ store.block_roots)
    (hnd : ds.Nodup)
    (hchain : List.IsChain (LedgerStepV2 cfg ext E store)
      (store.justified_checkpoint.root :: ds))
    (hlast : (store.justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b) :
    is_ancestor store (get_head cfg store) (get_node_for_root b) = true :=
  head_descends_of_ledger cfg hwf hsub hb hnd
    (hchain.imp (fun _ _ hab => descendStep_of_ledgerStepV2 cfg ext hab)) hlast

/-! ## Section 2 — `INV2` at `(w, m)` builds one fork's `LedgerStepV2`

The certificate extractor supplies, per fork on the confirmed chain, the ledger
invariant `INV2` at the honest store `(w, m)` together with the recorded-support
transport facts (the `b′`-side supporters record `c`-support — `hSmem`; the
sibling supporters are honest-confined to `Xclass` — `hHon` — or byz-confined to
the v2 enemy sets — `hByz`). This assembles them into a `LedgerStepV2`: the ledger
inequality is `INV2`'s endpoint strip, the `b′`-side score bound is
`Endpoint.recorded_bside_ge`, the sibling bound is `LedgerV2.recorded_sibling_le_v2`. -/

/-- **`INV2 ⟹ LedgerStepV2`.** From `INV2` at `(v₀, n₀, b′, lo, es, σ)` with the
registry-constant justified balance source (`hval`), the boost congruence
(`hboost`: `boost` equals the store's `get_proposer_score`), the
`b′`-side transport (`hSmem`) and the per-sibling honest/byz confinement
(`hHon`/`hByz`), the fork `(h, c)` has a v2 ledger certificate at `store`. The
ledger inequality is `INV2_endpoint`; the two recorded score bounds are
`recorded_bside_ge` / `recorded_sibling_le_v2`. -/
theorem inv2_ledgerStepV2 {E : Execution Root} {store : Store Root}
    (hval : (store.checkpoint_states store.justified_checkpoint).validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo es σ : Slot} {boost : ℕ}
    (hboost : boost = get_proposer_score cfg store)
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ boost)
    (hchild : ForkChoiceNode.mk c ∈
      get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h))
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hHon : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈
          get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ c' : Root,
      ForkChoiceNode.mk c' ∈
          get_node_children store (get_filtered_block_tree cfg store) (ForkChoiceNode.mk h) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint),
          i ∉ E.honest → i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    LedgerStepV2 cfg ext E store h c := by
  refine ⟨v₀, n₀, b', lo, es, σ, hchild, recorded_bside_ge cfg ext hval hSmem, ?_, ?_⟩
  · rw [← hboost]
    exact E.INV2_endpoint cfg ext v₀ n₀ b' lo es σ boost hinv
  · intro c' hc' hne
    exact E.recorded_sibling_le_v2 cfg ext hval (hHon c' hc' hne) (hByz c' hc' hne)

/-! ## Section 3 — the `INV2` maintenance iteration

The base-to-`σ` iteration of `LedgerV2.INV2_step`: given the base `INV2(es)`
(from the base arms via `INV2_base_of_arms`) and the per-slot step transition as
a functional (its class-delta hypotheses — `hs'`/`hx'`/`hE'`/`hJ'`/`hU'`/`hF3` —
are the store-dynamics residue `StepDischarge` discharges from `votes_head` + the
engine IH + delivery), `INV2` holds at every window end `σ ≥ es`. A clean
`Nat.le_induction`; the shell instantiates `hstep` per slot from `INV2_step`. -/

/-- **`INV2` maintenance.** From `INV2(es)` and the per-slot step transition
`hstep` (each slot's `INV2(σ) ⟹ INV2(σ+1)`, built by the caller from
`LedgerV2.INV2_step` + the class-delta facts), `INV2(σ)` holds for every
`σ ≥ es`. Past the saturation slot `T1` the caller supplies `hstep` from
`INV2_of_saturated` instead (no recurrence-tax bookkeeping); the shell threads
whichever the slot demands. -/
theorem INV2_maintained {E : Execution Root}
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hbase : E.INV2 cfg ext v₀ n₀ b' lo es es boost)
    (hstep : ∀ σ : Slot, es ≤ σ → E.INV2 cfg ext v₀ n₀ b' lo es σ boost →
      E.INV2 cfg ext v₀ n₀ b' lo es (σ + 1) boost) :
    ∀ σ : Slot, es ≤ σ → E.INV2 cfg ext v₀ n₀ b' lo es σ boost := by
  intro σ hσ
  induction σ, hσ using Nat.le_induction with
  | base => exact hbase
  | succ σ hσ ih => exact hstep σ hσ ih

/-! ## Section 4 — the shell: strong induction on the cutoff slot

Mirroring the paper's `head_safety_at_slot` / `head_safety_engine`
(`FastConfirmation/Paper/LMDGhost/Proof/HeadSafety.lean`): strong induction on the cutoff
slot `k`, the predicate (`EngineInv`) quantifying over *all* seconds `m` at slot
`k` and all honest `w`. The paper's per-ancestor `margin_maintained` + GHOST
canonicality assembly is, spec-side, the confirmed-chain `LedgerStepV2` fold
(`head_descends_of_ledger_chain_v2`) fed by the certificate functional
`LedgerChainInput`, which consumes the induction hypothesis exactly where the
paper feeds `hHead` (head-safety at strictly earlier slots). Everything the
functional packages — `INV2` base/step/endpoint, the recorded-support transport
bridges, the E5 never-filtered / filter-containment inputs — is the
certificate-extraction boundary of §8: the E6 / `TipRecency`-family gates live
there, not in the shell. -/

/-- **The certificate-chain functional.** At every honest node `(w, m)` past the
base second `n₀`, given head safety at every honest node at strictly earlier
slots (the strong-induction hypothesis, in the `< E.slot_at cfg m` form the paper
threads as `hHead`), the confirmed chain presents at `(w, m)` as a `List.IsChain`
of v2 ledger certificates from the justified checkpoint root down to `b`, together
with the fork-choice domain conditions (`parent_slot_lt`, filtered-tree
containment, `b`-knownness, path `Nodup`). This is precisely the store-dynamics
residue the shell cannot discharge internally — the L4 layer's certificate
extractor supplies it (per §8, incorporating the E5/E6 gates). -/
def LedgerChainInput (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
    E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∃ ds : List Root,
      (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
        r ∈ (E.store cfg ext w m).block_roots) ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      ds.Nodup ∧
      List.IsChain (LedgerStepV2 cfg ext E (E.store cfg ext w m))
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **The head-safety engine (shell headline).** Under the certificate functional
`LedgerChainInput`, the safe block `b` is on every honest node's fork-choice head
from second `n₀` on, through every cutoff slot `k` — `EngineInv cfg ext E b n₀ k`
for all `k`. Strong induction on `k`: for a second `m` at slot `< k` the induction
hypothesis closes it directly; at slot `k` the hypothesis, packaged in the
`hHead`-shaped `< E.slot_at cfg m` form, feeds `LedgerChainInput` to produce the
confirmed chain of v2 ledger certificates, folded to head descent by
`head_descends_of_ledger_chain_v2`. This is the shell the L4 fold (§8) instantiates
per confirmed block; `LedgerChainInput` is where the certificate extraction
(is_one_confirmed + the Arms/Base bridges + INV2 maintenance + E5) is discharged. -/
theorem spec_head_safety_engine {E : Execution Root} {b : Root} {n₀ : ℕ}
    (hcert : LedgerChainInput cfg ext E b n₀) :
    ∀ k : Slot, EngineInv cfg ext E b n₀ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro w hw m hm hmk hH
    by_cases hlt : E.slot_at cfg m < k
    · exact IH (E.slot_at cfg m) hlt w hw m hm (le_refl _) hH
    · have hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
          is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
            (get_node_for_root b) = true :=
        fun w' hw' m' hm' hlt' => by
          have hm'm : m' ≤ m := by
            by_contra hle
            have hmm' : m ≤ m' := Nat.le_of_not_ge hle
            exact (Nat.not_lt_of_ge (E.slot_at_mono cfg hmm')) hlt'
          exact IH (E.slot_at cfg m') (lt_of_lt_of_le hlt' hmk)
            w' hw' m' hm' (le_refl _) (E.withinHorizon_mono cfg hm'm hH)
      obtain ⟨ds, hwf, hsub, hb, hnd, hchain, hlast⟩ := hcert w hw m hm hH hIH
      exact head_descends_of_ledger_chain_v2 cfg ext hwf hsub hb hnd hchain hlast

end FastConfirmation.Spec

end
