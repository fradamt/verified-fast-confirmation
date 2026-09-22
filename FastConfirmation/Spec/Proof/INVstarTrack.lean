module
public import FastConfirmation.Spec.Proof.GroundBeta
public import FastConfirmation.Spec.Proof.Remainder
public import FastConfirmation.Spec.Proof.FinalWiring
public import FastConfirmation.Spec.Proof.Identities
public import FastConfirmation.Spec.Proof.StrongPrefixSafety

@[expose] public section


/-!
# Spec / Proof / INVstarTrack: the `hBb`-free per-edge pipeline

The **ground-truth-β / INV\*** route in
`FastConfirmation/Spec/Proof/GroundBeta.lean` uses
the endpoint enemy is the **store-independent** window weight `Bval` (`span_fraction`
budgeted directly at the endpoint), so the per-fork descent transports with the
**honest legs only** and needs **no** `hBb`.

This module used to re-derive the whole `fork_edges` per-edge pipeline on that track,
mirroring the v2 (`INV2`/`Enemy`, `hBb`-carrying) shapes but with the `INVstar` base, up to a
facade engine bundle that **dropped the `hBb` field**. The facade and the pipeline above the
per-edge record — `descendStep_of_forkEdgeGroundInputs`, `LedgerChainInputGround`,
`spec_head_safety_engine_ground`, `safeFrom_of_ground_certificates`, `ForkEdgeGroundSupply`,
`forkEdgeSupply_of_ground`, `SoundResidualsGround`, `l4Residual_of_soundResidualsGround`,
`EngineGroundResiduals`, `spec_safety_soundResidualsGround`, and the σ-general strip
`bval_endpoint_strip_sigma` — are **deleted** with the legacy `SpecAssumptions`
observed-anchor cone's orphan sweep (P-6; see the section notes below and
`docs/p6-justified-descends-derivation.md` §8).

What remains is the part other modules still consume: the per-edge input record
`ForkEdgeGroundInputs` (the `hBb`-free mirror of the v2 `ForkEdgeEngineInputs`, produced by
`EngineCore.forkEdgeGroundInputs_of`), its maintenance lemma `INVstar_maintained`, and the walk
helper `mem_isAncestor_of_parentChain` (`AnchorClose`, `CoveredMargin`,
`SelectedPreQueryHistoricalSIR`).

**Maintenance for σ > es.** The window end σ at a later endpoint exceeds the base
`es`; `INVstar_maintained` iterates `Ledger.INVstar_step` from the base
`INVstar(es)` to any `σ ≥ es`. Unlike the `INV2`/`Enemy` form, the enemy leg of the
step (`hB' : Bval(σ+1) ≤ Bval(σ) + β`) is the store-independent `Bval`, monotone in
the window (`Ledger.Bval_mono`) — **no** arrival/relay accounting; the funding
`hF3` is the per-slot `span_fraction` (`StepDischargeII.hF3_of_partition`), the same
honest-growth funding the v2 step uses.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the σ-general endpoint strip and the `INVstar` maintenance

`GroundBeta.bval_endpoint_strip_of_transport` transports the `INVstar` strip at the
**base** window end `es` (σ = es). At a later endpoint the relevant window end is the
current σ ≥ es, so this section re-states the strip transport at a general window end
σ, and delivers the `INVstar` maintenance that lifts the base `INVstar(es)` to
`INVstar(σ)` at the confirming anchor. -/

/-! ### Deleted: the `hBb`-free engine facade

Eleven declarations stood here: the σ-general endpoint strip `bval_endpoint_strip_sigma`, the
per-edge `DescendStep` lift `descendStep_of_forkEdgeGroundInputs`, the chain input
`LedgerChainInputGround`, the ground head-safety engine `spec_head_safety_engine_ground` and
its fold `safeFrom_of_ground_certificates`, the per-block supply `ForkEdgeGroundSupply` with
`forkEdgeSupply_of_ground`, and the facade `SoundResidualsGround` /
`l4Residual_of_soundResidualsGround` / `EngineGroundResiduals` /
`spec_safety_soundResidualsGround`.

The per-edge input record `ForkEdgeGroundInputs`, its maintenance lemma `INVstar_maintained`
and the walk helper `mem_isAncestor_of_parentChain` survive: `EngineCore`, `AnchorClose`,
`CoveredMargin` and `Dominance` still consume them.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-- **`INVstar` maintenance to any window end σ ≥ es.** From the base `INVstar(es)` and
a per-slot step functional `hstep` (each `INVstar(σ) ⟹ INVstar(σ+1)`, built by the
caller from `Ledger.INVstar_step` + the honest class-migration deltas; the enemy leg is
the store-independent `Bval`, monotone by `Ledger.Bval_mono`, so no arrival accounting),
`INVstar(σ)` holds for every `σ ≥ es`. A clean `Nat.le_induction` — the v1 analog of
`HeadSafetyEngine.INV2_maintained`, with `Bval` in place of the recorded `Enemy`. -/
theorem INVstar_maintained (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (boost : ℕ)
    (hbase : E.INVstar cfg ext v₀ n₀ b' lo es es boost)
    (hstep : ∀ σ : Slot, es ≤ σ → E.INVstar cfg ext v₀ n₀ b' lo es σ boost →
      E.INVstar cfg ext v₀ n₀ b' lo es (σ + 1) boost) :
    ∀ σ : Slot, es ≤ σ → E.INVstar cfg ext v₀ n₀ b' lo es σ boost := by
  intro σ hσ
  induction σ, hσ using Nat.le_induction with
  | base => exact hbase
  | succ σ hσ ih => exact hstep σ hσ ih

/-! ## Section 2 — the `hBb`-free per-edge bundle and its `DescendStep`

`ForkEdgeGroundInputs` is the `hBb`-free mirror of `ShellCompose.ForkEdgeEngineInputs`:
the base is `INVstar` at the confirming anchor `(vc, nc)` over `[lo, σ]` (the v1 invariant
over the store-independent `Bval`) instead of `INV2`, and there is **no** `hBb` field. Its
fields are exactly the inputs `GroundBeta.ledger_descendStep` consumes at window end σ: the
honest descent transports `hSt`/`hAt`, the invariant `hinv`, the filtered child `hchild`, the
`b`-side lower bound `hbside`, and the `Bval` sibling upper bound `hsib`. -/

/-- **The per-edge ground bundle** — the `hBb`-free store-dynamics inputs per confirmed
edge `a ← c` at honest endpoint `(w, m)`, over the certificate window `[lo, σ]` at the
confirming anchor `(vc, nc)`. Mirrors `ShellCompose.ForkEdgeEngineInputs` with the `INVstar`
base and **no** `hBb`: the endpoint enemy is the store-independent `Bval(lo, σ)`, transported
by the honest legs only. -/
structure ForkEdgeGroundInputs (E : Execution Root) (w : ValidatorIndex) (m : ℕ)
    (b h c : Root) (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot) : Prop where
  /-- forward `SupportsDesc` transport `(vc, nc) → (w, m)` at window end σ. -/
  hSt : ∀ i, E.SupportsDesc cfg ext vc nc b σ i → E.SupportsDesc cfg ext w m b σ i
  /-- forward `AncestorOrVoteless` transport `(vc, nc) → (w, m)` at window end σ. -/
  hAt : ∀ i, E.AncestorOrVoteless cfg ext vc nc b σ i → E.AncestorOrVoteless cfg ext w m b σ i
  /-- `INVstar` at the confirming anchor over `[lo, σ]` (boost = the endpoint proposer score);
      the `hBb`-free base — the `Bval` enemy is store-independent. -/
  hinv : E.INVstar cfg ext vc nc b lo es σ (get_proposer_score cfg (E.store cfg ext w m))
  /-- the fork-choice child membership of `c` under `h` at the endpoint. -/
  hchild : ForkChoiceNode.mk c ∈ get_node_children (E.store cfg ext w m)
    (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h)
  /-- the recorded `b`-side lower bound: `c`'s attestation score dominates `Sval(σ)`. -/
  hbside : E.Sval cfg ext w m b lo σ ≤ get_attestation_score cfg (E.store cfg ext w m)
    (get_node_for_root c)
    ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint)
  /-- the recorded `Bval` sibling upper bound: every competing child scores `≤ Xval + Bval`. -/
  hsib : ∀ c' : Root, ForkChoiceNode.mk c' ∈ get_node_children (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
    c' ≠ c →
    get_attestation_score cfg (E.store cfg ext w m) (get_node_for_root c')
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint)
      ≤ E.Xval cfg ext w m b lo σ + E.Bval lo σ

/-! ## Section 3 — the ground head-safety engine and the per-block supply

The path above `EngineInv`/`SafeFrom` is engine-agnostic: `spec_head_safety_engine_ground`
mirrors `HeadSafetyEngine.spec_head_safety_engine` but folds the `DescendStep` chain directly
through `Endpoint.head_descends_of_ledger` (no `LedgerStepV2`, no `INV2`, no `hBb`), and
`L4Fold.safeFrom_of_engineInv` collapses the cutoffs. `LedgerChainInputGround` is the ground
certificate functional; `ForkEdgeGroundSupply` the per-edge bundle supply;
`forkEdgeSupply_of_ground` lifts the supply plus the structural confirmed chain
(`ResidualMechanicalII.DynamicsChainStruct`) into the functional. -/

omit [Inhabited Root] in
/-- **Chain members are ancestors of the chain's last block.** Along a parent-linked
chain of known roots ending at `b` (`getLast? = some b`), every member `c` is an ancestor of `b`
(`is_ancestor store b c`): the suffix from `c` to `b` composes single parent steps
(`is_ancestor_of_parent`) by transitivity (`is_ancestor_trans`, walk domains from the blanket
`hwalk`). This lets the ground per-edge supply be
demanded **only** for the `b`-chain edges the `DescendStep` chain walks — the `c` of each
`ForkEdgeGroundInputs` is always a `b`-ancestor (a winning child), so the off-`b`-chain losing
siblings appear only as `hsib` recorded-bound objects, never as harm-carrying subjects. -/
theorem mem_isAncestor_of_parentChain {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r)
    {b : Root} (hb : b ∈ store.block_roots) :
    ∀ {L : List Root}, List.IsChain (fun a c => (store.blocks c).parent_root = a) L →
      (∀ x ∈ L, x ∈ store.block_roots) → L.getLast? = some b →
      ∀ c ∈ L, is_ancestor store (get_node_for_root b) (get_node_for_root c) = true := by
  intro L hchain
  induction hchain with
  | nil => intro _ hlast; simp at hlast
  | singleton a =>
    intro _ hlast c hc
    rw [List.getLast?_singleton, Option.some_inj] at hlast
    rw [List.mem_singleton] at hc
    subst hc; subst hlast
    exact is_ancestor_refl store _
  | @cons_cons a d rest hr _ ih =>
    intro hmem hlast c hc
    rw [List.getLast?_cons_cons] at hlast
    have hmem' : ∀ x ∈ d :: rest, x ∈ store.block_roots :=
      fun x hx => hmem x (List.mem_cons_of_mem _ hx)
    have hdmem : d ∈ store.block_roots := hmem' d (by simp)
    have hamem : a ∈ store.block_roots := hmem a (by simp)
    have ihd := ih hmem' hlast
    rcases List.mem_cons.mp hc with rfl | hc'
    · have hbd := ihd d (by simp)
      have hda := is_ancestor_of_parent hwf hdmem hamem hr
      exact is_ancestor_trans hwf (hwalk _ hamem b hb) (hwalk _ hamem d hdmem) hbd hda
    · exact ihd c hc'

/-! ## Section 4 — the `hBb`-free facade

`SoundResidualsGround` is `AnchorFacade.SoundResiduals` with the engine leg `advance_cert`
(`LedgerChainInputCert`, v2/`hBb`) replaced by the structural chain (`dynamics_struct`) plus the
ground per-block supply (`fork_edges_ground`, `ForkEdgeGroundSupply`, `hBb`-free). It reaches
`Spec_Safety` through the engine-agnostic `L4Fold` skeleton. `EngineGroundResiduals` mirrors
`Definitive.EngineOpenResiduals` with `fork_edges_engine` (`ForkEdgeEngineSupply`, `hBb`)
replaced by `fork_edges_ground`. The two safety headlines that used to close this track —
`Spec_Safety_of_ground` and its splitter `soundResidualsGround_of_split` — are deleted with the
legacy `SpecAssumptions` observed-anchor cone (P-6); see the notes where they stood. -/

/-! ### Deleted: `soundResidualsGround_of_split`

The `hBb`-free mirror of `shellResiduals_of_strongPrefixSafetyInputs` stood here. It rebuilt
`SoundResidualsGround` from `SameSlotFinalizedRootKnown` + `EngineGroundResiduals`, wiring the
observed-anchor leg through `ExportWiring.observedFilterResiduals_of_interface` and carrying
the ahead-regime head-tracking premise `htracks` explicitly. Nothing ever
produced that premise; it and the whole legacy `SpecAssumptions` observed-anchor cone are
deleted (P-6). See `docs/p6-justified-descends-derivation.md` §8. -/

end Execution

/-! ## Section 5 — the `hBb`-free safety headlines -/

/-! ### Deleted: `Spec_Safety_of_ground`

The `hBb`-free mirror of `Definitive.Spec_Safety_of_sameSlot_and_engine` stood here:
`Spec_Safety` from `SameSlotFinalizedRootKnown` + `EngineGroundResiduals`, composing
`soundResidualsGround_of_split` with `spec_safety_soundResidualsGround`. It carried the
unproduced ahead-regime head-tracking premise `htracks` and is deleted with the
rest of the legacy `SpecAssumptions` observed-anchor cone (P-6). See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec

end
