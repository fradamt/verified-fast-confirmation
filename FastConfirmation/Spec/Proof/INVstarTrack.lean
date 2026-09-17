import FastConfirmation.Spec.Proof.GroundBeta
import FastConfirmation.Spec.Proof.Definitive

/-!
# Spec / Proof / INVstarTrack: the `hBb`-free per-edge pipeline

The **ground-truth-β / INV\*** route in
`FastConfirmation/Spec/Proof/GroundBeta.lean` uses
the endpoint enemy is the **store-independent** window weight `Bval` (`span_fraction`
budgeted directly at the endpoint), so the per-fork descent transports with the
**honest legs only** and needs **no** `hBb`.

This module re-derives the whole `fork_edges` per-edge pipeline on that track,
mirroring the v2 (`INV2`/`Enemy`, `hBb`-carrying) shapes but with the `INVstar`
base, so the facade engine bundle **drops the `hBb` field**:

v2 track (`hBb`-carrying) ⟶ this module (`hBb`-free):

* `ForkEdgeEngineInputs` ⟶ `ForkEdgeGroundInputs`;
* `LedgerStepV2` per fork ⟶ `descendStep_of_forkEdgeGroundInputs` (a `DescendStep`);
* `spec_head_safety_engine` ⟶ `spec_head_safety_engine_ground`;
* `ForkEdgeEngineSupply`/`ForkEdgeSupply` ⟶ `ForkEdgeGroundSupply`/`LedgerChainInputGround`;
* `EngineOpenResiduals` (`fork_edges_engine`) ⟶ `EngineGroundResiduals` (`fork_edges_ground`).

The endpoint certificate is: `Ledger.INVstar` at the confirming anchor `(vc, nc)`
(the v1 invariant over the store-independent `Bval`) + `GroundBeta`'s honest-legs
strip transport (`bval_endpoint_strip_sigma` — the σ-general
`bval_endpoint_strip_of_transport`, **no** `hBb`) + `GroundBeta.ledger_descendStep`
(the per-fork `DescendStep`). The path above `EngineInv`/`SafeFrom` is
engine-agnostic, so `Endpoint.head_descends_of_ledger` folds the `DescendStep`
chain and `L4Fold.safeFrom_of_engineInv` collapses it — no v2-specific machinery.

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

/-- **The σ-general endpoint strip, `hBb`-free.** `GroundBeta.bval_endpoint_strip_of_transport`
at an arbitrary window end σ: from `INVstar` at the confirming anchor `(v₀, n₀)` over
`[lo, σ]` and the honest descent transports `hSt`/`hAt` at σ, the ground-truth-`Bval`
endpoint inequality `Xval + Bval + boost + 1 ≤ Sval` holds at `(w, m)` over `[lo, σ]`.
`Bval(lo, σ)` is store-independent (the identical term at both anchors), so only the
honest legs transport (`StepDischargeII.classes_base_transport`) — **no** enemy
movement `hBb`. `INVstar_endpoint` strips the invariant at the confirming anchor;
`bval_strip_transport` carries it across nodes. -/
theorem bval_endpoint_strip_sigma (v₀ w : ValidatorIndex) (n₀ m : ℕ) (b' : Root)
    (lo es σ : Slot) (boost : ℕ)
    (hSt : ∀ i, E.SupportsDesc cfg ext v₀ n₀ b' σ i → E.SupportsDesc cfg ext w m b' σ i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext v₀ n₀ b' σ i →
      E.AncestorOrVoteless cfg ext w m b' σ i)
    (hinv : E.INVstar cfg ext v₀ n₀ b' lo es σ boost) :
    E.Xval cfg ext w m b' lo σ + E.Bval lo σ + boost + 1
      ≤ E.Sval cfg ext w m b' lo σ := by
  obtain ⟨hS, hX⟩ := E.classes_base_transport cfg ext v₀ w n₀ m b' lo σ hSt hAt
  exact E.bval_strip_transport cfg ext v₀ w n₀ m b' lo σ boost
    (E.INVstar_endpoint cfg ext v₀ n₀ b' lo es σ boost hinv) hS hX

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

/-- **`ForkEdgeGroundInputs ⟹ DescendStep`, `hBb`-free.** The per-fork descent step at
the endpoint `(w, m)`: `bval_endpoint_strip_sigma` supplies the ground-truth-`Bval` endpoint
inequality (`hledger`, honest legs only — **no** `hBb`), and `GroundBeta.ledger_descendStep`
packages it with the `b`-side lower bound `hbside` and the `Bval` sibling upper bound `hsib`
into an `EngineStore.DescendStep`. The `hBb`-free drop-in for the v2
`ChainInput.ledgerCertInput_of_endpoint` → `LedgerStepV2` per-edge step. -/
theorem descendStep_of_forkEdgeGroundInputs {w : ValidatorIndex} {m : ℕ} {b h c : Root}
    {vc : ValidatorIndex} {nc : ℕ} {lo es σ : Slot}
    (hin : E.ForkEdgeGroundInputs cfg ext w m b h c vc nc lo es σ) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h c :=
  ledger_descendStep cfg ext hin.hchild hin.hbside
    (E.bval_endpoint_strip_sigma cfg ext vc w nc m b lo es σ
      (get_proposer_score cfg (E.store cfg ext w m)) hin.hSt hin.hAt hin.hinv) hin.hsib

/-! ## Section 3 — the ground head-safety engine and the per-block supply

The path above `EngineInv`/`SafeFrom` is engine-agnostic: `spec_head_safety_engine_ground`
mirrors `HeadSafetyEngine.spec_head_safety_engine` but folds the `DescendStep` chain directly
through `Endpoint.head_descends_of_ledger` (no `LedgerStepV2`, no `INV2`, no `hBb`), and
`L4Fold.safeFrom_of_engineInv` collapses the cutoffs. `LedgerChainInputGround` is the ground
certificate functional; `ForkEdgeGroundSupply` the per-edge bundle supply;
`forkEdgeSupply_of_ground` lifts the supply plus the structural confirmed chain
(`ResidualMechanicalII.DynamicsChainStruct`) into the functional. -/

/-- **The ground certificate-chain functional.** `HeadSafetyEngine.LedgerChainInput`
with the `LedgerStepV2` chain replaced by a plain `EngineStore.DescendStep` chain: at every
honest endpoint `(w, m)` past `n₀`, given head safety at strictly earlier slots, the confirmed
chain from the justified root to `b` presents as a `List.IsChain (DescendStep …)`, with the
fork-choice domain conditions. `hBb`-free — each edge is a ground-truth-`Bval` descent step. -/
def LedgerChainInputGround (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.WithinHorizon cfg m →
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
      List.IsChain (DescendStep cfg (E.store cfg ext w m)
          (get_filtered_block_tree cfg (E.store cfg ext w m)))
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **The ground head-safety engine.** The `hBb`-free mirror of
`HeadSafetyEngine.spec_head_safety_engine`: strong induction on the cutoff slot `k`; at each
honest `(w, m)` the confirmed `DescendStep` chain (from `LedgerChainInputGround`, fed the
induction hypothesis) folds to head descent by `Endpoint.head_descends_of_ledger`. Identical
control flow to the v2 shell, with the ground-truth-`Bval` `DescendStep` chain in place of the
`LedgerStepV2` chain. -/
theorem spec_head_safety_engine_ground {b : Root} {n₀ : ℕ}
    (hcert : E.LedgerChainInputGround cfg ext b n₀) :
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
      exact head_descends_of_ledger cfg hwf hsub hb hnd hchain hlast

/-- **`SafeFrom` from the ground certificate functional.** The engine composition
collapsed over cutoffs: `spec_head_safety_engine_ground` produces `EngineInv` at every cutoff,
`L4Fold.safeFrom_of_engineInv` folds `∀ k` in. The `hBb`-free analog of
`L4Fold.safeFrom_of_certificates`. -/
theorem safeFrom_of_ground_certificates {b : Root} {n₀ : ℕ}
    (hcert : E.LedgerChainInputGround cfg ext b n₀) :
    E.SafeFrom cfg ext b n₀ :=
  E.safeFrom_of_engineInv cfg ext (E.spec_head_safety_engine_ground cfg ext hcert)

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

/-- **The per-block ground supply.** `ShellCompose.ForkEdgeEngineSupply`'s
shape with the per-edge `ForkEdgeEngineInputs` replaced by the `hBb`-free `ForkEdgeGroundInputs`:
under the shell's head-safety IH, every parent edge of known blocks **whose child `c` is on `b`'s
chain** (`is_ancestor store b c`) carries a `ForkEdgeGroundInputs` (certificate coordinates
existentially supplied per edge). The `b`-chain scope demands the per-edge
bundle only for the edges the `DescendStep` chain from `jc` to `b` actually walks, so a losing
sibling `c` (which breaks `hbside`/`hsib`) is never a subject — it appears only inside `hsib`. -/
def ForkEdgeGroundSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root b) (get_node_for_root c) = true →
        ∃ (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot),
          E.ForkEdgeGroundInputs cfg ext w m b a c vc nc lo es σ

/-- **`ForkEdgeGroundSupply ⟹ LedgerChainInputGround`** — the ground supply lift, the
`hBb`-free analog of `ShellCompose.forkEdgeSupply_of_engineSupply` composed with the shell
instantiation. The structural confirmed chain (`DynamicsChainStruct`) supplies the parent-link
list; each edge's `ForkEdgeGroundInputs` lifts to a `DescendStep`
(`descendStep_of_forkEdgeGroundInputs`) edge-wise (`isChain_imp_of_mem`, member-scoped so the
per-edge bundle only ever fires on chain elements). The domain facts pass through unchanged. -/
theorem forkEdgeSupply_of_ground {b : Root} {n₀ : ℕ}
    (hwalkK : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hstruct : E.DynamicsChainStruct cfg ext b n₀)
    (hedge : E.ForkEdgeGroundSupply cfg ext b n₀) :
    E.LedgerChainInputGround cfg ext b n₀ := by
  intro w hw m hm hHm hIH
  obtain ⟨ds, hpsl, hfilt, hb, hnd, hmem, hchain, hlast⟩ :=
    hstruct w hw m hm hHm hIH
  have hlast? : ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast]
  refine ⟨ds, hpsl, hfilt, hb, hnd, ?_, hlast⟩
  refine isChain_imp_of_mem hchain ?_
  intro a ha c hc hlink
  have hscope := mem_isAncestor_of_parentChain hpsl (hwalkK w hw m) hb hchain hmem hlast? c hc
  obtain ⟨vc, nc, lo, es, σ, hin⟩ :=
    hedge w hw m hm hHm hIH a c (hmem a ha) (hmem c hc) hlink hscope
  exact E.descendStep_of_forkEdgeGroundInputs cfg ext hin

/-! ## Section 4 — the `hBb`-free facade

`SoundResidualsGround` is `AnchorFacade.SoundResiduals` with the engine leg `advance_cert`
(`LedgerChainInputCert`, v2/`hBb`) replaced by the structural chain (`dynamics_struct`) plus the
ground per-block supply (`fork_edges_ground`, `ForkEdgeGroundSupply`, `hBb`-free). It reaches
`Spec_Safety` through the engine-agnostic `L4Fold` skeleton. `EngineGroundResiduals` mirrors
`Definitive.EngineOpenResiduals` with `fork_edges_engine` (`ForkEdgeEngineSupply`, `hBb`)
replaced by `fork_edges_ground`. The two safety headlines that used to close this track —
`Spec_Safety_of_ground` and its splitter `soundResidualsGround_of_split` — are deleted with the
legacy `SpecAssumptions` observed-anchor cone (P-6); see the notes where they stood. -/

/-- **The ground sound-residual bundle.** `AnchorFacade.SoundResiduals` with the engine
leg instantiated on the ground track: the two E5 reset anchors (`genesis_dom`/`finalized_dom`)
and the sound observed-anchor filter route (`observed_filter`) are verbatim; the engine leg is
the structural confirmed chain (`dynamics_struct`) plus the per-block ground supply
(`fork_edges_ground`, `ForkEdgeGroundSupply` — **no** `hBb`). -/
structure SoundResidualsGround (E : Execution Root) : Prop where
  /-- E5: the genesis finalized reset anchor is known and justified-dominated everywhere. -/
  genesis_dom : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext v 0).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true
  /-- E5: each update's finalized reset anchor is known and justified-dominated past `n+1`. -/
  finalized_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true
  /-- E5 (sound filter route): the observed-anchor filter residuals. -/
  observed_filter : E.ObservedFilterResiduals cfg ext
  /-- `[E-struct]`: the structural confirmed chain per confirmed block. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E-edges]`: the per-block `hBb`-free ground supply per confirmed block. -/
  fork_edges_ground : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeGroundSupply cfg ext b (n + 1)

/-- **`L4Residual` from the ground sound bundle.** The `hBb`-free analog of
`AnchorFacade.l4Residual_of_soundResiduals`: `StoreDomainK` is Layer-0 discharged
(`store_domainK`); the finalized/genesis anchors go through `safeFrom_of_justified_dom_K`, the
observed anchor through the sound filter route; the advance leg is the **ground** engine —
`forkEdgeSupply_of_ground` builds the `DescendStep` chain, `safeFrom_of_ground_certificates`
folds it. No `hBb`, no `LedgerStepV2`. -/
theorem l4Residual_of_soundResidualsGround (hSA : SpecAssumptions cfg ext E)
    (h : E.SoundResidualsGround cfg ext) : E.L4Residual cfg ext := by
  obtain ⟨hgen, hwf, _, _, _, hec, _, _, hji⟩ := hSA
  have hdomK := E.store_domainK cfg ext hwf hec hgen hji
  exact
    { genesis_safe := fun v hv =>
        E.safeFrom_of_justified_dom_K cfg ext hdomK
          (fun w hw m _ hH => h.genesis_dom v hv w hw m hH)
      finalized_safe := fun v hv n => by
        rw [E.fcrStep_store]
        exact E.safeFrom_of_justified_dom_K cfg ext hdomK (h.finalized_dom v hv n)
      observed_safe := fun v hv n =>
        E.safeFrom_observed_of_filter_K cfg ext hji hdomK
          h.observed_filter.prev_greatest_justifiedIn h.observed_filter.observed_known
          h.observed_filter.observed_head_ahead v hv n
      advance_safe := fun v hv n b hconf =>
        E.safeFrom_of_ground_certificates cfg ext
          (E.forkEdgeSupply_of_ground cfg ext
            (fun w _ m => E.store_walkKnownK cfg ext hwf hec hgen w m)
            (h.dynamics_struct v hv n b hconf)
            (h.fork_edges_ground v hv n b hconf)) }

/-- **The engine-open ground residuals** — the `hBb`-free mirror of
`Definitive.EngineOpenResiduals`: the structural confirmed chain (`dynamics_struct`) and the
transparent per-block ground supply (`fork_edges_ground`, `ForkEdgeGroundSupply`), with the
`hBb` field of `ForkEdgeEngineSupply`/`ForkEdgeEngineInputs` **dropped** — the enemy is the
store-independent ground-truth `Bval`, transported by honest legs only. -/
structure EngineGroundResiduals (E : Execution Root) : Prop where
  /-- `[E-struct]` — verbatim `EngineOpenResiduals.dynamics_struct`. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E-edges]` — the per-block ground supply (the `hBb`-free reduction of `fork_edges`). -/
  fork_edges_ground : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeGroundSupply cfg ext b (n + 1)

/-! ### Deleted: `soundResidualsGround_of_split`

The `hBb`-free mirror of `shellResiduals_of_strongPrefixSafetyInputs` stood here. It rebuilt
`SoundResidualsGround` from `SameSlotFinalizedRootKnown` + `EngineGroundResiduals`, wiring the
observed-anchor leg through `ExportWiring.observedFilterResiduals_of_interface` and carrying
the ahead-regime head-tracking premise `htracks` explicitly. Nothing ever
produced that premise; it and the whole legacy `SpecAssumptions` observed-anchor cone are
deleted (P-6). See `docs/p6-justified-descends-derivation.md` §8. -/

end Execution

/-! ## Section 5 — the `hBb`-free safety headlines -/

/-- **`Spec_Safety` from the ground sound bundle.** FCR safety from a proof that every
execution's `SpecAssumptions` supplies `SoundResidualsGround` — the E5 reset anchors, the sound
observed-anchor filter route, the structural confirmed chain, and the `hBb`-free per-block
ground supply. Composes `l4Residual_of_soundResidualsGround` with `L4Fold.spec_safety_of_residual`.
The `hBb`-free analog of `AnchorFacade.spec_safety_sound_residuals`. -/
theorem spec_safety_soundResidualsGround
    (h : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.SoundResidualsGround cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_residual cfg ext
    (fun E hSA => E.l4Residual_of_soundResidualsGround cfg ext hSA (h E hSA))

/-! ### Deleted: `Spec_Safety_of_ground`

The `hBb`-free mirror of `Definitive.Spec_Safety_of_sameSlot_and_engine` stood here:
`Spec_Safety` from `SameSlotFinalizedRootKnown` + `EngineGroundResiduals`, composing
`soundResidualsGround_of_split` with `spec_safety_soundResidualsGround`. It carried the
unproduced ahead-regime head-tracking premise `htracks` and is deleted with the
rest of the legacy `SpecAssumptions` observed-anchor cone (P-6). See
`docs/p6-justified-descends-derivation.md` §8. -/

end FastConfirmation.Spec
