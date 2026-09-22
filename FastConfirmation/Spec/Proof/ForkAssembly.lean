module
public import FastConfirmation.Spec.Proof.InterfaceRewire
public import FastConfirmation.Spec.Proof.DynamicsClosure

@[expose] public section

/-!
# Spec / Proof / ForkAssembly: the `dynamics_edges` per-fork assembly

`InterfaceRewire.spec_safety_of_final` reduces FCR safety to
the four-field `Execution.FinalResiduals` bundle
`{anchor_guard, observed_dom, dynamics_struct, dynamics_edges}`. This module
discharges the last of those, `dynamics_edges` — the per-fork engine content
supplied as `Execution.DynamicsEdgeSupply` — by **composing the already-proven
family reductions** into one `Execution.DynamicsResidual` per parent edge, and
restates the conditional result over the resulting explicit input bundle.

## The composition (pure interface threading — no new mathematics)

`ResidualMechanicalII.DynamicsEdgeSupply cfg ext b (n+1)` asks, at every honest
endpoint `(w, m)` past `n+1` (under the shell's head-safety IH — supplied inside
`HeadSafetyEngine`'s strong induction) and every real parent edge `a ← c` of known
blocks, for a `ResidualDischarge.DynamicsResidual cfg ext w m a c`. That residual is
exactly the existential form of `ChainInput.ledgerCertInput_of_endpoint`'s thirteen
family hypotheses. `DynamicsClosure` (families 1–6) reduces each family to its
genuine store-dynamics input:

* `hSt`/`hAt` (family 5) ⟵ `SupportsDesc_transport_of_anc` /
  `AncestorOrVoteless_transport_of_anc` — one per-root `is_ancestor` transport
  `(vc, nc) → (w, m)` (block relay + `WalkKnown`, the `EngineTransport` residue);
* `hpre` (families 2–3) ⟵ `INV2_pre_step_of_deltas` per pre-`T1` slot — the
  class-migration deltas `hs'`/`hx'` and the `ρ = 0` partition `hρ`
  (`votes_head` + engine IH + delivery + same-epoch assignment bookkeeping);
* `hsat` (family 4) ⟵ `hsat_functional` — the saturated honest-majority `hmaj`
  (`committee_coverage` + `votes_head` + IH);
* `hSmem` (family 6) ⟵ `hSmem_of_recorded` — the per-member recorded-`c`-support
  `hrec` (`Delivery`/ubiquity + the epoch-cased root identification);
* `hbase` (family 1) is carried verbatim as the confirming-anchor `INV2(es)`; it
  reduces one step further via `DynamicsClosure.INV2_base_of_confirmed` (the
  `is_one_confirmed` premise is exactly `dynamics_edges`' hypothesis, so only the
  `Arms.arms_of_confirmed` accounting bridges remain explicit in
  `Arms.lean`, kept as a documented sub-residual rather than inlined here);
* `hBb`/`hval`/`hboost`/`hchild`/`hHon`/`hByz` (the `recorded-base reduction` recorded base-enemy movement,
  registry constancy, boost freeze, fork-choice child membership, and sibling
  confinements) are carried verbatim.

`ForkEdgeInput` bundles precisely those reduced inputs per edge;
`dynamicsResidual_of_forkEdgeInput` composes the reducers into a `DynamicsResidual`.
`ForkEdgeSupply` lifts it to the endpoint/edge quantification of `DynamicsEdgeSupply`.

## Edge-reduced input bundle

`FinalResidualsER` is `FinalResiduals` with `dynamics_edges` replaced by the
edge-reduced `fork_edges` (a `ForkEdgeSupply` per confirmed block). `spec_safety_final_residuals`
is FCR safety from a proof that every execution's `SpecAssumptions` supplies
`FinalResidualsER`, the explicit obligation set consumed by this facade:
the anchor-min guard `[A]`, the E5/E6 observed dominance `[D]`, the structural
confirmed chain `[E-struct]`, and the per-edge store-dynamics inputs `[E-edges]`
(`ForkEdgeInput`: the transports, migration deltas, saturated majority,
recorded-support, and sibling confinements enumerated above).

The epoch-crossing prev-epoch tax-arm is **not** an obligation here: `DynamicsResidual`
is the same-epoch (current-epoch loop) `INV2` certificate; the crossing member-arm
rides `ResidualDischarge.ledgerStepV2_of_crossing_member` at the L4/`advance_cert`
level, and the crossing tax-arm is supplied separately by `Crossing.lean`,
outside `dynamics_edges`.

The genuine store-dynamics facts are
carried as the named bundle `ForkEdgeInput` in the shapes the reducers consume.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the per-edge reduced input bundle -/

/-- **The per-edge store-dynamics input** (`ForkAssembly`). All of `DynamicsResidual`'s
family hypotheses at the fork `(h, c)` with confirmed block `b` at the endpoint
`(w, m)`, existentially over the certificate `(vc, nc, lo, es, σ, boost)`, but with
families 2–6 **reduced** to their genuine store-dynamics inputs (transports, deltas,
saturated majority, recorded-support) via `DynamicsClosure`. `hbase`, `hBb`,
`hval`, `hboost`, `hchild`, `hHon`, `hByz` are carried verbatim from
`DynamicsResidual`. -/
def ForkEdgeInput (E : Execution Root) (w : ValidatorIndex) (m : ℕ) (b h c : Root) : Prop :=
  ∃ (vc : ValidatorIndex) (nc : ℕ) (lo es σ : Slot) (boost : ℕ),
    es ≤ σ ∧
    E.SlotWithinHorizon cfg lo ∧
    E.SlotWithinHorizon cfg σ ∧
    E.INV2 cfg ext vc nc b lo es es boost ∧
    (∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root r) (get_node_for_root b) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root r) (get_node_for_root b) = true) ∧
    (∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root b) (get_node_for_root r) = true →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r) = true) ∧
    E.BbadVal cfg ext w m b lo es ≤ E.BbadVal cfg ext vc nc b lo es ∧
    lo ≤ es + 1 ∧
    (∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      ∃ ξ α : ℕ,
        (E.Sval cfg ext w m b lo σ' + ξ + α +
            E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
              (fun i => i ∈ E.honest))
          ≤ E.Sval cfg ext w m b lo (σ' + 1)) ∧
        (E.Xval cfg ext w m b lo (σ' + 1) + ξ ≤ E.Xval cfg ext w m b lo σ') ∧
        (E.weight ((E.span_committee (σ' + 1) (σ' + 1)).filter (fun i => i ∈ E.honest)) ≤
          E.weight (E.Unrec cfg ext w m b lo es σ' \ E.Unrec cfg ext w m b lo es (σ' + 1))
            + ξ + α +
            E.weight ((E.span_committee lo (σ' + 1) \ E.span_committee lo σ').filter
              (fun i => i ∈ E.honest)))) ∧
    (∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b lo σ'
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
              / (100 - cfg.confirmation_byzantine_threshold)
          + boost + 1 ≤ E.Sval cfg ext w m b lo σ') ∧
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry ∧
    get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon ∧
    boost = get_proposer_score cfg (E.store cfg ext w m) ∧
    ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))) ∧
    PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)) ∧
    (∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo σ) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ)

/-- **`ForkEdgeInput ⟹ DynamicsResidual`.** The per-fork composition: unpack the
reduced bundle and apply the `DynamicsClosure` family reducers — `hSt`/`hAt` from the
transports, `hpre` from the per-slot deltas, `hsat` from the saturated majority,
`hSmem` from the recorded-support — with `hbase`/`hBb`/`hval`/`hboost`/`hchild`/
`hHon`/`hByz` carried through. This is the whole of the per-edge engine, packaged. -/
theorem dynamicsResidual_of_forkEdgeInput
    (hbb : ByzantineBound cfg E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {b h c : Root}
    (hin : E.ForkEdgeInput cfg ext w m b h c)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    E.DynamicsResidual cfg ext w m h c := by
  obtain ⟨vc, nc, lo, es, σ, boost, hσ, hloH, hσH, hbase, htS, htA, hBb, hlo,
    hdeltas, hmaj, hval, hbsH, hboost, hchild, hstatus, hrec, hHon, hByz⟩ := hin
  refine ⟨vc, nc, b, lo, es, σ, boost, hσ, hloH, hσH, ?_, ?_, hBb, hbase, ?_, ?_,
    hval, hboost, hchild, hstatus, ?_, hHon, hByz⟩
  · exact E.SupportsDesc_transport_of_anc cfg ext vc w nc m b es htS
  · exact E.AncestorOrVoteless_transport_of_anc cfg ext vc w nc m b es htA
  · intro σ' h1 hσ'H hσ1H h2 hinv
    obtain ⟨ξ, α, hs', hx', hρ⟩ := hdeltas σ' h1 hσ'H hσ1H h2
    exact E.INV2_pre_step_of_deltas cfg ext hbb w m b lo es σ' boost ξ α
      hloH hσ'H hσ1H hlo h1 hs' hx' hρ hinv
  · exact E.hsat_functional cfg ext hbb w m b lo es boost hloH hlo hmaj
  · exact E.hSmem_of_recorded cfg ext (hw := hw) (hmH := hmH) hhb hec hsv hgen w m w m b c lo σ
      hval hbsH hσH hrec

/-! ## Section 2 — the endpoint/edge quantification: `DynamicsEdgeSupply` -/

/-- **The per-edge reduced supply.** `DynamicsEdgeSupply`'s shape with the per-edge
`DynamicsResidual` replaced by the reduced `ForkEdgeInput`: at every honest endpoint
`(w, m)` past `n₀`, given the shell's head-safety IH at strictly earlier slots, every
real parent edge `a ← c` of known blocks carries a `ForkEdgeInput`. This is the exact
functional the `HeadSafetyEngine` shell instantiates (its strong induction supplies
the IH), mirroring how the shell consumes `ChainInput`'s certificate families. -/
def ForkEdgeSupply (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m → E.WithinHorizon cfg m →
    (∀ w' ∈ E.honest, ∀ m' : ℕ, n₀ ≤ m' → E.slot_at cfg m' < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
        (get_node_for_root b) = true) →
    ∀ a c : Root, a ∈ (E.store cfg ext w m).block_roots →
      c ∈ (E.store cfg ext w m).block_roots →
      ((E.store cfg ext w m).blocks c).parent_root = a →
        E.ForkEdgeInput cfg ext w m b a c

/-- **`ForkEdgeSupply ⟹ DynamicsEdgeSupply`.** The endpoint/edge quantification and
the head-safety IH pass through unchanged; each edge's `ForkEdgeInput` composes to a
`DynamicsResidual` (`dynamicsResidual_of_forkEdgeInput`). The global coherence records
`hbb`/`hhb`/`hec`/`hsv`/`hgen` come from `SpecAssumptions`. -/
theorem dynamicsEdgeSupply_of_forkEdgeSupply
    (hbb : ByzantineBound cfg E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {b : Root} {n₀ : ℕ}
    (hsupply : E.ForkEdgeSupply cfg ext b n₀) :
    E.DynamicsEdgeSupply cfg ext b n₀ := by
  intro w hw m hm hHm hIH a c ha hc hlink
  exact E.dynamicsResidual_of_forkEdgeInput cfg ext (hw := hw) (hmH := hHm) hbb hhb hec hsv hgen
    (hsupply w hw m hm hHm hIH a c ha hc hlink)

/-! ## Section 3 — the edge-reduced input bundle

`FinalResidualsER` is `InterfaceRewire.FinalResiduals` with `dynamics_edges` (the raw
per-edge `DynamicsResidual` supply) replaced by `fork_edges` — the edge-reduced
`ForkEdgeSupply`. The other three fields are carried verbatim. -/

/-- **The edge-reduced input bundle** (`ForkAssembly`). `FinalResiduals` with the
per-edge engine field `dynamics_edges` replaced by the reduced `fork_edges`
(a `ForkEdgeSupply` per confirmed block — the transports, migration deltas, saturated
majority, recorded-support, and sibling confinements of `ForkEdgeInput`). The
anchor-min guard `[A]`, the E5/E6 observed dominance `[D]`, and the structural
confirmed chain `[E-struct]` are the same three residuals `InterfaceRewire` leaves. -/
structure FinalResidualsER (E : Execution Root) : Prop where
  /-- `[A]`: the anchor-min guard (verbatim `FinalResiduals.anchor_guard`). -/
  anchor_guard : ∀ (P : Root),
    (∀ w ∈ E.honest, ∀ m : ℕ, ParentInRootsOr P (E.store cfg ext w m)) →
    ∀ w ∈ E.honest, ∀ m : ℕ, ∀ sl : Slot,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root = P →
          ((E.store cfg ext w m).blocks r).slot ≤ sl
  /-- `[D]`: the E5/E6 observed-justified dominance (verbatim
      `FinalResiduals.observed_dom`). -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- `[E-struct]`: the structural confirmed-chain residual (verbatim
      `FinalResiduals.dynamics_struct`). -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- `[E-edges]`: the per-edge store-dynamics supply (the `ForkAssembly` reduction of
      `dynamics_edges` — `ForkEdgeSupply` per confirmed block). -/
  fork_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeSupply cfg ext b (n + 1)

/-- **`FinalResiduals` from `FinalResidualsER` + `SpecAssumptions`.** The three
carried fields pass through; `dynamics_edges` is rebuilt from `fork_edges` via
`dynamicsEdgeSupply_of_forkEdgeSupply`, drawing the coherence records from
`SpecAssumptions`. -/
theorem finalResiduals_of_ER (hSA : SpecAssumptions cfg ext E)
    (h : E.FinalResidualsER cfg ext) : E.FinalResiduals cfg ext := by
  obtain ⟨⟨ast, ablk, heq, _, _⟩, _hwf, _hdiv, hhb, _hsync, hec, hsv, hbb, _hji⟩ := hSA
  exact
    { anchor_guard := h.anchor_guard
      observed_dom := h.observed_dom
      dynamics_struct := h.dynamics_struct
      dynamics_edges := fun v hv n b hconf =>
        E.dynamicsEdgeSupply_of_forkEdgeSupply cfg ext hbb hhb hec hsv ⟨ast, ablk, heq⟩
          (h.fork_edges v hv n b hconf) }

end Execution

/-! ## Section 4 — the shrunken safety headline (`ForkAssembly`) -/

/-- **`Spec_Safety` from the edge-reduced final bundle.** Composing
`finalResiduals_of_ER` with `InterfaceRewire.spec_safety_of_final`: FCR safety follows
from a proof that every execution's `SpecAssumptions` supplies `FinalResidualsER`.
That explicit input bundle contains:

* `anchor_guard` `[A]` — the Layer-0 anchor-min guard (one `WellFormedExecution`-family
  fact; every known block naming the dangling anchor-parent has minimal slot);
* `observed_dom` `[D]` — the E5/E6 observed-justified dominance (not derivable from the
  justification-interface `justified_ancestry` export alone: it needs observed-anchor root knownness and
  the `obs.epoch ≤ jc.epoch` bound the residual does not carry — `InterfaceRewire`);
* `dynamics_struct` `[E-struct]` — the structural `get_ancestor_roots` confirmed chain
  (fork-choice-mechanical, `ResidualMechanicalII.dynamicsChainStruct_of_facts`);
* `fork_edges` `[E-edges]` — the per-edge `ForkEdgeInput` store-dynamics inputs: the
  `is_ancestor` transports `(vc, nc) → (w, m)` (`hSt`/`hAt`), the recorded base-enemy
  movement (`hBb`, `recorded-base reduction`), the confirming-anchor base `INV2(es)` (`hbase`; further reducible via
  `INV2_base_of_confirmed` to the `Arms` bridges), the per-slot pre-`T1` class-migration
  deltas (`hdeltas`: `hs'`/`hx'`/`hρ`), the saturated honest majority (`hmaj`), the
  registry-constant source / boost freeze / child membership (`hval`/`hboost`/`hchild`),
  the recorded-`c`-support (`hrec`), and the sibling confinements (`hHon`/`hByz`).

Not on this list: the epoch-crossing previous-epoch tax-arm from
`Crossing.lean`, which lies on the `advance_cert`/L4 path, not
`dynamics_edges`. -/
theorem spec_safety_final_residuals
    (h : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.FinalResidualsER cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_final cfg ext
    (fun E hSA => E.finalResiduals_of_ER cfg ext hSA (h E hSA))

end FastConfirmation.Spec

end
