module
public import FastConfirmation.Spec.Proof.AnchorFacade
public import FastConfirmation.Spec.Proof.ResidualMechanicalII

@[expose] public section

/-!
# Spec / Proof / ShellInstantiation: constructing the engine certificate input

This module constructs `AnchorFacade.SoundResiduals.advance_cert`, a
`LedgerChainInputCert` for each confirmed block, from a structural confirmed
chain (`DynamicsChainStruct`) and a per-edge store-dynamics supply
(`ForkAssembly.ForkEdgeSupply`).

## Certificate construction

Inside `HeadSafetyEngine.spec_head_safety_engine`'s strong induction on the cutoff slot,
head safety at strictly earlier slots (the IH `hHead`) is available at every honest
endpoint `(w, m)`. Every functional in the certificate chain carries that IH as a
hypothesis, so the IH-functional facts the engine parks — the per-slot pre-`T1`
class-migration deltas (`hdeltas`: `hs'`/`hx'`/`hρ`), the post-`T1` saturated majority
(`hmaj`), and the per-`Sclass`-member recorded `c`-support (`hrec`) — are threaded through
to their producers precisely at `(w, m)`. The composition wires:

```
ForkEdgeSupply                                   -- per-edge reduced store-dynamics bundle
  ─[dynamicsEdgeSupply_of_forkEdgeSupply]→  DynamicsEdgeSupply
DynamicsChainStruct + DynamicsEdgeSupply
  ─[dynamicsChainSupply_of_split]→          DynamicsChainSupply
  ─[ledgerChainInputCert_of_dynamicsChain]→ LedgerChainInputCert            (= advance_cert)
```

`AnchorFacade.spec_safety_sound_residuals` then folds `advance_cert` through
`L4Fold.safeFrom_of_certificates` — `spec_head_safety_engine ∘
ledgerChainInput_of_certificates` — to `SafeFrom`, and threads it along the FCR
trajectory to `Spec_Safety`. This module uses the engine through
`spec_head_safety_engine` and supplies its certificate interface.

## Post-shell input bundle

`ShellResiduals` is `AnchorFacade.SoundResiduals` with `advance_cert` replaced
by its instantiation `dynamics_struct` + `fork_edges`. The other three fields — the two
finalized reset anchors (`genesis_dom`/`finalized_dom`) and the observed-anchor
filter input (`observed_filter`) — are retained:

* `genesis_dom` / `finalized_dom` — the finalized reset anchors are known and
  on every honest justified chain (`jc ⪰ finalized`);
* `observed_filter` (`E5Filter.ObservedFilterResiduals`) — the
  observed-anchor filter inputs (boundary-source justification, observed-anchor
  knownness, and ahead-regime head domination);
* `dynamics_struct` — the structural `get_ancestor_roots` confirmed chain,
  fork-choice-mechanical (`ResidualMechanicalII.dynamicsChainStruct_of_facts`);
* `fork_edges` (`ForkAssembly.ForkEdgeSupply`) — the per-edge `ForkEdgeInput`
  store-dynamics inputs. Under the shell IH these split into:
  - relay containments (`hsub`/`hequiv`), ancestor transports (`hSt`/`hAt`),
    and the `hboost` freeze, derived in `EdgeDynamics` from `Synchrony` and the
    walk domain;
  - IH-dependent inputs — the class-migration
    deltas `hdeltas` (`hs'`/`hx'`/`hρ`; `votes_head` + the
    IH + `Delivery.vote_lands` landing at `(w, m)` + `StepDischargeII`'s `ρ = 0`
    bookkeeping), the saturated majority `hmaj` (`committee_coverage` + `votes_head` + IH),
    and the recorded `c`-support `hrec` (`EngineTransport.recorded_supports_c_of_IH`);
  - non-IH inputs — `hbase` (the confirming-anchor `INV2(es)`, further
    reducible to the `Arms.arms_of_confirmed` accounting), `hval` (registry-
    constant justified source, using justified-checkpoint key membership), `hchild`
    (fork-choice child membership), and the sibling confinements `hHon`/`hByz`.

Not on the list: the epoch-crossing previous-epoch tax-arm from `Crossing.lean`,
which belongs to the `advance_cert` crossing leg rather than `dynamics_edges`.

This is the shell-instantiated conditional safety theorem; its input structure
lists the obligations at this reduction layer.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the engine leg, instantiated: `advance_cert` from the edge-reduced bundle

`SoundResiduals.advance_cert` (`LedgerChainInputCert` per confirmed block) is
the certificate-extraction boundary the shell folds through
`L4Fold.safeFrom_of_certificates`. This section **instantiates** it: composing
`ForkAssembly.dynamicsEdgeSupply_of_forkEdgeSupply` (the per-edge reduction),
`ResidualMechanicalII.dynamicsChainSupply_of_split` (the structural chain lift) and
`ResidualMechanical.ledgerChainInputCert_of_dynamicsChain` (the per-edge
`DynamicsResidual ⟶ LedgerCertInput` chain lift) turns the structural confirmed chain plus
the per-edge `ForkEdgeSupply` into exactly that `LedgerChainInputCert`. -/

/-- **`LedgerChainInputCert` from the edge-reduced bundle.** At one confirmed block `b`,
the structural confirmed chain `DynamicsChainStruct` and the per-edge `ForkEdgeSupply`
compose to the engine's `LedgerChainInputCert`: `dynamicsEdgeSupply_of_forkEdgeSupply`
lifts `ForkEdgeSupply` to `DynamicsEdgeSupply`, `dynamicsChainSupply_of_split` glues it to
the structural chain, and `ledgerChainInputCert_of_dynamicsChain` produces the certificate
chain. -/
theorem ledgerChainInputCert_of_edges
    (hbb : ByzantineBound cfg E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {b : Root} {n₀ : ℕ}
    (hstruct : E.DynamicsChainStruct cfg ext b n₀)
    (hedges : E.ForkEdgeSupply cfg ext b n₀) :
    LedgerChainInputCert cfg ext E b n₀ :=
  E.ledgerChainInputCert_of_dynamicsChain cfg ext hec hsv
    (E.dynamicsChainSupply_of_split cfg ext hstruct
      (E.dynamicsEdgeSupply_of_forkEdgeSupply cfg ext hbb hhb hec hsv hgen hedges))

/-! ## Section 2 — the post-shell input bundle

`ShellResiduals` is `AnchorFacade.SoundResiduals` after the engine leg is instantiated:
`advance_cert` (`LedgerChainInputCert`) is replaced by its two constituents
`dynamics_struct` (`DynamicsChainStruct`, the structural confirmed chain) and `fork_edges`
(`ForkEdgeSupply`, the per-edge store-dynamics supply). The finalized reset
anchors and observed-anchor filter fields are copied from `SoundResiduals`. -/

/-- **The shell-instantiated input bundle** (`ShellInstantiation`): finalized
reset anchors, observed-anchor filter inputs, a structural confirmed chain, and
the per-edge store-dynamics supply. -/
structure ShellResiduals (E : Execution Root) : Prop where
  /-- The genesis finalized reset anchor is known and lies on the justified
      chain at every honest store (`SoundResiduals.genesis_dom`). -/
  genesis_dom : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext v 0).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true
  /-- Each update's finalized reset anchor is known and lies on the justified
      chain at every honest store past `n+1` (`SoundResiduals.finalized_dom`). -/
  finalized_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true
  /-- The observed-anchor filter inputs (`SoundResiduals.observed_filter`). -/
  observed_filter : E.ObservedFilterResiduals cfg ext
  /-- The structural `get_ancestor_roots` confirmed chain per confirmed
      block (fork-choice-mechanical; `ResidualMechanicalII.dynamicsChainStruct_of_facts`). -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- The per-edge `ForkEdgeInput` store-dynamics supply per confirmed block
      (`ForkAssembly.ForkEdgeSupply` — the transports, migration deltas `hdeltas`,
      saturated majority `hmaj`, recorded-support `hrec`, and sibling confinements). -/
  fork_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeSupply cfg ext b (n + 1)

/-- **`SoundResiduals` from `ShellResiduals` + `SpecAssumptions`.** The three carried
fields pass through; `advance_cert` is rebuilt per confirmed block from `dynamics_struct`
+ `fork_edges` via `ledgerChainInputCert_of_edges`, drawing the coherence records
`hbb`/`hhb`/`hec`/`hsv`/`hgen` from `SpecAssumptions`. -/
theorem soundResiduals_of_shell (hSA : SpecAssumptions cfg ext E)
    (h : E.ShellResiduals cfg ext) : E.SoundResiduals cfg ext := by
  obtain ⟨⟨ast, ablk, heq, _, _⟩, _hwf, _hdiv, hhb, _hsync, hec, hsv, hbb, _hji⟩ := hSA
  exact
    { genesis_dom := h.genesis_dom
      finalized_dom := h.finalized_dom
      observed_filter := h.observed_filter
      advance_cert := fun v hv n b hconf =>
        E.ledgerChainInputCert_of_edges cfg ext hbb hhb hec hsv ⟨ast, ablk, heq⟩
          (h.dynamics_struct v hv n b hconf) (h.fork_edges v hv n b hconf) }

end Execution

/-! ## Section 3 — the shell-instantiated safety headline (`ShellInstantiation`)

Composing `soundResiduals_of_shell` with `AnchorFacade.spec_safety_sound_residuals`: FCR
safety follows from a proof that every execution's `SpecAssumptions` supplies
`ShellResiduals`. This is the shell-instantiated conditional result — the sound
`spec_safety_sound_residuals` with the engine certificate input constructed from
a structural chain and a per-edge store-dynamics supply. -/

/-- **`Spec_Safety` from the shell-instantiated input bundle** (`ShellInstantiation`) — the
end-to-end headline after shell instantiation. FCR safety from a proof that every
execution's `SpecAssumptions` supplies `ShellResiduals`. The engine leg
`advance_cert : LedgerChainInputCert` of the sound headline is now **instantiated** as the
edge-reduced `dynamics_struct` plus `fork_edges`; `genesis_dom`, `finalized_dom`,
and `observed_filter` are copied from `AnchorFacade.SoundResiduals`.
Everything the shell threads its head-safety IH through — the `fork_edges` migration
deltas, saturated majority, and recorded-support — is enumerated in the module header. -/
theorem spec_safety_shell_residuals
    (h : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.ShellResiduals cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_sound_residuals cfg ext
    (fun E hSA => E.soundResiduals_of_shell cfg ext hSA (h E hSA))

end FastConfirmation.Spec

end
