module
public import FastConfirmation.Spec.Proof.L4Fold
public import FastConfirmation.Spec.Proof.Crossing

@[expose] public section

/-!
# Spec / Proof / ResidualDischarge: deriving `L4Fold.L4Residual`

`L4Fold.confirmed_safeFrom_of_residual` reduces `Spec_Safety` to the four-field
bundle `L4Fold.L4Residual`. This module derives those fields from the named
store-dynamics and FFG-interface inputs in `L4ResidualHyps`.

The four `L4Residual` fields and their reductions:

* **`genesis_safe`** and **`finalized_safe`** (the
  finalized reset anchor): both are "a fixed finalized root `r₀` is on every
  honest justified chain from the base second on". `safeFrom_of_finalized_track`
  routes them through `JustificationInterface.finalized_justified_ancestry`
  (justified ⪰ finalized at each honest store) composed with a **cross-store
  finalized-descent** input (each honest store's finalized block descends from
  `r₀`) and the shared `StoreDomain` fork-choice domain conditions, closed by
  `L4Fold.safeFrom_of_justified_dom`.

* **`observed_safe`**: the rotated observed-justified anchor is
  on every honest justified chain — `safeFrom_of_domain_dom` from a
  **justified-dominance** input together with `StoreDomain`.

* **`advance_safe`**: every `is_one_confirmed` block is
  safe — `L4Fold.safeFrom_of_certificates` from a per-confirmed-block
  `LedgerChainInputCert` input. `DynamicsResidual` packages
  `ChainInput.ledgerCertInput_of_endpoint`'s hypotheses per fork edge and is
  converted to a `LedgerCertInput`.
  The epoch-crossing prev-epoch path rides `Crossing`'s member-arm `INVmem`
  machinery; its tax-arm (the epoch-seam double-recurrence condition) and the
  chain assembly stay named residuals.

`l4Residual_of_hyps : L4ResidualHyps → L4Residual` assembles these inputs, and
`L4Fold.spec_safety_of_residual` then proves `Spec_Safety`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the reset-anchor reductions (genesis / finalized / observed)

The three reset-anchor fields of `L4Residual` are all instances of "a fixed root
`r₀` is on every honest node's justified chain from the base second on", which
`L4Fold.safeFrom_of_justified_dom` turns into `SafeFrom r₀ n₀` given the
per-honest-store fork-choice domain conditions. `StoreDomain` names those domain
conditions once: `parent_slot_lt`,
the `WalkKnown` walk domain, justified-knownness — exactly `head_ge_of_justified_ge`'s
hypotheses); the two helpers below feed the per-anchor dominance into it. -/

/-- **The shared per-honest-store fork-choice domain conditions.** At every honest
`(w, m)`: the `parent_slot_lt` well-formedness, the `WalkKnown` walk domain over
all known roots, and justified-knownness — precisely the domain hypotheses
`L4Fold.safeFrom_of_justified_dom` / `EngineStore.head_ge_of_justified_ge` consume.
`WFTrajectory.store_wellFormedStore_core_plus` supplies `parent_slot_lt` under the
`hanchor` guard; the `WalkKnown` walk domain and justified-knownness are explicit
fields of this predicate. -/
def StoreDomain : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks
              ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot) ∧
      (∀ t r : Root, r ∈ (E.store cfg ext w m).block_roots →
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r) ∧
      (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots

/-- **`SafeFrom` from `StoreDomain` + justified dominance.** If `r₀` is
on every honest store's justified chain from `n₀` on (`hdom`), then `r₀` is safe
from `n₀`. Assembles the per-`(w, m)` bundle `L4Fold.safeFrom_of_justified_dom`
wants from `StoreDomain`'s three domain conditions and `hdom`'s dominance. This is
the reduction the observed-justified anchor uses directly, and the finalized/genesis
anchors use after the ancestry composition below. -/
theorem safeFrom_of_domain_dom (hdomain : E.StoreDomain cfg ext) {r₀ : Root} {n₀ : ℕ}
    (hdom : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root r₀) = true) :
    E.SafeFrom cfg ext r₀ n₀ := by
  apply E.safeFrom_of_justified_dom cfg ext
  intro w hw m hm hH
  obtain ⟨hwf, hwalk, hjust⟩ := hdomain w hw m hH
  exact ⟨hwf, hwalk, hjust, hdom w hw m hm hH⟩

/-- **`SafeFrom` of a finalized anchor from cross-store finalized tracking.** For a
fixed finalized root `r₀`, if at every honest store `(w, m)` from `n₀` on the
store's own finalized block is known and descends to `r₀` (`hfin` — the cross-store
finalized-descent input), then `r₀` is safe. The dominance
`justified ⪰ r₀` is `finalized_justified_ancestry` (justified ⪰ finalized, from the
interface) composed with `hfin` (finalized ⪰ r₀) by `is_ancestor_trans` over the
`StoreDomain` walk domain. Closes both `genesis_safe` (r₀ = the genesis anchor's
finalized root, `n₀ = 0`) and `finalized_safe` (r₀ = the update store's finalized
root, `n₀ = n + 1`). -/
theorem safeFrom_of_finalized_track (hji : JustificationInterface cfg ext E)
    (hdomain : E.StoreDomain cfg ext) {r₀ : Root} {n₀ : ℕ}
    (hfin : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
        (get_node_for_root r₀) = true) :
    E.SafeFrom cfg ext r₀ n₀ := by
  apply E.safeFrom_of_domain_dom cfg ext hdomain
  intro w hw m hm hH
  obtain ⟨hwf, hwalk, hjust⟩ := hdomain w hw m hH
  obtain ⟨hfin_known, hfin_anc⟩ := hfin w hw m hm hH
  exact is_ancestor_trans hwf (hwalk r₀ _ hjust) (hwalk r₀ _ hfin_known)
    (hji.finalized_justified_ancestry w hw m hH hfin_known hjust) hfin_anc

/-! ## Section 2 — the residual bundle and the `L4Residual` reduction

`L4ResidualHyps` collects the named inputs used by `l4Residual_of_hyps` to derive
all four `L4Residual` fields. `L4Fold.spec_safety_of_residual` then derives
`Spec_Safety`. -/

/-- **The input bundle for the L4 fold.** Six named store-dynamics /
FFG-interface residuals, each in an existing shape:

* `interface` — the FFG `JustificationInterface` (a `SpecAssumptions` component);
* `store_domain` — the shared per-honest-store fork-choice `StoreDomain`;
* `genesis_fin_track` — cross-store finalized descent for the genesis anchor;
* `finalized_track` — cross-store finalized descent for each update's finalized
  anchor;
* `observed_dom` — justified-dominance for each update's observed anchor;
* `advance_cert` — the per-confirmed-block `LedgerChainInputCert` (the engine
  certificate input). -/
structure L4ResidualHyps : Prop where
  /-- the FFG interface (a `SpecAssumptions` field). -/
  interface : JustificationInterface cfg ext E
  /-- the shared fork-choice domain conditions at every honest store. -/
  store_domain : E.StoreDomain cfg ext
  /-- Every honest store's finalized block descends from the genesis anchor's
      finalized root (`E.store v 0 = E.genesis_store`, shared across honest `v`). -/
  genesis_fin_track : ∀ v ∈ E.honest, ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v 0).finalized_checkpoint.root) = true
  /-- Every honest store's finalized block descends from the finalized reset
      anchor the update store picked. -/
  finalized_track : ∀ v ∈ E.honest, ∀ n : ℕ,
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    (E.store cfg ext w m).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root)
      (get_node_for_root (E.store cfg ext v (n + 1)).finalized_checkpoint.root) = true
  /-- The rotated observed-justified anchor is on every honest justified
      chain. -/
  observed_dom : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root) = true
  /-- Every `is_one_confirmed` block at an update store carries a
      `LedgerChainInputCert`. -/
  advance_cert : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    LedgerChainInputCert cfg ext E b (n + 1)

/-- **`L4Residual` from the named residuals.** All four `L4Residual` fields are
discharged: the two finalized anchors through `safeFrom_of_finalized_track`
(interface + cross-store tracking), the observed anchor through
`safeFrom_of_domain_dom`, and the advance through `L4Fold.safeFrom_of_certificates`.
Thus `L4ResidualHyps` implies the input required by
`L4Fold.spec_safety_of_residual`. -/
theorem l4Residual_of_hyps (h : E.L4ResidualHyps cfg ext) : E.L4Residual cfg ext where
  genesis_safe := fun v hv =>
    E.safeFrom_of_finalized_track cfg ext h.interface h.store_domain
      (fun w hw m _ hH => h.genesis_fin_track v hv w hw m hH)
  finalized_safe := fun v hv n => by
    rw [E.fcrStep_store]
    exact E.safeFrom_of_finalized_track cfg ext h.interface h.store_domain
      (h.finalized_track v hv n)
  observed_safe := fun v hv n =>
    E.safeFrom_of_domain_dom cfg ext h.store_domain (h.observed_dom v hv n)
  advance_safe := fun v hv n b hconf =>
    E.safeFrom_of_certificates cfg ext (h.advance_cert v hv n b hconf)

/-! ## Section 3 — the per-edge certificate: `DynamicsResidual`

`advance_cert` packages a whole `LedgerChainInputCert` — a `List.IsChain
LedgerCertInput` from the justified root down to `b`. `DynamicsResidual` is the
single-edge predicate collecting `ChainInput.ledgerCertInput_of_endpoint`'s
hypotheses: base transport, per-slot step, saturation, class transports, and
recorded-support bridges for one fork `(h, c)` at an honest endpoint
`(w, m)`, existentially over the certificate parameters. `ledgerCertInput_of_dynamicsResidual`
converts it to a `LedgerCertInput`. This is the same-epoch tentative path; the
epoch-crossing member-arm rides `Crossing` (below).

Assembling the per-edge certificates into the `LedgerChainInputCert` chain
(loop-inversion → the ascending `is_one_confirmed` chain → this bundle per edge)
is represented by the `advance_cert` input. -/

/-- **The per-edge dynamics residual.** For one fork `(h, c)` at the honest
endpoint `(w, m)`, the `ledgerCertInput_of_endpoint` hypotheses, existentially
quantified over the certificate `(vc, nc, b', lo, es, σ, boost)`: the base honest
transports `hSt`/`hAt`, recorded enemy movement `hBb`, base `hbase`, the per-slot
step `hpre`, saturation `hsat`, and the
endpoint data `hval`/`hboost`/`hchild` + recorded-support bridges
`hSmem`/`hHon`/`hByz`. -/
def DynamicsResidual (w : ValidatorIndex) (m : ℕ) (h c : Root) : Prop :=
  ∃ (vc : ValidatorIndex) (nc : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ),
    es ≤ σ ∧
    E.SlotWithinHorizon cfg lo ∧
    E.SlotWithinHorizon cfg σ ∧
    (∀ i, E.SupportsDesc cfg ext vc nc b' es i → E.SupportsDesc cfg ext w m b' es i) ∧
    (∀ i, E.AncestorOrVoteless cfg ext vc nc b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i) ∧
    E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext vc nc b' lo es ∧
    E.INV2 cfg ext vc nc b' lo es es boost ∧
    (∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.INV2 cfg ext w m b' lo es σ' boost → E.INV2 cfg ext w m b' lo es (σ' + 1) boost) ∧
    (∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b' lo σ' + E.Enemy cfg ext w m b' lo es σ' + boost + 1
        ≤ E.Sval cfg ext w m b' lo σ') ∧
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry ∧
    boost = get_proposer_score cfg (E.store cfg ext w m) ∧
    ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))) ∧
    (∀ i ∈ E.Sclass cfg ext w m b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint)) ∧
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
          i ∈ E.honest → i ∈ E.Xclass cfg ext w m b' lo σ) ∧
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
          i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b' lo es ∨ i ∈ E.SpentSet es σ)

/-- **`DynamicsResidual ⟹ LedgerCertInput`.** Unpack the family bundle and apply
`ChainInput.ledgerCertInput_of_endpoint`. The per-edge certificate at the endpoint
`(w, m)`, using the global coherence records `hec`/`hsv`. -/
theorem ledgerCertInput_of_dynamicsResidual (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E) {w : ValidatorIndex} {m : ℕ} {h c : Root}
    (hres : E.DynamicsResidual cfg ext w m h c) :
    LedgerCertInput cfg ext E (E.store cfg ext w m) h c := by
  obtain ⟨vc, nc, b', lo, es, σ, boost, hσ, hloH, hσH, hSt, hAt, hBb, hbase, hpre, hsat,
    hval, hboost, hchild, hSmem, hHon, hByz⟩ := hres
  exact ledgerCertInput_of_endpoint cfg ext hec hsv vc nc b' lo es σ boost hσ hσH
    hSt hAt hBb hbase hpre hsat hval hboost hchild hSmem hHon hByz

/-! ### The epoch-crossing member-arm edge (consuming `Crossing.lean`)

The prev-epoch-loop path confirms blocks whose window `[parent.slot+1, es]` crosses
an epoch boundary. Per `Crossing.lean`, the base disjunction still holds
(`arms_pure` is window-shape-agnostic, `adjust_committee_weight_estimate_ge`), and
its **member-arm** branch (`s₀ ≥ x₀ + m₁ + ⌊C·J₀/D⌋`) sustains the `Enemy`-free
invariant `Crossing.INVmem` — immune to the epoch-seam double-recurrence because
its step and endpoint reference no byz weight. `ledgerStepV2_of_crossing_member`
turns one such edge into a `LedgerStepV2` directly: `INVmem_endpoint` supplies the
ledger inequality (in place of `INV2_endpoint`), the recorded-support bounds are the
same `recorded_bside_ge` / `recorded_sibling_le_v2`. The crossing **tax-arm** branch
requires an additional epoch-seam condition. -/

/-- **Crossing member-arm edge ⟹ `LedgerStepV2`.** From the `Enemy`-free member-arm
invariant `Crossing.INVmem` at the endpoint `(w, m)` (window `[lo, σ]`, base window
end `es`), the boost congruence `hboost`, the child-membership `hchild`, and the
recorded-support bridges `hSmem`/`hHon`/`hByz`, the fork `(h, c)` has a v2 ledger
certificate. `INVmem_endpoint` gives the ledger inequality
`Xval + Enemy + boost + 1 ≤ Sval` (the enemy stripped from the member cap by the
unconditional `Enemy_capacity`); `recorded_bside_ge` / `recorded_sibling_le_v2` give
the two recorded score bounds — the `Crossing`-fed analogue of
`HeadSafetyEngine.inv2_ledgerStepV2`. -/
theorem ledgerStepV2_of_crossing_member (hbb : ByzantineBound cfg E)
    {w : ValidatorIndex} {m : ℕ} {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root}
    {lo es σ : Slot} {boost : ℕ}
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ)
    (hlo : lo ≤ es + 1) (hes : es ≤ σ)
    (hval : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry)
    (hboost : boost = get_proposer_score cfg (E.store cfg ext w m))
    (hinv : E.INVmem cfg ext v₀ n₀ b' lo σ boost)
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))))
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint))
    (hHon : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m))
              (ForkChoiceNode.mk h
                (get_parent_payload_status (E.store cfg ext w m)
                  ((E.store cfg ext w m).blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∉ E.honest →
            i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    LedgerStepV2 cfg ext E (E.store cfg ext w m) h c := by
  refine ⟨v₀, n₀, b', lo, es, σ, hchild, recorded_bside_ge cfg ext hval hSmem, ?_, ?_⟩
  · rw [← hboost]
    exact E.INVmem_endpoint cfg ext hbb v₀ n₀ b' lo es σ boost hloH hσH hlo hes hinv
  · intro c' hc' hne
    exact E.recorded_sibling_le_v2 cfg ext hval (hHon c' hc' hne) (hByz c' hc' hne)

end Execution

/-- **`Spec_Safety` from the named residuals.** Composing `l4Residual_of_hyps` with
`L4Fold.spec_safety_of_residual`: if `SpecAssumptions` supplies `L4ResidualHyps` for
every execution, the FCR safety guarantee holds. The residual list `L4ResidualHyps`
is the input bundle produced by `ResidualDischarge`. -/
theorem spec_safety_of_residualHyps
    (hres : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.L4ResidualHyps cfg ext) :
    Spec_Safety cfg ext :=
  spec_safety_of_residual cfg ext (fun E hSA => E.l4Residual_of_hyps cfg ext (hres E hSA))

end FastConfirmation.Spec

end
