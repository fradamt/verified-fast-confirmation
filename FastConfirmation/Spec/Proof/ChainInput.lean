module
public import FastConfirmation.Spec.Proof.StepDischargeII

@[expose] public section

/-!
# Spec / Proof / ChainInput: constructing `LedgerChainInput`

`HeadSafetyEngine.spec_head_safety_engine` proves `EngineInv` from the functional
`LedgerChainInput`: per honest endpoint `(w, m)`, given head safety at strictly
earlier slots (the strong-induction hypothesis), the confirmed chain presents at
`(w, m)` as a `List.IsChain (LedgerStepV2 …)` from the justified checkpoint root
down to `b`, plus the fork-choice domain conditions.

This module constructs that obligation from a per-edge `INV2` certificate and
provides the composition theorem that builds each edge's `INV2` at the endpoint
from the confirming anchor.

* **Section 1 — `inv2_at_endpoint`.** `INV2(es)` at the confirming anchor
  `(vc, nc)` transports once to the endpoint
  `(w, m)` (`StepDischargeII.INV2_base_transport_of_transport`) and then iterates
  to every window end `σ ≥ es` (`StepDischargeII.INV2_maintained_same_epoch`),
  routing pre-`T1` slots through the per-slot step and post-`T1` through
  saturation. A clean two-step composition; the transport witnesses / step
  functionals are explicit theorem inputs.

* **Section 2 — `LedgerCertInput` ⟶ `LedgerStepV2`.** A per-edge certificate
  bundling exactly `HeadSafetyEngine.inv2_ledgerStepV2`'s inputs: the
  registry-constant justified balance source, boost congruence, `INV2` at the
  endpoint, the child-membership, and the recorded-support transport bridges
  (`hSmem`/`hHon`/`hByz`). `ledgerStepV2_of_certInput` lifts it to `LedgerStepV2`
  via `inv2_ledgerStepV2` (whose internals — `INV2_endpoint`, `recorded_bside_ge`,
  `recorded_sibling_le_v2` — are hidden from the L4 fold).

* **Section 3 — `ledgerChainInput_of_certificates`.** The headline. From the
  cert-level functional `LedgerChainInputCert` (the `LedgerStepV2` chain replaced
  by the more primitive `LedgerCertInput` chain), `LedgerChainInput` follows by
  lifting the chain edge-wise (`List.IsChain.imp` + `ledgerStepV2_of_certInput`).
  The hypothesis list packaged by `LedgerChainInputCert` is exactly the L4
  fold's obligation set.

Filter containment and chain knownness are functional hypotheses inside
`LedgerChainInputCert`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `INV2` at the endpoint

`INV2(es)` at the confirming anchor `(vc, nc)` transports once to the endpoint
`(w, m)` and iterates to any window end `σ ≥ es`. The composition of
`StepDischargeII.INV2_base_transport_of_transport` (base transport) and
`INV2_maintained_same_epoch` (per-slot step / saturation). -/

/-- **`INV2` at the endpoint.** From `INV2(es)` at the confirming anchor `(vc, nc)`
(`hbase`), the forward honest-class transports `(vc, nc) → (w, m)` (`hSt`/`hAt`,
`StepDischargeII`'s `is_ancestor_transport`-shaped witnesses), the recorded base-enemy
movement `hBb` (`BbadVal@(w,m) ≤ BbadVal@(vc,nc)`) and the per-slot maintenance
functionals — pre-`T1` step
`hpre`, post-`T1` saturated endpoint `hsat` — `INV2(σ)` holds at the endpoint `(w, m)`
for every `σ ≥ es`: the base transports once, then maintenance iterates at the
endpoint store. -/
theorem inv2_at_endpoint (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (vc w : ValidatorIndex) (nc m : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ)
    (hσ : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hSt : ∀ i, E.SupportsDesc cfg ext vc nc b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext vc nc b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i)
    (hBb : E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext vc nc b' lo es)
    (hbase : E.INV2 cfg ext vc nc b' lo es es boost)
    (hpre : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.INV2 cfg ext w m b' lo es σ' boost → E.INV2 cfg ext w m b' lo es (σ' + 1) boost)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b' lo σ' + E.Enemy cfg ext w m b' lo es σ' + boost + 1
        ≤ E.Sval cfg ext w m b' lo σ') :
    E.INV2 cfg ext w m b' lo es σ boost := by
  have hbase' : E.INV2 cfg ext w m b' lo es es boost :=
    E.INV2_base_transport_of_transport cfg ext vc w nc m b' lo es boost hSt hAt hBb hbase
  exact E.INV2_maintained_same_epoch cfg ext hec hsv w m b' lo es boost hbase' hpre hsat
    σ hσ hσH

end Execution

/-! ## Section 2 — the per-edge `INV2` certificate and its lift to `LedgerStepV2`

`HeadSafetyEngine.inv2_ledgerStepV2` turns one fork's `INV2` (at the endpoint
store, justified balance source) plus the recorded-support transport bridges
into a `LedgerStepV2`. `LedgerCertInput` bundles precisely those inputs — the
registry-constant balance source, boost congruence, `INV2`, child-membership,
and `hSmem`/`hHon`/`hByz` — existentially over the certificate parameters, so a
`List.IsChain LedgerCertInput` is the certificate shape (INV2 + set-membership
bridges, none of `LedgerStepV2`'s recorded-score internals). -/

/-- **Per-edge `INV2` certificate.** All of `inv2_ledgerStepV2`'s inputs for the
fork `(h, c)` at `store`, existentially over the certificate `(v₀, n₀, b', lo, es,
σ, boost)`: `hval` (registry-constant justified balance source), `hboost` (frozen
boost = the store's proposer score), `hinv` (`INV2` at the endpoint), `hchild`
(`c` is the `b′`-side filtered child), and the recorded-support bridges — `hSmem`
(`Sclass` records `c`-support), `hHon`/`hByz` (each sibling's supporters are
honest-confined to `Xclass` or byz-confined to `BbadSet ∪ SpentSet`). The
certificate form of `LedgerStepV2`. -/
def LedgerCertInput (E : Execution Root) (store : Store Root) (h c : Root) : Prop :=
  ∃ (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ),
    (store.checkpoint_states store.justified_checkpoint).validators = E.registry ∧
    boost = get_proposer_score cfg store ∧
    E.INV2 cfg ext v₀ n₀ b' lo es σ boost ∧
    ForkChoiceNode.mk c .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) ∧
    PendingStatusMargin cfg store (get_filtered_block_tree cfg store) h
      (get_parent_payload_status store (store.blocks c)) ∧
    (∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint)) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children store (get_filtered_block_tree cfg store)
            (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ) ∧
    (∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
          get_node_children store (get_filtered_block_tree cfg store)
            (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint),
          i ∉ E.honest → i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ)

/-- **`LedgerCertInput ⟹ LedgerStepV2`.** Unpack the certificate and apply
`inv2_ledgerStepV2` — the boost congruence, `INV2` endpoint strip
(`INV2_endpoint`), the `b′`-side transport (`recorded_bside_ge`) and the sibling
confinement (`recorded_sibling_le_v2`) are all internal to that lemma. -/
theorem ledgerStepV2_of_certInput {E : Execution Root} {store : Store Root} {h c : Root}
    (hc : LedgerCertInput cfg ext E store h c) :
    LedgerStepV2 cfg ext E store h c := by
  obtain ⟨v₀, n₀, b', lo, es, σ, boost, hval, hboost, hinv, hchild, hstatus,
    hSmem, hHon, hByz⟩ := hc
  exact inv2_ledgerStepV2 cfg ext hval hboost hinv hchild hstatus hSmem hHon hByz

/-! ## Section 3 — `LedgerChainInput` from the certificate functional

`LedgerChainInputCert` is `LedgerChainInput` with the `LedgerStepV2` chain replaced
by the more primitive `LedgerCertInput` chain (INV2 + set-membership bridges per
edge). The theorem below lifts the chain edge-wise. -/

/-- **The cert-level chain functional.** `LedgerChainInput` with each edge's
`LedgerStepV2` replaced by the per-edge `INV2` certificate `LedgerCertInput`
(Section 2). At every honest endpoint `(w, m)` past `n₀`, given head safety at
strictly earlier slots, the confirmed chain from the justified root to `b` is a
`List.IsChain LedgerCertInput` together with the fork-choice domain conditions
(`parent_slot_lt`, filtered-tree containment, `b`-knownness, path `Nodup`). This
is the shape consumed by `ledgerChainInput_of_certificates`: per confirmed chain block the endpoint
`INV2` (`inv2_at_endpoint` from the confirming-anchor base + transport +
maintenance), the recorded-support bridges, filter containment, and chain
knownness are all explicit fields. -/
def LedgerChainInputCert (E : Execution Root) (b : Root) (n₀ : ℕ) : Prop :=
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
      List.IsChain (LedgerCertInput cfg ext E (E.store cfg ext w m))
        ((E.store cfg ext w m).justified_checkpoint.root :: ds) ∧
      ((E.store cfg ext w m).justified_checkpoint.root :: ds).getLast (List.cons_ne_nil _ _) = b

/-- **`LedgerChainInput` from the certificates.** The `LedgerChainInput`
functional follows from the cert-level `LedgerChainInputCert`: at each honest
endpoint the domain facts pass through unchanged and the per-edge `LedgerCertInput`
chain lifts to a `LedgerStepV2` chain (`List.IsChain.imp` +
`ledgerStepV2_of_certInput`). `spec_head_safety_engine` can then use the resulting
`LedgerChainInput` to establish `EngineInv` for every cutoff slot. -/
theorem ledgerChainInput_of_certificates {E : Execution Root} {b : Root} {n₀ : ℕ}
    (hcert : LedgerChainInputCert cfg ext E b n₀) :
    LedgerChainInput cfg ext E b n₀ := by
  intro w hw m hm hH hIH
  obtain ⟨ds, hwf, hsub, hb, hnd, hchain, hlast⟩ := hcert w hw m hm hH hIH
  exact ⟨ds, hwf, hsub, hb, hnd,
    hchain.imp (fun _ _ hab => ledgerStepV2_of_certInput cfg ext hab), hlast⟩

/-! ## Section 4 — the per-edge certificate from the confirming-anchor base

The `ChainInput` pipeline made explicit: one edge's `LedgerCertInput` at the endpoint
`(w, m)` from the confirming-anchor base `INV2(es)` (the `INV2_base_of_arms` output
at `(vc, nc)`), the class transports `(vc, nc) → (w, m)` and the per-slot
maintenance functionals (`inv2_at_endpoint` builds the endpoint `INV2` from these),
together with the endpoint recorded-support bridges. The certificate is anchored at
the **endpoint** `(w, m)`; the whole `INV2` chain runs at that endpoint and only
the base `INV2(es)` transports across from the confirming anchor. -/

/-- **Endpoint certificate from the confirming-anchor base.** Given at the endpoint
`store = E.store cfg ext w m`: the confirming-anchor base `INV2(es)` (`hbase`, at
`(vc, nc)`), the forward honest-class transports `hSt`/`hAt` + the recorded base-enemy
movement `hBb`, the maintenance functionals `hpre`/`hsat`, and the endpoint data —
registry-constant justified
source `hval`, boost congruence `hboost`, child-membership `hchild`, and the
recorded-support bridges `hSmem`/`hHon`/`hByz` (all anchored at the endpoint
`(w, m)`) — the fork `(h, c)` has a `LedgerCertInput` at `store`. `inv2_at_endpoint`
supplies the endpoint `INV2(σ)`; the rest is `LedgerCertInput`'s bundle. -/
theorem ledgerCertInput_of_endpoint {E : Execution Root} {w : ValidatorIndex} {m : ℕ}
    {h c : Root}
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (vc : ValidatorIndex) (nc : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ)
    (hσ : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hSt : ∀ i, E.SupportsDesc cfg ext vc nc b' es i → E.SupportsDesc cfg ext w m b' es i)
    (hAt : ∀ i, E.AncestorOrVoteless cfg ext vc nc b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i)
    (hBb : E.BbadVal cfg ext w m b' lo es ≤ E.BbadVal cfg ext vc nc b' lo es)
    (hbase : E.INV2 cfg ext vc nc b' lo es es boost)
    (hpre : ∀ σ' : Slot, es ≤ σ' →
      E.SlotWithinHorizon cfg σ' → E.SlotWithinHorizon cfg (σ' + 1) →
      compute_epoch_at_slot cfg (σ' + 1) < compute_epoch_at_slot cfg es + 2 →
      E.INV2 cfg ext w m b' lo es σ' boost → E.INV2 cfg ext w m b' lo es (σ' + 1) boost)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext w m b' lo σ' + E.Enemy cfg ext w m b' lo es σ' + boost + 1
        ≤ E.Sval cfg ext w m b' lo σ')
    (hval : ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry)
    (hboost : boost = get_proposer_score cfg (E.store cfg ext w m))
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children (E.store cfg ext w m)
        (get_filtered_block_tree cfg (E.store cfg ext w m))
          (ForkChoiceNode.mk h
            (get_parent_payload_status (E.store cfg ext w m)
              ((E.store cfg ext w m).blocks c))))
    (hstatus : PendingStatusMargin cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) h
      (get_parent_payload_status (E.store cfg ext w m)
        ((E.store cfg ext w m).blocks c)))
    (hSmem : ∀ i ∈ E.Sclass cfg ext w m b' lo σ,
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
          i ∈ E.honest → i ∈ E.Xclass cfg ext w m b' lo σ)
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
          i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b' lo es ∨ i ∈ E.SpentSet es σ) :
    LedgerCertInput cfg ext E (E.store cfg ext w m) h c :=
  ⟨w, m, b', lo, es, σ, boost, hval, hboost,
    E.inv2_at_endpoint cfg ext hec hsv vc w nc m b' lo es σ boost hσ hσH
      hSt hAt hBb hbase hpre hsat,
    hchild, hstatus, hSmem, hHon, hByz⟩

end FastConfirmation.Spec

end
