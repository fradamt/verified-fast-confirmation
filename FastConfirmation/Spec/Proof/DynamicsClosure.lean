import FastConfirmation.Spec.Proof.ChainInput

/-!
# Spec / Proof / DynamicsClosure: endpoint input families

`ChainInput.ledgerCertInput_of_endpoint` reduces the shell's
per-endpoint `LedgerCertInput` to six functional-hypothesis families; this module
wires their independently proved components and states the remaining inputs
explicitly.

The six families (as they appear as hypotheses of `ledgerCertInput_of_endpoint`):

1. **`hbase`** — `INV2(es)` at the confirming anchor `(vc, nc)` from
   `is_one_confirmed = true`. `Section 1`: the **Arms↔Ledger accessor linkage**
   — identify `arms_of_confirmed`'s abstract class atoms with the ledger
   accessors `Sval`/`Xval`/`BbadVal`/`Jspec` and `compute_proposer_score`, then
   feed `LedgerV2.INV2_base_of_arms`. The class-decomposition identities and the
   Arms accounting bridges remain explicit inputs to `Arms.arms_of_confirmed`.

2/3. **`hpre`** — the per-slot `INV2` step `INV2(σ) ⟹ INV2(σ+1)` pre-`T1`.
   `Section 2`: reduce `hpre` to `StepDischargeII.INV2_step_same_epoch`'s two
   class-migration deltas `hs'`/`hx'` (family 2) plus the `ρ = 0` partition `hρ`
   (family 3, funding `hF3` through `hF3_of_partition`). Those two stay the
   genuine store-dynamics residue (`votes_head` + IH + delivery + the same-epoch
   assignment bookkeeping).

4. **`hsat`** — the post-`T1` saturated endpoint majority. `Section 3`: the
   saturated honest-majority arithmetic — enemy `≤` the window cap
   (`LedgerV2.Enemy_capacity`) against the saturated honest support — reduced to
   the honest-mass floor as a named input.

5. **`hSt`/`hAt`/`hequiv`** — the base class transports `(vc, nc) → (w, m)`.
   `Section 4`: per-supporter `EngineTransport.is_ancestor_transport` +
   knownness, and the equivocator containment from `attester_slashing_relay`.

6. **`hSmem`/`hHon`/`hByz`** — the endpoint recorded-support bridges. `Section 5`:
   `EngineTransport`'s `HS0_in_AttSupporters`-shaped machinery + the sibling
   confinement, reduced to the enumerated per-store knownness/provenance inputs.

`Section 6` bundles families 1–6 into `ledgerCertInput_of_endpoint`'s hypothesis
slots, exposing the residual list as one predicate (`DynamicsResidual`) the L4
fold supplies.

Store-dynamics facts not derived in this module are represented as named
hypotheses in the shapes justified by each lemma's docstring.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — family 1: `hbase` from `is_one_confirmed` (the Arms↔Ledger linkage)

`Arms.arms_of_confirmed` produces, from `is_one_confirmed = true` and the accounting
bridges, the floored base-arms disjunction over **abstract** class atoms
`s₀`/`aV`/`xV`/`Hpar`/`apre`/`xpre`/`Bbad`. `LedgerV2.INV2_base_of_arms` consumes the
same disjunction phrased over the **ledger accessors** `Sval`/`Xval`/`BbadVal`/`Jspec`.
`INV2_base_of_confirmed` is the bridge: it takes the accessor identities
(`s₀ = Sval`, `xV + xpre = Xval`, `Bbad = BbadVal`,
`s₀ + aV + xV + (Hpar + apre + xpre) = Jspec`, which follow from `Ledger.weight_partition`
plus the finer `a = aV + Hpar + apre` / `x = xV + xpre` accounting splits) and the boost
congruence, rewrites the arms disjunction into accessor form, and applies
`INV2_base_of_arms`. The class-decomposition identities and the Arms bridges are the
inputs; they are the accounting facts explicit in `arms_of_confirmed`. -/

/-- **Family 1 — the `INV2` base from a confirmed instance.** From
`is_one_confirmed cfg ext store bs b' = true`, the `Arms.arms_of_confirmed`
accounting bridges (`hS`…`hBbad`, tied to the real spec quantities at `store`/`bs`),
the boost congruence `hboost : boost = compute_proposer_score cfg bs`, and the four
Arms↔Ledger accessor identities, `INV2(es)` holds at `(v₀, n₀)`. Wires
`arms_of_confirmed` into `LedgerV2.INV2_base_of_arms` by rewriting the abstract arms
atoms to the ledger accessors. -/
theorem INV2_base_of_confirmed (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b' : Root}
    (hconf : is_one_confirmed cfg ext store bs b' = true)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (lo es : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo) (hesH : E.SlotWithinHorizon cfg es)
    {s0 aV xV Hpar apre xpre B_V B0 Bsup eqV Bpar Bbad qV : ℕ}
    (hboost : boost = compute_proposer_score cfg bs)
    (hS : get_attestation_score cfg store (get_node_for_root b') bs ≤ s0 + Bsup)
    (hd : get_support_discount cfg ext store bs b' ≤ Hpar + Bpar)
    (hAhi : get_adversarial_weight cfg ext store bs b'
        ≤ qV * cfg.confirmation_byzantine_threshold)
    (hAlo : qV * cfg.confirmation_byzantine_threshold
        ≤ get_adversarial_weight cfg ext store bs b' + eqV)
    (hBsup : Bsup ≤ get_adversarial_weight cfg ext store bs b')
    (hR4b : Bsup + eqV ≤ B_V)
    (hR8aW : s0 + aV + xV + B_V ≤ 100 * qV)
    (hR8cW : s0 + aV + xV + (Hpar + apre + xpre) + B0
        ≤ 100 * (estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
            ((store.blocks (store.blocks b').parent_root).slot + 1)
            (get_current_slot cfg store - 1) / 100))
    (hBbad : Bbad + Bsup + eqV + Bpar ≤ B0)
    (hSval : s0 = E.Sval cfg ext v₀ n₀ b' lo es)
    (hXval : xV + xpre = E.Xval cfg ext v₀ n₀ b' lo es)
    (hBbadVal : Bbad = E.BbadVal cfg ext v₀ n₀ b' lo es)
    (hJval : s0 + aV + xV + (Hpar + apre + xpre) = E.Jspec lo es) :
    E.INV2 cfg ext v₀ n₀ b' lo es es boost := by
  have harm := arms_of_confirmed cfg ext hconf hS hd hAhi hAlo hBsup hR4b hR8aW hR8cW hBbad
  rw [← hboost, hJval, hSval, hXval, hBbadVal] at harm
  exact E.INV2_base_of_arms cfg ext hbb v₀ n₀ b' lo es boost hloH hesH harm

/-! ## Section 3 — family 4: `hsat` (the post-`T1` saturated endpoint majority)

Past `T1` the recurrence tax vanishes (`LedgerV2.Uval_eq_zero_of_coverage`) and
`INV2` collapses to its endpoint form `x(σ) + Enemy(σ) + boost + 1 ≤ s(σ)`
(`LedgerV2.INV2_of_saturated`). The remaining content is that endpoint inequality
at saturation. `hsat_of_majority` replaces the enemy `Enemy(σ)` by the window
capacity `⌊C·J(σ)/(100−C)⌋` (`LedgerV2.Enemy_capacity` + `Nat.le_div_iff_mul_le`),
reducing `hsat` to the pure **saturated honest-majority** inequality `hmaj`
(honest support covers `x(σ) + ⌊C·J/(100−C)⌋ + boost + 1`) — the store-dynamics
fact that every honest active validator has re-voted `desc(b′)` by `T1`
(`committee_coverage` + `votes_head` + IH), which drives `x(σ)` down and `s(σ)`
up. `hmaj` is the named residual. -/

/-- **Family 4 — the saturated endpoint majority.** From the window enemy cap
(`Enemy_capacity`: `(100−C)·Enemy(σ) ≤ C·J(σ)`, so `Enemy(σ) ≤ ⌊C·J(σ)/(100−C)⌋`)
and the saturated honest-majority inequality `hmaj`, the endpoint form
`x(σ) + Enemy(σ) + boost + 1 ≤ s(σ)` follows — exactly `hsat`'s conclusion for a
saturated `σ`. Needs `lo ≤ es + 1` and `es ≤ σ` for the cap. -/
theorem hsat_of_majority (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo) (hσH : E.SlotWithinHorizon cfg σ)
    (hlo : lo ≤ es + 1) (hσ : es ≤ σ)
    (hmaj : E.Xval cfg ext v₀ n₀ b' lo σ
        + cfg.confirmation_byzantine_threshold * E.Jspec lo σ
            / (100 - cfg.confirmation_byzantine_threshold)
        + boost + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ) :
    E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ := by
  have hcap := E.Enemy_capacity cfg ext hbb v₀ n₀ b' lo es σ hloH hσH hlo hσ
  have hC : cfg.confirmation_byzantine_threshold ≤ 25 := cfg.confirmation_byzantine_threshold_le
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by omega
  have henemy : E.Enemy cfg ext v₀ n₀ b' lo es σ ≤
      cfg.confirmation_byzantine_threshold * E.Jspec lo σ
        / (100 - cfg.confirmation_byzantine_threshold) :=
    (Nat.le_div_iff_mul_le hDpos).mpr (by rw [Nat.mul_comm]; exact hcap)
  exact le_trans (by gcongr) hmaj

/-- **Family 4 — the saturated endpoint functional.** The `∀ σ`-form of
`hsat_of_majority`, in the exact slot shape `ChainInput.inv2_at_endpoint`'s `hsat`
argument expects: from the `∀ σ`-saturated-majority `hmaj`, the endpoint enemy form
holds for every saturated `σ ≥ es`. This is the `hsat` functional the shell wires. -/
theorem hsat_functional (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot) (boost : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hlo : lo ≤ es + 1)
    (hmaj : ∀ σ : Slot, es ≤ σ →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ →
      E.SlotWithinHorizon cfg σ →
      E.Xval cfg ext v₀ n₀ b' lo σ
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ
              / (100 - cfg.confirmation_byzantine_threshold)
          + boost + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ) :
    ∀ σ : Slot, es ≤ σ →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ →
      E.SlotWithinHorizon cfg σ →
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Enemy cfg ext v₀ n₀ b' lo es σ + boost + 1
        ≤ E.Sval cfg ext v₀ n₀ b' lo σ :=
  fun σ hσ hsat hσH =>
    E.hsat_of_majority cfg ext hbb v₀ n₀ b' lo es σ boost hloH hσH hlo hσ
      (hmaj σ hσ hsat hσH)

/-! ## Section 2 — families 2 & 3: the per-slot pre-`T1` step `hpre`

`ledgerCertInput_of_endpoint`'s `hpre` is the single-slot transition
`INV2(σ) ⟹ INV2(σ+1)` for a pre-`T1` slot. `StepDischargeII.INV2_step_same_epoch`
provides it from the two class-migration deltas `hs'`/`hx'` (family 2) and the
per-slot `span_fraction` funding `hF3`; `StepDischargeII.hF3_of_partition` produces
`hF3` from the `ρ = 0` same-epoch committee partition `hρ` (family 3).
`INV2_pre_step_of_deltas` composes them, so the residual is exactly `hs'`/`hx'`/`hρ`
— the genuine store-dynamics facts (every honest committee member of slot `σ+1`
re-votes `desc(b′)` under `votes_head` + the engine IH, landing recorded at `(w, m)`
by delivery; the same-epoch assignment bookkeeping gives the exact `ρ = 0`
partition). -/

/-- **Families 2 & 3 — one pre-`T1` `INV2` step.** From the class-migration deltas
`hs'` (honest support grows by the migrants `ξ`/`α` + honest committee growth) and
`hx'` (the sibling-stuck class sheds the `x→s` migrants `ξ`), plus the `ρ = 0`
same-epoch partition `hρ` (honest slot-`(σ+1)` committee weight bounded by the
recurrence + migrant + fresh weights), `INV2(σ) ⟹ INV2(σ+1)`.
`INV2_step_same_epoch` after `hF3_of_partition` closes `hF3`. This is `hpre`'s body
at one slot; the shell threads it over the pre-`T1` slots. -/
theorem INV2_pre_step_of_deltas (hbb : ByzantineBound cfg E)
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es σ : Slot) (boost ξ α : ℕ)
    (hloH : E.SlotWithinHorizon cfg lo)
    (hσH : E.SlotWithinHorizon cfg σ) (hσ1H : E.SlotWithinHorizon cfg (σ + 1))
    (hlo : lo ≤ es + 1) (hσ : es ≤ σ)
    (hs' : E.Sval cfg ext v₀ n₀ b' lo σ + ξ + α +
        E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
          (fun i => i ∈ E.honest))
      ≤ E.Sval cfg ext v₀ n₀ b' lo (σ + 1))
    (hx' : E.Xval cfg ext v₀ n₀ b' lo (σ + 1) + ξ ≤ E.Xval cfg ext v₀ n₀ b' lo σ)
    (hρ : E.weight ((E.span_committee (σ + 1) (σ + 1)).filter (fun i => i ∈ E.honest)) ≤
        E.weight (E.Unrec cfg ext v₀ n₀ b' lo es σ
            \ E.Unrec cfg ext v₀ n₀ b' lo es (σ + 1))
          + ξ + α +
          E.weight ((E.span_committee lo (σ + 1) \ E.span_committee lo σ).filter
            (fun i => i ∈ E.honest)))
    (hinv : E.INV2 cfg ext v₀ n₀ b' lo es σ boost) :
    E.INV2 cfg ext v₀ n₀ b' lo es (σ + 1) boost :=
  E.INV2_step_same_epoch cfg ext hbb v₀ n₀ b' lo es σ boost ξ α hloH hσH hσ1H
    hlo hσ hs' hx' (E.hF3_of_partition cfg ext hbb v₀ n₀ b' lo es σ ξ α hσ1H hρ) hinv

/-! ## Section 4 — family 5: the base class transports `hSt`/`hAt`/`hequiv`

`ledgerCertInput_of_endpoint`'s `hSt`/`hAt` are the forward descent transports of
the ground classes across anchors `(vc, nc) → (w, m)` at the cutoff `es`. Since
`E.vote` is store-independent, `SupportsDesc`/`AncestorOrVoteless` differ across
anchors *only* in their `is_ancestor` conjunct, evaluated at the two stores. The
reductions `SupportsDesc_transport_of_anc` / `AncestorOrVoteless_transport_of_anc`
peel the vote witness and hand the single `is_ancestor` fact to a per-root
transport `htrans` — which the L4 fold supplies from
`EngineTransport.is_ancestor_transport` (block-relay knownness `hsub` + the
`WalkKnown` domain conditions, the usual shapes). `hequiv`
(`equivocating@(vc,nc) ⊆ equivocating@(w,m)`) is the `attester_slashing_relay`
evidence-forwarding fact; it is supplied as a named hypothesis. -/

/-- **Family 5 — `SupportsDesc` transports.** With the per-root forward
`is_ancestor` transport `htrans` (`r ⪰ b′` at `(vc, nc)` implies `r ⪰ b′` at
`(w, m)`; `EngineTransport.is_ancestor_transport` per vote block), `SupportsDesc`
at the confirming anchor implies it at the endpoint anchor — the vote witness
`(t, k, a)` is carried unchanged (`E.vote` is store-independent). This is `hSt`. -/
theorem SupportsDesc_transport_of_anc (vc w : ValidatorIndex) (nc m : ℕ) (b' : Root)
    (es : Slot)
    (htrans : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root r) (get_node_for_root b') = true →
      is_ancestor (E.store cfg ext w m) (get_node_for_root r) (get_node_for_root b') = true) :
    ∀ i, E.SupportsDesc cfg ext vc nc b' es i → E.SupportsDesc cfg ext w m b' es i := by
  rintro i ⟨t, k, a, ht, hvote, hlater, hanc⟩
  exact ⟨t, k, a, ht, hvote, hlater, htrans _ hanc⟩

/-- **Family 5 — `AncestorOrVoteless` transports.** With the per-root forward
`is_ancestor` transport `htrans` in the reversed orientation (`b′ ⪰ r` at
`(vc, nc)` implies `b′ ⪰ r` at `(w, m)`), `AncestorOrVoteless` at the confirming
anchor implies it at the endpoint anchor: the voteless branch is store-independent,
the ancestor branch carries its vote witness and transports the single
`is_ancestor` fact. This is `hAt`. -/
theorem AncestorOrVoteless_transport_of_anc (vc w : ValidatorIndex) (nc m : ℕ)
    (b' : Root) (es : Slot)
    (htrans : ∀ r : Root, is_ancestor (E.store cfg ext vc nc)
        (get_node_for_root b') (get_node_for_root r) = true →
      is_ancestor (E.store cfg ext w m) (get_node_for_root b') (get_node_for_root r) = true) :
    ∀ i, E.AncestorOrVoteless cfg ext vc nc b' es i →
      E.AncestorOrVoteless cfg ext w m b' es i := by
  rintro i (hvoteless | ⟨t, k, a, ht, hvote, hlater, hanc⟩)
  · exact Or.inl hvoteless
  · exact Or.inr ⟨t, k, a, ht, hvote, hlater, htrans _ hanc⟩

/-- **Family 5 — per-root `is_ancestor` transport from block relay.** The
`htrans` witnesses `SupportsDesc_transport_of_anc` / `AncestorOrVoteless_transport_of_anc`
consume, packaged from `EngineTransport.is_ancestor_transport`: under a
`WellFormedExecution`, the block-relay containment `hsub`
(`block_roots@(vc,nc) ⊆ block_roots@(w,m)`), `b′`-knownness, and the per-root
`WalkKnown` domain condition `hwalk`, an `r ⪰ b′` fact at `(vc, nc)` (which pins
`r` known) transports to `(w, m)`. The `hr`/`hwalk` per-root inputs are the usual
domain-condition shapes the fold supplies. -/
theorem is_ancestor_transport_of_relay (hwf : WellFormedExecution E)
    (vc w : ValidatorIndex) (nc m : ℕ) (b' r : Root)
    (hsub : (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hr : r ∈ (E.store cfg ext vc nc).block_roots)
    (hb : b' ∈ (E.store cfg ext vc nc).block_roots)
    (hwalk : WalkKnown (E.store cfg ext vc nc) ((E.store cfg ext vc nc).blocks b').slot r)
    (hanc : is_ancestor (E.store cfg ext vc nc)
      (get_node_for_root r) (get_node_for_root b') = true) :
    is_ancestor (E.store cfg ext w m) (get_node_for_root r) (get_node_for_root b') = true :=
  is_ancestor_transport cfg ext hwf hsub hr hb hwalk hanc

/-! ## Section 5 — family 6: the endpoint recorded-support bridges `hSmem`/`hHon`/`hByz`

`inv2_ledgerStepV2` (via `ledgerCertInput_of_endpoint`) needs, at the endpoint
`(w, m)`: the `b′`-side class `Sclass` records `c`-support (`hSmem`), and each
sibling's supporters are honest-confined to `Xclass` (`hHon`) or byz-confined to
`BbadSet ∪ SpentSet` (`hByz`).

`hSmem_of_recorded` closes `hSmem` **modulo the per-member recorded-`c`-support
fact**: given, for each `Sclass` member, a recorded latest message at `(w, m)`
supporting `get_node_for_root c`, the honest/committee membership is discharged
internally (`EngineTransport.mem_AttSupporters_of_honest_committee`, with committee
membership read off `Sclass ⊆ span_committee`), yielding `AttSupporters` membership.
The per-member recorded-support fact is `EngineTransport.recorded_supports_c_of_IH`'s
output (ubiquity + epoch-cased root identification + the engine IH + the cross-store
walk-domain conditions), represented by the corresponding `EdgeInputResidual`
field.

`hHon`/`hByz` (the sibling-side confinements: provenance slot-confinement +
`no_index_supports_both_siblings` + the byz `BbadSet`/`SpentSet` dichotomy) are the
deepest residue and stay as the enumerated residual obligations. -/

/-- **Family 6 — `hSmem` from per-member recorded `c`-support.** For each `Sclass`
member `i`, given a recorded latest message at `(w, m)` that supports
`get_node_for_root c` (`hrec`, the `recorded_supports_c_of_IH` output), `i` sits in
`AttSupporters cfg (store w m) (get_node_for_root c) bs` for the registry-constant
justified source `bs`. Honest-ness and committee assignment come from
`Sclass ⊆ span_committee` + the honest filter; active/unslashed/non-equivocation are
internal to `mem_AttSupporters_of_honest_committee`. This is `hSmem`. -/
theorem hSmem_of_recorded (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (w : ValidatorIndex) (m : ℕ) {bs : BeaconState Root}
    (v₀ : ValidatorIndex) (n₀ : ℕ) (b' c : Root) (lo σ : Slot)
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hrec : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true) :
    ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bs := by
  intro i hi
  have hi' := hi
  simp only [Execution.Sclass, Finset.mem_filter] at hi'
  obtain ⟨t, ht, hcomm⟩ := Finset.mem_biUnion.mp hi'.1.1
  have htle : t ≤ σ := (Finset.mem_Icc.mp ht).2
  have htH : E.SlotWithinHorizon cfg t :=
    ⟨htle.trans hσH.1,
      lt_of_le_of_lt (Nat.div_le_div_right htle) hσH.2⟩
  obtain ⟨lm, hlm, hsupp⟩ := hrec i hi
  exact mem_AttSupporters_of_honest_committee cfg ext hhb hec hsv hgen hval hbsH
    hi'.1.2 htH hcomm hlm hsupp

end Execution

end FastConfirmation.Spec
