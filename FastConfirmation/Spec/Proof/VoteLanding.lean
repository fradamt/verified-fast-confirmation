module
public import FastConfirmation.Spec.Proof.IHMechanize
public import FastConfirmation.Spec.Proof.ByzVpre

@[expose] public section

/-!
# Spec / Proof / VoteLanding: vote and sibling-confinement inputs

`IHMechanize` expresses several fields of `EdgeDynamics.EdgeInputResidual` in
terms of the following inputs:

* `hmaj_of_saturation` ← the support-saturation crux `hsat` + the boost-dilution
  crux `hdil`;
* `hdeltas_of_monotone` ← the per-slot monotonicity cruxes `hSmono` / `hXmono` / `hρ0`;
* `dynamicsChainStruct_of_endpoint` ← the two per-endpoint residuals `hb` / `hcase`;
* `hrec_of_domain` ← the per-endpoint domain package.

This module proves the boost-dilution inequality and combines the honest and
Byzantine sibling-confinement lemmas into the shared `hHon`/`hByz` input:

* **Section 1 — `hdil` (boost dilution).** The pure-ℕ inequality
  `⌊C·J/(100−C)⌋ + boost + 1 ≤ J` from the saturated-regime `Jspec` lower bound
  `2·(boost+1) ≤ J` (`interval_cases C` over the floor witness). `boost_dilution`
  produces the exact `hdil` shape `hmaj_of_saturation` consumes.

* **Section 2 — the sibling confinement wiring (`hHon`/`hByz`).**
  `sibling_confinement` cases on `i ∈ E.honest` and dispatches to the two *proven*
  lemmas — `Confinement.honest_sibling_confinement` (honest ⟹ `Xclass es`) and
  `ByzVpre.byz_sibling_confinement` (byz ⟹ `BbadSet es ∪ SpentSet es σ`) —
  discharging the two Layer-0-mechanical domain premises (`ParentSlotLt`, the
  blanket `store_walkKnownK` walk domain) from `SpecAssumptions`. The provenance /
  recorded-knownness / domination / fork-geometry premises stay as the enumerated
  per-endpoint residuals. `hHon_of_confinement` / `hByz_of_confinement` are the
  `EdgeInputResidual`-field wrappers.

* **Section 3 — the honest committee vote existence (`votes_head` consequence).**
  `honest_committee_vote` extracts, for an honest committee-`s` member (with
  `s ≥ slot_at 0`), its own assigned vote at `s` — the ground-vote witness the
  `Sclass`-membership bridge and the `ρ = 0` partition build on.

* **Section 4 — the `ρ = 0` same-epoch partition (`hρ0`).** `rho0_same_epoch`:
  in the strict same-epoch regime a slot-`σ+1` honest committee member is
  *fresh* (its only span assignment is `σ+1`, by `committee_assignment_unique`),
  so the honest committee of `σ+1` is contained in the window-growth set — funding
  `hρ0` with the `Unrec`-difference contribution non-negative.

The store-dynamics inputs retained by this reduction (the `Sclass`/`Xclass`
migration weights `hSmono`/`hXmono`, the saturation support crux `hsat`, and the
per-endpoint knownness `hb`/`hcase`) are
the cross-store `is_ancestor` transport of late voters' heads (`vote_lands`'s
`hhead_known`/`hhead_walk` statement-layer batch) plus the Finset migration
algebra. Their consumers require the `get_head`/`get_checkpoint_block`
well-formedness inputs stated by the corresponding interfaces.


**P-6 note.** Some names used in this header no longer exist. The legacy `SpecAssumptions`
observed-anchor cone was retired and swept for orphans, which removed `EdgeDynamics.EdgeInputResidual`, `IHMechanize.dynamicsChainStruct_of_endpoint`
and `hdeltas_of_monotone`, and this module's own `rho0_same_epoch` / `hdeltas_sameEpoch`.
The descriptions above are kept because they still identify the *shapes* the surviving
declarations produce and consume. See `docs/p6-justified-descends-derivation.md` §8.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — `hdil`: the boost dilution from the saturated `Jspec` lower bound -/

/-- Two-sided floor bounds of `n / m` (`0 < m`) as linear atoms. Local copy of
`Arms.div_floor_bounds` / `StepDischargeII.div_floor_bounds`. -/
private theorem div_floor_bounds (n m : ℕ) (hm : 0 < m) :
    m * (n / m) ≤ n ∧ n < m * (n / m + 1) := by
  have e := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  rw [Nat.mul_succ]
  omega

/-- **Pure-ℕ boost dilution.** For `C ≤ 25`, `q := ⌊C·J/(100−C)⌋` and the
saturated-regime lower bound `2·(boost+1) ≤ J`, the diluted reserve plus the boost
margin stays under `J`: `q + boost + 1 ≤ J`. The floor witness `hq`
(`(100−C)·q ≤ C·J`) makes `interval_cases C` + `omega` linear (26 cases): for every
`C ≤ 25` the reserve `q ≤ C·J/(100−C) ≤ J/3` and `boost+1 ≤ J/2`, so
`q + boost + 1 ≤ 5J/6 ≤ J`. -/
private theorem boost_dilution_arith {C J boost q : ℕ} (hC : C ≤ 25)
    (hJ : 2 * (boost + 1) ≤ J) (hq : (100 - C) * q ≤ C * J) :
    q + boost + 1 ≤ J := by
  interval_cases C <;> omega

namespace Execution

variable (E : Execution Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- **`hdil` from the saturated `Jspec` lower bound** (`VoteLanding`). Produces the exact
boost-dilution field `IHMechanize.hmaj_of_saturation` consumes: for every post-`T1`
slot the diluted reserve `⌊C·J(σ')/(100−C)⌋ + boost + 1 ≤ J(σ')`. Funded by the
saturated-regime `Jspec` lower bound `hJlb` (`2·(boost+1) ≤ J(σ')`) — the genuine
engine residual (`span_fraction` over the saturated full epoch's honest window; it
dominates twice the per-epoch proposer boost, the paper's Assumption-2 margin). -/
theorem boost_dilution (lo es : Slot) (boost : ℕ)
    (hJlb : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      2 * (boost + 1) ≤ E.Jspec lo σ') :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
          / (100 - cfg.confirmation_byzantine_threshold) + boost + 1 ≤ E.Jspec lo σ' := by
  intro σ' h1 h2 hσH
  set C := cfg.confirmation_byzantine_threshold with hCdef
  have hC25 : C ≤ 25 := cfg.confirmation_byzantine_threshold_le
  have hDpos : 0 < 100 - C := by omega
  obtain ⟨hqlo, _⟩ := div_floor_bounds (C * E.Jspec lo σ') (100 - C) hDpos
  exact boost_dilution_arith hC25 (hJlb σ' h1 h2 hσH) hqlo

/-! ## Section 2 — the sibling confinement wiring (`hHon` / `hByz`)

`EdgeDynamics.EdgeInputResidual.hHon`/`hByz` confine every recorded supporter of a
filtered sibling `c'` of the `b`-side child `c` to the base classes at the cutoff
`es` (honest ⟹ `Xclass es`; byz ⟹ `BbadSet es ∪ SpentSet es σ`). Both are the
*proven* lemmas `Confinement.honest_sibling_confinement` and
`ByzVpre.byz_sibling_confinement` — this is the shared structural step left as
an explicit input by the lower-level reductions (`ByzVpre` is a leaf, and honest confinement is a convenience
lemma). Here the two Layer-0-mechanical domain premises — `ParentSlotLt`
(`store_parentSlotLt`) and the blanket walk domain (`store_walkKnownK`) — are
discharged from `SpecAssumptions`, and the sibling's `hc'`/`hpc'`/`hlo` are derived
from the fork-choice child membership (`mem_get_node_children` +
`filtered_subset_block_roots` + `ParentSlotLt`). The provenance (`hprov`), recorded
knownness (`hlmknown`), domination (`hdom`), and the `b`-side fork-edge geometry
(`hh`/`hpc`/`hbc`/`hlo_h`) stay as the enumerated per-endpoint residuals. -/

/-- **`hHon`, wired** (`VoteLanding`). Every honest recorded supporter of a filtered sibling
`c'` (child of the fork point `h`, `c' ≠ c`) of the `b`-side child `c` is confined to
`Xclass … es` at the endpoint `(w, m)`. This is `EdgeInputResidual.hHon` at the base
slice `σ := es`, produced by `Confinement.honest_sibling_confinement` with its two
mechanical domain premises discharged from `SpecAssumptions`; the sibling knownness
`hc'`, its parent link `hpc'`, and its window membership `lo ≤ c'.slot` come from the
child membership + `ParentSlotLt` (`lo ≤ h.slot + 1 = hlo_h`). -/
theorem hHon_of_confinement (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b h c : Root} {lo es : Slot}
    (hjc : (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    (hdom : E.RecordedEpochMax cfg ext w m es)
    (hes : es = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo_h : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∈ E.honest → i ∈ E.Xclass cfg ext w m b lo es := by
  obtain ⟨hgen, hwf, _hdiv, hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, heq, _, _⟩ := hgen; exact ⟨ast, ablk, heq⟩
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled w m
  have hwalkK := E.store_walkKnownK cfg ext hwf hec hgen w m
  intro c' hchild hne' i hi_supp hih
  rw [mem_get_node_children] at hchild
  have hc'mem : c' ∈ get_filtered_block_tree cfg (E.store cfg ext w m) := hchild.1
  have hc' : c' ∈ (E.store cfg ext w m).block_roots :=
    filtered_subset_block_roots cfg (E.store cfg ext w m) hjc c' hc'mem
  have hpc' : ((E.store cfg ext w m).blocks c').parent_root = h := hchild.2
  have hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot := by
    have hlt := hpsl c' hc' (by rw [hpc']; exact hh)
    rw [hpc'] at hlt; exact le_trans hlo_h hlt
  exact E.honest_sibling_confinement cfg ext hhb hec hgen' hprov hpsl hwalkK hes
    hb hc hc' hh hpc hpc' (Ne.symm hne') hbc hlo hlmknown hdom hi_supp hih

/-- **`hByz`, wired** (`VoteLanding`). Every byzantine recorded supporter of a filtered
sibling `c'` of the `b`-side child `c` is confined to `BbadSet … es ∪ SpentSet es σ`
at the endpoint `(w, m)`. This is `EdgeInputResidual.hByz`, produced by
`ByzVpre.byz_sibling_confinement` (the byz analog, purely recorded — no `no_forgery`)
with the same mechanical-domain discharge and sibling derivation as `hHon_of_confinement`.
The tail bound `hσcur : current_slot − 1 ≤ σ` and the fork-edge geometry are the
per-endpoint residuals. -/
theorem hByz_of_confinement (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b h c : Root} {lo es σ : Slot}
    (hjc : (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo_h : lo ≤ ((E.store cfg ext w m).blocks h).slot + 1) :
    ∀ c' : Root,
      ForkChoiceNode.mk c' ∈
          get_node_children (E.store cfg ext w m)
            (get_filtered_block_tree cfg (E.store cfg ext w m)) (ForkChoiceNode.mk h) →
        c' ≠ c →
        ∀ i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c')
            ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint),
          i ∉ E.honest → i ∈ E.BbadSet cfg ext w m b lo es ∨ i ∈ E.SpentSet es σ := by
  obtain ⟨hgen, hwf, _hdiv, _hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  have hpsl : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled w m
  have hwalkK := E.store_walkKnownK cfg ext hwf hec hgen w m
  intro c' hchild hne' i hi_supp hib
  rw [mem_get_node_children] at hchild
  have hc'mem : c' ∈ get_filtered_block_tree cfg (E.store cfg ext w m) := hchild.1
  have hc' : c' ∈ (E.store cfg ext w m).block_roots :=
    filtered_subset_block_roots cfg (E.store cfg ext w m) hjc c' hc'mem
  have hpc' : ((E.store cfg ext w m).blocks c').parent_root = h := hchild.2
  have hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot := by
    have hlt := hpsl c' hc' (by rw [hpc']; exact hh)
    rw [hpc'] at hlt; exact le_trans hlo_h hlt
  exact E.byz_sibling_confinement cfg ext hprov hpsl hwalkK hb hc hc' hh hpc hpc'
    (Ne.symm hne') hbc hlo hσcur hlmknown hi_supp hib

/-! ## Section 3 — the honest committee vote existence (`votes_head` consequence)

The `Sclass`-membership bridge and the `ρ = 0` partition both start from an honest
committee member's own ground vote. `honest_committee_vote` is `HonestBehavior.votes_head`
packaged: an honest validator assigned to slot `s` (with `s` at or after the anchor
slot) casts, at some second `n` with `slot_at n = s`, exactly the validator-spec
attestation computed from its own store — the `(n, honest_attestation …)` witness the
`SupportsDesc` predicate and `Delivery.vote_ubiquity` consume. -/

/-- **Honest committee members vote at their assigned slot** (`VoteLanding`). Direct
consequence of `HonestBehavior.votes_head`: an honest validator `v` assigned to slot
`s` (`s ≥ slot_at 0`) has a recorded vote at `s` equal to its own honest attestation
computed at the voting second `n` (`slot_at n = s`). This is the ground-vote witness
the pre-`T1` fresh-committee entry (`hSmono`) and the saturation crux (`hsat`) build on
via `Delivery.vote_ubiquity` + the `SupportsDesc` bridge. -/
theorem honest_committee_vote (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot}
    (hcomm : v ∈ E.committee s) (hsH : E.SlotWithinHorizon cfg s)
    (hs0 : E.slot_at cfg 0 ≤ s) :
    ∃ (n : ℕ) (index : CommitteeIndex), E.slot_at cfg n = s ∧
      E.vote v s = some (n, honest_attestation cfg ext (E.store cfg ext v n) s index v) :=
  by
    obtain ⟨n, index, _hnH, hslot, hvote⟩ := hhb.votes_head v hv s hcomm hsH hs0
    exact ⟨n, index, hslot, hvote⟩

/-! ## Section 4 — the `ρ = 0` same-epoch partition (`hρ0`)

`IHMechanize.hdeltas_of_monotone`'s `hρ0` asks that the honest committee of slot
`σ'+1` is covered by the base-supporter recurrence (`Unrec σ' \ Unrec (σ'+1)`) plus
the honest window growth (`span lo (σ'+1) \ span lo σ'`) — the `ξ = α = 0` witness of
the migrant existential. In the **strict same-epoch** regime (every slot of the window
`[lo, σ']` sits in `epoch(σ'+1)`), a slot-`σ'+1` honest committee member cannot also be
assigned anywhere in `[lo, σ']`: `committee_assignment_unique` would force that slot to
be `σ'+1` itself. So the honest committee of `σ'+1` is **entirely fresh** — contained in
the window-growth set — and `hρ0` holds with the `Unrec`-difference contribution merely
non-negative. This is the tentative (current-epoch) loop's `ρ = 0`; the crossing
(previous-epoch) regime has earlier-epoch recurrers and uses the explicit
`ξ`/`α > 0` migration inputs. -/

/-! ### Deleted: `rho0_same_epoch` and `hdeltas_sameEpoch`

The `ρ = 0` same-epoch partition and the migration-delta assembly built on it. Both were
consumed only by `ShellCompose`'s engine composition.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

/-! ## Section 5 — the IHMechanize-facing compositions

The two clean compositions delivering the `EdgeInputResidual` fields directly from
the reduced cruxes: `hmaj` from support saturation + the `Jspec` lower bound, and
`hdeltas` from the two migration monotonicities with `hρ0` discharged in the
same-epoch regime. -/

/-- **`hmaj` from support saturation + the `Jspec` lower bound** (`VoteLanding`). Composes
`IHMechanize.hmaj_of_saturation` with `boost_dilution`: the post-`T1` saturated
honest majority `x(σ') + ⌊C·J(σ')/(100−C)⌋ + boost + 1 ≤ s(σ')` follows from the
support-saturation crux `hsat` (every honest window member re-votes `desc(b')` past
`T1`) and the saturated-regime `Jspec` lower bound `hJlb`. This is exactly the
`EdgeInputResidual.hmaj` field, reduced to its two genuine engine residuals. -/
theorem hmaj_of_saturation_lb (v₀ : ValidatorIndex) (n₀ : ℕ) (b' : Root) (lo es : Slot)
    (boost : ℕ)
    (hsat : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      ∀ i ∈ (E.span_committee lo σ').filter (fun i => i ∈ E.honest),
        E.SupportsDesc cfg ext v₀ n₀ b' σ' i)
    (hJlb : ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      2 * (boost + 1) ≤ E.Jspec lo σ') :
    ∀ σ' : Slot, es ≤ σ' →
      compute_epoch_at_slot cfg es + 2 ≤ compute_epoch_at_slot cfg σ' →
      E.SlotWithinHorizon cfg σ' →
      E.Xval cfg ext v₀ n₀ b' lo σ'
          + cfg.confirmation_byzantine_threshold * E.Jspec lo σ'
              / (100 - cfg.confirmation_byzantine_threshold)
          + boost + 1 ≤ E.Sval cfg ext v₀ n₀ b' lo σ' :=
  E.hmaj_of_saturation cfg ext v₀ n₀ b' lo es boost hsat
    (E.boost_dilution cfg lo es boost hJlb)

end Execution

end FastConfirmation.Spec

end
