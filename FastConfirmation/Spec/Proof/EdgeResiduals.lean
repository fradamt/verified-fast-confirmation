import FastConfirmation.Spec.Proof.Confinement
import FastConfirmation.Spec.Proof.ByzVpre
import FastConfirmation.Spec.Proof.Cruxes
import FastConfirmation.Spec.Proof.DynamicsClosure

/-!
# Spec / Proof / EdgeResiduals: per-edge inputs for the confirm-margin supply

This module proves the **sibling/support** inputs of
`AnchorClose.ForkEdgeConfirmMarginSupply` — the per-`b`-chain-edge residual bundle that the
confirm-margin collapse (`Dominance.descendStep_of_confirmMargin` /
`Assembly.descendStep_of_assemblyResidual`) consumes — into the exact field shapes the
supply names, from the committed confinement/support machinery.

The confirm-margin instantiation pins `σ = slot_at m − 1 = get_current_slot (store w m) − 1`
(the endpoint's fork-contest window end, `Growth.lean` header). At that `σ` the two
sibling confinements land **directly** at the window end — no `es → σ` migration residual:

* **`hByz` → `Bwin lo σ`** (`byz_confinement_bwin`): `ByzVpre.byz_sibling_confinement`
  puts a byz sibling supporter in `BbadSet lo es ∪ SpentSet es σ`; `bwin_of_bbad_or_spent`
  weighs both into the window byz set `Bwin lo σ` (`BbadSet ⊆ Bwin lo es ⊆ Bwin lo σ` by
  `span_committee_mono`; `SpentSet es σ ⊆ Bwin lo σ` by `span_committee_mono_lo`
  (`lo ≤ es+1`).
  This yields the confirm-margin `Bwin` shape rather than the v2
  `BbadSet ∪ SpentSet` shape.
* **`hHon` → `Xclass w m b lo σ`** (`honest_confinement_xclass`):
  `Confinement.honest_sibling_confinement` at its base cutoff `es := σ`
  (`σ = get_current_slot (store w m) − 1`), so the recorded newest-by-`σ` message is the
  ground newest-by-`σ` vote and `siblings_incompatible` confines the honest sibling
  supporter to `Xclass … σ` outright.
* **`hSmem`** (`sclass_subset_attSupporters`): `Cruxes.hrec_crux` (every `Sclass` member
  records a `c`-supporting latest message) composed with `DynamicsClosure.hSmem_of_recorded`
  (honest + committee-seat side conditions → `AttSupporters`), at the endpoint node
  `(v₀, n₀) := (w, m)` and the justified balance source (`EdgeDynamics.hval_of_interface`).

The per-endpoint domain packages (`LatestMessageProvenance`, `ParentSlotLt`, the blanket
walk domain `hwalkK`, recorded-root knownness `hlmknown`, `RecordedEpochMax`) and the fork
geometry (`b`/`c`/`c'`/`h` known, parent links, `hbc`, `lo ≤ c'.slot`) enter as hypotheses
in the confinement producers' shapes; the `hrec_crux` domain package (the engine IH `hIH`,
ubiquity `hubiq`, vote-block/recorded-root knownness) enters in its shape. Deriving those
packages from `SpecAssumptions` is the shared store-domain plumbing (`store_domainK`,
`LatestMessageProvenance` trajectory invariant), not re-proved here.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `hByz`: byz sibling supporters land in `Bwin lo σ` -/

/-- **`BbadSet lo es ∪ SpentSet es σ ⊆ Bwin lo σ`.** The two byz destinations of
`ByzVpre.byz_sibling_confinement` both weigh into the window byz set `Bwin lo σ`: the base
enemy `BbadSet lo es` sits in `Bwin lo es ⊆ Bwin lo σ` (`span_committee_mono`, `es ≤ σ`);
the tail `SpentSet es σ = span (es+1) σ .filter (∉honest)` sits in `Bwin lo σ`
(`span_committee_mono_lo`, `lo ≤ es+1`). -/
theorem bwin_of_bbad_or_spent {v₀ : ValidatorIndex} {n₀ : ℕ} {b' : Root} {lo es σ : Slot}
    (hlo : lo ≤ es + 1) (hes : es ≤ σ) {i : ValidatorIndex}
    (hi : i ∈ E.BbadSet cfg ext v₀ n₀ b' lo es ∨ i ∈ E.SpentSet es σ) :
    i ∈ E.Bwin lo σ := by
  simp only [Execution.Bwin, Finset.mem_filter]
  rcases hi with hb | hs
  · simp only [Execution.BbadSet, Finset.mem_filter] at hb
    exact ⟨E.span_committee_mono lo hes hb.1.1, hb.1.2⟩
  · simp only [Execution.SpentSet, Finset.mem_filter] at hs
    exact ⟨span_committee_mono_lo hlo hs.1, hs.2⟩

/-- **`hByz` core (confirm-margin `Bwin` shape).** A byz supporter of a filtered sibling
`c'` of the `b`-side child `c` at `(w, m)` lands in the window byz set `Bwin lo σ`. Composes
`ByzVpre.byz_sibling_confinement` (byz sibling supporter `∈ BbadSet lo es ∪ SpentSet es σ`)
with `bwin_of_bbad_or_spent`. The `hByz` field of `AnchorClose.ForkEdgeConfirmMarginSupply`
in `Bwin` shape (vs. the v2 `BbadSet ∪ SpentSet`). -/
theorem byz_confinement_bwin
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo es σ : Slot}
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hloes : lo ≤ es + 1) (hes : es ≤ σ)
    (hσcur : get_current_slot cfg (E.store cfg ext w m) - 1 ≤ σ)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hib : i ∉ E.honest) :
    i ∈ E.Bwin lo σ :=
  E.bwin_of_bbad_or_spent cfg ext hloes hes
    (E.byz_sibling_confinement cfg ext hprov hwf hwalkK hb hc hc' hh hpc hpc' hne hbc hlo hσcur
      hlmknown hi_supp hib)

/-! ## Section 2 — `hHon`: honest sibling supporters land in `Xclass w m b lo σ` -/

/-- **`hHon` core (confirm-margin `Xclass` shape).** At the fork-contest window end
`σ = get_current_slot (store w m) − 1`, an honest supporter of a filtered sibling `c'` of the
`b`-side child `c` lands in `Xclass w m b lo σ`. This is `Confinement.honest_sibling_confinement`
at its base cutoff `es := σ`: with `σ` the endpoint's own `current − 1`, the recorded
newest-by-`σ` message *is* the ground newest-by-`σ` vote, so `siblings_incompatible` confines
the supporter to `Xclass … σ` with **no** `es → σ` migration. The `hHon` field of
`AnchorClose.ForkEdgeConfirmMarginSupply` at the pinned `σ`. -/
theorem honest_confinement_xclass
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg (E.store cfg ext w m))
      (E.store cfg ext w m))
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    {bs : BeaconState Root} {b h c c' : Root} {lo σ : Slot}
    (hσ : σ = get_current_slot cfg (E.store cfg ext w m) - 1)
    (hb : b ∈ (E.store cfg ext w m).block_roots)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hc' : c' ∈ (E.store cfg ext w m).block_roots)
    (hh : h ∈ (E.store cfg ext w m).block_roots)
    (hpc : ((E.store cfg ext w m).blocks c).parent_root = h)
    (hpc' : ((E.store cfg ext w m).blocks c').parent_root = h)
    (hne : c ≠ c')
    (hbc : is_ancestor (E.store cfg ext w m) (get_node_for_root b) (get_node_for_root c) = true)
    (hlo : lo ≤ ((E.store cfg ext w m).blocks c').slot)
    (hlmknown : ∀ (lm : LatestMessage Root) (i : ValidatorIndex),
      (E.store cfg ext w m).latest_messages i = some lm →
        lm.root ∈ (E.store cfg ext w m).block_roots)
    (hdom : E.RecordedEpochMax cfg ext w m σ)
    {i : ValidatorIndex}
    (hi_supp : i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c') bs)
    (hih : i ∈ E.honest) :
    i ∈ E.Xclass cfg ext w m b lo σ :=
  E.honest_sibling_confinement cfg ext hhb hec hgen hprov hwf hwalkK hσ hb hc hc' hh hpc hpc'
    hne hbc hlo hlmknown hdom hi_supp hih

/-! ## Section 3 — `hSmem`: `Sclass` members support the `b`-side child `c` -/

/-- **Vote-descent from head-descent** (the honest-model bridge). The
vote-descent IH that `EngineTransport.recorded_supports_c_of_IH` / `Cruxes.hrec_crux` consume —
every honest `[σ+1, slot_at m)`-vote block descends from `b` at `(w, m)` — follows from the
**head-descent** IH clause (every honest node's head at such a second, viewed at `(w, m)`, descends
from `b`) plus the honest-voting model: an honest vote **is** the validator-spec
`honest_attestation` of the voter's own store (`HonestBehavior.votes_head` + `votes_assigned`),
whose `beacon_block_root` is that store's head
(`Delivery.honest_attestation_data_beacon_block_root`). So the arbitrary-vote quantifier collapses
to the honest node's head at its vote second `jj` (`slot_at jj = t'`), where the
head-descent clause applies directly. The one clock hypothesis `hslot0` (`slot_at 0 ≤ σ+1`, genesis
is the earliest slot) lets `votes_head` fire. The cross-store head transport producing the
head-descent clause is supplied by the shell head-safety IH plus one block relay, once per node
rather than per vote — cf. `EngineCore`'s "cross-store head transport" input. -/
theorem voteDescent_of_headDescent (hhb : HonestBehavior cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b : Root} {σ : Slot}
    (hHm : E.WithinHorizon cfg m)
    (hslot0 : E.slot_at cfg 0 ≤ σ + 1)
    (hheadIH : ∀ j ∈ E.honest, ∀ jj : ℕ,
      σ + 1 ≤ E.slot_at cfg jj → E.slot_at cfg jj < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (get_head cfg (E.store cfg ext j jj)).root)
        (get_node_for_root b) = true) :
    ∀ j ∈ E.honest, ∀ t' : Slot, σ + 1 ≤ t' → t' < E.slot_at cfg m →
      ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true := by
  intro j hj t' ht'lo ht'hi jj a' hvote
  have hcs : j ∈ E.committee t' :=
    hhb.votes_assigned j hj t' (by rw [hvote]; exact Option.some_ne_none _)
  have ht'H : E.SlotWithinHorizon cfg t' :=
    E.slotWithinHorizon_of_le cfg (Nat.le_of_lt ht'hi) hHm
  have hs0 : E.slot_at cfg 0 ≤ t' := le_trans hslot0 ht'lo
  obtain ⟨n, index, _hnH, hn, hvh⟩ := hhb.votes_head j hj t' hcs ht'H hs0
  rw [hvote] at hvh
  simp only [Option.some.injEq, Prod.mk.injEq] at hvh
  obtain ⟨-, ha'⟩ := hvh
  rw [ha']
  have hbbr : (honest_attestation cfg ext (E.store cfg ext j n) t' index j).data.beacon_block_root
      = (get_head cfg (E.store cfg ext j n)).root := by
    rw [honest_attestation_data_eq]
    exact honest_attestation_data_beacon_block_root cfg ext (E.store cfg ext j n) t' index
  rw [hbbr]
  exact hheadIH j hj n (by rw [hn]; exact ht'lo) (by rw [hn]; exact ht'hi)

/-- **`hSmem` (confirm-margin shape).** Every `Sclass w m b lo σ` member sits in
`AttSupporters cfg (store w m) (node c) (checkpoint_states justified)` at the endpoint node
`(w, m)`. `Cruxes.hrec_crux` gives the recorded-`c`-support latest message for each `Sclass`
member; `DynamicsClosure.hSmem_of_recorded` wraps in the honest + committee-seat side
conditions (`Sclass ⊆ span_committee`, `mem_AttSupporters_of_honest_committee`) at the
justified balance source (`EdgeDynamics.hval_of_interface`). The `hSmem` field of
`AnchorClose.ForkEdgeConfirmMarginSupply`. Reduces `hSmem` to the `hrec_crux` domain package —
now the **head-descent** engine IH `hheadIH` (the shell's natural head-safety shape) rather than
the raw vote-descent IH, the two bridged by `voteDescent_of_headDescent`;
plus the clock lower bound `hslot0`, ubiquity `hubiq`, and the vote-block/recorded-root
knownness. -/
theorem sclass_subset_attSupporters (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} {m : ℕ} {b c : Root} {lo σ : Slot} (hw : w ∈ E.honest)
    (hHm : E.WithinHorizon cfg m)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hb_wm : b ∈ (E.store cfg ext w m).block_roots)
    (hc_wm : c ∈ (E.store cfg ext w m).block_roots)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hslot0 : E.slot_at cfg 0 ≤ σ + 1)
    (hheadIH : ∀ j ∈ E.honest, ∀ jj : ℕ,
      σ + 1 ≤ E.slot_at cfg jj → E.slot_at cfg jj < E.slot_at cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (get_head cfg (E.store cfg ext j jj)).root)
        (get_node_for_root b) = true)
    (hubiq : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∀ (t : Slot) (kk : ℕ) (a : Attestation Root), E.vote i t = some (kk, a) →
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        compute_epoch_at_slot cfg t ≤ lm.epoch)
    (hbbr_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) → a.data.beacon_block_root ∈ (E.store cfg ext w m).block_roots)
    (hlm_known : ∀ i ∈ E.Sclass cfg ext w m b lo σ, ∀ lm,
      (E.store cfg ext w m).latest_messages i = some lm →
      lm.root ∈ (E.store cfg ext w m).block_roots) :
    ∀ i ∈ E.Sclass cfg ext w m b lo σ,
      i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c)
        ((E.store cfg ext w m).checkpoint_states (E.store cfg ext w m).justified_checkpoint) := by
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := by
    obtain ⟨ast, ablk, hgeq, _⟩ := hgen; exact ⟨ast, ablk, hgeq⟩
  have hIH := E.voteDescent_of_headDescent cfg ext hhb hHm hslot0 hheadIH
  have hval := E.hval_of_interface cfg ext hec hgen0 hji w hw m hHm
  have hbsH := E.justified_balance_source_epoch_lt_horizon cfg ext hec hji hdiv hgen0
    w hw m hHm
  have hrec := E.hrec_crux cfg ext (hmH := hHm) ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
    hw hb_wm hc_wm hbc_wm hIH hubiq hbbr_known hlm_known
  exact E.hSmem_of_recorded cfg ext (hw := hw) (hmH := hHm) hhb hec hsv hgen0 w m w m b c lo σ
    hval hbsH hσH hrec

end Execution

end FastConfirmation.Spec
