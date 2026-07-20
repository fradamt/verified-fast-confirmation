import FastConfirmation.Spec.Proof.Growth
import FastConfirmation.Spec.Proof.VoterIndex
import FastConfirmation.Spec.Proof.Dominance

/-!
# Spec / Proof / Fresh Producer

The fresh-voter producer and the growth package starting at the confirming
cutoff `es`.  The equality-slot voter-index argument closes the former
`es → es+1` boundary split.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Restricting an endpoint chain fact to an earlier relayed store -/

omit [Inhabited Root] in
/-- If all blocks of `source` occur in `target`, a chain segment `b ⪰ c` known
at `target` can be recovered at `source` once `source` already knows `b` and a
descendant `a ⪰ b`. The source walk starts at its actual trusted-anchor slot
`sa`; the endpoint lower bound extends that walk far enough to land `c` in
`source`. -/
theorem chain_descent_restrict (hwfE : WellFormedExecution E)
    {source target : Store Root} {a b c : Root} {sa : Slot}
    (hsource : BlockProvenance E source) (htarget : BlockProvenance E target)
    (hparent : ∀ r ∈ source.block_roots,
      (source.blocks r).parent_root ∈ source.block_roots →
        (source.blocks (source.blocks r).parent_root).slot < (source.blocks r).slot)
    (hwalkA : ∀ r ∈ source.block_roots, WalkKnown source sa r)
    (hsa_c : sa ≤ (target.blocks c).slot)
    (hsub : source.block_roots ⊆ target.block_roots)
    (ha : a ∈ source.block_roots)
    (hb : b ∈ source.block_roots)
    (hab : is_ancestor source (get_node_for_root a) (get_node_for_root b) = true)
    (hbc : is_ancestor target (get_node_for_root b) (get_node_for_root c) = true) :
    c ∈ source.block_roots ∧
      is_ancestor source (get_node_for_root a) (get_node_for_root c) = true := by
  have hagree : ∀ r ∈ source.block_roots, source.blocks r = target.blocks r :=
    fun r hr => hwfE.blocks_agree hsource htarget hr (hsub hr)
  have hwalk_b_target : WalkKnown source (target.blocks c).slot b :=
    (hwalkA b hb).mono hsa_c
  have hget_target :
      get_ancestor target (ForkChoiceNode.mk b) (target.blocks c).slot =
        ForkChoiceNode.mk c := by
    simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hbc
  have hget_source :
      get_ancestor source (ForkChoiceNode.mk b) (target.blocks c).slot =
        ForkChoiceNode.mk c := by
    rw [get_ancestor_congr hagree hb hwalk_b_target]
    exact hget_target
  have hc_source : c ∈ source.block_roots := by
    have hmem := (get_ancestor_spec hparent hwalk_b_target).1
    rw [hget_source] at hmem
    exact hmem
  have hc_agree : source.blocks c = target.blocks c := hagree c hc_source
  have hbc_source :
      is_ancestor source (get_node_for_root b) (get_node_for_root c) = true := by
    simp only [is_ancestor, get_node_for_root, decide_eq_true_eq]
    rw [hc_agree]
    exact hget_source
  have hwalk_a_c : WalkKnown source (source.blocks c).slot a :=
    (hwalkA a ha).mono (by rwa [hc_agree])
  have hwalk_b_c : WalkKnown source (source.blocks c).slot b := by
    rwa [hc_agree]
  exact ⟨hc_source,
    is_ancestor_trans hparent hwalk_a_c hwalk_b_c hab hbc_source⟩

/-! ## Fresh engine inputs from the confirming cutoff onward -/

/-- For `es ≤ σ'`, every fresh honest voter at slot `σ' + 1` lies in the
head-safety IH range and its whole block store relays to the endpoint `(w,m)`.
The IH gives `head ⪰ glc` at the voting store; selected-root knownness and
`chain_descent_restrict` recover the endpoint segment `glc ⪰ c` there under
the actual trusted-anchor walk, yielding exactly `FreshEngineInputs` for
subject `c` at `(w,m)`.

At the boundary `σ' = es`, the strict slot advance `slot_at n < slot_at (n+1)`
ensures the voting second is still at least `n+1`; this is the equality case of
`voter_index_bound`.  The geometry is `slot_at (n+1) = es+1`, `es ≤ σ'`, and
`σ'+1 ≤ σ < slot_at m`. -/
theorem freshEngineInputs_of_IH (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n m : ℕ} {glc c : Root}
    {lo es σ σ' : Slot}
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1))
    (hes : es ≤ σ') (hσ' : σ' + 1 ≤ σ) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' → glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m')
          (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.FreshEngineInputs cfg ext w m c lo σ' := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  intro i hi nᵢ hslotᵢ
  have hi_honest : i ∈ E.honest := (Finset.mem_filter.mp hi).2
  have hni_lower : n + 1 ≤ nᵢ :=
    E.voter_index_bound cfg hslotᵢ hn hadvance hes
  have hni_lt_m : E.slot_at cfg nᵢ < E.slot_at cfg m := by
    rw [hslotᵢ]
    exact lt_of_le_of_lt hσ' hσm
  have hni_lt_index : nᵢ < m := by
    apply Nat.lt_of_not_ge
    intro hmni
    exact (Nat.not_le_of_gt hni_lt_m) (E.slot_at_mono cfg hmni)
  have hHni : E.WithinHorizon cfg nᵢ :=
    E.withinHorizon_mono cfg (Nat.le_of_lt hni_lt_index) hHm
  have hhead_glc : is_ancestor (E.store cfg ext i nᵢ)
      (get_head cfg (E.store cfg ext i nᵢ)) (get_node_for_root glc) = true :=
    hIH i hi_honest nᵢ hni_lower hni_lt_m
  have hglcᵢ : glc ∈ (E.store cfg ext i nᵢ).block_roots :=
    hglcKnown i hi_honest nᵢ hni_lower hHni
  have hgate : E.slot_at cfg nᵢ + 1 ≤ E.slot_at cfg (m + 1) :=
    le_trans (Nat.succ_le_of_lt hni_lt_m) (E.slot_at_mono cfg (Nat.le_succ m))
  have hsub : (E.store cfg ext i nᵢ).block_roots ⊆
      (E.store cfg ext w m).block_roots :=
    E.blockRoots_subset_of_relay cfg ext hsync hi_honest hw hHni hHm hgate
  obtain ⟨hparentᵢ, hwalkK, _hjust⟩ :=
    E.store_domainK cfg ext hwfE hec hgen' hji i hi_honest nᵢ hHni
  have hhead : (get_head cfg (E.store cfg ext i nᵢ)).root ∈
      (E.store cfg ext i nᵢ).block_roots :=
    E.head_root_known cfg ext hji hi_honest nᵢ hHni
  have hanchor_mem0 : ablk.root ∈ E.genesis_store.block_roots := by
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor_mem : ablk.root ∈ (E.store cfg ext i nᵢ).block_roots :=
    (E.store_storeLE cfg ext i (Nat.zero_le nᵢ)).1 hanchor_mem0
  have hanchor_slot : ((E.store cfg ext i nᵢ).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq i nᵢ hanchor_mem]
  have hwalkA : ∀ r ∈ (E.store cfg ext i nᵢ).block_roots,
      WalkKnown (E.store cfg ext i nᵢ) ablk.message.slot r := by
    intro r hr
    have hwalk := hwalkK ablk.root hanchor_mem r hr
    rwa [hanchor_slot] at hwalk
  have hanchor_le_c : ablk.message.slot ≤
      ((E.store cfg ext w m).blocks c).slot :=
    E.store_anchor_min_slot cfg ext hwfE hec hgeq hslot hparent w m c hc
  obtain ⟨hcᵢ, hhead_c⟩ := E.chain_descent_restrict hwfE
    (E.blockProvenance cfg ext i nᵢ) (E.blockProvenance cfg ext w m)
    hparentᵢ hwalkA hanchor_le_c hsub hhead hglcᵢ hhead_glc hchain
  exact ⟨hhead_c, hsub, hcᵢ, hwalkK c hcᵢ _ hhead⟩

/-! ## Growth from `es` -/

/-- Honest-support growth on `[es, σ]`, including the first step `es → es+1`.
The equality-slot voter-index case supplies that boundary from the shell IH. -/
theorem hgrowS_of_IH (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n m : ℕ} {glc c : Root}
    {lo es σ : Slot}
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1))
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hs0 : E.slot_at cfg 0 ≤ es) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' → glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m')
          (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.Sval cfg ext w m c lo es +
        (E.Jspec lo σ - E.Jspec lo es) ≤
      E.Sval cfg ext w m c lo σ := by
  have hSA' := hSA
  obtain ⟨_hgen, hwfE, _hdiv, hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA'
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hσm) hHm
  refine E.hgrowS_of_engine cfg ext hhb hec hwfE w m c lo
    hlo hbase hσH hs0 hsame (fun σ' hlow hhigh => ?_)
  exact E.freshEngineInputs_of_IH cfg ext hSA hw hn hadvance
    hlow (Nat.succ_le_of_lt hhigh) hσm hHm hc hchain hglcKnown hIH

/-- Sibling-stuck antitonicity on `[es, σ]`, including the first cutoff step. -/
theorem hgrowX_of_IH (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n m : ℕ} {glc c : Root}
    {lo es σ : Slot}
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1))
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hs0 : E.slot_at cfg 0 ≤ es) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' → glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m')
          (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true) :
    E.Xval cfg ext w m c lo σ ≤ E.Xval cfg ext w m c lo es := by
  have hSA' := hSA
  obtain ⟨_hgen, hwfE, _hdiv, hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA'
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hσm) hHm
  refine E.hgrowX_of_engine cfg ext hhb hec hwfE w m c lo
    hlo hbase hσH hs0 hsame (fun σ' hlow hhigh => ?_)
  exact E.freshEngineInputs_of_IH cfg ext hSA hw hn hadvance
    hlow (Nat.succ_le_of_lt hhigh) hσm hHm hc hchain hglcKnown hIH

/-- The same-epoch aggregate Byzantine budget from `es`. -/
theorem hbudget_sameEpoch_of_IH (hbb : ByzantineBound cfg E)
    (hec : ExternalsCoherence cfg ext E) {lo es σ : Slot}
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hσH : E.SlotWithinHorizon cfg σ)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo) :
    (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold *
        (E.Jspec lo σ - E.Jspec lo es) :=
  E.hbudget_sameEpoch cfg ext hbb hec hlo hbase hσH hsame

/-! ## Complete same-epoch endpoint strip -/

/-- The complete same-epoch endpoint strip from the ordinary confirm-margin
strip at `es`.  Every growth step, including `es → es+1`, is produced from the
shell IH; no separate first-cutoff hypothesis is needed. -/
theorem strip_of_IH (hSA : SpecAssumptions cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n m : ℕ} {glc c : Root}
    {lo es σ : Slot} (boost : ℕ)
    (hn : E.slot_at cfg (n + 1) = es + 1)
    (hadvance : E.slot_at cfg n < E.slot_at cfg (n + 1))
    (hlo : lo ≤ es) (hbase : es ≤ σ)
    (hs0 : E.slot_at cfg 0 ≤ es) (hσm : σ < E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (hsame : ∀ t : Slot, lo ≤ t → t ≤ σ →
      compute_epoch_at_slot cfg t = compute_epoch_at_slot cfg lo)
    (hchain : is_ancestor (E.store cfg ext w m)
      (get_node_for_root glc) (get_node_for_root c) = true)
    (hc : c ∈ (E.store cfg ext w m).block_roots)
    (hglcKnown : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.WithinHorizon cfg m' → glc ∈ (E.store cfg ext w' m').block_roots)
    (hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n + 1 ≤ m' →
      E.slot_at cfg m' < E.slot_at cfg m →
        is_ancestor (E.store cfg ext w' m')
          (get_head cfg (E.store cfg ext w' m')) (get_node_for_root glc) = true)
    (hstrip : E.Xval cfg ext w m c lo es + E.Bval lo es + boost + 1 ≤
      E.Sval cfg ext w m c lo es) :
    E.Xval cfg ext w m c lo σ + E.Bval lo σ + boost + 1 ≤
      E.Sval cfg ext w m c lo σ := by
  have hSA' := hSA
  obtain ⟨_hgen, _hwfE, _hdiv, _hhb, _hsync, hec, _hsv, hbb, _hji⟩ := hSA'
  have hσH : E.SlotWithinHorizon cfg σ :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hσm) hHm
  refine E.bval_strip_window_uniform cfg ext w m c lo es σ boost hstrip
    (E.hgrowS_of_IH cfg ext hSA hw hn hadvance hlo hbase hs0 hσm hHm
      hsame hchain hc hglcKnown hIH)
    (E.hgrowX_of_IH cfg ext hSA hw hn hadvance hlo hbase hs0 hσm hHm
      hsame hchain hc hglcKnown hIH)
    (E.hbudget_sameEpoch_of_IH cfg ext hbb hec hlo hbase hσH hsame)

end Execution

end FastConfirmation.Spec
