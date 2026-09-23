module
public import FastConfirmationProofs.Checkpoints.AnchorChainSafety
public import FastConfirmationProofs.Execution.Delivery.MarginProducer
public import FastConfirmationInternal.FCRRule.SelectedMargin

@[expose] public section

/-!
# Minimal coherence domain for strict selected-result safety

The strict selected-result theorems use the two-field selected margin domain
defined in `FastConfirmationInternal.FCRRule.SelectedMargin`.

The exact `find_latest_confirmed_descendant` path does not consume the broad
Casper/LMD conclusions bundled by `JustificationInterface`.  Its local
fork-choice plumbing needs only two model-coherence facts:

* the store's justified root is a known block (so the totalized `get_head`
  fallback is in-domain), and
* the store's justified checkpoint state is cached (so endpoint score reads
  use the actual validator registry).

This module proves the strict selected-result path over precisely that
two-field domain plus the lower execution, behavior, synchrony, and economic
assumptions.  The legacy `SpecAssumptions` theorems remain unchanged.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The registry seed only needs the store-equality component of the trusted
genesis initialization. -/
theorem SelectedMarginAssumptions.genesis_store
    (hA : SelectedMarginAssumptions cfg ext E) :
    ∃ (anchor_state : BeaconState Root) (anchor_block : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchor_state anchor_block := by
  obtain ⟨anchor_state, anchor_block, hstore, _, _⟩ := hA.genesis
  exact ⟨anchor_state, anchor_block, hstore⟩

/-- Compatibility projection: the old broad bundle implies the strict local
bundle, but none of the reverse (and in particular none of the circular
ancestry/head fields) is required. -/
theorem SpecAssumptions.toSelectedMarginAssumptions {E : Execution Root}
    (hSA : SpecAssumptions cfg ext E) (hpayload : PayloadEnvelopeRelay cfg ext E) :
    SelectedMarginAssumptions cfg ext E := by
  obtain ⟨hgen, hwf, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  exact ⟨hgen, hwf, hdiv, hhb,
    hsync.toPaperSafetySynchrony cfg ext hpayload.1 hpayload.2, hec, hsv, hbb,
    ⟨fun w hw m _hH => (hji.checkpoint_known w hw m).1,
      hji.justified_checkpoint_cached⟩⟩

private theorem exists_mem_of_map_sum_pos_minimal {Alpha : Type*}
    (l : List Alpha) (f : Alpha → ℕ) (h : 0 < (l.map f).sum) :
    ∃ x ∈ l, 0 < f x := by
  induction l with
  | nil => simp at h
  | cons a rest ih =>
      rw [List.map_cons, List.sum_cons] at h
      rcases Nat.eq_zero_or_pos (f a) with ha | ha
      · rw [ha, Nat.zero_add] at h
        obtain ⟨x, hx, hpos⟩ := ih h
        exact ⟨x, List.mem_cons_of_mem a hx, hpos⟩
      · exact ⟨a, List.mem_cons_self, ha⟩

private theorem honest_weight_pos_minimal {H maximum boost discount : ℕ}
    (hmain : 2 * H + discount ≥ maximum + boost + 1)
    (hdiscount : discount ≤ maximum) : 0 < H := by
  omega

omit [LinearOrder Root] [Inhabited Root] in
private theorem chain_member_slot_gt_terminal_minimal {store : Store Root}
    (hwf : ParentSlotLt store) :
    ∀ {roots : List Root},
      List.IsChain (fun a b => (store.blocks b).parent_root = a) roots →
      (∀ r ∈ roots, r ∈ store.block_roots) →
      ∀ {terminal : Root}, terminal ∈ store.block_roots →
      (∀ r, roots.head? = some r → (store.blocks r).parent_root = terminal) →
      ∀ r ∈ roots, (store.blocks terminal).slot < (store.blocks r).slot := by
  intro roots hchain
  induction hchain with
  | nil => intro _ terminal _ _ r hr; simp at hr
  | singleton a =>
      intro hmem terminal ht hhead r hr
      rw [List.mem_singleton] at hr
      subst r
      have hpa := hhead a rfl
      have hpMem : (store.blocks a).parent_root ∈ store.block_roots := by
        rw [hpa]
        exact ht
      have hlt := hwf a (hmem a (by simp)) hpMem
      rw [hpa] at hlt
      exact hlt
  | @cons_cons a d rest hparent _ ih =>
      intro hmem terminal ht hhead r hr
      have ha : a ∈ store.block_roots := hmem a (by simp)
      have hta : (store.blocks terminal).slot < (store.blocks a).slot := by
        have hpa := hhead a rfl
        have hpMem : (store.blocks a).parent_root ∈ store.block_roots := by
          rw [hpa]
          exact ht
        have hlt := hwf a ha hpMem
        rw [hpa] at hlt
        exact hlt
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hta
      · have hmem' : ∀ x ∈ d :: rest, x ∈ store.block_roots :=
          fun x hx => hmem x (List.mem_cons_of_mem a hx)
        have hhead' : ∀ x, (d :: rest).head? = some x →
            (store.blocks x).parent_root = a := by
          intro x hx
          rw [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact hparent
        exact hta.trans (ih hmem' ha hhead' r hr)

namespace Execution

variable (E : Execution Root)

/-- `StoreDomainK` from the local justified-root knownness fact. -/
theorem store_domainK_of_selectedMarginDomain
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (hdom : SelectedMarginDomain cfg ext E) :
    E.StoreDomainK cfg ext := by
  intro w hw m _hH
  exact ⟨E.store_parentSlotLt cfg ext hwf hec hgen
      hwf.anchor_parent_unscheduled w m,
    E.store_walkKnownK cfg ext hwf hec hgen w m,
    hdom.justified_root_known w hw m _hH⟩

/-- `get_head` is known using only the local justified-root fallback fact. -/
theorem head_root_known_of_selectedMarginDomain
    (hdom : SelectedMarginDomain cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m) :
    (get_head cfg (E.store cfg ext w m)).root ∈
      (E.store cfg ext w m).block_roots := by
  rcases get_head_root_mem_or cfg (E.store cfg ext w m) with h | h
  · exact h
  · rw [h]
    exact hdom.justified_root_known w hw m hH

/-- Endpoint registry identity from the local justified-cache fact. -/
theorem hval_of_selectedMarginDomain
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hdom : SelectedMarginDomain cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m) :
    ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint).validators = E.registry :=
  (E.registryConstant cfg ext hec hgen w hw m).2 _
    (hdom.justified_checkpoint_cached w hw m hH)

/-- Time-parametric strong-induction shell.  Unlike the legacy helper, its
cutoff is `n` itself rather than definitionally `k + 1`, which is required for
arbitrary in-slot invocations (including `n = 0`). -/
theorem safeFrom_of_headStep_at {b : Root} {n : ℕ}
    (hstep : ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
      E.WithinHorizon cfg m →
      (∀ w' ∈ E.honest, ∀ m' : ℕ, n ≤ m' →
        E.slot_at cfg m' < E.slot_at cfg m →
        E.WithinHorizon cfg m' →
        is_ancestor (E.store cfg ext w' m') (get_head cfg (E.store cfg ext w' m'))
          (get_node_for_root b) = true) →
      is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true) :
    E.SafeFrom cfg ext b n := by
  refine E.safeFrom_of_engineInv cfg ext ?_
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro w hw m hm hmk hH
    by_cases hlt : E.slot_at cfg m < k
    · exact IH (E.slot_at cfg m) hlt w hw m hm (le_refl _) hH
    · have hIH : ∀ w' ∈ E.honest, ∀ m' : ℕ, n ≤ m' →
          E.slot_at cfg m' < E.slot_at cfg m →
          E.WithinHorizon cfg m' →
          is_ancestor (E.store cfg ext w' m')
            (get_head cfg (E.store cfg ext w' m'))
            (get_node_for_root b) = true :=
        fun w' hw' m' hm' hlt' hH' =>
          IH (E.slot_at cfg m') (lt_of_lt_of_le hlt' hmk)
            w' hw' m' hm' (le_refl _) hH'
      exact hstep w hw m hm hH hIH

/-! ## Selected-candidate same-slot provenance over the minimal bundle -/

/-- A successful concrete confirmation exposes an honest recorded supporter.
This part uses only the lower execution/economic assumptions. -/
theorem honestSupporter_of_confirmed_known_at_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b : Root)
    (hH : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true) :
    ∃ (i : ValidatorIndex) (lm : LatestMessage Root), i ∈ E.honest ∧
      (E.store cfg ext v n).latest_messages i = some lm ∧
      is_ancestor (E.store cfg ext v n)
        (get_supported_node (E.store cfg ext v n) lm)
        (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  set c := fcrStore.current_epoch_observed_justified_checkpoint
  set bs := get_current_balance_source fcrStore
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true := by
    have ht := hconf
    rw [hstore] at ht
    exact ht
  have hbseq : bs = (E.store cfg ext v n).checkpoint_states c := by
    simp only [bs, c, get_current_balance_source]
    rw [hstore]
  have hkey : c ∈ (E.store cfg ext v n).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen0 v n c b
    rw [← hbseq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbseq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen0
      v hv n).2 c hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbseq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence (hdiv := hA.whole_seconds) v hv n c hkey hH
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen0 v n (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v n] at hprov
  have hwf : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hroot⟩ hA.wellFormed.anchor_parent_unscheduled
      v n
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hroot⟩ v n
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ :=
      E.latestMessageProvenance cfg ext hA.wellFormed hA.externals_coherence
        hgen0 v n (by assumption) (by assumption) i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hbslot : ((E.store cfg ext v n).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v n) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v n b hb
  have hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v n).blocks b).slot := by
    apply E.slotWithinHorizon_of_le cfg
    · rw [E.store_current_slot cfg ext v n] at hbslot
      exact hbslot
    · exact hH
  have hstart : ((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1 ≤
      ((E.store cfg ext v n).blocks b).slot :=
    Nat.succ_le_iff.mpr (hwf b hb hparent)
  have hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v n).blocks
        ((E.store cfg ext v n).blocks b).parent_root).slot + 1) :=
    ⟨hstart.trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hstart) hbH.2⟩
  have hsm := honest_support_majority cfg ext hA.honest_behavior
    hA.externals_coherence hA.byzantine_bound hgen0 hv
    (n := n) hH hwf hbH hval htab hprov hconf' hwalk
  have hne : ∀ i ∈ (E.store cfg ext v n).equivocating_indices,
      i ∉ E.honest := fun i hi hih =>
    E.honest_not_equivocating cfg ext hA.honest_behavior
      hA.externals_coherence hgen0 hih v n (by assumption) (by assumption) hi
  have hdisc := support_discount_le_parent_stuck cfg ext hA.externals_coherence
    hA.byzantine_bound hv hH hval hstartH hbH htab hne
  have hsub : ParentStuck cfg E (E.store cfg ext v n) bs b ⊆
      E.span_committee
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v n).blocks b).slot - 1) := by
    simp only [ParentStuck, ParentSupport]
    exact (Finset.filter_subset _ _).trans
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hmono := E.span_committee_mono
    (((E.store cfg ext v n).blocks
      ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
    (Nat.sub_le_sub_right hbslot 1)
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n)) := by
    rw [E.store_current_slot cfg ext v n]
    exact ⟨hH.2.1, hH.2.2⟩
  have hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v n) - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  have hdle : get_support_discount cfg ext (E.store cfg ext v n) bs b ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
        (((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks b).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v n) - 1) := by
    refine le_trans hdisc (le_trans (E.weight_mono hsub)
      (le_trans (E.weight_mono hmono) (le_trans
        (hA.byzantine_bound.estimate_sound _ _ hstartH hendH) (le_of_eq ?_))))
    rw [htab]
  have hpos : 0 < (((AttSupporters cfg (E.store cfg ext v n)
      (get_node_for_root b) bs).filter (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum := by
    exact honest_weight_pos_minimal hsm hdle
  obtain ⟨i, hi, _⟩ := exists_mem_of_map_sum_pos_minimal _ _ hpos
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨hiAtt, hiHon⟩ := hi
  obtain ⟨lm, hlm, _, hsupp⟩ := mem_AttSupporters cfg hiAtt
  exact ⟨i, lm, hiHon, hlm, hsupp⟩

/-- An honest recorded supporter unwinds to a known head in a strictly
earlier honest voting store, using only justified-root fallback knownness. -/
theorem past_descendant_of_honest_supporter_known_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (hH : E.WithinHorizon cfg n)
    (i : ValidatorIndex) (hi : i ∈ E.honest) (lm : LatestMessage Root)
    (hlm : (E.store cfg ext v n).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext v n)
      (get_supported_node (E.store cfg ext v n) lm) (get_node_for_root b) = true) :
    ∃ (u : ValidatorIndex) (nu : ℕ) (d : Root),
      u ∈ E.honest ∧ E.WithinHorizon cfg nu ∧
      E.slot_at cfg nu < E.slot_at cfg n ∧
      d ∈ (E.store cfg ext u nu).block_roots ∧
      is_ancestor (E.store cfg ext v n)
        (get_node_for_root d) (get_node_for_root b) = true := by
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hA.genesis
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hA.whole_seconds ast ablk] at ht
    rw [← ht, hslot]
  obtain ⟨a', sender, sentAt, ifb, hsched, hiatt, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen0 v n i lm hlm
  obtain ⟨voteAt, own, hvote, hdata⟩ :=
    hA.honest_behavior.no_forgery sender sentAt a' ifb hsched i hi hiatt
  set s := a'.data.slot
  have hcomm : i ∈ E.committee s :=
    hA.honest_behavior.votes_assigned i hi s
      (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨ap, _hiap, _htarget, _hbbrap, hapEpoch, hapBound, hapComm,
      hlmKnown, hlmSlot⟩ :=
    E.latestMessageProvenance cfg ext hA.wellFormed hA.externals_coherence
      hgen0 v n hv hH i lm hlm
  have hepoch : compute_epoch_at_slot cfg s =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, hapEpoch]
  have hsap : s = ap.data.slot :=
    hA.externals_coherence.committee_assignment_unique i s ap.data.slot
      hcomm hapComm hepoch
  have hslt : s < E.slot_at cfg n := by
    rw [hsap]
    exact Nat.lt_of_succ_le hapBound
  have hanchorle : ablk.message.slot ≤
      ((E.store cfg ext v n).blocks lm.root).slot :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hslot hroot v n lm.root hlmKnown
  have hs0 : E.slot_at cfg 0 ≤ s := by
    rw [hcur0, hsap]
    exact hanchorle.trans hlmSlot.1
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hslt) hH
  obtain ⟨nu, index, hHnu, hnu, hvoteHead⟩ :=
    hA.honest_behavior.votes_head i hi s hcomm hsH hs0
  rw [hvoteHead] at hvote
  simp only [Option.some.injEq, Prod.mk.injEq] at hvote
  obtain ⟨_, hown⟩ := hvote
  have hrootEq : own.data.beacon_block_root = lm.root := by
    rw [← hdata]
    exact hbbr
  have hhead : (get_head cfg (E.store cfg ext i nu)).root = lm.root := by
    rw [← hrootEq, ← hown]
    rfl
  have hd : lm.root ∈ (E.store cfg ext i nu).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext i nu) with hmem | heq
    · rw [← hhead]
      exact hmem
    · rw [← hhead, heq]
      exact hA.domain.justified_root_known i hi nu hHnu
  refine ⟨i, nu, lm.root, hi, hHnu, ?_, hd, ?_⟩
  · rw [hnu]
    exact hslt
  · simpa only [get_node_for_root, is_ancestor_supported_pending] using hsupp

theorem mem_of_known_honest_past_descendant_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hHnu : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg n)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hanc : is_ancestor (E.store cfg ext v n)
      (get_node_for_root d) (get_node_for_root b) = true) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  set rb := ((E.store cfg ext v n).blocks b).slot
  have hgateUV : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (n + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ n))
  have hsub : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v n).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hHnu hr v hv n hHn hgateUV
  have hagree : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext v n).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext v n) hr (hsub hr)
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hpsl : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen'
      hA.wellFormed.anchor_parent_unscheduled u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence hgen' u nu
      ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  have hbound : ablk.message.slot ≤ rb :=
    E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
      hgeq hstateSlot hroot v n b hb
  have hwalk : WalkKnown (E.store cfg ext u nu) rb d := hwalk0.mono hbound
  have hvlands : (get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d .pending) rb).root =
      b := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hanc
  have hulands : (get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d .pending) rb).root =
      b := by
    rw [get_ancestor_congr hagree hd hwalk]
    exact hvlands
  have hbu : b ∈ (E.store cfg ext u nu).block_roots := by
    have hspec := (get_ancestor_spec hpsl hwalk).1
    rw [hulands] at hspec
    exact hspec
  have hgateUW : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    hslot.trans_le (hnm.trans (E.slot_at_mono cfg (Nat.le_succ m)))
  exact hA.synchrony.block_relay u hu nu b hHnu hbu w hw m hHm hgateUW

theorem ancestry_of_known_honest_past_descendant_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b r₀ : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hr₀ : r₀ ∈ (E.store cfg ext v n).block_roots)
    (hbge : is_ancestor (E.store cfg ext v n)
      (get_node_for_root b) (get_node_for_root r₀) = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (nu : ℕ)
    (hHnu : E.WithinHorizon cfg nu) (d : Root)
    (hslot : E.slot_at cfg nu < E.slot_at cfg n)
    (hd : d ∈ (E.store cfg ext u nu).block_roots)
    (hdb : is_ancestor (E.store cfg ext v n)
      (get_node_for_root d) (get_node_for_root b) = true) :
    r₀ ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r₀) = true := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hgateUV : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (n + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ n))
  have hsubUV : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v n).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hHnu hr v hv n hHn hgateUV
  have hagreeUV : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext v n).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext v n) hr (hsubUV hr)
  have hdv : d ∈ (E.store cfg ext v n).block_roots := hsubUV hd
  have hwfv : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen'
      hA.wellFormed.anchor_parent_unscheduled v n
  have hwalkv := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen' v n
  have hdr₀ : is_ancestor (E.store cfg ext v n)
      (get_node_for_root d) (get_node_for_root r₀) = true :=
    is_ancestor_trans (a := get_node_for_root d) (b := get_node_for_root b)
        (c := get_node_for_root r₀) hwfv (hwalkv r₀ hr₀ d hdv) (hwalkv r₀ hr₀ b hb) hdb hbge
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hwfu : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen'
      hA.wellFormed.anchor_parent_unscheduled u nu
  have hwalku := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen' u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hA.wellFormed hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := hwalku ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  have recover (x : Root) (hx : x ∈ (E.store cfg ext v n).block_roots)
      (hdx : is_ancestor (E.store cfg ext v n)
        (get_node_for_root d) (get_node_for_root x) = true) :
      x ∈ (E.store cfg ext u nu).block_roots := by
    set sx := ((E.store cfg ext v n).blocks x).slot
    have hbound : ablk.message.slot ≤ sx :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hstateSlot hroot v n x hx
    have hwalkx : WalkKnown (E.store cfg ext u nu) sx d := hwalk0.mono hbound
    have hvlands : (get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d .pending) sx).root =
        x := by
      simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq, sx] using hdx
    have hulands : (get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d .pending) sx).root =
        x := by
      rw [get_ancestor_congr hagreeUV hd hwalkx]
      exact hvlands
    have hspec := (get_ancestor_spec hwfu hwalkx).1
    rw [hulands] at hspec
    exact hspec
  have hbu : b ∈ (E.store cfg ext u nu).block_roots := recover b hb hdb
  have hr₀u : r₀ ∈ (E.store cfg ext u nu).block_roots := recover r₀ hr₀ hdr₀
  have hwalkbr : WalkKnown (E.store cfg ext u nu)
      ((E.store cfg ext u nu).blocks r₀).slot b := hwalku r₀ hr₀u b hbu
  have hbgeu : is_ancestor (E.store cfg ext u nu)
      (get_node_for_root b) (get_node_for_root r₀) = true := by
    simp only [get_node_for_root]
    rw [is_ancestor_congr hagreeUV hbu hr₀u hwalkbr]
    simpa only [get_node_for_root] using hbge
  have hgateUW : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    hslot.trans_le (hnm.trans (E.slot_at_mono cfg (Nat.le_succ m)))
  have hsubUW : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext w m).block_roots := fun r hr =>
    hA.synchrony.block_relay u hu nu r hHnu hr w hw m hHm hgateUW
  have hagreeUW : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext w m).blocks r :=
    fun r hr => hA.wellFormed.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext w m) hr (hsubUW hr)
  refine ⟨hsubUW hr₀u, hsubUW hbu, ?_⟩
  simp only [get_node_for_root] at hbgeu ⊢
  rwa [← is_ancestor_congr hagreeUW hbu hr₀u hwalkbr]

/-- A concretely confirmed candidate is known at every honest endpoint whose
slot is not before the arbitrary selecting slot.  This includes the selecting
slot's first second even when the query occurs later in that slot. -/
theorem confirmed_known_at_all_honest_endpoints_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv n
      fcrStore hstore b hHn hb hparent hconf
  obtain ⟨u, nu, d, hu, hHnu, hslot, hd, hanc⟩ :=
    E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
      v hv n b hHn i hi lm hlm hsupp
  exact E.mem_of_known_honest_past_descendant_minimal cfg ext hA
    v hv n b hHn hb w hw m hnm hHm u hu nu hHnu d hslot hd hanc

/-- The same arbitrary-time transport preserves a known selected/base
ancestry pair, not merely selected-root membership. -/
theorem confirmed_ancestry_at_all_honest_endpoints_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n) (b r₀ : Root)
    (hHn : E.WithinHorizon cfg n)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hparent : ((E.store cfg ext v n).blocks b).parent_root ∈
      (E.store cfg ext v n).block_roots)
    (hr₀ : r₀ ∈ (E.store cfg ext v n).block_roots)
    (hbge : is_ancestor (E.store cfg ext v n)
      (get_node_for_root b) (get_node_for_root r₀) = true)
    (hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hnm : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    r₀ ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r₀) = true := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known_at_minimal cfg ext hA v hv n
      fcrStore hstore b hHn hb hparent hconf
  obtain ⟨u, nu, d, hu, hHnu, hslot, hd, hdb⟩ :=
    E.past_descendant_of_honest_supporter_known_minimal cfg ext hA
      v hv n b hHn i hi lm hlm hsupp
  exact E.ancestry_of_known_honest_past_descendant_minimal cfg ext hA
    v hv n b r₀ hHn hb hr₀ hbge w hw m hnm hHm
      u hu nu hHnu d hslot hd hdb

theorem canonical_member_parent_known_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (base b : Root)
    (hbase : base ∈ (E.store cfg ext v n).block_roots)
    (hmem : b ∈ get_ancestor_roots (E.store cfg ext v n)
      (get_head cfg (E.store cfg ext v n)).root base) :
    b ∈ (E.store cfg ext v n).block_roots ∧
      ((E.store cfg ext v n).blocks b).parent_root ∈
        (E.store cfg ext v n).block_roots := by
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hA.genesis
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hwf : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence hgen'
      hA.wellFormed.anchor_parent_unscheduled v n
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence hgen' v n
  have hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v n) with h | h
    · exact h
    · rw [h]
      exact hA.domain.justified_root_known v hv n hHn
  have hb : b ∈ (E.store cfg ext v n).block_roots :=
    get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hmem
  have hstrict : ((E.store cfg ext v n).blocks base).slot <
      ((E.store cfg ext v n).blocks b).slot :=
    chain_member_slot_gt_terminal_minimal hwf
      (get_ancestor_roots_isChain hwf (hwalkK base hbase _ hhead))
      (fun r hr => get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hr)
      hbase
      (fun r hr => get_ancestor_roots_head? hwf (hwalkK base hbase _ hhead) hr)
      b hmem
  rcases E.store_nonAnchorParentKnown cfg ext hgeq v n b hb with heq | hp
  · subst b
    have hbaseMin :=
      E.store_anchor_min_slot cfg ext hA.wellFormed hA.externals_coherence
        hgeq hstateSlot hroot v n base hbase
    have hanchorRecord := E.store_anchor_block cfg ext hA.wellFormed hgeq v n
      (by
        have h0 : ablk.root ∈ (E.store cfg ext v 0).block_roots := by
          change ablk.root ∈ E.genesis_store.block_roots
          rw [hgeq]
          simp [get_forkchoice_store]
        exact (E.store_storeLE cfg ext v (Nat.zero_le n)).1 h0)
    rw [hanchorRecord] at hstrict
    exact absurd hstrict (not_lt_of_ge hbaseMin)
  · exact ⟨hb, hp⟩

theorem find_latest_confirmed_descendant_selected_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n)
    (lcr : Root) (hlcr : lcr ∈ fcrStore.store.block_roots) :
    find_latest_confirmed_descendant cfg ext fcrStore lcr = lcr ∨
      (is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore)
          (find_latest_confirmed_descendant cfg ext fcrStore lcr) = true ∧
        find_latest_confirmed_descendant cfg ext fcrStore lcr ∈
          fcrStore.store.block_roots ∧
        (fcrStore.store.blocks
            (find_latest_confirmed_descendant cfg ext fcrStore lcr)).parent_root ∈
          fcrStore.store.block_roots) := by
  set P : Root → Prop := fun r => r = lcr ∨
    (is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true ∧
      r ∈ fcrStore.store.block_roots ∧
      (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots)
  have fresh : ∀ (base r : Root), base ∈ fcrStore.store.block_roots →
      r ∈ get_ancestor_roots fcrStore.store (get_head cfg fcrStore.store).root base →
      is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true →
      P r := by
    intro base r hbase hr hconf
    have hbaseE : base ∈ (E.store cfg ext v n).block_roots := by
      simpa only [hstore] using hbase
    have hrE : r ∈ get_ancestor_roots (E.store cfg ext v n)
        (get_head cfg (E.store cfg ext v n)).root base := by
      simpa only [hstore] using hr
    have hp := E.canonical_member_parent_known_minimal cfg ext hA v hv n hHn base r
      hbaseE hrE
    have hp' : r ∈ fcrStore.store.block_roots ∧
        (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots := by
      simpa only [hstore] using hp
    exact Or.inr ⟨hconf, hp'⟩
  have known_of_P : ∀ r, P r → r ∈ fcrStore.store.block_roots := by
    intro r hr
    rcases hr with heq | hright
    · rw [heq]
      exact hlcr
    · exact hright.2.1
  have hprev : ∀ (ce : Epoch) (base acc : Root),
      base ∈ fcrStore.store.block_roots → P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore ce
        (get_ancestor_roots fcrStore.store (get_head cfg fcrStore.store).root base) acc) := by
    intro ce base acc hbase hacc
    rcases prev_epoch_loop_spec cfg ext fcrStore ce
      (get_ancestor_roots fcrStore.store (get_head cfg fcrStore.store).root base) acc with
      heq | ⟨r, hr, heq, hconf⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      exact fresh base r hbase hr hconf
  have htent : ∀ (base acc : Root),
      base ∈ fcrStore.store.block_roots → P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots fcrStore.store (get_head cfg fcrStore.store).root base) acc) := by
    intro base acc hbase hacc
    rcases tentative_loop_spec cfg ext fcrStore
      (get_ancestor_roots fcrStore.store (get_head cfg fcrStore.store).root base) acc with
      heq | ⟨r, hr, heq, hconf⟩
    · rw [heq]
      exact hacc
    · rw [heq]
      exact fresh base r hbase hr hconf
  change P (find_latest_confirmed_descendant cfg ext fcrStore lcr)
  generalize hout : find_latest_confirmed_descendant cfg ext fcrStore lcr = result
  rw [find_latest_confirmed_descendant] at hout
  simp only at hout
  split_ifs at hout with h1 h2 h3 h4 h5 <;>
    subst hout <;>
      first
      | exact Or.inl rfl
      | (have hp := hprev (get_current_store_epoch cfg fcrStore.store)
            lcr lcr hlcr (Or.inl rfl)
         exact htent _ _ (known_of_P _ hp) hp)
      | exact htent _ _ hlcr (Or.inl rfl)
      | exact hprev _ _ _ hlcr (Or.inl rfl)

/-! ## Exact arbitrary-time function bridge -/










/-! ## Growth from `es` -/




/-- Minimal-domain version of the endpoint-anchored full-span third producer.
The broad justification interface is unnecessary: the local cached-justified
state fact supplies the endpoint registry and its horizon bound directly. -/
theorem futureCrossing_descendStep_of_selectedInputs_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc a b : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.FutureCrossingSelectedMarginInputs cfg ext glc a b v q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      v hv q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence v hv q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q) ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v q b hin.block_known
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hSbase := (E.classes_base_transport_honest cfg ext v w q m b
    ((E.store cfg ext v q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hend := E.intraEpochFuture_endpoint_inequality_of_confirmed_window cfg ext
    hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hv hqH
    hwf hval htab hprov hconf hwalk hin.cutoff_eq hslotlt hbcur
    hin.recorded_epoch_max hin.edge_same_epoch hin.es_le_sigma hin.sigma_horizon
    hboost hSbase (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered
    hin.status_margin hbside hend
    hin.sibling_score

/-- Minimal-domain endpoint-anchored producer for a selected edge that itself
crosses an epoch. -/
theorem crossingEdge_descendStep_of_selectedInputs_minimal
    (hA : SelectedMarginAssumptions cfg ext E)
    {glc a b : Root} {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hmH : E.WithinHorizon cfg m)
    {query : FastConfirmationStore Root} {es sigma querySlot : Slot}
    (hin : E.CrossingEdgeSelectedMarginInputs cfg ext glc a b v q w m query
      es sigma querySlot) :
    DescendStep cfg (E.store cfg ext w m)
      (get_filtered_block_tree cfg (E.store cfg ext w m)) a b := by
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  let bs := get_current_balance_source query
  let cp := query.current_epoch_observed_justified_checkpoint
  have hconf : is_one_confirmed cfg ext (E.store cfg ext v q) bs b = true := by
    simpa only [bs, hin.query_store_eq] using hin.confirmation
  have hbsEq : bs = (E.store cfg ext v q).checkpoint_states cp := by
    simp only [bs, cp, get_current_balance_source]
    rw [hin.query_store_eq]
  have hkey : cp ∈ (E.store cfg ext v q).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen v q cp b
    rw [← hbsEq]
    exact hconf
  have hval : bs.validators = E.registry := by
    rw [hbsEq]
    exact (E.registryConstant cfg ext hA.externals_coherence hgen
      v hv q).2 cp hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbsEq]
    exact E.checkpoint_states_total_active_balance cfg ext hA.static_validators
      hA.externals_coherence v hv q cp hkey hqH
        (hdiv := hA.whole_seconds) (hgen := hgen)
  have hbsH : get_current_epoch cfg bs < E.verification_horizon := by
    have hstateSlot := (E.stateSlotsLE cfg ext hA.whole_seconds
      hA.externals_coherence hgen v q).2 cp hkey
    rw [hbsEq]
    exact lt_of_le_of_lt (Nat.div_le_div_right hstateSlot) hqH.2.2
  have hwf : ParentSlotLt (E.store cfg ext v q) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgeq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled v q
  have hprov := E.latestMessageProvenance cfg ext hA.wellFormed
    hA.externals_coherence hgen v q (by assumption) (by assumption)
  rw [← E.store_current_slot cfg ext v q] at hprov
  have hwalkK := E.store_walkKnownK cfg ext hA.wellFormed
    hA.externals_coherence ⟨ast, ablk, hgeq, hslot, hparent⟩ v q
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v q)
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v q).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v q) ((E.store cfg ext v q).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _, _⟩ := hprov i lm hlm
    exact hwalkK b hin.block_known lm.root hlmKnown
  have hslotlt : ((E.store cfg ext v q).blocks
      ((E.store cfg ext v q).blocks b).parent_root).slot <
      ((E.store cfg ext v q).blocks b).slot :=
    hwf b hin.block_known hin.parent_known
  have hbcur : ((E.store cfg ext v q).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v q) :=
    E.store_blocks_slot_le_current cfg ext hA.whole_seconds
      ⟨ast, ablk, hgeq, hslot⟩ v q b hin.block_known
  have hvalEnd := E.hval_of_selectedMarginDomain cfg ext hA.externals_coherence
    hgen hA.domain w hw m hmH
  have hkeyEnd := hA.domain.justified_checkpoint_cached w hw m hmH
  have hstateSlotEnd := (E.stateSlotsLE cfg ext hA.whole_seconds
    hA.externals_coherence hgen w m).2
      (E.store cfg ext w m).justified_checkpoint hkeyEnd
  have hEstH : get_current_epoch cfg ((E.store cfg ext w m).checkpoint_states
      (E.store cfg ext w m).justified_checkpoint) < E.verification_horizon :=
    lt_of_le_of_lt (Nat.div_le_div_right hstateSlotEnd) hmH.2.2
  have hboost : compute_proposer_score cfg bs =
      get_proposer_score cfg (E.store cfg ext w m) := by
    simp only [get_proposer_score]
    refine compute_proposer_score_congr cfg (hval.trans hvalEnd.symm) ?_
    intro i
    rw [hval, hvalEnd]
    exact hA.static_validators.registry_activity_constant i _ _ hbsH hEstH
  have hSbase := (E.classes_base_transport_honest cfg ext v w q m b
    ((E.store cfg ext v q).blocks b).slot es
    hin.support_transport hin.ancestor_transport).1
  have hAX := E.hgrowAX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hxS := E.hgrowX_of_committee_support cfg ext hA.honest_behavior w m b
    ((E.store cfg ext v q).blocks b).slot hin.es_le_sigma hin.committee_support
  have hend := E.crossingEdgeFuture_endpoint_inequality_of_confirmed_window cfg ext
    hA.honest_behavior hA.externals_coherence hA.byzantine_bound hgen hv hqH
    hwf hval htab hprov hconf hwalk hin.cutoff_eq hslotlt hbcur
    hin.recorded_epoch_max hin.edge_crosses hin.es_le_sigma hin.sigma_horizon
    hboost hSbase (by simpa only [bs] using hin.parent_sub_endpoint) hAX hxS
  have hbside := recorded_bside_ge cfg ext hvalEnd hin.selected_recording
  exact E.crossing_ledger_descendStep cfg ext hin.child_filtered
    hin.status_margin hbside hend
    hin.sibling_score



end Execution

end FastConfirmation.Spec

end
