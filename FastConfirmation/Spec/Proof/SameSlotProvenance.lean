import FastConfirmation.Spec.Proof.CheckpointDomain
import FastConfirmation.Spec.Proof.HonestWeight
import FastConfirmation.Spec.Proof.Discount
import FastConfirmation.Spec.Proof.AnchorFacade
import FastConfirmation.Spec.Proof.MicroSteps

/-!
# Spec / Proof / SameSlotProvenance

Executable provenance closes the confirmed-block knownness corner once the
block is kept in the concrete canonical-chain domain where the FCR actually
selects it:

* an applied latest message comes from a vote slot strictly before the
  receiving store's current slot (`validate_on_attestation`'s `slot + 1`
  gate);
* a successful confirmation has an honest supporter (the economic bound),
  with no cache-key residual because `CheckpointStatesExact` makes an unkeyed
  balance source the default zero-score state;
* that honest supporter's own head was known in its earlier-slot store; and
* two same-slot block-relay hops transport the confirmed ancestor through that
  earlier store to every honest endpoint.

The parent-known premise below is not an extra protocol assumption.  It is the
executable provenance carried by an actual advance candidate from
`get_ancestor_roots`; keeping it explicit prevents the old over-generalization
to arbitrary roots that merely satisfy the totalized `is_one_confirmed` call.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

private theorem exists_mem_of_map_sum_pos_ss {Alpha : Type*}
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

private theorem honest_weight_pos_ss {H maximum boost discount : ℕ}
    (hmain : 2 * H + discount ≥ maximum + boost + 1)
    (hdiscount : discount ≤ maximum) : 0 < H := by
  omega

omit [LinearOrder Root] [Inhabited Root] in
/-- Every member of a known parent-linked chain lies strictly above its
terminal when the oldest member's parent is that terminal. -/
private theorem chain_member_slot_gt_terminal {store : Store Root}
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

omit [Inhabited Root] in
/-- A strictly positive score exposes a concrete recorded supporter. -/
theorem exists_recorded_supporter_of_score_pos {store : Store Root}
    {node : ForkChoiceNode Root} {state : BeaconState Root}
    (h : 0 < get_attestation_score cfg store node state) :
    ∃ (i : ValidatorIndex) (lm : LatestMessage Root),
      store.latest_messages i = some lm ∧
      is_ancestor store (get_supported_node store lm) node = true := by
  simp only [get_attestation_score] at h
  obtain ⟨i, hi, _⟩ := exists_mem_of_map_sum_pos_ss _ _ h
  rw [List.mem_filter] at hi
  obtain ⟨_, hisupp⟩ := hi
  cases hlm : store.latest_messages i with
  | none => simp only [hlm] at hisupp; contradiction
  | some lm =>
      simp only [hlm, Bool.and_eq_true] at hisupp
      exact ⟨i, lm, hlm, hisupp.2⟩

namespace Execution

variable (E : Execution Root)

/-- A successful confirmation through a concrete cached balance source has an
honest recorded supporter, provided the candidate block and its parent are in
the confirming store.  Both knownness facts are executable canonical-chain
provenance; no genesis-slot specialization is used. -/
theorem honestSupporter_of_confirmed_known
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (hH : E.WithinHorizon cfg (n + 1))
    (hb : b ∈ (E.store cfg ext v (n + 1)).block_roots)
    (hparent : ((E.store cfg ext v (n + 1)).blocks b).parent_root ∈
      (E.store cfg ext v (n + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true) :
    ∃ (i : ValidatorIndex) (lm : LatestMessage Root), i ∈ E.honest ∧
      (E.store cfg ext v (n + 1)).latest_messages i = some lm ∧
      is_ancestor (E.store cfg ext v (n + 1))
        (get_supported_node (E.store cfg ext v (n + 1)) lm)
        (get_node_for_root b) = true := by
  obtain ⟨hgen, hwfE, hdiv, hhb, _hsync, hec, hsv, hbb, _hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  set c := (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
  set bs := get_current_balance_source (E.fcrStep cfg ext v n)
  have hconf' : is_one_confirmed cfg ext (E.store cfg ext v (n + 1)) bs b = true := by
    have ht := hconf
    rw [E.fcrStep_store cfg ext v n] at ht
    exact ht
  have hbseq : bs = (E.store cfg ext v (n + 1)).checkpoint_states c := by
    simp only [bs, c, get_current_balance_source]
    rw [E.fcrStep_store cfg ext v n]
  have hkey : c ∈ (E.store cfg ext v (n + 1)).checkpoint_state_keys := by
    apply E.checkpoint_state_key_of_one_confirmed cfg ext hgen0 v (n + 1) c b
    rw [← hbseq]
    exact hconf'
  have hval : bs.validators = E.registry := by
    rw [hbseq]
    exact (E.registryConstant cfg ext hec hgen0 v (n + 1)).2 c hkey
  have htab : get_total_active_balance cfg bs = E.total_active cfg := by
    rw [hbseq]
    exact E.checkpoint_states_total_active_balance cfg ext hsv hec v (n + 1) c hkey hH
  have hprov := E.latestMessageProvenance cfg ext hwfE hec hgen0 v (n + 1)
  rw [← E.store_current_slot cfg ext v (n + 1)] at hprov
  have hwf : ParentSlotLt (E.store cfg ext v (n + 1)) :=
    E.store_parentSlotLt cfg ext hwfE hec ⟨ast, ablk, hgeq, hslot, hroot⟩
      hwfE.anchor_parent_unscheduled v (n + 1)
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec
    ⟨ast, ablk, hgeq, hslot, hroot⟩ v (n + 1)
  have hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v (n + 1))
      (get_node_for_root b) bs, ∀ lm,
      (E.store cfg ext v (n + 1)).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v (n + 1))
          ((E.store cfg ext v (n + 1)).blocks b).slot lm.root := by
    intro i _ lm hlm
    obtain ⟨_, _, _, _, _, _, _, hlmKnown, _⟩ :=
      E.latestMessageProvenance cfg ext hwfE hec hgen0 v (n + 1) i lm hlm
    exact hwalkK b hb lm.root hlmKnown
  have hbslot : ((E.store cfg ext v (n + 1)).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext v (n + 1)) :=
    E.store_blocks_slot_le_current cfg ext hdiv ⟨ast, ablk, hgeq, hslot⟩
      v (n + 1) b hb
  have hbH : E.SlotWithinHorizon cfg
      ((E.store cfg ext v (n + 1)).blocks b).slot := by
    apply E.slotWithinHorizon_of_le cfg
    · rw [E.store_current_slot cfg ext v (n + 1)] at hbslot
      exact hbslot
    · exact hH
  have hstart : ((E.store cfg ext v (n + 1)).blocks
      ((E.store cfg ext v (n + 1)).blocks b).parent_root).slot + 1 ≤
      ((E.store cfg ext v (n + 1)).blocks b).slot :=
    Nat.succ_le_iff.mpr (hwf b hb hparent)
  have hstartH : E.SlotWithinHorizon cfg
      (((E.store cfg ext v (n + 1)).blocks
        ((E.store cfg ext v (n + 1)).blocks b).parent_root).slot + 1) :=
    ⟨hstart.trans hbH.1,
      lt_of_le_of_lt (Nat.div_le_div_right hstart) hbH.2⟩
  have hsm := honest_support_majority cfg ext hhb hec hbb hgen0 hv
    (n := n + 1) hH hwf hbH hval htab hprov hconf' hwalk
  have hne : ∀ i ∈ (E.store cfg ext v (n + 1)).equivocating_indices,
      i ∉ E.honest := fun i hi hih =>
    E.honest_not_equivocating cfg ext hhb hec hgen0 hih v (n + 1) hi
  have hdisc := support_discount_le_parent_stuck cfg ext hec hbb hv hH hval
    hstartH hbH htab hne
  have hsub : ParentStuck cfg E (E.store cfg ext v (n + 1)) bs b ⊆
      E.span_committee
        (((E.store cfg ext v (n + 1)).blocks
          ((E.store cfg ext v (n + 1)).blocks b).parent_root).slot + 1)
        (((E.store cfg ext v (n + 1)).blocks b).slot - 1) := by
    simp only [ParentStuck, ParentSupport]
    exact (Finset.filter_subset _ _).trans
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hmono := E.span_committee_mono
    (((E.store cfg ext v (n + 1)).blocks
      ((E.store cfg ext v (n + 1)).blocks b).parent_root).slot + 1)
    (Nat.sub_le_sub_right hbslot 1)
  have hcurH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) := by
    rw [E.store_current_slot cfg ext v (n + 1)]
    exact ⟨hH.2.1, hH.2.2⟩
  have hendH : E.SlotWithinHorizon cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1)) - 1) :=
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
  have hdle : get_support_discount cfg ext (E.store cfg ext v (n + 1)) bs b ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
        (((E.store cfg ext v (n + 1)).blocks
          ((E.store cfg ext v (n + 1)).blocks b).parent_root).slot + 1)
        (get_current_slot cfg (E.store cfg ext v (n + 1)) - 1) := by
    refine le_trans hdisc (le_trans (E.weight_mono hsub)
      (le_trans (E.weight_mono hmono) (le_trans
        (hbb.estimate_sound _ _ hstartH hendH) (le_of_eq ?_))))
    rw [htab]
  have hpos : 0 < (((AttSupporters cfg (E.store cfg ext v (n + 1))
      (get_node_for_root b) bs).filter (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum := by
    exact honest_weight_pos_ss hsm hdle
  obtain ⟨i, hi, _⟩ := exists_mem_of_map_sum_pos_ss _ _ hpos
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨hiAtt, hiHon⟩ := hi
  obtain ⟨lm, hlm, _, hsupp⟩ := mem_AttSupporters cfg hiAtt
  exact ⟨i, lm, hiHon, hlm, hsupp⟩

/-! ## An honest recorded supporter voted strictly before the confirming slot -/

/-- An honest supporter recorded at `(v,n)` unwinds to the validator's own
head at a strictly earlier vote slot.  The lower bound required by
`votes_head` comes from the validated message root being known: every known
block is at or above the trusted anchor, and validation says the voted block
is no later than the attestation slot.  Hence this works for checkpoint-sync
anchors as well as genesis starts. -/
theorem past_descendant_of_honest_supporter_known
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (n : ℕ) (b : Root)
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
  obtain ⟨hgen, hwfE, hdiv, hhb, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hroot⟩ := hgen
  have hgen0 : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  have hcur0 : E.slot_at cfg 0 = ablk.message.slot := by
    have ht := E.store_current_slot cfg ext v 0
    rw [show E.store cfg ext v 0 = E.genesis_store from rfl, hgeq,
      get_current_slot_get_forkchoice_store cfg hdiv ast ablk] at ht
    rw [← ht, hslot]
  obtain ⟨a', sender, sentAt, ifb, hsched, hiatt, hbbr, hslotep⟩ :=
    E.schedLMProv cfg ext hgen0 v n i lm hlm
  obtain ⟨voteAt, own, hvote, hdata⟩ :=
    hhb.no_forgery sender sentAt a' ifb hsched i hi hiatt
  set s := a'.data.slot
  have hcomm : i ∈ E.committee s :=
    hhb.votes_assigned i hi s (by rw [hvote]; exact Option.some_ne_none _)
  obtain ⟨ap, _hiap, _htarget, _hbbrap, hapEpoch, hapBound, hapComm,
      hlmKnown, hlmSlot⟩ :=
    E.latestMessageProvenance cfg ext hwfE hec hgen0 v n i lm hlm
  have hepoch : compute_epoch_at_slot cfg s =
      compute_epoch_at_slot cfg ap.data.slot := by
    rw [hslotep, hapEpoch]
  have hsap : s = ap.data.slot :=
    hec.committee_assignment_unique i s ap.data.slot hcomm hapComm hepoch
  have hslt : s < E.slot_at cfg n := by
    rw [hsap]
    exact Nat.lt_of_succ_le hapBound
  have hanchorle : ablk.message.slot ≤
      ((E.store cfg ext v n).blocks lm.root).slot :=
    E.store_anchor_min_slot cfg ext hwfE hec hgeq hslot hroot v n lm.root hlmKnown
  have hs0 : E.slot_at cfg 0 ≤ s := by
    rw [hcur0, hsap]
    exact hanchorle.trans hlmSlot
  have hsH : E.SlotWithinHorizon cfg s :=
    E.slotWithinHorizon_of_le cfg (le_of_lt hslt) hH
  obtain ⟨nu, index, hHnu, hnu, hvoteHead⟩ :=
    hhb.votes_head i hi s hcomm hsH hs0
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
      exact (hji.checkpoint_known i hi nu hHnu).1
  refine ⟨i, nu, lm.root, hi, hHnu, ?_, hd, ?_⟩
  · rw [hnu]
    exact hslt
  · simpa only [get_supported_node, get_node_for_root] using hsupp

/-! ## Earlier-store ancestry transport and same-slot relay -/

/-- If the confirming store knows `b`, an honest earlier-slot store holding a
known descendant `d` can recover `b` by the same parent walk, and relay it to
every honest endpoint at or after the confirmation second.  The target walk's
lower bound comes from `b` being known in the confirming store, so no
genesis-slot assumption is needed. -/
theorem mem_of_known_honest_past_descendant
    (hSA : SpecAssumptions cfg ext E)
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
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  set rb := ((E.store cfg ext v n).blocks b).slot
  have hgateUV : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (n + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ n))
  have hsub : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v n).block_roots := fun r hr =>
    hsync.block_relay u hu nu r hHnu hr v hv n hHn hgateUV
  have hagree : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext v n).blocks r :=
    fun r hr => hwfE.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext v n) hr (hsub hr)
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hpsl : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := E.store_walkKnownK cfg ext hwfE hec hgen' u nu
      ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  have hbound : ablk.message.slot ≤ rb :=
    E.store_anchor_min_slot cfg ext hwfE hec hgeq hstateSlot hroot v n b hb
  have hwalk : WalkKnown (E.store cfg ext u nu) rb d := hwalk0.mono hbound
  have hvlands : get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d) rb =
      ForkChoiceNode.mk b := by
    simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq] using hanc
  have hulands : get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d) rb =
      ForkChoiceNode.mk b := by
    rw [get_ancestor_congr hagree hd hwalk]
    exact hvlands
  have hbu : b ∈ (E.store cfg ext u nu).block_roots := by
    have hspec := (get_ancestor_spec hpsl hwalk).1
    rw [hulands] at hspec
    exact hspec
  have hgateUW : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) :=
    hslot.trans_le (hnm.trans (E.slot_at_mono cfg (Nat.le_succ m)))
  exact hsync.block_relay u hu nu b hHnu hbu w hw m hHm hgateUW

/-- A known ancestor pair on the confirming store's chain can be recovered in
the honest supporter's strictly earlier store and relayed together to every
honest endpoint.  Consequently the ancestry relation, not just membership of
the confirmed block, survives the same-slot transport.

This is the checkpoint-sync-safe form of the old `anchor_ge_of_pastDescendant`
argument: the walk starts at the execution's actual trusted anchor slot rather
than assuming that slot is genesis. -/
theorem ancestry_of_known_honest_past_descendant
    (hSA : SpecAssumptions cfg ext E)
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
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hgateUV : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (n + 1) :=
    hslot.trans_le (E.slot_at_mono cfg (Nat.le_succ n))
  have hsubUV : (E.store cfg ext u nu).block_roots ⊆
      (E.store cfg ext v n).block_roots := fun r hr =>
    hsync.block_relay u hu nu r hHnu hr v hv n hHn hgateUV
  have hagreeUV : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext v n).blocks r :=
    fun r hr => hwfE.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext v n) hr (hsubUV hr)
  have hdv : d ∈ (E.store cfg ext v n).block_roots := hsubUV hd
  have hwfv : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled v n
  have hwalkv := E.store_walkKnownK cfg ext hwfE hec hgen' v n
  have hdr₀ : is_ancestor (E.store cfg ext v n)
      (get_node_for_root d) (get_node_for_root r₀) = true :=
    is_ancestor_trans hwfv (hwalkv r₀ hr₀ d hdv) (hwalkv r₀ hr₀ b hb) hdb hbge
  have hanchor0 : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]
    simp [get_forkchoice_store]
  have hanchor : ablk.root ∈ (E.store cfg ext u nu).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le nu)).1 hanchor0
  have hwfu : ParentSlotLt (E.store cfg ext u nu) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled u nu
  have hwalku := E.store_walkKnownK cfg ext hwfE hec hgen' u nu
  have hanchorSlot : ((E.store cfg ext u nu).blocks ablk.root).slot =
      ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq u nu hanchor]
  have hwalk0 : WalkKnown (E.store cfg ext u nu) ablk.message.slot d := by
    have ht := hwalku ablk.root hanchor d hd
    rwa [hanchorSlot] at ht
  have recover (x : Root) (hx : x ∈ (E.store cfg ext v n).block_roots)
      (hdx : is_ancestor (E.store cfg ext v n)
        (get_node_for_root d) (get_node_for_root x) = true) :
      x ∈ (E.store cfg ext u nu).block_roots := by
    set sx := ((E.store cfg ext v n).blocks x).slot
    have hbound : ablk.message.slot ≤ sx :=
      E.store_anchor_min_slot cfg ext hwfE hec hgeq hstateSlot hroot v n x hx
    have hwalkx : WalkKnown (E.store cfg ext u nu) sx d := hwalk0.mono hbound
    have hvlands : get_ancestor (E.store cfg ext v n) (ForkChoiceNode.mk d) sx =
        ForkChoiceNode.mk x := by
      simpa only [is_ancestor, get_node_for_root, decide_eq_true_eq, sx] using hdx
    have hulands : get_ancestor (E.store cfg ext u nu) (ForkChoiceNode.mk d) sx =
        ForkChoiceNode.mk x := by
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
    hsync.block_relay u hu nu r hHnu hr w hw m hHm hgateUW
  have hagreeUW : ∀ r ∈ (E.store cfg ext u nu).block_roots,
      (E.store cfg ext u nu).blocks r = (E.store cfg ext w m).blocks r :=
    fun r hr => hwfE.blocks_agree (E.blockProvenance cfg ext u nu)
      (E.blockProvenance cfg ext w m) hr (hsubUW hr)
  refine ⟨hsubUW hr₀u, hsubUW hbu, ?_⟩
  simp only [get_node_for_root] at hbgeu ⊢
  rwa [← is_ancestor_congr hagreeUW hbu hr₀u hwalkbr]

/-- Full same-slot knownness composition for a concrete advance candidate:
candidate and parent known at the confirming store, confirmation, honest
support extraction, strict-past vote provenance, and two relay hops.  The
conclusion is slot-ordered: it holds at every honest endpoint whose slot is not
before the confirming slot, including that slot's first second even when its
execution index precedes the query index. -/
theorem confirmed_known_at_all_honest_endpoints
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ) (b : Root)
    (hHk : E.WithinHorizon cfg (k + 1))
    (hb : b ∈ (E.store cfg ext v (k + 1)).block_roots)
    (hparent : ((E.store cfg ext v (k + 1)).blocks b).parent_root ∈
      (E.store cfg ext v (k + 1)).block_roots)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v k).store
      (get_current_balance_source (E.fcrStep cfg ext v k)) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hkm : E.slot_at cfg (k + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known cfg ext hSA v hv k b hHk hb hparent hconf
  obtain ⟨u, nu, d, hu, hHnu, hslot, hd, hanc⟩ :=
    E.past_descendant_of_honest_supporter_known cfg ext hSA v (k + 1) b hHk
      i hi lm hlm hsupp
  exact E.mem_of_known_honest_past_descendant cfg ext hSA v hv (k + 1) b hHk hb
    w hw m hkm hHm u hu nu hHnu d hslot hd hanc

/-- The full selected-candidate transport also preserves a known ancestor
`r₀` of the confirmed block.  This is the concrete replacement for the old
same-slot `HonestPastDescendant` residual used by the closing path. -/
theorem confirmed_ancestry_at_all_honest_endpoints
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ) (b r₀ : Root)
    (hHk : E.WithinHorizon cfg (k + 1))
    (hb : b ∈ (E.store cfg ext v (k + 1)).block_roots)
    (hparent : ((E.store cfg ext v (k + 1)).blocks b).parent_root ∈
      (E.store cfg ext v (k + 1)).block_roots)
    (hr₀ : r₀ ∈ (E.store cfg ext v (k + 1)).block_roots)
    (hbge : is_ancestor (E.store cfg ext v (k + 1))
      (get_node_for_root b) (get_node_for_root r₀) = true)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v k).store
      (get_current_balance_source (E.fcrStep cfg ext v k)) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hkm : E.slot_at cfg (k + 1) ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    r₀ ∈ (E.store cfg ext w m).block_roots ∧
      b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root b) (get_node_for_root r₀) = true := by
  obtain ⟨i, lm, hi, hlm, hsupp⟩ :=
    E.honestSupporter_of_confirmed_known cfg ext hSA v hv k b hHk hb hparent hconf
  obtain ⟨u, nu, d, hu, hHnu, hslot, hd, hdb⟩ :=
    E.past_descendant_of_honest_supporter_known cfg ext hSA v (k + 1) b hHk
      i hi lm hlm hsupp
  exact E.ancestry_of_known_honest_past_descendant cfg ext hSA v hv (k + 1) b r₀
    hHk hb hr₀ hbge w hw m hkm hHm u hu nu hHnu d hslot hd hdb

/-! ## Executable advance-candidate provenance -/

/-- Every member of the executable canonical segment has a known parent.  The
list is terminal-exclusive, so its members sit strictly above the known base;
they therefore cannot be the trusted anchor, and the trajectory's
non-anchor-parent invariant supplies the parent. -/
theorem canonical_member_parent_known
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (base b : Root)
    (hbase : base ∈ (E.store cfg ext v n).block_roots)
    (hmem : b ∈ get_ancestor_roots (E.store cfg ext v n)
      (get_head cfg (E.store cfg ext v n)).root base) :
    b ∈ (E.store cfg ext v n).block_roots ∧
      ((E.store cfg ext v n).blocks b).parent_root ∈
        (E.store cfg ext v n).block_roots := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, _hsync, hec, _hsv, _hbb, hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hstateSlot, hroot⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hstateSlot, hroot⟩
  have hwf : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled v n
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec hgen' v n
  have hhead : (get_head cfg (E.store cfg ext v n)).root ∈
      (E.store cfg ext v n).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v n) with h | h
    · exact h
    · rw [h]
      exact (hji.checkpoint_known v hv n hHn).1
  have hb : b ∈ (E.store cfg ext v n).block_roots :=
    get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hmem
  have hstrict : ((E.store cfg ext v n).blocks base).slot <
      ((E.store cfg ext v n).blocks b).slot :=
    chain_member_slot_gt_terminal hwf
      (get_ancestor_roots_isChain hwf (hwalkK base hbase _ hhead))
      (fun r hr => get_ancestor_roots_mem hwf (hwalkK base hbase _ hhead) hr)
      hbase
      (fun r hr => get_ancestor_roots_head? hwf (hwalkK base hbase _ hhead) hr)
      b hmem
  rcases E.store_nonAnchorParentKnown cfg ext hgeq v n b hb with heq | hp
  · subst b
    have hbaseMin :=
      E.store_anchor_min_slot cfg ext hwfE hec hgeq hstateSlot hroot v n base hbase
    have hanchorRecord := E.store_anchor_block cfg ext hwfE hgeq v n
      (by
        have h0 : ablk.root ∈ (E.store cfg ext v 0).block_roots := by
          change ablk.root ∈ E.genesis_store.block_roots
          rw [hgeq]
          simp [get_forkchoice_store]
        exact (E.store_storeLE cfg ext v (Nat.zero_le n)).1 h0)
    rw [hanchorRecord] at hstrict
    exact absurd hstrict (not_lt_of_ge hbaseMin)
  · exact ⟨hb, hp⟩

/-- Strengthened executable inversion for `find_latest_confirmed_descendant`:
the result is unchanged, or it both passed `is_one_confirmed` and is a known
non-anchor canonical-chain block with a known parent.  This is the provenance
discarded by the older `find_latest_confirmed_descendant_spec`. -/
theorem find_latest_confirmed_descendant_selected
    (hSA : SpecAssumptions cfg ext E)
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
    have hp := E.canonical_member_parent_known cfg ext hSA v hv n hHn base r
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

/-- An actual strict advance selected by `find_latest_confirmed_descendant` is
known at every honest endpoint from the selecting second onward, including
foreign nodes in the very same slot. -/
theorem selected_advance_known_at_all_honest_endpoints
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ)
    (hHk : E.WithinHorizon cfg (k + 1))
    (lcr : Root)
    (hlcr : lcr ∈ (E.fcrStep cfg ext v k).store.block_roots)
    (hadvance : find_latest_confirmed_descendant cfg ext
      (E.fcrStep cfg ext v k) lcr ≠ lcr)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hkm : k + 1 ≤ m) (hHm : E.WithinHorizon cfg m) :
    find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr ∈
      (E.store cfg ext w m).block_roots := by
  rcases E.find_latest_confirmed_descendant_selected cfg ext hSA v hv (k + 1) hHk
      (E.fcrStep cfg ext v k) (E.fcrStep_store cfg ext v k) lcr hlcr with
    heq | ⟨hconf, hb, hparent⟩
  · exact absurd heq hadvance
  · exact E.confirmed_known_at_all_honest_endpoints cfg ext hSA v hv k _ hHk
      (by rwa [E.fcrStep_store cfg ext v k] at hb)
      (by rwa [E.fcrStep_store cfg ext v k] at hparent)
      hconf w hw m (E.slot_at_mono cfg hkm) hHm

/-- Strengthened `get_latest_confirmed` inversion.  The reset cases are the
three executable anchors; the strict-advance case retains confirmation plus
candidate and parent membership instead of erasing them to a bare predicate
over an arbitrary root. -/
theorem get_latest_confirmed_selected
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn : E.WithinHorizon cfg n)
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n)
    (hconfirmed : fcrStore.confirmed_root ∈ fcrStore.store.block_roots)
    (hfinalized : fcrStore.store.finalized_checkpoint.root ∈
      fcrStore.store.block_roots)
    (hobserved : fcrStore.current_epoch_observed_justified_checkpoint.root ∈
      fcrStore.store.block_roots) :
    (get_latest_confirmed cfg ext fcrStore = fcrStore.confirmed_root ∨
      get_latest_confirmed cfg ext fcrStore = fcrStore.store.finalized_checkpoint.root ∨
      get_latest_confirmed cfg ext fcrStore =
        fcrStore.current_epoch_observed_justified_checkpoint.root) ∨
      (is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore)
          (get_latest_confirmed cfg ext fcrStore) = true ∧
        get_latest_confirmed cfg ext fcrStore ∈ fcrStore.store.block_roots ∧
        (fcrStore.store.blocks (get_latest_confirmed cfg ext fcrStore)).parent_root ∈
          fcrStore.store.block_roots) := by
  set Q : Root → Prop := fun r =>
    (r = fcrStore.confirmed_root ∨ r = fcrStore.store.finalized_checkpoint.root ∨
      r = fcrStore.current_epoch_observed_justified_checkpoint.root) ∨
    (is_one_confirmed cfg ext fcrStore.store (get_current_balance_source fcrStore) r = true ∧
      r ∈ fcrStore.store.block_roots ∧
      (fcrStore.store.blocks r).parent_root ∈ fcrStore.store.block_roots)
  have hadv : ∀ lcr : Root,
      (lcr = fcrStore.confirmed_root ∨ lcr = fcrStore.store.finalized_checkpoint.root ∨
        lcr = fcrStore.current_epoch_observed_justified_checkpoint.root) →
      lcr ∈ fcrStore.store.block_roots →
      Q (find_latest_confirmed_descendant cfg ext fcrStore lcr) := by
    intro lcr hkind hlcr
    rcases E.find_latest_confirmed_descendant_selected cfg ext hSA v hv n hHn
      fcrStore hstore lcr hlcr with heq | hselected
    · exact Or.inl (by rw [heq]; exact hkind)
    · exact Or.inr hselected
  change Q (get_latest_confirmed cfg ext fcrStore)
  generalize hout : get_latest_confirmed cfg ext fcrStore = result
  simp only [get_latest_confirmed] at hout
  split_ifs at hout <;>
    subst hout <;>
      first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr (Or.inl rfl))
      | exact Or.inl (Or.inr (Or.inr rfl))
      | exact hadv _ (Or.inl rfl) hconfirmed
      | exact hadv _ (Or.inr (Or.inl rfl)) hfinalized
      | exact hadv _ (Or.inr (Or.inr rfl)) hobserved

/-- The observed-justified reset root selected by `fcrStep` is known at its
update store.  This is the interface fact needed by the selected-result
confirmed-root induction below. -/
theorem fcrStep_observed_known_selected
    (hji : JustificationInterface cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
  have hle : E.slot_at cfg n ≤ E.slot_at cfg (n + 1) := E.slot_at_mono cfg (Nat.le_succ n)
  have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hobsn := hji.observed_checkpoint_known v hv n v hv (n + 1) hHn hHn1 hle
  have hobsn1 := hji.observed_checkpoint_known v hv (n + 1) v hv (n + 1)
    hHn1 hHn1 (le_refl _)
  simp only [Execution.fcrStep, update_fast_confirmation_variables]
  split_ifs <;>
    first
      | exact hobsn1.1
      | exact hobsn.2.1
      | exact hobsn.2.2

/-- Every honest node's executable confirmed root is known in its own store,
without a genesis-start specialization.  The induction retains the concrete
`get_latest_confirmed` selection certificate: reset outputs use their existing
knownness witnesses, while a strict advance is known because it is a member of
the canonical candidate list.  No statement about an arbitrary root satisfying
the totalized confirmation predicate is needed. -/
theorem confirmed_root_known_selected
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) :
    ∀ k : ℕ, E.WithinHorizon cfg k →
      E.confirmed cfg ext v k ∈ (E.store cfg ext v k).block_roots := by
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  intro k
  induction k with
  | zero =>
    intro hH0
    rw [E.confirmed_zero]
    exact (hji.checkpoint_known v hv 0 hH0).2
  | succ n ih =>
    intro hHn1
    have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
    by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)
    · rw [E.confirmed_succ_of_advance cfg ext v n hadv]
      have hconfirmed : (E.fcrStep cfg ext v n).confirmed_root ∈
          (E.fcrStep cfg ext v n).store.block_roots := by
        rw [E.fcrStep_confirmed_root, E.fcrStep_store]
        exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1 (ih hHn)
      have hfinalized : (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
          (E.fcrStep cfg ext v n).store.block_roots := by
        rw [E.fcrStep_store]
        exact (hji.checkpoint_known v hv (n + 1) hHn1).2
      have hobserved :
          (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
            (E.fcrStep cfg ext v n).store.block_roots := by
        rw [E.fcrStep_store]
        exact E.fcrStep_observed_known_selected cfg ext hji v hv n hHn1
      rcases E.get_latest_confirmed_selected cfg ext hSA v hv (n + 1) hHn1
          (E.fcrStep cfg ext v n) (E.fcrStep_store cfg ext v n)
          hconfirmed hfinalized hobserved with hreset | hselected
      · rcases hreset with h | h | h
        · rw [h]
          simpa only [E.fcrStep_store] using hconfirmed
        · rw [h]
          simpa only [E.fcrStep_store] using hfinalized
        · rw [h]
          simpa only [E.fcrStep_store] using hobserved
      · simpa only [E.fcrStep_store] using hselected.2.1
    · rw [E.confirmed_succ_of_no_advance cfg ext v n hadv]
      exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1 (ih hHn)

/-- The three executable reset roots are known in the concrete `fcrStep`
store.  The previous confirmed root comes from the selected-result induction,
the other two from the pinned justification interface. -/
theorem fcrStep_reset_roots_known_selected
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    (E.fcrStep cfg ext v n).confirmed_root ∈
        (E.fcrStep cfg ext v n).store.block_roots ∧
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
        (E.fcrStep cfg ext v n).store.block_roots ∧
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
        (E.fcrStep cfg ext v n).store.block_roots := by
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  refine ⟨?_, ?_, ?_⟩
  · rw [E.fcrStep_confirmed_root, E.fcrStep_store]
    exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1
      (E.confirmed_root_known_selected cfg ext hSA v hv n hHn)
  · rw [E.fcrStep_store]
    exact (hji.checkpoint_known v hv (n + 1) hHn1).2
  · rw [E.fcrStep_store]
    exact E.fcrStep_observed_known_selected cfg ext hji v hv n hHn1

/-- Same-slot knownness for the actual strict-advance branch of
`get_latest_confirmed`.  Reset-anchor cases are excluded by the three
inequalities; the retained selected-candidate provenance feeds the complete
support/vote/relay proof above. -/
theorem get_latest_confirmed_strict_advance_known
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ)
    (hHk : E.WithinHorizon cfg (k + 1))
    (hconfirmed : (E.fcrStep cfg ext v k).confirmed_root ∈
      (E.fcrStep cfg ext v k).store.block_roots)
    (hfinalized : (E.fcrStep cfg ext v k).store.finalized_checkpoint.root ∈
      (E.fcrStep cfg ext v k).store.block_roots)
    (hobserved : (E.fcrStep cfg ext v k).current_epoch_observed_justified_checkpoint.root ∈
      (E.fcrStep cfg ext v k).store.block_roots)
    (hnotConfirmed : get_latest_confirmed cfg ext (E.fcrStep cfg ext v k) ≠
      (E.fcrStep cfg ext v k).confirmed_root)
    (hnotFinalized : get_latest_confirmed cfg ext (E.fcrStep cfg ext v k) ≠
      (E.fcrStep cfg ext v k).store.finalized_checkpoint.root)
    (hnotObserved : get_latest_confirmed cfg ext (E.fcrStep cfg ext v k) ≠
      (E.fcrStep cfg ext v k).current_epoch_observed_justified_checkpoint.root)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hkm : k + 1 ≤ m) (hHm : E.WithinHorizon cfg m) :
    get_latest_confirmed cfg ext (E.fcrStep cfg ext v k) ∈
      (E.store cfg ext w m).block_roots := by
  rcases E.get_latest_confirmed_selected cfg ext hSA v hv (k + 1) hHk
      (E.fcrStep cfg ext v k) (E.fcrStep_store cfg ext v k)
      hconfirmed hfinalized hobserved with hreset | ⟨hconf, hb, hparent⟩
  · rcases hreset with h | h | h
    · exact absurd h hnotConfirmed
    · exact absurd h hnotFinalized
    · exact absurd h hnotObserved
  · exact E.confirmed_known_at_all_honest_endpoints cfg ext hSA v hv k _ hHk
      (by rwa [E.fcrStep_store cfg ext v k] at hb)
      (by rwa [E.fcrStep_store cfg ext v k] at hparent)
      hconf w hw m (E.slot_at_mono cfg hkm) hHm

end Execution

end FastConfirmation.Spec
