module
public import FastConfirmation.Spec.Proof.Closing
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.Delivery
public import FastConfirmation.Spec.Proof.EngineTransport

@[expose] public section

/-!
# Spec / Proof / Knownness: the confirmed-block knownness family

This module addresses the knownness family
of `Closing.EngineAdvanceCore` via the **support-vote route**, under the same genesis-start scope
`Spec_Safety_closed` already takes (`hanchor0`):

* `hbconf` (the confirmed block is a known block at its own confirming store `(v, n+1)`) — **closed
  outright** from `SpecAssumptions` + `hanchor0` (`hbconf_of_genesisStart`);
* `hck` (single-store confirmed-root knownness, the monotonicity residual) — **closed outright**
  from `SpecAssumptions` + `hanchor0` (`hck_of_genesisStart`, no residual);
* `hb_sameslot` (foreign-endpoint same-slot knownness, the same-slot availability corner) — its **geometric
  transport core is proven in full** (`mem_of_honest_past_descendant`), reducing the field to the
  single honest-liveness residual `HonestPastDescendant` (`hb_sameslot_of_pastDescendant`).

The headlines `Spec_Safety_of_knownness` / `Spec_Monotonicity_of_knownness` compose these into the
public guarantees: `hbconf`/`hck` are discharged internally, so the public `Spec_Safety` /
`Spec_Monotonicity` reduce to `hanchor0` + `HonestPastDescendant` + the two carried engine fields
`hcov`/`heng`.

## The support-vote route (`hbconf`)

An `is_one_confirmed` block `b` has strictly positive recorded attestation score at the confirming
store `S := (fcrStep v n).store = store v (n+1)` (`support > safety_threshold ≥ 0`). A positive
`List.sum` forces a nonempty summand list, so **some** validator `i` sits in
`get_attestation_score`'s filter: `S.latest_messages i = some lm` with
`is_ancestor S (get_supported_node S lm) (get_node_for_root b) = true`, i.e. the recorded block
`lm.root` descends from `b`. `LatestMessageProvenance` (the `validate_on_attestation` known-block
gate captured at recording) places `lm.root ∈ S.block_roots`. The parent walk from the known
`lm.root` down to `b`'s slot stays known (`AnchorFacade.store_walkKnownK`), and at the genesis
start `b` sits at or above the slot-`0` anchor trivially, so
`LastCruxes.mem_of_is_ancestor_above_anchor` concludes `b ∈ S.block_roots` — exactly the confirming
store `(v, n+1)`. This is the same transport `Structural.finalized_cross_known_of_boundary` runs
at the finalized reset anchor, here with `a := lm.root` (a supporter's recorded block) and `b` the
confirmed block; it needs an honest node and an in-horizon second, but no relay
(same store).

## The genesis-start scope

`hbconf` (own store) is delivered from `SpecAssumptions` alone under the genesis-start hypothesis
`hanchor0` (anchor block at `GENESIS_SLOT`), which makes the above-anchor boundary `0 ≤ _` trivial.
The genesis-start scope is the same one `Spec_Safety_closed` already takes (`hanchor0`); in the
checkpoint-sync above-anchor obstruction, an unknown `b` looks up to the totalized default slot `0`
below a checkpoint-sync anchor, so `mem_of_is_ancestor_above_anchor`'s `hab` is not derivable there.

-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Section 1 — a supporter from positive attestation score -/

/-- A positive `(l.map f).sum` over a `ℕ`-valued weight exposes a list member with positive
weight. -/
theorem exists_mem_of_map_sum_pos {α : Type*} (l : List α) (f : α → ℕ)
    (h : 0 < (l.map f).sum) : ∃ x ∈ l, 0 < f x := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.lt_irrefl] at h
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons] at h
    rcases Nat.eq_zero_or_pos (f a) with ha | ha
    · rw [ha, Nat.zero_add] at h
      obtain ⟨x, hx, hfx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩
    · exact ⟨a, List.mem_cons_self, ha⟩

omit [Inhabited Root] in
/-- **A supporter from positive attestation score.** If `get_attestation_score` of `node` is
strictly positive at store `S`, then some validator `i` has a recorded latest message `lm` whose
supported node is an ancestor test hit for `node` (`is_ancestor S (mk lm.root) node = true`). The
score is a `List.sum` over the filtered index list; positivity forces that list nonempty, and the
filter predicate is exactly the recorded-message support test. -/
theorem exists_supporter_of_score_pos {S : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root}
    (h : 0 < get_attestation_score cfg S node state) :
    ∃ (i : ValidatorIndex) (lm : LatestMessage Root),
      S.latest_messages i = some lm ∧
      is_ancestor S (get_supported_node S lm) node = true := by
  simp only [get_attestation_score] at h
  obtain ⟨i, hiL, _⟩ := exists_mem_of_map_sum_pos _ _ h
  rw [List.mem_filter] at hiL
  obtain ⟨_, hPi⟩ := hiL
  cases hlm : S.latest_messages i with
  | none => simp only [hlm] at hPi; exact absurd hPi (by decide)
  | some lm =>
    simp only [hlm, Bool.and_eq_true] at hPi
    exact ⟨i, lm, hlm, hPi.2⟩

namespace Execution

variable (E : Execution Root)

/-! ## Section 2 — `hbconf`: knownness at the own confirming store -/

/-- **`hbconf` under genesis-start.** A block `b` passing `is_one_confirmed` at the confirming store
`(fcrStep v n).store = store v (n+1)` is a known block there. The positive attestation score yields
a supporter whose recorded `lm.root` descends from `b` and is known (`LatestMessageProvenance`); the
`store_walkKnownK` walk from `lm.root` down to the slot-`0` anchor, with `b` trivially above the
anchor at a genesis start, lands `b` in `block_roots` via `mem_of_is_ancestor_above_anchor`. No
relay is needed; the node and second are in the validity-law domain. -/
theorem hbconf_of_genesisStart (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (_hHn1 : E.WithinHorizon cfg (n + 1))
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true) :
    b ∈ (E.store cfg ext v (n + 1)).block_roots := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, _hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  rw [E.fcrStep_store cfg ext v n] at hconf
  -- positive attestation score ⟹ a supporter
  simp only [is_one_confirmed, gt_iff_lt, decide_eq_true_eq] at hconf
  have hsupp_pos : 0 < get_attestation_score cfg (E.store cfg ext v (n + 1)) (get_node_for_root b)
      (get_current_balance_source (E.fcrStep cfg ext v n)) :=
    lt_of_le_of_lt (Nat.zero_le _) hconf
  obtain ⟨i, lm, hlm, hanc⟩ := exists_supporter_of_score_pos cfg hsupp_pos
  -- the recorded block is known at `(v, n+1)`
  obtain ⟨_a, _, _, _, _, _, _, hlm_known, _⟩ :=
    E.latestMessageProvenance cfg ext hwfE hec ⟨ast, ablk, hgeq⟩ v (n + 1) (by assumption) (by assumption) i lm hlm
  -- the anchor root and the walk domain
  have hanchor_mem0 : ablk.root ∈ (E.store cfg ext v 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]; simp [get_forkchoice_store]
  have hanchor_mem : ablk.root ∈ (E.store cfg ext v (n + 1)).block_roots :=
    (E.store_storeLE cfg ext v (Nat.zero_le (n + 1))).1 hanchor_mem0
  have hpsl : ParentSlotLt (E.store cfg ext v (n + 1)) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled v (n + 1)
  have hwalkK := E.store_walkKnownK cfg ext hwfE hec hgen' v (n + 1)
  have hanchor_slot : ((E.store cfg ext v (n + 1)).blocks ablk.root).slot = ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq v (n + 1) hanchor_mem]
  have hwa : WalkKnown (E.store cfg ext v (n + 1)) ablk.message.slot lm.root := by
    have := hwalkK ablk.root hanchor_mem lm.root hlm_known
    rwa [hanchor_slot] at this
  have hab : ablk.message.slot ≤ ((E.store cfg ext v (n + 1)).blocks b).slot := by
    rw [hanchor0 ast ablk hgeq, GENESIS_SLOT]; exact Nat.zero_le _
  have hanc' := hanc
  rw [get_node_for_root, is_ancestor_supported_pending] at hanc'
  exact mem_of_is_ancestor_above_anchor hpsl hwa hab hanc'

/-! ## Section 3 — `hb_sameslot`: knownness at a foreign same-slot endpoint

The `+1` gossip gate of `block_relay` does not reach `(w, m)` from `(v, n+1)` at the same slot
(FinalWiring's later-slot route needs the strictly-later slot). The support-vote route beats it by
routing knownness through an **honest supporter's own past-slot store** `(u, n_u)` (`slot n_u <
slot (n+1)`): that store is fully contained in the confirming store `(v, n+1)` by `block_relay`
(the past-slot gate `slot n_u + 1 ≤ slot (n+2)` holds), so the `is_ancestor` walk from the
supporter's recorded block `d` down to `b` — computed at `(v, n+1)` — transports **verbatim** to
`(u, n_u)` (`BlockAgreement.get_ancestor_congr`, blanket agreement from the containment) and lands
`b ∈ (store u n_u).block_roots`. A second `block_relay` from that *past* store reaches `(w, m)`
(gate `slot n_u + 1 ≤ slot (n+1) ≤ slot (m+1)`), same slot included. The one input this route needs
that `SpecAssumptions` alone does not supply is the honest past descendant `(u, n_u, d)` — the
honest-supporter existence + head-knownness residual (`HonestPastDescendant` below); everything else
is Layer-0 / synchrony-mechanical. -/

/-- **The transport core (fully proven).** Under genesis-start, from an honest supporter's past-slot
store `(u, n_u)` (`slot n_u < slot (n+1)`) holding a block `d` that descends from `b` at the
confirming store `(v, n+1)`, the confirmed block `b` is known at **every** honest `(w, m)` with
`n + 1 ≤ m` — same slot included, past `block_relay`'s `+1` gate. Two `block_relay` hops
(`(u, n_u) ⊆ (v, n+1)` for the ancestry transport, `(u, n_u) ⊆ (w, m)` for the endpoint) sandwich a
`get_ancestor_congr` that carries the `b ≼ d` walk from `(v, n+1)` to `(u, n_u)`. -/
theorem mem_of_honest_past_descendant (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hHn1 : E.WithinHorizon cfg (n + 1)) (hHm : E.WithinHorizon cfg m)
    (u : ValidatorIndex) (hu : u ∈ E.honest) (n_u : ℕ) (d : Root)
    (hHnu : E.WithinHorizon cfg n_u)
    (hslot_lt : E.slot_at cfg n_u < E.slot_at cfg (n + 1))
    (hd_u : d ∈ (E.store cfg ext u n_u).block_roots)
    (hanc_v : is_ancestor (E.store cfg ext v (n + 1))
      (get_node_for_root d) (get_node_for_root b) = true) :
    b ∈ (E.store cfg ext w m).block_roots := by
  obtain ⟨hgen, hwfE, _hdiv, _hhb, hsync, hec, _hsv, _hbb, _hji⟩ := hSA
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen' : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root :=
    ⟨ast, ablk, hgeq, hslot, hparent⟩
  set rb := ((E.store cfg ext v (n + 1)).blocks b).slot with hrb
  -- containment `(u, n_u) ⊆ (v, n+1)` from block_relay (past-slot gate)
  have hgate_uv : E.slot_at cfg n_u + 1 ≤ E.slot_at cfg (n + 1 + 1) :=
    le_trans hslot_lt (E.slot_at_mono cfg (Nat.le_succ (n + 1)))
  have hsub_uv : (E.store cfg ext u n_u).block_roots ⊆ (E.store cfg ext v (n + 1)).block_roots :=
    fun r hr => hsync.block_relay u hu n_u r hHnu hr v hv (n + 1) hHn1 hgate_uv
  -- blanket block agreement on the contained store
  have hagree : ∀ x ∈ (E.store cfg ext u n_u).block_roots,
      (E.store cfg ext u n_u).blocks x = (E.store cfg ext v (n + 1)).blocks x := fun x hx =>
    hwfE.blocks_agree (E.blockProvenance cfg ext u n_u) (E.blockProvenance cfg ext v (n + 1))
      hx (hsub_uv hx)
  -- the walk from `d` at `(u, n_u)` toward `rb`
  have hanchor_mem0u : ablk.root ∈ (E.store cfg ext u 0).block_roots := by
    change ablk.root ∈ E.genesis_store.block_roots
    rw [hgeq]; simp [get_forkchoice_store]
  have hanchor_memu : ablk.root ∈ (E.store cfg ext u n_u).block_roots :=
    (E.store_storeLE cfg ext u (Nat.zero_le n_u)).1 hanchor_mem0u
  have hpsl_u : ParentSlotLt (E.store cfg ext u n_u) :=
    E.store_parentSlotLt cfg ext hwfE hec hgen' hwfE.anchor_parent_unscheduled u n_u
  have hanchor_slotu : ((E.store cfg ext u n_u).blocks ablk.root).slot = ablk.message.slot := by
    rw [E.store_anchor_block cfg ext hwfE hgeq u n_u hanchor_memu]
  have hwalk0 : WalkKnown (E.store cfg ext u n_u) ablk.message.slot d := by
    have := E.store_walkKnownK cfg ext hwfE hec hgen' u n_u ablk.root hanchor_memu d hd_u
    rwa [hanchor_slotu] at this
  have hwalk_u : WalkKnown (E.store cfg ext u n_u) rb d :=
    hwalk0.mono (by rw [hanchor0 ast ablk hgeq, GENESIS_SLOT]; exact Nat.zero_le _)
  -- the `b ≼ d` walk lands on `b`; transport it to `(u, n_u)`
  have hv_lands : (get_ancestor (E.store cfg ext v (n + 1)) (ForkChoiceNode.mk d .pending) rb).root =
      b := by
    simpa only [get_node_for_root, is_ancestor_pending, decide_eq_true_eq] using hanc_v
  have hu_lands : (get_ancestor (E.store cfg ext u n_u) (ForkChoiceNode.mk d .pending) rb).root =
      b := by
    rw [get_ancestor_congr hagree hd_u hwalk_u]; exact hv_lands
  have hb_u : b ∈ (E.store cfg ext u n_u).block_roots := by
    have hspec := (get_ancestor_spec hpsl_u hwalk_u).1
    rw [hu_lands] at hspec; exact hspec
  -- second block_relay hop `(u, n_u) → (w, m)` (same-slot included)
  have hgate_uw : E.slot_at cfg n_u + 1 ≤ E.slot_at cfg (m + 1) :=
    le_trans (le_trans hslot_lt (E.slot_at_mono cfg hm)) (E.slot_at_mono cfg (Nat.le_succ m))
  exact hsync.block_relay u hu n_u b hHnu hb_u w hw m hHm hgate_uw

/-- **The honest-past-descendant residual for `hb_sameslot`.** For every confirmed block `b` at a
slot-update store, an honest node `u` and past-slot second `n_u` (`slot n_u < slot (n+1)`) whose
store holds a block `d` that descends from `b` at the confirming store. This is exactly the
support-vote route's remaining obligation: an honest supporter's recorded message roots to a block
`d` (its own head, `b ≼ d`) that the supporter knew at a slot `< slot (n+1)` (`HonestBehavior`'s
`votes_head` + `no_forgery` unwinding of the recorded supporter message, keyed on the supporter
being honest — `HonestWeight.honest_support_majority` supplies the honest supporter). -/
def HonestPastDescendant (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ (n : ℕ) (b : Root),
    E.WithinHorizon cfg (n + 1) →
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    ∃ (u : ValidatorIndex) (n_u : ℕ) (d : Root), u ∈ E.honest ∧
      E.WithinHorizon cfg n_u ∧
      E.slot_at cfg n_u < E.slot_at cfg (n + 1) ∧
      d ∈ (E.store cfg ext u n_u).block_roots ∧
      is_ancestor (E.store cfg ext v (n + 1))
        (get_node_for_root d) (get_node_for_root b) = true

/-- **`hb_sameslot` from the honest-past-descendant residual.** Discharges `EngineAdvanceCore`'s
`hb_sameslot` field (indeed for every `m ≥ n+1`, same slot or later) from `HonestPastDescendant` via
`mem_of_honest_past_descendant`. -/
theorem hb_sameslot_of_pastDescendant (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (hpast : E.HonestPastDescendant cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (b : Root)
    (hconf : is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hm : n + 1 ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    b ∈ (E.store cfg ext w m).block_roots := by
  have hHn1 := E.withinHorizon_mono cfg hm hHm
  obtain ⟨u, n_u, d, hu, hHnu, hslot_lt, hd_u, hanc_v⟩ :=
    hpast v hv n b hHn1 hconf
  exact E.mem_of_honest_past_descendant cfg ext hSA hanchor0 v hv n b w hw m hm
    hHn1 hHm u hu n_u d hHnu hslot_lt hd_u hanc_v

/-! ## Section 3b — `hck`: single-store confirmed-root knownness (monotonicity) -/

/-- **`fcrStep`'s observed-justified reset root is known.** The rotated
`current_epoch_observed_justified_checkpoint` of `fcrStep v n` — one of the reset anchors
`get_latest_confirmed` can return — is a known block at the update store `(v, n+1)`. Unfolding
`update_fast_confirmation_variables` the rotated value is, per the two epoch-boundary guards, either
`(fcr v n)`'s observed checkpoint, `(fcr v n)`'s previous-epoch greatest unrealized checkpoint, or
`(store v (n+1))`'s unrealized justified checkpoint — each known by
`JustificationInterface.observed_checkpoint_known`. -/
theorem fcrStep_observed_known (hji : JustificationInterface cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ)
    (hHn1 : E.WithinHorizon cfg (n + 1)) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
  have hle : E.slot_at cfg n ≤ E.slot_at cfg (n + 1) := E.slot_at_mono cfg (Nat.le_succ n)
  have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
  have hobs_n := hji.observed_checkpoint_known v hv n v hv (n + 1) hHn hHn1 hle
  have hobs_n1 := hji.observed_checkpoint_known v hv (n + 1) v hv (n + 1)
    hHn1 hHn1 (le_refl _)
  simp only [Execution.fcrStep, update_fast_confirmation_variables]
  split_ifs <;>
    first
      | exact hobs_n1.1
      | exact hobs_n.2.1
      | exact hobs_n.2.2

/-- **`hck` under genesis-start** (monotonicity residual). Every honest node's confirmed root at
every second is a known block in its own store. Induction on the second: the genesis root is the
anchor's finalized root (`checkpoint_known`); a non-slot-update second carries the previous root
forward (`StoreLE`); a slot update runs `get_latest_confirmed`, whose four
`get_latest_confirmed_spec` outputs are the previous confirmed root (IH + `StoreLE`), the finalized
reset root
(`checkpoint_known`), the observed reset root (`fcrStep_observed_known`), and an `is_one_confirmed`
block (`hbconf_of_genesisStart`). This is exactly the support-vote route of `hbconf` closing the
engine leg, the interface knownness closing the reset legs. -/
theorem hck_of_genesisStart (hSA : SpecAssumptions cfg ext E)
    (hanchor0 : ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (v : ValidatorIndex) (hv : v ∈ E.honest) :
    ∀ k : ℕ, E.WithinHorizon cfg k →
      E.confirmed cfg ext v k ∈ (E.store cfg ext v k).block_roots := by
  have hji : JustificationInterface cfg ext E := hSA.2.2.2.2.2.2.2.2
  intro k
  induction k with
  | zero =>
    intro hH0
    rw [E.confirmed_zero]
    exact (hji.checkpoint_known v hv 0).2
  | succ n ih =>
    intro hHn1
    have hHn := E.withinHorizon_mono cfg (Nat.le_succ n) hHn1
    by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)
    · rw [E.confirmed_succ_of_advance cfg ext v n hadv]
      rcases get_latest_confirmed_spec cfg ext (E.fcrStep cfg ext v n) with (h | h | h) | h
      · rw [h, E.fcrStep_confirmed_root cfg ext v n]
        exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1 (ih hHn)
      · rw [h, E.fcrStep_store cfg ext v n]
        exact (hji.checkpoint_known v hv (n + 1)).2
      · rw [h]; exact E.fcrStep_observed_known cfg ext hji v hv n hHn1
      · exact E.hbconf_of_genesisStart cfg ext hSA hanchor0 v hv n _ hHn1 h
    · rw [E.confirmed_succ_of_no_advance cfg ext v n hadv]
      exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1 (ih hHn)

end Execution

/-! ## Section 4 — the knownness-closed `Spec_Safety` headline

Composes `Closing.Spec_Safety_closed` with the two knownness dischargers: `hbconf` is closed
outright from `SpecAssumptions` + genesis-start (`hbconf_of_genesisStart`), and `hb_sameslot` is
reduced to the honest-past-descendant residual `HonestPastDescendant`
(`hb_sameslot_of_pastDescendant`).
So the public `Spec_Safety` reduces to `hanchor0` + `HonestPastDescendant` + the two carried engine
fields `hcov`/`heng` — the confirmed-block knownness family collapses to a single honest-liveness
residual (`hpast`), the geometric transport core being fully proven above. -/

/-- **`Spec_Safety` from the knownness residual + the carried engine fields.** The public
FCR safety guarantee follows from a proof that every execution's `SpecAssumptions` supplies

* the **genesis-start anchor** `hanchor0` (as `Spec_Safety_closed`);
* the **honest-past-descendant** residual `hpast` (`HonestPastDescendant`) — the one input the
  support-vote route needs beyond `SpecAssumptions`: an honest supporter of every confirmed block
  knew a descendant of it at a strictly earlier slot (honest-supporter existence +
  `votes_head`/`no_forgery` head-knownness); it discharges the same-slot availability corner
  `hb_sameslot` via the fully-proven `mem_of_honest_past_descendant` transport;
* the carried engine fields `hcov`/`heng` (the disjunction's covering justified checkpoint with its
  strict-epoch advance sub-case, and the chain-branch head-safety engine).

`hbconf` is discharged internally (`hbconf_of_genesisStart`); it needs no residual. Composes
`Spec_Safety_closed` with the `EngineAdvanceCore` assembled from these. -/
theorem Spec_Safety_of_knownness
    (hanchor0 : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (hpast : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.HonestPastDescendant cfg ext)
    (hcov : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
          E.WithinHorizon cfg m →
          ∃ jcb : Checkpoint Root,
            b ∈ (E.store cfg ext w m).block_roots ∧
            JustifiedIn (E.store cfg ext w m) jcb ∧
            jcb.root ∈ (E.store cfg ext w m).block_roots ∧
            is_ancestor (E.store cfg ext w m)
              (get_node_for_root b) (get_node_for_root jcb.root) = true ∧
            (jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
              is_ancestor (E.store cfg ext w m)
                (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
                (get_node_for_root b) = true))
    (heng : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
          E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
          is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
            (get_node_for_root b) = true) :
    Spec_Safety cfg ext :=
  Spec_Safety_closed cfg ext hanchor0 (fun E hSA =>
    { hbconf := fun v _hv n b hH hconf =>
        E.hbconf_of_genesisStart cfg ext hSA (hanchor0 E hSA) v _hv n b hH hconf
      hb_sameslot := fun v hv n b hconf w hw m hm hH _hgap =>
        E.hb_sameslot_of_pastDescendant cfg ext hSA (hanchor0 E hSA) (hpast E hSA)
          v hv n b hconf w hw m hm hH
      hcov := hcov E hSA
      heng := heng E hSA })

/-- **`Spec_Monotonicity` from the same knownness bundle.** The monotonicity companion of
`Spec_Safety_of_knownness`: chain consistency of an honest node's confirmed roots follows from the
knownness-closed safety plus the single-store confirmed-root knownness `hck`, which is **fully
discharged** here (`hck_of_genesisStart`, no residual) — so monotonicity reduces to exactly the same
`hanchor0` + `hpast` + `hcov` + `heng` as safety, with no extra `hck` hypothesis. Composes
`spec_monotonicity_of_safety` on `Spec_Safety_of_knownness`. -/
theorem Spec_Monotonicity_of_knownness
    (hanchor0 : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
        E.genesis_store = get_forkchoice_store cfg ast ablk → ablk.message.slot = GENESIS_SLOT)
    (hpast : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.HonestPastDescendant cfg ext)
    (hcov : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
          E.WithinHorizon cfg m →
          ∃ jcb : Checkpoint Root,
            b ∈ (E.store cfg ext w m).block_roots ∧
            JustifiedIn (E.store cfg ext w m) jcb ∧
            jcb.root ∈ (E.store cfg ext w m).block_roots ∧
            is_ancestor (E.store cfg ext w m)
              (get_node_for_root b) (get_node_for_root jcb.root) = true ∧
            (jcb.epoch < (E.store cfg ext w m).justified_checkpoint.epoch →
              is_ancestor (E.store cfg ext w m)
                (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
                (get_node_for_root b) = true))
    (heng : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
        is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
          (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
        ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
          E.WithinHorizon cfg m →
          is_ancestor (E.store cfg ext w m) (get_node_for_root b)
              (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true →
          is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
            (get_node_for_root b) = true) :
    Spec_Monotonicity cfg ext :=
  spec_monotonicity_of_safety cfg ext
    (Spec_Safety_of_knownness cfg ext hanchor0 hpast hcov heng)
    (hkc_of_confirmed_known cfg ext
      (fun E hSA v hv k => E.hck_of_genesisStart cfg ext hSA (hanchor0 E hSA) v hv k))

end FastConfirmation.Spec

end
