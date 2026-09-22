module
public import FastConfirmation.Spec.Proof.Closing
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.Delivery
public import FastConfirmation.Spec.Proof.EngineTransport

@[expose] public section

/-!
# Spec / Proof / Knownness: the confirmed-block knownness family

This module addresses the knownness family
of `Closing.EngineAdvanceCore` via the **support-vote route**, under a genesis-start scope
`hanchor0`:

* `hbconf` (the confirmed block is a known block at its own confirming store `(v, n+1)`) — **closed
  outright** from `SpecAssumptions` + `hanchor0` (`hbconf_of_genesisStart`);
* `hck` (single-store confirmed-root knownness, the monotonicity residual) — **closed outright**
  from `SpecAssumptions` + `hanchor0` (`hck_of_genesisStart`, no residual);
* `hb_sameslot` (foreign-endpoint same-slot knownness, the same-slot availability corner) — its **geometric
  transport core is proven in full** (`mem_of_honest_past_descendant`), reducing the field to the
  single honest-liveness residual `HonestPastDescendant` (`hb_sameslot_of_pastDescendant`).

The headlines `Spec_Safety_of_knownness` / `Spec_Monotonicity_of_knownness` that composed these
into the public guarantees are **deleted** (P-6): they inherited `AheadFacade`'s ahead-regime
head-tracking premise from `Closing.Spec_Safety_closed`, nothing ever produced it, and no
audited witness reached them. See the Section 4 note below and
`docs/p6-justified-descends-derivation.md` §8. The knownness results themselves stand.

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
In the checkpoint-sync above-anchor obstruction, an unknown `b` looks up to the totalized default
slot `0` below a checkpoint-sync anchor, so `mem_of_is_ancestor_above_anchor`'s `hab` is not
derivable there.


**P-6 note.** Some names used in this header no longer exist. The legacy `SpecAssumptions`
observed-anchor cone was retired and swept for orphans, which removed `Closing.Spec_Safety_closed` and this module's own
`mem_of_honest_past_descendant` / `hb_sameslot_of_pastDescendant`.
The descriptions above are kept because they still identify the *shapes* the surviving
declarations produce and consume. See `docs/p6-justified-descends-derivation.md` §8.
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
  exact mem_of_is_ancestor_above_anchor hpsl hwa hab hanc

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

/-! ### Deleted: `mem_of_honest_past_descendant` and `hb_sameslot_of_pastDescendant`

The geometric transport for the same-slot knownness corner, and the `hb_sameslot` discharge
built on it. Their only consumer was `Spec_Safety_of_knownness`. `HonestPastDescendant`,
`hbconf_of_genesisStart` and `hck_of_genesisStart` are unaffected.

They are deleted by the orphan sweep that follows the retirement of the legacy
`SpecAssumptions` observed-anchor cone (P-6): every consumer they had was in that cone.
See `docs/p6-justified-descends-derivation.md` §8. -/

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
    exact (hji.checkpoint_known v hv 0 hH0).2
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
        exact (hji.checkpoint_known v hv (n + 1) hHn1).2
      · rw [h]; exact E.fcrStep_observed_known cfg ext hji v hv n hHn1
      · exact E.hbconf_of_genesisStart cfg ext hSA hanchor0 v hv n _ hHn1 h
    · rw [E.confirmed_succ_of_no_advance cfg ext v n hadv]
      exact (E.store_storeLE cfg ext v (Nat.le_succ n)).1 (ih hHn)

end Execution

/-! ## Section 4 — deleted: the knownness-closed headlines

`Spec_Safety_of_knownness` and `Spec_Monotonicity_of_knownness` stood here. They composed
`Closing.Spec_Safety_closed` with the two knownness dischargers (`hbconf_of_genesisStart`,
`hb_sameslot_of_pastDescendant`), and inherited from it the unproduced ahead-regime head-tracking premise `htracks`. Both were unconsumed roots of the legacy
`SpecAssumptions` observed-anchor cone and are deleted with it (P-6).

The knownness content of Sections 1-3b is unaffected: `hbconf_of_genesisStart`,
`mem_of_honest_past_descendant`, `HonestPastDescendant`, `hb_sameslot_of_pastDescendant` and
`hck_of_genesisStart` all stand, and none of them touches the ahead regime. See
`docs/p6-justified-descends-derivation.md` §8. -/


end FastConfirmation.Spec

end
