module
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.Registry
public import FastConfirmation.Spec.Proof.Quorum
public import FastConfirmation.Spec.Proof.SupportTransport
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Spec / Proof / QuorumAccounting

`Proof/Quorum.lean` reduces
`is_one_confirmed = true` to the branch-free inequality

`2·support + support_discount ≥ maximum_support + proposer_score +
2·adversarial_weight + 1`.

This module identifies `support` (`get_attestation_score`) with a ground-truth
weight sum, splits it into an honest and a Byzantine part, confines the
supporters to the slot spans `ByzantineBound` budgets (via the
`LatestMessageProvenance` provenance record), and bounds the Byzantine part by
`estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`.

The pieces are:

* **Step 1** (`get_attestation_score_eq_sum`, `attestation_score_honest_split`):
  the score is a `List.sum` over the *supporter list* `AttSupporters`
  (unslashed active non-equivocating indices whose latest message supports the
  node), and it splits into the sub-sums over honest and non-honest supporters.
* **Step 2** (`supporter_mem_span_committee`): every supporter of `b` at an
  honest node carrying `LatestMessageProvenance` sits in the ground-truth span
  committee `E.span_committee sa (current_slot - 1)` for any `sa ≤ (blocks
  b).slot` — in particular both `get_adversarial_weight` spans.
* **Step 3** (`byzantine_supporter_weight_le`): under `ByzantineBound` and
  registry constancy the non-honest supporters' total (ground-truth) weight is
  at most `estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`.

Every hypothesis is a field of an existing assumption record, a
`WalkKnown`/`hwf`-shaped domain condition, or a fact exported by an existing
`Proof/` module (`LatestMessageProvenance`, `RegistryConstant`,
`Execution.store_current_slot`). No new behavioral assumptions enter.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Step 1 — the supporter list and the honest / Byzantine split -/

/-- The **supporter list** of `node` under `state`: the unslashed active
non-equivocating validators whose recorded latest message supports `node`
(`is_ancestor store (get_supported_node …) node`). This is exactly the list
`get_attestation_score` maps to effective balances and sums. -/
def AttSupporters (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) : List ValidatorIndex :=
  ((get_active_validator_indices state (get_current_epoch cfg state)).filter
      (fun i => !(state.validators.getD i default).slashed)).filter
    (fun i => match store.latest_messages i with
      | none => false
      | some latest_message =>
          decide (i ∉ store.equivocating_indices) &&
            is_ancestor store (get_supported_node store latest_message) node)

omit [Inhabited Root] in
/-- Step 1: `get_attestation_score` is the sum of effective balances over the
supporter list. -/
theorem get_attestation_score_eq_sum (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) :
    get_attestation_score cfg store node state =
      ((AttSupporters cfg store node state).map
        (fun i => (state.validators.getD i default).effective_balance)).sum :=
  rfl

omit [Inhabited Root] in
/-- The supporter list has no duplicates (it is a double filter of
`List.range`). -/
theorem AttSupporters_nodup (store : Store Root) (node : ForkChoiceNode Root)
    (state : BeaconState Root) : (AttSupporters cfg store node state).Nodup := by
  simp only [AttSupporters, get_active_validator_indices]
  exact (((List.nodup_range).filter _).filter _).filter _

omit [Inhabited Root] in
/-- A supporter is unslashed-active-non-equivocating and supports the node; in
particular it has a recorded latest message whose root is an ancestor of the
node. -/
theorem mem_AttSupporters {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg store node state) :
    ∃ lm, store.latest_messages i = some lm ∧
      i ∉ store.equivocating_indices ∧
      is_ancestor store (get_supported_node store lm) node = true := by
  simp only [AttSupporters, List.mem_filter] at hi
  obtain ⟨_, hQ⟩ := hi
  cases hlm : store.latest_messages i with
  | none => rw [hlm] at hQ; exact absurd hQ (by simp)
  | some lm =>
    rw [hlm] at hQ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
    exact ⟨lm, rfl, hQ.1, hQ.2⟩

omit [Inhabited Root] in
/-- Step 1 (split): the score is the sum over honest supporters plus the sum
over non-honest supporters. -/
theorem attestation_score_honest_split (E : Execution Root)
    (store : Store Root) (node : ForkChoiceNode Root) (state : BeaconState Root) :
    get_attestation_score cfg store node state =
      (((AttSupporters cfg store node state).filter (fun i => i ∈ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum +
      (((AttSupporters cfg store node state).filter (fun i => i ∉ E.honest)).map
        (fun i => (state.validators.getD i default).effective_balance)).sum := by
  rw [get_attestation_score_eq_sum]
  exact (List.sum_map_filter_add_sum_map_filter_not (fun i => i ∈ E.honest)
    (fun i => (state.validators.getD i default).effective_balance)
    (AttSupporters cfg store node state)).symm

/-! ## Step 2 — supporter slot confinement

At an honest node carrying `LatestMessageProvenance` (`Proof/Provenance.lean`),
every supporter `i` of `b` has a provenance attestation `a` whose slot lands in
`[(blocks b).slot, current_slot − 1]` (the voted block is at or below `a`'s
slot, and `a` was applied no later than `current_slot − 1`), and `i` sits in
`a`'s slot committee. Hence `i` is in the ground-truth span committee over any
window starting at or below `b`'s slot — in particular both
`get_adversarial_weight` spans. -/

omit [Inhabited Root] in
/-- Step 2: a supporter of `b` lies in the ground-truth span committee
`E.span_committee sa (current_slot - 1)` for any `sa ≤ (blocks b).slot`. The
`hwalk` domain condition (a `WalkKnown` witness pinning the supporter's
latest-message walk down to `b`'s slot) feeds `get_ancestor_slot_le`; `hprov`
is `LatestMessageProvenance` at `sl = current_slot` (the honest node's own
clock, `Execution.store_current_slot`). -/
theorem supporter_mem_span_committee {E : Execution Root}
    {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {b : Root} {i : ValidatorIndex} {sa : Slot}
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hi : i ∈ AttSupporters cfg store (get_node_for_root b) bs)
    (hwalk : ∀ lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks b).slot lm.root)
    (hsa : sa ≤ (store.blocks b).slot) :
    i ∈ E.span_committee sa (get_current_slot cfg store - 1) := by
  obtain ⟨lm, hlm, _, hanc⟩ := mem_AttSupporters cfg hi
  obtain ⟨a, hia, _, _, _, h5, hcomm, _, h8⟩ := hprov i lm hlm
  -- `b` is an ancestor of `lm.root`, so `(blocks b).slot ≤ (blocks lm.root).slot`.
  have hble : (store.blocks b).slot ≤ (store.blocks lm.root).slot := by
    have hsle := get_ancestor_slot_le hwf (hwalk lm hlm)
    rw [get_node_for_root, is_ancestor_supported_pending] at hanc
    simp only [is_ancestor_pending, decide_eq_true_eq] at hanc
    rw [hanc] at hsle
    simpa using hsle
  refine Finset.mem_biUnion.mpr ⟨a.data.slot, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hcomm⟩
  · exact hsa.trans (hble.trans h8)
  · exact Nat.le_sub_one_of_lt h5

/-! ## Step 3 — the Byzantine budget

The non-honest supporters' total weight is bounded by
`estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`. Their `bs`-effective
balances equal the ground-truth weights `E.weight_of` (registry constancy,
`hval`); the Nodup supporter list identifies the list sum with a `Finset` sum,
which is monotone under the inclusion into the non-honest slice of the span
committee (step 2, folded into `hspan`); and `ByzantineBound.span_bound`
supplies the headline bound, with `htab` matching the two total-active-balance
readings. -/

omit [Inhabited Root] in
/-- Step 3: the total (ground-truth = `bs`-effective) weight of the non-honest
supporters of `b` is at most `estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`
over any span `[sa, es]` that contains all of them (`hspan`). -/
theorem byzantine_supporter_weight_le {E : Execution Root} (hbb : ByzantineBound cfg E)
    {store : Store Root} {bs : BeaconState Root} {b : Root} {sa es : Slot}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hsaH : E.SlotWithinHorizon cfg sa) (hesH : E.SlotWithinHorizon cfg es)
    (hspan : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs,
      i ∉ E.honest → i ∈ E.span_committee sa es) :
    (((AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa es
        / 100 * cfg.confirmation_byzantine_threshold := by
  set L := (AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∉ E.honest)
    with hL
  have hLnodup : L.Nodup := (AttSupporters_nodup cfg store _ bs).filter _
  have hmap : L.map (fun i => (bs.validators.getD i default).effective_balance)
      = L.map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  have hsub : L.toFinset ⊆ (E.span_committee sa es).filter (fun i => i ∉ E.honest) := by
    intro i hi
    rw [List.mem_toFinset, hL, List.mem_filter] at hi
    have hnh : i ∉ E.honest := of_decide_eq_true hi.2
    exact Finset.mem_filter.mpr ⟨hspan i hi.1 hnh, hnh⟩
  rw [htab]
  calc (L.map (fun i => (bs.validators.getD i default).effective_balance)).sum
      = ∑ i ∈ L.toFinset, E.weight_of i := by
        rw [hmap]; exact (List.sum_toFinset E.weight_of hLnodup).symm
    _ ≤ ∑ i ∈ (E.span_committee sa es).filter (fun i => i ∉ E.honest), E.weight_of i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = E.weight ((E.span_committee sa es).filter (fun i => i ∉ E.honest)) := rfl
    _ ≤ estimate_committee_weight_between_slots cfg (E.total_active cfg) sa es / 100 *
          cfg.confirmation_byzantine_threshold := hbb.span_bound sa es hsaH hesH

omit [Inhabited Root] in
/-- Steps 2 + 3 composed at an honest node: with `LatestMessageProvenance` and
the per-supporter `WalkKnown` witnesses discharging the confinement `hspan`, the
non-honest supporters' weight is bounded by
`estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD` over any span
`[sa, current_slot − 1]` with `sa ≤ (blocks b).slot` — in particular both
`get_adversarial_weight` spans (`Quorum.get_adversarial_weight_eq`). -/
theorem byzantine_supporter_weight_le_of_provenance {E : Execution Root}
    (hbb : ByzantineBound cfg E) {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {b : Root} {sa : Slot}
    (hval : bs.validators = E.registry)
    (htab : get_total_active_balance cfg bs = E.total_active cfg)
    (hsaH : E.SlotWithinHorizon cfg sa)
    (hcurH : E.SlotWithinHorizon cfg (get_current_slot cfg store))
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hsa : sa ≤ (store.blocks b).slot)
    (hwalk : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs, ∀ lm,
      store.latest_messages i = some lm → WalkKnown store (store.blocks b).slot lm.root) :
    (((AttSupporters cfg store (get_node_for_root b) bs).filter (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum ≤
      estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs) sa
          (get_current_slot cfg store - 1) / 100 * cfg.confirmation_byzantine_threshold :=
  byzantine_supporter_weight_le cfg hbb hval htab hsaH
    ⟨(Nat.sub_le _ _).trans hcurH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hcurH.2⟩
    (fun i hi _ => supporter_mem_span_committee cfg hwf hprov hi (hwalk i hi) hsa)

/-! ## Step 4 — the honest-support majority (arithmetic assembly)

`is_one_confirmed_ineq` (`Proof/Quorum.lean`) gives

`2·score + support_discount ≥ maximum_support + proposer_score +
2·adversarial_weight + 1`,

and Step 1 splits `score` into the honest and Byzantine sub-sums. Cancelling
`2·adversarial_weight` against `2·byz_score` (given `byz_score ≤
adversarial_weight`) yields the honest-majority conclusion. The lemma below is
that final `ℕ`-arithmetic assembly; the input `hbyz : byz_score ≤
adversarial_weight` is therefore explicit.  The note at the end of this module
explains why the stated assumption set does not imply it. -/

/-- Pure `ℕ` core of the assembly: cancel `2·A` against `2·z` in the
`is_one_confirmed` inequality once `z ≤ A`. -/
private theorem majority_arith {h z d ms ps a : ℕ}
    (hineq : 2 * (h + z) + d ≥ ms + ps + 2 * a + 1) (hbyz : z ≤ a) :
    2 * h + d ≥ ms + ps + 1 := by omega

/-- Step 4 (assembly): given `is_one_confirmed = true` and the Byzantine-supporter
bound `hbyz : byz_score ≤ adversarial_weight`, twice the honest supporters'
weight plus the support discount dominates `maximum_support + proposer_score +
1`. This is the spec-side Lemma 3∘4 headline modulo `hbyz`. -/
theorem honest_support_majority_of_byz_le {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hconf : is_one_confirmed cfg ext store bs b = true)
    (hbyz : (((AttSupporters cfg store (get_node_for_root b) bs).filter
          (fun i => i ∉ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      ≤ get_adversarial_weight cfg ext store bs b) :
    2 * (((AttSupporters cfg store (get_node_for_root b) bs).filter
          (fun i => i ∈ E.honest)).map
        (fun i => (bs.validators.getD i default).effective_balance)).sum
      + get_support_discount cfg ext store bs b
      ≥ estimate_committee_weight_between_slots cfg (get_total_active_balance cfg bs)
          ((store.blocks (store.blocks b).parent_root).slot + 1)
          (get_current_slot cfg store - 1)
        + compute_proposer_score cfg bs + 1 := by
  have hineq := is_one_confirmed_ineq cfg ext hconf
  rw [attestation_score_honest_split cfg E store (get_node_for_root b) bs] at hineq
  exact majority_arith hineq hbyz

/-! ## Equivocator-disjointness input for the full Step 4

`honest_support_majority_of_byz_le` reduces the headline to the single bound
`hbyz : byz_score ≤ get_adversarial_weight …`. Steps 2 + 3
(`byzantine_supporter_weight_le_of_provenance`) discharge the *weaker*
`byz_score ≤ estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD` — the
pre-discount budget — but `get_adversarial_weight` is that budget *minus* the
span's `get_equivocation_score` (`byzantine_net_le_compute_adversarial_weight`).
The stronger bound additionally needs

  `byz_score + get_equivocation_score … ≤ E.weight (non-honest span committee)`,

which follows when the equivocating validators of the span are non-honest, i.e.
the invariant **no honest validator is in `store.equivocating_indices`** (so the
honest equivocator weight is `0`). That invariant is a trajectory fact about
`on_attester_slashing` under `HonestBehavior.not_slashable` /
`no_forgery`; consumers provide it through the corresponding trajectory
invariant. -/

end FastConfirmation.Spec

end
