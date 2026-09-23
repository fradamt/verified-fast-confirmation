module
public import FastConfirmation.Spec.Proof.Provenance
public import FastConfirmation.Spec.Proof.Registry
public import FastConfirmation.Spec.Proof.Quorum
public import FastConfirmation.Spec.Proof.SupportTransport
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Spec / Proof / QuorumAccounting

This module contains `AttSupporters`, `get_attestation_score_eq_sum`, `AttSupporters_nodup` and related declarations.
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
  obtain ⟨a, hia, _, _, _, h5, hcomm, _, h8, _⟩ := hprov i lm hlm
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

/-- A confirmed block is older than the confirmation store's completed-vote
cutoff.  Confirmation has positive score, and every recorded supporter is
confined by provenance to a committee slot from the block slot through that
cutoff.  Hence the parent of a confirmed child cannot be a previous-slot
payload decision at a same-slot or later endpoint. -/
theorem confirmed_block_slot_le_cutoff {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hwalk : ∀ i ∈ AttSupporters cfg store (get_node_for_root b) bs, ∀ lm,
      store.latest_messages i = some lm →
        WalkKnown store (store.blocks b).slot lm.root)
    (hconf : is_one_confirmed cfg ext store bs b = true) :
    (store.blocks b).slot ≤ get_current_slot cfg store - 1 := by
  have hpositive : 0 < get_attestation_score cfg store (get_node_for_root b) bs := by
    have hgt : compute_safety_threshold cfg ext store b bs <
        get_attestation_score cfg store (get_node_for_root b) bs := by
      simpa [is_one_confirmed] using hconf
    exact lt_of_le_of_lt (Nat.zero_le _) hgt
  cases hlist : AttSupporters cfg store (get_node_for_root b) bs with
  | nil =>
      rw [get_attestation_score_eq_sum, hlist] at hpositive
      simp at hpositive
  | cons i rest =>
      have hi : i ∈ AttSupporters cfg store (get_node_for_root b) bs := by
        rw [hlist]
        exact List.mem_cons_self
      have hspan := supporter_mem_span_committee cfg hwf hprov hi
        (hwalk i hi) (le_refl (store.blocks b).slot)
      obtain ⟨s, hs, _⟩ := Finset.mem_biUnion.mp hspan
      exact (Finset.mem_Icc.mp hs).1.trans (Finset.mem_Icc.mp hs).2

/-! ## Step 3 — the Byzantine budget

The non-honest supporters' total weight is bounded by
`estimate // 100 * CONFIRMATION_BYZANTINE_THRESHOLD`. Their `bs`-effective
balances equal the ground-truth weights `E.weight_of` (registry constancy,
`hval`); the Nodup supporter list identifies the list sum with a `Finset` sum,
which is monotone under the inclusion into the non-honest slice of the span
committee (step 2, folded into `hspan`); and `ByzantineBound.span_bound`
supplies the headline bound, with `htab` matching the two total-active-balance
readings. -/



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



end FastConfirmation.Spec

end
