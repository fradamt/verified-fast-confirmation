module
public import FastConfirmation.Spec.Proof.Delivery

@[expose] public section

/-!
# Spec / Proof / MajorityPersists: the persistence ledger

The two-window accounting behind head persistence: the honest
majority established by the confirmation inequality over the OLD window
(`[parent(b).slot+1, s−1]`) plus honest coverage of the NEW window
(`[s, k−1]`) strictly dominates any sibling's budget at every later honest
store — the spec-side analogue of the paper's `childWeight_sibling_le` +
`Hmaj_step` arithmetic.

This module holds the pure ℕ ledger; the set-accounting instantiation
(recorded-support lower bound via `vote_ubiquity`, the sibling upper bound
via provenance slot-confinement + sibling disjointness + the
zero-contribution argument for pre-fork committee slots) composes with the
engine assembly.
-/

namespace FastConfirmation.Spec

/-- The persistence ledger, additive form (truncation-free). Hypotheses and
their instantiation sources:
- `hconf`: the confirmation inequality at `v/n₀`
  (`honest_support_majority` + `estimate_sound`, old window `Wold`);
- `hD`: `support_discount` soundness — the discount is at most the weight
  `D` genuinely stuck on the fork parent;
- `hnb`: new-window Byzantine recorded support is at most new-window honest
  recorded support (`span_bound` + honest coverage under
  `CONFIRMATION_BYZANTINE_THRESHOLD ≤ 25` and the 5‰-adjusted estimate);
- `hsib`: the disjoint decomposition — sibling supporters, `b`'s old honest
  supporters, and the stuck-on-parent set are pairwise disjoint inside the
  old-window members plus new-window Byzantine voters;
- `hscore`: `b`'s recorded support at the later store contains the old
  honest supporters and the new honest voters (`vote_ubiquity` + the
  engine IH).
Conclusion: the sibling loses even with the full proposer boost. -/
theorem persists_ledger {H0 Hnew Bnew Wold D discount boost sib scoreC : ℕ}
    (hconf : Wold + boost + 1 ≤ 2 * H0 + discount)
    (hD : discount ≤ D)
    (hnb : Bnew ≤ Hnew)
    (hsib : sib + H0 + D ≤ Wold + Bnew)
    (hscore : H0 + Hnew ≤ scoreC) :
    sib + boost < scoreC := by
  omega

/-! ## The `get_weight` bridge to `Descent.DescendsTo`

`Descent.lean`'s `hdom` fork condition is stated in terms of `get_weight`, the
fork-choice weight (attestation score + the proposer boost, added at most once).
The ledger conclusion `sib + boost < scoreC` is in raw attestation-score terms
(`sib`/`scoreC` = the siblings' scores, `boost` = the full proposer boost). The
bridge below turns a strict attestation-score-plus-boost inequality into the
`get_weight` strict inequality: the losing sibling gets the boost charged in
full, the winner keeps at least its bare score. -/

variable {Root : Type*} [LinearOrder Root] [Inhabited Root] (cfg : Config)

/-- `get_weight` is at most the bare attestation score plus the full proposer
boost: the boost is added at most once, and only when the boost root is set and
an ancestor of `node`. -/
theorem get_weight_le (store : Store Root) (node : ForkChoiceNode Root) :
    get_weight cfg store node ≤
      get_attestation_score cfg store node
          (store.checkpoint_states store.justified_checkpoint)
        + get_proposer_score cfg store := by
  simp only [get_weight]
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _
  · exact Nat.add_le_add_left (Nat.zero_le _) _

/-- A node which is not a previous-slot payload decision keeps its bare
attestation score. Gloas gives previous-slot resolved nodes zero weight. -/
theorem get_weight_ge_of_not_payload_decision (store : Store Root)
    (node : ForkChoiceNode Root)
    (h : is_previous_slot_payload_decision cfg store node = false) :
    get_attestation_score cfg store node
        (store.checkpoint_states store.justified_checkpoint)
      ≤ get_weight cfg store node := by
  simp only [get_weight, h, Bool.false_eq_true, if_false]
  split_ifs
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _

/-- Pending beacon-root support is a lower bound for its Gloas weight. -/
theorem get_weight_ge (store : Store Root) (root : Root) :
    get_attestation_score cfg store (ForkChoiceNode.mk root .pending)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ get_weight cfg store (ForkChoiceNode.mk root .pending) := by
  apply get_weight_ge_of_not_payload_decision
  simp [is_previous_slot_payload_decision]

/-- **The fork-weight bridge.** If the sibling `c'`'s bare attestation score plus
the full proposer boost is strictly below `c`'s bare attestation score, then
`c'` loses to `c` in `get_weight` — the exact single-sibling shape of
`Descent.DescendsTo`'s `hdom`. Both scores are read against the justified
checkpoint state, the balance source `get_weight` uses. -/
theorem fork_weight_lt {store : Store Root} {c c' : Root}
    (hlt : get_attestation_score cfg store (ForkChoiceNode.mk c' .pending)
          (store.checkpoint_states store.justified_checkpoint)
        + get_proposer_score cfg store
      < get_attestation_score cfg store (ForkChoiceNode.mk c .pending)
          (store.checkpoint_states store.justified_checkpoint)) :
    get_weight cfg store (ForkChoiceNode.mk c' .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) :=
  lt_of_le_of_lt (get_weight_le cfg store _) (lt_of_lt_of_le hlt (get_weight_ge cfg store _))

/-- **`fork_majority`** — the per-fork weight inequality `Descent.DescendsTo`'s
`hdom` consumes, assembled from `persists_ledger` and `fork_weight_lt`. The
five hypotheses are the ledger inputs in their spec-side shapes at the later
honest store, read against the justified checkpoint state:

- `hconf` — the confirmation inequality (`honest_support_majority` at `v/n₀`,
  with `Wold` the OLD-window maximum-support estimate and `boost` the proposer
  score, which registry constancy keeps equal across stores);
- `hD` — `support_discount` soundness (`discount ≤ D`, the fork-parent stuck
  weight);
- `hnb` — the new-window Byzantine budget is covered by honest voters
  (`Bnew ≤ Hnew`, result 3);
- `hsib` — the sibling upper bound (`c'`'s score plus `H0 + D` fits in the
  old-window plus new-window Byzantine budget, result 2);
- `hscore` — the recorded-support lower bound (`c`'s score at `w/m` covers the
  old honest supporters plus the new honest voters, result 1).

The conclusion is the `get_weight` strict domination of `c` over its sibling
`c'`. -/
theorem fork_majority {store : Store Root} {c c' : Root}
    {H0 Hnew Bnew Wold D discount : ℕ}
    (hconf : Wold + get_proposer_score cfg store + 1 ≤ 2 * H0 + discount)
    (hD : discount ≤ D)
    (hnb : Bnew ≤ Hnew)
    (hsib : get_attestation_score cfg store (ForkChoiceNode.mk c' .pending)
          (store.checkpoint_states store.justified_checkpoint) + H0 + D ≤ Wold + Bnew)
    (hscore : H0 + Hnew ≤ get_attestation_score cfg store (ForkChoiceNode.mk c .pending)
          (store.checkpoint_states store.justified_checkpoint)) :
    get_weight cfg store (ForkChoiceNode.mk c' .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) :=
  fork_weight_lt cfg (persists_ledger hconf hD hnb hsib hscore)

/-! ## Set-accounting helper for the recorded-support lower bound (result 1)

`get_attestation_score` at the later honest store is the ground-truth weight of
its whole supporter set `AttSupporters` (registry constancy identifies the
balance-source effective balances with `E.weight_of`; the supporter list is
`Nodup`). So any set of validators known to support the node at that store
contributes a *lower* bound — reducing result 1 (`H0 + Hnew ≤ score c`) to
the membership fact that every old honest supporter and every new honest voter
records a `c`-supporting latest message at `w/m`. -/

omit [Inhabited Root] in
/-- **Recorded-support lower bound (set form).** On a registry-constant balance
source, the attestation score of `node` at `store` is at least the ground-truth
weight of any validator set `HS` all of whose members support `node` there
(`hmem`: each sits in the supporter list). Mirrors
`QuorumAccounting.byz_score_eq_weight` on the lower-bound side. -/
theorem recorded_support_lower {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {node : ForkChoiceNode Root} (hval : bs.validators = E.registry)
    (HS : Finset ValidatorIndex)
    (hmem : ∀ i ∈ HS, i ∈ AttSupporters cfg store node bs) :
    E.weight HS ≤ get_attestation_score cfg store node bs := by
  have hnodup : (AttSupporters cfg store node bs).Nodup := AttSupporters_nodup cfg store node bs
  have hmapeq : (AttSupporters cfg store node bs).map
        (fun i => (bs.validators.getD i default).effective_balance)
      = (AttSupporters cfg store node bs).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [get_attestation_score_eq_sum, hmapeq, ← List.sum_toFinset E.weight_of hnodup]
  simp only [Execution.weight]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro i hi
  rw [List.mem_toFinset]
  exact hmem i hi

omit [Inhabited Root] in
/-- **Score = ground-truth supporter weight.** On a registry-constant balance
source, the attestation score of `node` at `store` is exactly the ground-truth
weight of its supporter set (the `Nodup` list `AttSupporters`, its balance-source
effective balances identified with `E.weight_of`). This is the identity behind
both the recorded-support lower bound (a supporting subset lower-bounds it) and
the sibling upper bound (the sibling's supporter set is confined and disjoint
from `b`'s). -/
theorem attestation_score_eq_weight {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} {node : ForkChoiceNode Root} (hval : bs.validators = E.registry) :
    get_attestation_score cfg store node bs =
      E.weight (AttSupporters cfg store node bs).toFinset := by
  have hnodup : (AttSupporters cfg store node bs).Nodup := AttSupporters_nodup cfg store node bs
  have hmapeq : (AttSupporters cfg store node bs).map
        (fun i => (bs.validators.getD i default).effective_balance)
      = (AttSupporters cfg store node bs).map E.weight_of :=
    List.map_congr_left (fun i _ => by rw [Execution.weight_of, hval])
  rw [get_attestation_score_eq_sum, hmapeq, ← List.sum_toFinset E.weight_of hnodup]
  rfl

omit [Inhabited Root] in
/-- **Sibling supporter disjointness (set form).** The supporter sets of two
distinct children `c ≠ c'` of one parent `p` are disjoint at any store: no index
supports both siblings (`SupportTransport.no_index_supports_both_siblings`). The
`hwalk` domain condition supplies, for every recorded latest message, the
`WalkKnown` witnesses down to each sibling's slot the incompatibility needs.
This is the disjointness core of the sibling upper bound (result 2): with
`attestation_score_eq_weight` it gives `score c' + weight(b-supporters) ≤
weight(any common superset)`. -/
theorem supporters_disjoint {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {bs : BeaconState Root} {p c c' : Root}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots) (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p) (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c')
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks c).slot lm.root ∧
      WalkKnown store (store.blocks c').slot lm.root) :
    Disjoint (AttSupporters cfg store (get_node_for_root c) bs).toFinset
      (AttSupporters cfg store (get_node_for_root c') bs).toFinset := by
  rw [Finset.disjoint_left]
  intro i hic hic'
  rw [List.mem_toFinset] at hic hic'
  obtain ⟨lm, hlm, _, hancc⟩ := mem_AttSupporters cfg hic
  obtain ⟨lm', hlm', _, hancc'⟩ := mem_AttSupporters cfg hic'
  have hlmeq : lm' = lm := Option.some_inj.mp (hlm'.symm.trans hlm)
  obtain ⟨hwc, hwc'⟩ := hwalk i lm hlm
  exact no_index_supports_both_siblings hwf hc hc' hp hpc hpc' hne hwc hwc' hancc (hlmeq ▸ hancc')

end FastConfirmation.Spec

end
