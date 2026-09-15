import FastConfirmation.Spec.Proof.SelectedEdgeGeometry
import FastConfirmation.Spec.Proof.WeakSelectorBetween
import FastConfirmation.Spec.Proof.WeakOneShotSafety

/-!
# Spec / Proof / WeakSelectedEdgeGeometry

Margin-discharge wave, Stage J-d: the weak twin of
`SelectedEdgeGeometry.StrictSelectedEdgeGeometry` /
`strictSelectedEdgeGeometry_of_query_minimal`, read at an arbitrary (not
necessarily honest) observer.

`Weak.StrictSelectedEdgeGeometry` is a verbatim clone of the strong record
with

* `result_eq` over `Weak.find_latest_confirmed_descendant`;
* `confirmation` over `Weak.is_one_confirmed`;
* three new endpoint fields `endpoint_block_known` / `endpoint_parent_known`
  / `endpoint_parent_eq`.

The strong record leaves those last three implicit because its consumers
re-derive them from the whole-store inclusion
`(E.store cfg ext u nu).block_roots ⊆ (E.store cfg ext v q).block_roots`
(`hsubUQ` in the strong producer), which is obtained by relaying the honest
past store *into the observer* — `PaperSafetySynchrony.block_relay u hu nu …
v hv q hqH`. That relay direction is exactly what the weak model forbids: the
observer need not be honest, so nothing is ever delivered to it. Here the
endpoint-side block data therefore becomes structure data, supplied by the
producer out of the material every caller already holds at `(w, m)`.

## Substitutions in the producer (design §2-J3)

* `store_domainK_of_selectedMarginDomain … hv q` ↦ `store_parentSlotLt` /
  `store_walkKnownK` (both already proved for an arbitrary node);
* `head_root_known_of_selectedMarginDomain … hv q` ↦ `get_head_root_mem_or`
  + `hW.coherence.justified_root_known` (the `hheadConfirm` idiom of
  `WeakOneShotSafety` §5);
* `find_latest_confirmed_descendant_selected_minimal` ↦
  `find_latest_confirmed_descendant_selected_minimal_weak`; its
  `WeakSelectorGuardEvidence` disjunct is discarded exactly where the strong
  proof discards the certificate, and its strong `is_one_confirmed` component
  is what feeds the two dissemination calls below;
* `find_latest_confirmed_descendant_ge` ↦
  `weak_find_latest_confirmed_descendant_ge`;
* `confirmed_ancestry_at_all_honest_endpoints_minimal` ↦
  `confirmed_ancestry_at_all_honest_endpoints_at_observer`;
* `confirmed_pastDescendant_minimal` ↦ `confirmed_pastDescendant_at_observer`;
* `hsubUQ` + `hagreeUQ` + `chain_descent_restrict` into the query store ↦
  `is_ancestor_transport_closed` / `is_ancestor_replay_closed` at the
  doubly-known witness `d`, plus containment-free
  `WellFormedExecution.blocks_agree`;
* `find_latest_confirmed_descendant_between` ↦
  `Weak.find_latest_confirmed_descendant_between`.

The *endpoint* leg (`hsubUM`, honest `w`) is untouched: `u` and `w` are both
honest, so `block_relay` between them is available, and the three
`chain_descent_restrict` pulls of `c`, `a` and `r0` back into `u`'s store are
verbatim. Only the observer leg is rebuilt. The doubly-known witness `d`
(known at `u`'s own store *and* at the observer's, from
`Execution.confirmed_pastDescendant_at_observer`) drives every observer-side
step:

* `glc` is pushed from the observer's store into `u`'s store
  (`is_ancestor_transport_closed`, with the observer-side ancestry
  `is_ancestor (E.store cfg ext obs q) d glc`), replacing the first
  `chain_descent_restrict`;
* `c` and `a` are pulled back from `u`'s store into the observer's store
  (`is_ancestor_transport_closed` along `d → glc → c` and `d → glc → a`),
  replacing `hsubUQ hcU` / `hsubUQ haU`;
* the two query-side ancestries `glc → c` and `c → r0` come from
  `is_ancestor_replay_closed` at the now doubly-known `glc` and `c`,
  replacing the `is_ancestor_congr`-over-`hagreeUQ` steps;
* `hagreeUQ` itself survives as the containment-free
  `WellFormedExecution.blocks_agree` at roots known to *both* stores, which is
  all the parent-root and child-slot bookkeeping ever needed it for.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-- Query-local, canonical coordinates and geometry for one strict edge of an
actual `Weak.find_latest_confirmed_descendant` result, read at an arbitrary
(not necessarily honest) observer `obs`.

Verbatim clone of `Execution.StrictSelectedEdgeGeometry` with `v := obs`,
`result_eq` over the weak selector and `confirmation` over
`Weak.is_one_confirmed`, plus the three endpoint fields
`endpoint_block_known` / `endpoint_parent_known` / `endpoint_parent_eq`,
which the strong record's consumers re-derive from the observer-relay leg
`hsubUQ` the weak model forbids. As in the strong record, the contents are
only executable selection, block-domain, clock, horizon and epoch-regime
facts: no filter, recording, sibling-score or cross-epoch accounting. -/
structure StrictSelectedEdgeGeometry
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (glc r0 a c : Root) (obs : ValidatorIndex) (q : Nat)
    (query : FastConfirmationStore Root)
    (w : ValidatorIndex) (m : Nat)
    (lo es sigma querySlot : Slot) : Prop where
  query_store_eq : query.store = E.store cfg ext obs q
  result_eq : Weak.find_latest_confirmed_descendant cfg ext query r0 = glc
  confirmation : Weak.is_one_confirmed cfg ext query.store
    (get_current_balance_source query) c = true
  block_known : c ∈ (E.store cfg ext obs q).block_roots
  parent_known : ((E.store cfg ext obs q).blocks c).parent_root ∈
    (E.store cfg ext obs q).block_roots
  parent_eq : ((E.store cfg ext obs q).blocks c).parent_root = a
  endpoint_block_known : c ∈ (E.store cfg ext w m).block_roots
  endpoint_parent_known : ((E.store cfg ext obs q).blocks c).parent_root ∈
    (E.store cfg ext w m).block_roots
  endpoint_parent_eq : ((E.store cfg ext w m).blocks c).parent_root =
    ((E.store cfg ext obs q).blocks c).parent_root
  result_to_child : is_ancestor (E.store cfg ext obs q)
    (get_node_for_root glc) (get_node_for_root c) = true
  child_to_anchor : is_ancestor (E.store cfg ext obs q)
    (get_node_for_root c) (get_node_for_root r0) = true
  parent_slot_lt : ((E.store cfg ext obs q).blocks
      ((E.store cfg ext obs q).blocks c).parent_root).slot <
    ((E.store cfg ext obs q).blocks c).slot
  child_slot_le_cutoff : ((E.store cfg ext obs q).blocks c).slot ≤ es
  lo_eq : lo = ((E.store cfg ext obs q).blocks
    ((E.store cfg ext obs q).blocks c).parent_root).slot + 1
  cutoff_eq : es = get_current_slot cfg query.store - 1
  query_slot_eq : querySlot = get_current_slot cfg query.store
  sigma_eq : sigma = E.slot_at cfg m - 1
  confirming_cutoff : E.slot_at cfg q = es + 1
  lo_le_cutoff : lo ≤ es
  cutoff_le_sigma : es ≤ sigma
  start_le_cutoff : E.slot_at cfg 0 ≤ es
  sigma_lt_endpoint : sigma < E.slot_at cfg m
  lo_horizon : E.SlotWithinHorizon cfg lo
  cutoff_horizon : E.SlotWithinHorizon cfg es
  sigma_horizon : E.SlotWithinHorizon cfg sigma
  regime : Execution.StrictSelectedEdgeRegime cfg
    (E.store cfg ext obs q) c lo sigma

end Weak

end FastConfirmation.Spec
