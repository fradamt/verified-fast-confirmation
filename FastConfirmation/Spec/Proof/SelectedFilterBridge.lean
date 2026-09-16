import FastConfirmation.Spec.Proof.SelectedFilter
import FastConfirmation.Spec.Proof.CheckpointDomain
import FastConfirmation.Spec.Proof.FFGAccountability

/-!
# Spec / Proof / SelectedFilterBridge: concrete FFG/store visibility

`SelectedFilter` recovers the booleans which an accepted executable FCR edge
actually passed.  `FFGCertificates` and `FFGAccountability` prove the
certificate-level Casper consequences.  This module connects the two as far as
the transcribed model permits, without using the generally false
`JustificationInterface.justified_ancestry`, `justified_descends`, or
`finalized_descent` fields.

There are two genuine model boundaries:

* `Externals.process_justification_and_finalization` and `state_transition` are
  opaque.  Their present coherence record constrains slots, registries, and
  checkpoint epochs, but does not say that a checkpoint written into an honest
  `Store` is backed by scheduled supermajority-link attestations.
* The same opaque functions write `unrealized_justifications` and block-state
  justified checkpoints read by `get_voting_source`.  Nothing in the handlers
  connects those reads to a concrete certificate, or guarantees their future
  recency on the selected branch.

Accordingly, `EndpointFFGPipeline` is the exact endpoint contract required of
the missing beacon-state FFG pipeline: the realized store fields have concrete
certificates, their certified prefix is represented by the endpoint store's
checkpoint walk, and the ordinary epoch order is preserved.  The separate
`TipSourceFresh` predicate is the exact call-site visibility output needed from
that pipeline for a chosen selected-branch tip.  Neither contract contains a
fork-choice-head or FCR-safety conclusion.

The main theorem `filterTipCertificate_of_pipeline` then derives the full
mechanical `FilterTipCertificate`.  In particular its `finalized_ok` field is
not assumed: it follows from concrete accountable safety plus checkpoint-walk
transport.  The only FFG leaf premise left verbatim is `TipSourceFresh`, because
the current executable model has no provenance from accepted `will_*` booleans
to future `get_voting_source` reads.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Executable accepted-edge facts and checkpoint-map provenance -/

/-- Updating the fast-confirmation bookkeeping does not mutate its fork-choice
store snapshot. -/
theorem update_fast_confirmation_variables_store
    (fcrStore : FastConfirmationStore Root) :
    (update_fast_confirmation_variables cfg fcrStore).store = fcrStore.store := by
  unfold update_fast_confirmation_variables
  dsimp only
  split <;> split <;> rfl

/-- The fast-confirmation handler only updates fast-confirmation bookkeeping;
its embedded fork-choice store is read-only. -/
theorem on_fast_confirmation_store (fcrStore : FastConfirmationStore Root) :
    (on_fast_confirmation cfg ext fcrStore).store = fcrStore.store := by
  simp only [on_fast_confirmation]
  exact update_fast_confirmation_variables_store cfg _

/-- The execution's FCR snapshot always carries the execution store at the
same second, including between the once-per-slot updates. -/
theorem Execution.fcr_store_eq (E : Execution Root) (v : ValidatorIndex) :
    ∀ n : ℕ, (E.fcr cfg ext v n).store = E.store cfg ext v n := by
  intro n
  induction n with
  | zero => rfl
  | succ n =>
      simp only [Execution.fcr]
      split_ifs
      · rw [on_fast_confirmation_store]
      · rfl

/-- Ghost trace of the complete executable wrapper.  The first edge list is
the selected previous-epoch trace.  The second is the tentative trace only
when the wrapper's final acceptance guard keeps its result; if that guard
rejects the tentative accumulator, its edges are erased as well. -/
def findLatestSelectedTrace (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot : Root) : Root × (List (Root × Root) × List (Root × Root)) :=
  let store := fcrStore.store
  let head := (get_head cfg store).root
  let currentEpoch := get_current_store_epoch cfg store
  let previousGuard :=
    get_block_epoch cfg store latestConfirmedRoot + 1 = currentEpoch ∧
        (get_voting_source cfg store fcrStore.previous_slot_head).epoch + 2 ≥
          currentEpoch ∧
        (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
          (will_no_conflicting_checkpoint_be_justified cfg ext store = true ∧
            ((store.unrealized_justifications fcrStore.previous_slot_head).epoch + 1 ≥
                currentEpoch ∨
              (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch)))
  let previousRoot :=
    if previousGuard then
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot
    else
      latestConfirmedRoot
  let previousEdges :=
    if previousGuard then
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch
        (get_ancestor_roots store head latestConfirmedRoot) latestConfirmedRoot).2
    else
      []
  let tentativeGuard :=
    is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
      (store.unrealized_justifications head).epoch + 1 ≥ currentEpoch
  let tentativeRoot :=
    if tentativeGuard then
      find_latest_confirmed_descendant_tentative_loop cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot
    else
      previousRoot
  let tentativeAccepted :=
    tentativeGuard ∧
      (get_block_epoch cfg store tentativeRoot = currentEpoch ∨
        ((get_voting_source cfg store tentativeRoot).epoch + 2 ≥ currentEpoch ∧
            (is_start_slot_at_epoch cfg (get_current_slot cfg store) = true ∨
              will_no_conflicting_checkpoint_be_justified cfg ext store = true)))
  let tentativeEdges :=
    if tentativeAccepted then
      (tentativeLoopTrace cfg ext fcrStore
        (get_ancestor_roots store head previousRoot) previousRoot).2
    else
      []
  (find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot,
    (previousEdges, tentativeEdges))

/-- Erasing both ghost edge lists gives the exact executable wrapper result. -/
theorem findLatestSelectedTrace_fst
    (fcrStore : FastConfirmationStore Root) (latestConfirmedRoot : Root) :
    (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).1 =
      find_latest_confirmed_descendant cfg ext fcrStore latestConfirmedRoot := by
  rfl

/-- Every tentative edge retained by the complete wrapper trace passed the
tentative loop's two executable guards. -/
theorem mem_findLatestSelectedTrace_tentative
    (fcrStore : FastConfirmationStore Root) (latestConfirmedRoot a c : Root)
    (h : (a, c) ∈
      (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2) :
    is_one_confirmed cfg ext fcrStore.store
        (get_current_balance_source fcrStore) c = true ∧
      (get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store c →
        will_current_target_be_justified cfg ext fcrStore.store = true) := by
  simp only [findLatestSelectedTrace] at h
  split_ifs at h <;> try simp at h
  all_goals
    exact mem_tentativeLoopTrace cfg ext fcrStore _ _ a c h

/-- A previous-loop edge retained by the complete wrapper trace. -/
def PreviousAcceptedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1

/-- Every retained previous-loop edge passed confirmation; its wrapper entry
also passed either the epoch-start escape or the no-conflict prediction. -/
theorem PreviousAcceptedEdge.gates
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    get_block_epoch cfg fcrStore.store c ≠
        get_current_store_epoch cfg fcrStore.store ∧
      is_ancestor fcrStore.store
        (get_node_for_root fcrStore.previous_slot_head)
        (get_node_for_root c) = true ∧
      is_one_confirmed cfg ext fcrStore.store
        (get_current_balance_source fcrStore) c = true ∧
      (is_start_slot_at_epoch cfg
          (get_current_slot cfg fcrStore.store) = true ∨
        will_no_conflicting_checkpoint_be_justified cfg ext
          fcrStore.store = true) := by
  simp only [PreviousAcceptedEdge, findLatestSelectedTrace] at h
  split_ifs at h with hentry <;> try simp at h
  have hm := mem_prevEpochLoopTrace cfg ext fcrStore _ _ _ a c h
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  rcases hentry.2.2 with hstart | ⟨hwill, _⟩
  · exact Or.inl hstart
  · exact Or.inr hwill

/-- Away from the epoch-start escape, every retained previous-loop edge
therefore has the executable no-conflict gate. -/
theorem PreviousAcceptedEdge.no_conflict_gate
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c)
    (hnot_start : is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true) :
    will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true := by
  rcases (h.gates cfg ext).2.2.2 with hstart | hgate
  · exact False.elim (hnot_start hstart)
  · exact hgate

/-- A selected-path tentative edge which actually crossed to a later block
epoch.  Unlike bare loop instrumentation, this predicate is indexed by the
wrapper input and excludes tentative edges discarded by the final acceptance
guard. -/
def CurrentTargetAcceptedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.2 ∧
    get_block_epoch cfg fcrStore.store a < get_block_epoch cfg fcrStore.store c

/-- A crossing tentative edge passed the executable
`will_current_target_be_justified` guard. -/
theorem CurrentTargetAcceptedEdge.current_target_gate
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    will_current_target_be_justified cfg ext fcrStore.store = true := by
  exact (mem_findLatestSelectedTrace_tentative cfg ext fcrStore
    latestConfirmedRoot a c h.1).2 h.2

/-- Every crossing tentative edge also passed `is_one_confirmed`. -/
theorem CurrentTargetAcceptedEdge.one_confirmed
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (h : CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) c = true := by
  exact (mem_findLatestSelectedTrace_tentative cfg ext fcrStore
    latestConfirmedRoot a c h.1).1

/-- A previous-epoch trace edge also passed `is_one_confirmed`. -/
theorem previousAcceptedEdge_one_confirmed
    (fcrStore : FastConfirmationStore Root) (currentEpoch : Epoch)
    (roots : List Root) (accumulator a c : Root)
    (h : (a, c) ∈
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots accumulator).2) :
    is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) c = true :=
  (mem_prevEpochLoopTrace cfg ext fcrStore currentEpoch roots accumulator a c h).2.2

/-- The totalized checkpoint map cannot make an accepted crossing edge pass
confirmation through an out-of-domain balance source.  At an actual execution
store, the current observed checkpoint used by the call is necessarily keyed.

This is the strongest handler-level checkpoint provenance presently derivable:
it proves dictionary membership, but not that the keyed checkpoint was
eventually justified or certified. -/
theorem CurrentTargetAcceptedEdge.current_balance_checkpoint_key
    {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (hstore : fcrStore.store = E.store cfg ext v n)
    (h : CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
  have hconf := h.one_confirmed cfg ext
  have hkey := E.checkpoint_state_key_of_one_confirmed cfg ext hgen v n
    fcrStore.current_epoch_observed_justified_checkpoint c
  rw [← hstore] at hkey
  apply hkey
  simpa only [get_current_balance_source] using hconf

/-- The exact-domain conclusion for an edge in the full wrapper's retained
previous trace. -/
theorem PreviousAcceptedEdge.current_balance_checkpoint_key
    {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    {fcrStore : FastConfirmationStore Root} {latestConfirmedRoot a c : Root}
    (hstore : fcrStore.store = E.store cfg ext v n)
    (h : PreviousAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c) :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
  have hconf := (h.gates cfg ext).2.2.1
  have hkey := E.checkpoint_state_key_of_one_confirmed cfg ext hgen v n
    fcrStore.current_epoch_observed_justified_checkpoint c
  rw [← hstore] at hkey
  apply hkey
  simpa only [get_current_balance_source] using hconf

/-- The same exact-domain conclusion for an accepted previous-epoch edge. -/
theorem previousAcceptedEdge_current_balance_checkpoint_key
    {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n)
    (currentEpoch : Epoch) (roots : List Root) (accumulator a c : Root)
    (h : (a, c) ∈
      (prevEpochLoopTrace cfg ext fcrStore currentEpoch roots accumulator).2) :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
  have hconf := previousAcceptedEdge_one_confirmed cfg ext fcrStore currentEpoch
    roots accumulator a c h
  have hkey := E.checkpoint_state_key_of_one_confirmed cfg ext hgen v n
    fcrStore.current_epoch_observed_justified_checkpoint c
  rw [← hstore] at hkey
  apply hkey
  simpa only [get_current_balance_source] using hconf

/-- Any strict wrapper result, regardless of which advancing loop produced it,
used an in-domain current observed checkpoint as its confirmation balance
source. -/
theorem selected_strict_current_balance_checkpoint_key
    {E : Execution Root}
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v : ValidatorIndex} {n : ℕ}
    (fcrStore : FastConfirmationStore Root)
    (hstore : fcrStore.store = E.store cfg ext v n)
    (lcr result : Root)
    (hout : find_latest_confirmed_descendant cfg ext fcrStore lcr = result)
    (hstrict : result ≠ lcr) :
    fcrStore.current_epoch_observed_justified_checkpoint ∈
      fcrStore.store.checkpoint_state_keys := by
  have hconf : is_one_confirmed cfg ext fcrStore.store
      (get_current_balance_source fcrStore) result = true := by
    rcases find_latest_confirmed_descendant_spec cfg ext fcrStore lcr with heq | hconfirmed
    · exact False.elim (hstrict (hout.symm.trans heq))
    · rwa [hout] at hconfirmed
  have hkey := E.checkpoint_state_key_of_one_confirmed cfg ext hgen v n
    fcrStore.current_epoch_observed_justified_checkpoint result
  rw [← hstore] at hkey
  apply hkey
  simpa only [get_current_balance_source] using hconf

/-- Away from the epoch-start escape hatch, a strict previous-epoch result
passed the executable no-conflicting-checkpoint gate. -/
theorem selected_previous_result_no_conflict_gate
    (fcrStore : FastConfirmationStore Root) (lcr result : Root)
    (hout : find_latest_confirmed_descendant cfg ext fcrStore lcr = result)
    (hstrict : result ≠ lcr)
    (hprevious : get_block_epoch cfg fcrStore.store result ≠
      get_current_store_epoch cfg fcrStore.store)
    (hnot_start : is_start_slot_at_epoch cfg
      (get_current_slot cfg fcrStore.store) ≠ true) :
    will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true := by
  rcases selected_previous_result_outer_gate cfg ext fcrStore lcr result
    hout hstrict hprevious with hstart | hgate
  · exact False.elim (hnot_start hstart)
  · exact hgate

/-! ## Concrete accountability, without global store-level ancestry axioms -/

/-- The two certificate-level consequences needed for finalized-prefix.  They
are the output of the concrete quorum/no-forgery proofs in
`FFGCertificates`, `FFGQuorum`, and `FFGAccountability`; keeping them in this
narrow record avoids importing any unrelated store-level
`JustificationInterface` law. -/
structure CertificateAccountability (E : Execution Root)
    (anchor : Checkpoint Root) : Prop where
  justified_unique : ∀ {x y : Checkpoint Root},
    CertifiedJustified cfg E anchor x →
    CertifiedJustified cfg E anchor y →
    x.epoch = y.epoch → x.root = y.root
  links_not_surround : ∀ {s t s' t' : Checkpoint Root},
    (L : SupermajorityLink cfg E s t) →
    (L' : SupermajorityLink cfg E s' t') →
    ¬ (s.epoch < s'.epoch ∧ t'.epoch < t.epoch)

/-- Every concretely certified justified checkpoint descends from the trusted
anchor.  This is structural induction over its link chain and needs no
accountability premise. -/
theorem CertifiedJustified.descends_anchor
    {E : Execution Root} {anchor justified : Checkpoint Root}
    (h : CertifiedJustified cfg E anchor justified) :
    E.RootDescends justified.root anchor.root := by
  induction h with
  | anchor => exact .refl _
  | link _ link ih =>
      exact Execution.RootDescends.trans E link.target_descends_source ih

/-- Concrete finalized-prefix from the narrow accountability record. -/
theorem CertificateAccountability.finalized_prefix
    {E : Execution Root} {anchor finalized justified : Checkpoint Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hf : CertifiedFinalized cfg E anchor finalized)
    (hj : CertifiedJustified cfg E anchor justified)
    (hepoch : finalized.epoch ≤ justified.epoch) :
    E.RootDescends justified.root finalized.root :=
  CertifiedFinalized.prefix_of_accountable cfg hacc.justified_unique
    hacc.links_not_surround hf hj hepoch

/-- Build the narrow accountability record from the concrete economic,
committee, no-forgery, and honest-slashing assumptions proved sufficient in
`FFGAccountability`.  No `JustificationInterface` premise is involved. -/
theorem CertificateAccountability.of_assumptions
    {E : Execution Root} {anchor : Checkpoint Root}
    (hA : FFGAccountabilityAssumptions cfg ext E) :
    CertificateAccountability cfg E anchor where
  justified_unique := fun hx hy he =>
    E.certified_justified_unique cfg ext hA hx hy he
  links_not_surround := fun L L' =>
    E.certified_links_not_surround cfg ext hA L L'

/-! ## Exact external FFG-pipeline contract -/

/-- Endpoint realization of the concrete certificate layer.

`certified_prefix_checkpoint` is deliberately conditional on the concrete
`RootDescends` proof.  Thus it does not assume arbitrary justified-checkpoint
ancestry: it says only that a prefix already proved from accountable safety is
represented faithfully by this endpoint store's block/checkpoint walk.  This
is precisely the provenance omitted by the opaque beacon-state transition. -/
structure EndpointFFGPipeline (E : Execution Root) (anchor : Checkpoint Root)
    (store : Store Root) : Prop where
  justified_root_known : store.justified_checkpoint.root ∈ store.block_roots
  justified_certificate :
    Nonempty (CertifiedJustified cfg E anchor store.justified_checkpoint)
  /-- Genesis-epoch finality is accepted directly by the executable filter;
  the trusted anchor needs no new in-segment finalizing link.  Any other
  finalized checkpoint carries a concrete certificate. -/
  finalized_evidence : store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
    store.finalized_checkpoint = anchor ∨
      Nonempty (CertifiedFinalized cfg E anchor store.finalized_checkpoint)
  finalized_epoch_le_justified :
    store.finalized_checkpoint.epoch ≤ store.justified_checkpoint.epoch
  finalized_boundary_le_justified_slot :
    compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch ≤
      (store.blocks store.justified_checkpoint.root).slot
  certified_prefix_checkpoint :
    store.finalized_checkpoint.epoch ≠ GENESIS_EPOCH →
      E.RootDescends store.justified_checkpoint.root
        store.finalized_checkpoint.root →
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store store.justified_checkpoint.root
          store.finalized_checkpoint.epoch

/-- Exact `correct_justified` visibility required at a selected-branch tip.
This is separated from `EndpointFFGPipeline`: accountable safety constrains
certificate compatibility, whereas recency of a future `get_voting_source`
read is an honest-participation/epoch-processing fact. -/
def TipSourceFresh (store : Store Root) (tip : Root) : Prop :=
  store.justified_checkpoint.epoch = GENESIS_EPOCH ∨
    (get_voting_source cfg store tip).epoch = store.justified_checkpoint.epoch ∨
    (get_voting_source cfg store tip).epoch + 2 ≥ get_current_store_epoch cfg store

namespace ChainDown

omit [Inhabited Root] in
/-- Every member of a `ChainDown` list is known and descends from its top.
This is the ancestry fact implicit in the list representation; exposing it
here avoids asking the FFG pipeline to supply a duplicate chain-placement
premise. -/
theorem mem_known_descends {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hwalk : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r) :
    ∀ {top : Root} {roots : List Root}, ChainDown store top roots →
      top ∈ store.block_roots →
      ∀ r ∈ roots, r ∈ store.block_roots ∧
        is_ancestor store (get_node_for_root r) (get_node_for_root top) = true := by
  intro top roots hchain htop r hr
  induction roots generalizing top with
  | nil => simp at hr
  | cons c rest ih =>
      simp only [ChainDown] at hchain
      obtain ⟨⟨hcmem, hcparent⟩, hrest⟩ := hchain
      have hc_top : is_ancestor store (get_node_for_root c)
          (get_node_for_root top) = true :=
        is_ancestor_of_parent hwf hcmem htop hcparent
      rw [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨hcmem, hc_top⟩
      · obtain ⟨hrmem, hr_c⟩ := ih hrest hcmem hr
        exact ⟨hrmem, is_ancestor_trans hwf
          (hwalk top htop r hrmem) (hwalk top htop c hcmem) hr_c hc_top⟩

end ChainDown

/-- Mechanical selected-branch data, excluding only the two leaf FFG checks.
The walk and boundary facts are ordinary finite-store domain facts; they are
kept explicit so the FFG pipeline contract itself contains no fork-choice
conclusion. -/
structure FilterTipSkeleton (store : Store Root) (c : Root) where
  mids : List Root
  tip : Root
  chain : ChainDown store store.justified_checkpoint.root (mids ++ [tip])
  child_on_chain : c ∈ mids ∨ c = tip ∨ c = store.justified_checkpoint.root
  tip_is_leaf : store.block_roots.filter
    (fun x => (store.blocks x).parent_root = tip) = []
  parent_slot_lt : ∀ r ∈ store.block_roots,
    (store.blocks r).parent_root ∈ store.block_roots →
      (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot
  walk_known : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
    WalkKnown store (store.blocks t).slot r
  finalized_walk_known : WalkKnown store
    (compute_start_slot_at_epoch cfg store.finalized_checkpoint.epoch) tip

/-- The complete, narrow external contract needed to turn accepted executable
gates into endpoint filter viability.

The first field is the narrow concrete Casper assumption bundle and the
second realizes its certificates in each endpoint store.  The latter two are
call-site visibility statements, gated by the spec's own
`HonestVotesSupportTarget` proviso.  They mention only the selected-branch
leaf's `get_voting_source` recency and existentially choose one viable leaf;
they do not require every adversarial leaf to be fresh and do not assume that
the endpoint head already descends from the selected block.  When the endpoint
justified root has advanced below the selected block, no `FilterTipSkeleton`
through that block exists and the surrounding safety proof uses direct
justified coverage instead of this filter branch.  Accordingly each source
field is conditional on that direct-coverage test being false; it never
postulates the coverage alternative itself.

Endpoint order is deliberately by **slot**, not by second: a late in-slot
query must also establish the filter fact at every honest slot-start store in
that same slot.  This is a retrospective proof obligation from the accepted
edge's already-delivered past-slot support; it is not backward message
propagation.  The executable model can derive the selected root's slot-start
knownness through `SameSlotProvenance`, but cannot derive this FFG source
recency because the state-transition checkpoint writes are opaque. -/
structure SelectedFilterFFGPipeline (E : Execution Root)
    (anchor : Checkpoint Root) : Prop where
  accountability_assumptions : FFGAccountabilityAssumptions cfg ext E
  endpoint : ∀ w ∈ E.honest, ∀ m : ℕ, E.WithinHorizon cfg m →
    EndpointFFGPipeline cfg E anchor (E.store cfg ext w m)
  current_target_tip_source :
    ∀ v ∈ E.honest, ∀ n : ℕ,
      E.WithinHorizon cfg n →
      ∀ (fcrStore : FastConfirmationStore Root),
      fcrStore = E.fcr cfg ext v n →
      fcrStore.current_epoch_observed_justified_checkpoint ∈
        fcrStore.store.checkpoint_state_keys →
      ∀ latestConfirmedRoot a c : Root,
      CurrentTargetAcceptedEdge cfg ext fcrStore latestConfirmedRoot a c →
      will_current_target_be_justified cfg ext fcrStore.store = true →
      HonestVotesSupportTarget cfg E
        (get_current_target cfg fcrStore.store) n →
      ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg n ≤ E.slot_at cfg m → E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root c) ≠ true →
      ∃ hskel : FilterTipSkeleton cfg (E.store cfg ext w m) c,
        TipSourceFresh cfg (E.store cfg ext w m) hskel.tip
  no_conflict_tip_source :
    ∀ v ∈ E.honest, ∀ n : ℕ,
      E.WithinHorizon cfg n →
      ∀ (fcrStore : FastConfirmationStore Root),
      fcrStore = E.fcr cfg ext v n →
      fcrStore.current_epoch_observed_justified_checkpoint ∈
        fcrStore.store.checkpoint_state_keys →
      ∀ lcr result : Root,
      find_latest_confirmed_descendant cfg ext fcrStore lcr = result →
      result ≠ lcr →
      get_block_epoch cfg fcrStore.store result ≠
        get_current_store_epoch cfg fcrStore.store →
      will_no_conflicting_checkpoint_be_justified cfg ext fcrStore.store = true →
      HonestVotesSupportTarget cfg E
        (get_current_target cfg fcrStore.store) n →
      ∀ w ∈ E.honest, ∀ m : ℕ,
      E.slot_at cfg n ≤ E.slot_at cfg m → E.WithinHorizon cfg m →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root result) ≠ true →
      ∃ hskel : FilterTipSkeleton cfg (E.store cfg ext w m) result,
        TipSourceFresh cfg (E.store cfg ext w m) hskel.tip

/-!
### Scope

This module deliberately states `SelectedFilterFFGPipeline` as the narrow
store/certificate visibility contract used by the selected-filter bridge.

`HonestVotesSupportTarget` also remains an explicit call-site premise.  The
present proof tree contains no theorem deriving its cross-validator target
agreement from `HonestBehavior`; doing so is the documented E6 obligation.

The current-target theorem below covers every retained epoch-crossing
tentative trace edge, including at epoch start.  The previous-result theorem
covers a strict retained previous-epoch result only away from epoch start,
where the executable outer disjunction forces the no-conflict boolean.  A
result-level certificate does not separately certify every intermediate edge
in the retained previous trace.  A
previous-epoch advancement admitted solely by the epoch-start escape has no
`will_*` premise from which this bridge can derive future source freshness and
is intentionally not covered here.
-/

/-! ## Mechanical assembly -/

/-- The concrete certificate pipeline proves the finalized leaf check at a
selected-branch tip.  The proof first derives finalized-prefix from concrete
accountability, realizes that prefix at the endpoint's justified root, then
transports the checkpoint-boundary equality down the selected branch. -/
theorem EndpointFFGPipeline.finalized_ok_of_tip
    {E : Execution Root} {anchor : Checkpoint Root}
    {store : Store Root} {c : Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hpipe : EndpointFFGPipeline cfg E anchor store)
    (hskel : FilterTipSkeleton cfg store c) :
    store.finalized_checkpoint.epoch = GENESIS_EPOCH ∨
      store.finalized_checkpoint.root =
        get_checkpoint_block cfg store hskel.tip
          store.finalized_checkpoint.epoch := by
  by_cases hgen : store.finalized_checkpoint.epoch = GENESIS_EPOCH
  · exact Or.inl hgen
  right
  have hprefix : E.RootDescends store.justified_checkpoint.root
      store.finalized_checkpoint.root := by
    obtain ⟨hj⟩ := hpipe.justified_certificate
    rcases hpipe.finalized_evidence with hgen' | htrusted | hcertified
    · exact False.elim (hgen hgen')
    · rw [htrusted]
      exact hj.descends_anchor cfg
    · obtain ⟨hf⟩ := hcertified
      exact hacc.finalized_prefix cfg hf hj hpipe.finalized_epoch_le_justified
  have hbase := hpipe.certified_prefix_checkpoint hgen hprefix
  have htip_descends := (ChainDown.mem_known_descends hskel.parent_slot_lt
    hskel.walk_known hskel.chain hpipe.justified_root_known hskel.tip
      (by simp)).2
  exact finalized_check_of_ancestor cfg hskel.parent_slot_lt htip_descends
    hpipe.finalized_boundary_le_justified_slot hskel.finalized_walk_known hbase

/-- Full filter-tip certificate from the exact endpoint FFG contract and a
call-site voting-source freshness witness.  No global justified ancestry,
head-descent, or cross-store finalized-descent premise occurs. -/
def filterTipCertificate_of_pipeline
    {E : Execution Root} {anchor : Checkpoint Root}
    {store : Store Root} {c : Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hpipe : EndpointFFGPipeline cfg E anchor store)
    (hskel : FilterTipSkeleton cfg store c)
    (hsource : TipSourceFresh cfg store hskel.tip) :
    FilterTipCertificate cfg store c where
  mids := hskel.mids
  tip := hskel.tip
  chain := hskel.chain
  child_on_chain := hskel.child_on_chain
  tip_is_leaf := hskel.tip_is_leaf
  parent_slot_lt := hskel.parent_slot_lt
  justified_ok := hsource
  finalized_ok := hpipe.finalized_ok_of_tip cfg hacc hskel

/-- Direct `child_filtered` output for the selected-margin producer. -/
theorem selected_child_filtered_of_pipeline
    {E : Execution Root} {anchor : Checkpoint Root}
    {store : Store Root} {a c : Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hpipe : EndpointFFGPipeline cfg E anchor store)
    (hskel : FilterTipSkeleton cfg store c)
    (hsource : TipSourceFresh cfg store hskel.tip)
    (hparent : (store.blocks c).parent_root = a) :
    ForkChoiceNode.mk c ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk a) := by
  exact (filterTipCertificate_of_pipeline cfg hacc hpipe hskel hsource)
    |>.child_filtered cfg hparent

omit [Inhabited Root] in
/-- Eliminate the call-site existential certificate directly into the
`child_filtered` proposition consumed by the selected-margin producer. -/
theorem child_filtered_of_filterTipCertificate_nonempty
    {store : Store Root} {a c : Root}
    (h : Nonempty (FilterTipCertificate cfg store c))
    (hparent : (store.blocks c).parent_root = a) :
    ForkChoiceNode.mk c ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk a) := by
  obtain ⟨hcert⟩ := h
  exact hcert.child_filtered cfg hparent

end FastConfirmation.Spec
