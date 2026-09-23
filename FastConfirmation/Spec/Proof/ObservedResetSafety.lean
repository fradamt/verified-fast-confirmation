module
public import FastConfirmation.Spec.Proof.FinalizedResetSafety
public import FastConfirmation.Spec.Proof.Descent

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Genesis and observed-reset safety without the legacy justification interface

The public trajectory fold used to demand `SafeFrom` for the rotated observed
checkpoint on every slot update, even though `get_latest_confirmed` reads that
checkpoint as a reset input only when its epoch-start restart guard fires.  This
file makes the executable branch condition explicit and scopes the reset
obligation to that condition.

The local half of the restart is fully concrete: the guard says that the
observed checkpoint is the unrealized justification of the query head.  The
common `ChainFFGState` therefore identifies it with `GU(head)`, supplies AU
evidence, and realizes it as the corresponding checkpoint on the head chain.

The cross-view half has two protocol-native ways to finish:

* the endpoint justified checkpoint has a concrete justification chain whose
  trusted anchor is the observed checkpoint; or
* while the endpoint still lags that checkpoint, the filtered LMD-GHOST tree
  has an explicit weight-dominant descent from its justified root to the
  observed root.

The first case is turned into concrete store ancestry by execution-parent
reflection.  The second is consumed directly by the ordinary GHOST descent
theorem.  Neither branch assumes a head/ancestry/`SafeFrom` conclusion.

The trusted genesis anchor needs neither branch: every concretely certified
global justified checkpoint descends from it, so the filter root and hence the
head do as well.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The exact restart core -/

/-- The three safety-relevant conjuncts of the executable observed restart.

The fourth executable conjunct only says that the restart moves the candidate
strictly forward.  It is irrelevant to placement of the restart checkpoint and
is deliberately omitted here. -/
structure ObservedRestartCompatible
    (fcrStore : FastConfirmationStore Root) : Prop where
  epoch_start :
    is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) = true
  root_previous_epoch :
    get_block_epoch cfg fcrStore.store
        fcrStore.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg fcrStore.store
  observed_eq_head_unrealized :
    fcrStore.current_epoch_observed_justified_checkpoint =
      fcrStore.store.unrealized_justifications
        (get_head cfg fcrStore.store).root

/-- Boolean form of the exact restart guard, parameterized by the candidate
after the preceding finalized-reset test. -/
def observedRestartGuard
    (fcrStore : FastConfirmationStore Root) (candidate : Root) : Bool :=
  is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) &&
    decide (get_block_epoch cfg fcrStore.store
        fcrStore.current_epoch_observed_justified_checkpoint.root + 1 =
      get_current_store_epoch cfg fcrStore.store) &&
    decide (fcrStore.current_epoch_observed_justified_checkpoint =
      fcrStore.store.unrealized_justifications
        (get_head cfg fcrStore.store).root) &&
    decide (get_block_slot fcrStore.store candidate <
      get_block_slot fcrStore.store
        fcrStore.current_epoch_observed_justified_checkpoint.root)

/-- Firing the executable Boolean restart guard supplies its three
safety-relevant conjuncts. -/
theorem observedRestartCompatible_of_guard
    (fcrStore : FastConfirmationStore Root) (candidate : Root)
    (hguard : observedRestartGuard cfg fcrStore candidate = true) :
    ObservedRestartCompatible cfg fcrStore := by
  simp only [observedRestartGuard, Bool.and_eq_true, decide_eq_true_eq] at hguard
  exact ⟨hguard.1.1.1, hguard.1.1.2, hguard.1.2⟩

namespace Execution

variable (E : Execution Root)

/-- Under the common semantic FFG state, the exact restart checkpoint is AU
on the actual query head.  This is the formal local content of the paper's
`GU(head) = observed` active-restart conjunct. -/
theorem observedRestart_AU_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hrestart : ObservedRestartCompatible cfg (E.fcrStep cfg ext v n)) :
    S.AU cfg (get_head cfg (E.store cfg ext v (n + 1))).root
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint := by
  have hheadKnown : (get_head cfg (E.store cfg ext v (n + 1))).root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (n + 1)) with hhead | hfallback
    · exact hhead
    · rw [hfallback]
      exact E.justifiedRootKnown_of_globalTrajectory cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hcoh hanchor hboundary hv (n + 1) hHn1
  have hprojection := E.unrealized_justification_eq hcoh v (n + 1) hheadKnown
  have hGU :
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
        S.GU (get_head cfg (E.store cfg ext v (n + 1))).root := by
    rw [hrestart.observed_eq_head_unrealized, E.fcrStep_store]
    exact hprojection
  rw [hGU]
  exact S.gu_AU cfg (get_head cfg (E.store cfg ext v (n + 1))).root
    ⟨(E.store cfg ext v (n + 1)).blocks
        (get_head cfg (E.store cfg ext v (n + 1))).root,
      E.blockAt_of_store_known cfg ext hheadKnown⟩

/-- The same local restart evidence identifies the observed checkpoint with
the concrete epoch checkpoint of the actual query head. -/
theorem observedRestart_checkpoint_on_queryHead
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hrestart : ObservedRestartCompatible cfg (E.fcrStep cfg ext v n)) :
    (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint =
      get_checkpoint_for_block cfg (E.store cfg ext v (n + 1))
        (get_head cfg (E.store cfg ext v (n + 1))).root
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch := by
  have hheadKnown : (get_head cfg (E.store cfg ext v (n + 1))).root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (n + 1)) with hhead | hfallback
    · exact hhead
    · rw [hfallback]
      exact E.justifiedRootKnown_of_globalTrajectory cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hcoh hanchor hboundary hv (n + 1) hHn1
  exact hcoh.au_checkpoint_of_known v hv (n + 1) hHn1 _ hheadKnown _
    (E.observedRestart_AU_of_globalTrajectory cfg ext hA hcoh hanchor
      hboundary hv hHn1 hrestart)

/-! ## Cross-view certificate-or-filter takeover -/

/-- Concrete endpoint evidence sufficient for a checkpoint to be below the
endpoint fork-choice head.

The certificate branch says that the endpoint's realized justified checkpoint
is obtained by a real FFG link chain anchored at `c`.  The dominant-descent
branch exposes the exact filtered-tree/weight fact needed while the endpoint's
realized checkpoint still lags `c`. -/
def CheckpointTakeoverEvidence
    (c : Checkpoint Root) (store : Store Root) : Prop :=
  Nonempty (CertifiedJustified cfg E c store.justified_checkpoint) ∨
    ∃ depth : ℕ,
      DescendsTo cfg store (get_filtered_block_tree cfg store) c.root depth
          store.justified_checkpoint.root ∧
        depth ≤ (get_filtered_block_tree cfg store).length + 1

/-- Two concrete certificates at the same epoch make the continuation branch
of `CheckpointTakeoverEvidence` automatic.  Accountable same-epoch uniqueness
identifies the endpoint checkpoint with `c`; the required certificate from
`c` is then the zero-link anchor certificate.

This is the exact certificate consequence available from accountability for
two merely justified checkpoints.  A *strictly newer* certified justified
checkpoint need not continue from `c`: Casper accountable safety orders later
checkpoints only above a finalized checkpoint, not above every justified one. -/
theorem checkpointTakeoverEvidence_of_sameEpochCertificates
    {anchor c : Checkpoint Root} {store : Store Root}
    (hacc : CertificateAccountability cfg E anchor)
    (hc : Nonempty (CertifiedJustified cfg E anchor c))
    (hstore : Nonempty
      (CertifiedJustified cfg E anchor store.justified_checkpoint))
    (hepoch : c.epoch = store.justified_checkpoint.epoch) :
    E.CheckpointTakeoverEvidence cfg c store := by
  obtain ⟨hc⟩ := hc
  obtain ⟨hstore⟩ := hstore
  have hroot : c.root = store.justified_checkpoint.root :=
    hacc.justified_unique hc hstore hepoch
  have hcheckpoint : c = store.justified_checkpoint := by
    cases hcEq : c with
    | mk cEpoch cRoot =>
        cases hstoreEq : store.justified_checkpoint with
        | mk storeEpoch storeRoot =>
            simp only [hcEq, hstoreEq] at hepoch hroot ⊢
            cases hepoch
            cases hroot
            rfl
  unfold CheckpointTakeoverEvidence
  left
  rw [← hcheckpoint]
  exact ⟨CertifiedJustified.anchor⟩

/-- For the actual observed restart, equality of the endpoint justified epoch
with the observed epoch therefore constructs the certificate-takeover branch
from the common global FFG trajectory.  No endpoint ancestry, head, filter, or
safety premise is used. -/
theorem observedRestart_takeoverEvidence_of_equalJustifiedEpoch
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) {n : ℕ}
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hrestart : ObservedRestartCompatible cfg (E.fcrStep cfg ext v n))
    (w : ValidatorIndex) (m : ℕ)
    (hepoch :
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.epoch =
        (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.CheckpointTakeoverEvidence cfg
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
      (E.store cfg ext w m) := by
  have hobservedAU := E.observedRestart_AU_of_globalTrajectory cfg ext hA
    hcoh hanchor hboundary hv hHn1 hrestart
  have hobservedCertificate := S.certifiedJustified_of_AU cfg hobservedAU
  obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hA.genesis
  have hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hstoreCertificate :=
    E.globalJustified_certificate cfg ext hcoh hgen hanchor w m
  have hacc : CertificateAccountability cfg E anchor :=
    CertificateAccountability.of_assumptions cfg ext
      (SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA)
  exact E.checkpointTakeoverEvidence_of_sameEpochCertificates cfg hacc
    hobservedCertificate hstoreCertificate hepoch

/-- Certificate continuation or an explicit filtered dominant descent forces
the endpoint head below `c`.  Root delivery and concrete store ancestry in the
certificate branch are conclusions, reconstructed from the execution parent
graph. -/
theorem checkpointTakeover_head_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {c : Checkpoint Root} (hcRoot : E.ExecutionRoot c.root)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hHm : E.WithinHorizon cfg m)
    (htakeover : E.CheckpointTakeoverEvidence cfg c
      (E.store cfg ext w m)) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m)) (get_node_for_root c.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hA.genesis
  have hjustKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justifiedRootKnown_of_globalTrajectory cfg ext hA.wellFormed
      hA.externals_coherence ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh
      hanchor hboundary hw m hHm
  have hwf : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hA.wellFormed.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r :=
    E.store_walkKnownK cfg ext hA.wellFormed hA.externals_coherence
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
  have hsub : ∀ r ∈ get_filtered_block_tree cfg (E.store cfg ext w m),
      r ∈ (E.store cfg ext w m).block_roots := by
    intro r hr
    have hr' : r ∈ (filter_block_tree_aux cfg (E.store cfg ext w m)
        ((E.store cfg ext w m).block_roots.length + 1)
        (E.store cfg ext w m).justified_checkpoint.root).2 := hr
    rcases filter_block_tree_aux_output_mem cfg _ _ _ hr' with hrKnown | hrBase
    · exact hrKnown
    · rw [hrBase]
      exact hjustKnown
  rcases htakeover with hcertificate | ⟨depth, hdescent, hfuel⟩
  · obtain ⟨hcertificate⟩ := hcertificate
    have hsemantic : E.RootDescends
        (E.store cfg ext w m).justified_checkpoint.root c.root :=
      hcertificate.descends_anchor cfg
    obtain ⟨hcKnown, hstoreAncestor⟩ :=
      E.store_known_ancestor_of_rootDescends cfg ext hA.wellFormed
        hA.externals_coherence hgenEq hslot hparent hjustKnown hcRoot hsemantic
    exact head_ge_of_justified_ge_K cfg hwf hwalkK hjustKnown hcKnown hstoreAncestor
  · exact is_ancestor_get_head cfg hwf hsub hdescent hfuel

/-- The observed restart checkpoint is safe from the update second whenever
every later endpoint supplies the concrete certificate-or-filter takeover
evidence.  The evidence is required only under the actual restart core. -/
theorem observedRestart_safeFrom_of_takeover
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) (n : ℕ)
    (hrestart : ObservedRestartCompatible cfg (E.fcrStep cfg ext v n))
    (htakeover : ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      E.CheckpointTakeoverEvidence cfg
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
        (E.store cfg ext w m)) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
      (n + 1) := by
  intro w hw m hnm hHm
  have hHn1 : E.WithinHorizon cfg (n + 1) :=
    E.withinHorizon_mono cfg hnm hHm
  have hheadKnown : (get_head cfg (E.store cfg ext v (n + 1))).root ∈
      (E.store cfg ext v (n + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (n + 1)) with hhead | hfallback
    · exact hhead
    · rw [hfallback]
      exact E.justifiedRootKnown_of_globalTrajectory cfg ext hA.wellFormed
        hA.externals_coherence hA.genesis hcoh hanchor hboundary hv (n + 1) hHn1
  have hAU := E.observedRestart_AU_of_globalTrajectory cfg ext hA hcoh
    hanchor hboundary hv hHn1 hrestart
  have hrealized :=
    E.resetCheckpointRealizedAt_of_known_AU cfg ext hA hcoh hanchor
      hboundary hv hHn1 hheadKnown hAU
  have hcRoot : E.ExecutionRoot
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root :=
    ⟨(E.store cfg ext v (n + 1)).blocks
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root,
      E.blockAt_of_store_known cfg ext hrealized.root_known⟩
  exact E.checkpointTakeover_head_of_globalTrajectory cfg ext hA hcoh hanchor
    hboundary hcRoot hw hHm (htakeover w hw m hnm hHm)

/-! ## Genesis certificate continuation -/

/-- The boundary-aligned trusted anchor is below every honest endpoint head.
Every endpoint global justified checkpoint has a concrete certificate from
the anchor, so no generic finalized-descent or head-tracking premise is used. -/
theorem trustedAnchor_safeFrom_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor)) :
    E.SafeFrom cfg ext anchor.root 0 := by
  intro w hw m _hm hHm
  have hanchorRealized := E.resetCheckpointRealizedAt_anchor cfg ext hA
    hanchor hboundary w m
  have hanchorRoot : E.ExecutionRoot anchor.root :=
    ⟨(E.store cfg ext w m).blocks anchor.root,
      E.blockAt_of_store_known cfg ext hanchorRealized.root_known⟩
  have hgenShort : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot := by
    obtain ⟨ast, ablk, hgenEq, hslot, _hparent⟩ := hA.genesis
    exact ⟨ast, ablk, hgenEq, hslot⟩
  have hjustified := E.globalJustified_certificate cfg ext hcoh hgenShort
    hanchor w m
  have htakeover : E.CheckpointTakeoverEvidence cfg anchor
      (E.store cfg ext w m) := Or.inl hjustified
  exact E.checkpointTakeover_head_of_globalTrajectory cfg ext hA hcoh hanchor
    hboundary hanchorRoot hw hHm htakeover

/-- The exact genesis field consumed by the public fold equals the trusted
anchor and therefore inherits the preceding closed safety theorem. -/
theorem genesisReset_safeFrom_of_globalTrajectory
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root} {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (v : ValidatorIndex) :
    E.SafeFrom cfg ext (E.store cfg ext v 0).finalized_checkpoint.root 0 := by
  have hroot : (E.store cfg ext v 0).finalized_checkpoint.root = anchor.root := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hA.genesis
    change E.genesis_store.finalized_checkpoint.root = anchor.root
    rw [hgenEq] at hanchor ⊢
    simpa only [get_forkchoice_store] using congrArg Checkpoint.root hanchor.symm
  rw [hroot]
  exact E.trustedAnchor_safeFrom_of_globalTrajectory cfg ext hA hcoh hanchor hboundary

/-! ## Restart-scoped public fold -/

/-- `get_latest_confirmed` safety with the observed premise scoped to the
actual Boolean restart guard. -/
theorem safeFrom_get_latest_confirmed_restartScoped
    {fcrStore : FastConfirmationStore Root} {n : ℕ}
    (hprev : E.SafeFrom cfg ext fcrStore.confirmed_root n)
    (hfin : E.SafeFrom cfg ext fcrStore.store.finalized_checkpoint.root n)
    (hobs : ObservedRestartCompatible cfg fcrStore →
      E.SafeFrom cfg ext
        fcrStore.current_epoch_observed_justified_checkpoint.root n)
    (heng : ∀ b : Root,
      is_one_confirmed cfg ext fcrStore.store
          (get_current_balance_source fcrStore) b = true →
      E.SafeFrom cfg ext b n) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext fcrStore) n := by
  let initial : Root :=
    if get_block_epoch cfg fcrStore.store fcrStore.confirmed_root + 1 <
          get_current_store_epoch cfg fcrStore.store ∨
        ¬ is_ancestor fcrStore.store
          (get_node_for_root (get_head cfg fcrStore.store).root)
          (get_node_for_root fcrStore.confirmed_root) ∨
        (is_start_slot_at_epoch cfg (get_current_slot cfg fcrStore.store) ∧
          ¬ is_confirmed_chain_safe cfg ext fcrStore fcrStore.confirmed_root) then
      fcrStore.store.finalized_checkpoint.root
    else fcrStore.confirmed_root
  have hinitial : E.SafeFrom cfg ext initial n := by
    simp only [initial]
    split_ifs <;> assumption
  let restarted : Root :=
    if observedRestartGuard cfg fcrStore initial then
      fcrStore.current_epoch_observed_justified_checkpoint.root
    else initial
  have hrestarted : E.SafeFrom cfg ext restarted n := by
    simp only [restarted]
    split_ifs with hguard
    · exact hobs (observedRestartCompatible_of_guard cfg fcrStore initial hguard)
    · exact hinitial
  have hadvance : E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext fcrStore restarted) n := by
    rcases find_latest_confirmed_descendant_spec cfg ext fcrStore restarted with heq | hconf
    · rw [heq]
      exact hrestarted
    · exact heng _ hconf
  change E.SafeFrom cfg ext (get_latest_confirmed cfg ext fcrStore) n
  simp only [get_latest_confirmed]
  change E.SafeFrom cfg ext
    (if get_block_epoch cfg fcrStore.store restarted + 1 ≥
          get_current_store_epoch cfg fcrStore.store then
        find_latest_confirmed_descendant cfg ext fcrStore restarted
      else restarted) n
  split_ifs <;> assumption

/-- Public-fold residual with observed-reset safety demanded only when the
restart's concrete core holds. -/
structure L4ResidualRestartScoped (E : Execution Root) : Prop where
  genesis_safe : ∀ v ∈ E.honest,
    E.SafeFrom cfg ext (E.store cfg ext v 0).finalized_checkpoint.root 0
  finalized_safe : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1)
  observed_restart_safe : ∀ v ∈ E.honest, ∀ n : ℕ,
    ObservedRestartCompatible cfg (E.fcrStep cfg ext v n) →
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
      (n + 1)
  advance_safe : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.SafeFrom cfg ext b (n + 1)

/-- The ordinary trajectory induction, now using the restart-scoped
`get_latest_confirmed` composition theorem. -/
theorem confirmed_safeFrom_of_restartScopedResidual
    (hres : E.L4ResidualRestartScoped cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) :
    ∀ n : ℕ, E.SafeFrom cfg ext (E.confirmed cfg ext v n) n := by
  intro n
  induction n with
  | zero =>
      rw [E.confirmed_zero]
      exact hres.genesis_safe v hv
  | succ n ih =>
      by_cases hadv : get_current_slot cfg (E.store cfg ext v (n + 1)) >
          get_current_slot cfg (E.store cfg ext v n)
      · rw [E.confirmed_succ_of_advance cfg ext v n hadv]
        have hprev : E.SafeFrom cfg ext
            (E.fcrStep cfg ext v n).confirmed_root (n + 1) := by
          rw [E.fcrStep_confirmed_root]
          exact SafeFrom.mono (E := E) (cfg := cfg) (ext := ext)
            ih (Nat.le_succ n)
        exact E.safeFrom_get_latest_confirmed_restartScoped cfg ext hprev
          (hres.finalized_safe v hv n)
          (hres.observed_restart_safe v hv n)
          (hres.advance_safe v hv n)
      · rw [E.confirmed_succ_of_no_advance cfg ext v n hadv]
        exact SafeFrom.mono (E := E) (cfg := cfg) (ext := ext)
          ih (Nat.le_succ n)

/-- Consumer wiring: a producer for the restart-scoped residual proves the
pinned public safety statement. -/
theorem spec_safety_of_restartScopedResidual
    (hres : ∀ E : Execution Root, SpecAssumptions cfg ext E →
      E.L4ResidualRestartScoped cfg ext) :
    Spec_Safety cfg ext := by
  intro E hSA v hv n w hw m hnm hHm
  exact E.confirmed_safeFrom_of_restartScopedResidual cfg ext (hres E hSA)
    v hv n w hw m hnm hHm

end Execution

end FastConfirmation.Spec

end
