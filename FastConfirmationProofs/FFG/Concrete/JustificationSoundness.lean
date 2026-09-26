module
public import FastConfirmationProofs.FFG.Concrete.ProvenanceInvariant
public import FastConfirmationStatements.Premises.FFGCertificates

@[expose] public section

/-! Proves justification soundness for the concrete FFG model: every justified
or finalized checkpoint of an in-horizon reachable state is the genesis stub or
has a supermajority link of distinct weighted signers of included,
target-matching body votes from a justified source. It also proves canonical
target inclusion, source consistency, exact checkpoint roots, and the body
authenticity adapter to the block oracle. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### Body-vote provenance -/

theorem mem_attestationVotes {S : FFGSetup Root} {block : FFGWireBlock Root}
    {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state : FFGBeaconState Root)
      (r : IncludedVote Root), r ∈ attestationVotes S block parentSlot state attestations →
      r.block = block ∧ r.vote ∈ attestations ∧ r.parentSlot = parentSlot ∧
      ∃ next, process_attestation S.cfg S.preset S.schedule r.pre r.vote r.parentSlot = .ok next
  | [], _, _, h => by simp [attestationVotes] at h
  | vote :: attestations, state, r, h => by
    unfold attestationVotes at h
    split at h
    · rename_i next hnext
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨rfl, List.mem_cons_self, rfl, next, hnext⟩
      · obtain ⟨h1, h2, h3, h4⟩ := mem_attestationVotes attestations next r h
        exact ⟨h1, List.mem_cons_of_mem _ h2, h3, h4⟩
    · simp at h

/-- **Body authenticity adapter.** Every recorded vote is a body vote of an
accepted block of the run: the block oracle accepted that block, and the
concrete `process_attestation` call on the recorded pre-state succeeded. The
oracle only accepts or rejects; it supplies no FFG state. -/
theorem includedVote_provenance {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {state : FFGBeaconState Root}
    (h : Reachable S blocks votes state) :
    ∀ r ∈ votes, r.block ∈ blocks ∧ r.vote ∈ r.block.attestations ∧
      (∃ pre post, S.oracle.accepts pre r.block post = true) ∧
      ∃ next, process_attestation S.cfg S.preset S.schedule r.pre r.vote r.parentSlot =
        .ok next := by
  induction h with
  | genesis => simp
  | slots _ _ ih => exact ih
  | block blk hreach htrans ih =>
    rename_i state' next'
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨h1, h2, h3, h4⟩ := ih r hr
      exact ⟨List.mem_append_left _ h1, h2, h3, h4⟩
    · obtain ⟨atSlot, hslots, hblock, hacc⟩ := state_transition_eq_ok htrans
      obtain ⟨paid, headed, hpaid, hheaded, -⟩ := process_block_eq_ok hblock
      rw [blockVotes_eq hslots hpaid hheaded] at hr
      obtain ⟨hb, hv, -, h4⟩ := mem_attestationVotes _ _ r hr
      subst hb
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), hv, ⟨atSlot, next', hacc⟩, h4⟩

/-- Every recorded body vote is authentic when the block oracle authenticates
the bodies of the blocks it accepts. -/
theorem includedVote_authentic {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {state : FFGBeaconState Root}
    {Authentic : FFGWireBlock Root → FFGWireAttestation Root → Prop}
    (h : Reachable S blocks votes state) (hauth : OracleAuthenticatesBodies S Authentic) :
    ∀ r ∈ votes, Authentic r.block r.vote := by
  intro r hr
  obtain ⟨-, hv, ⟨pre, post, hacc⟩, -⟩ := includedVote_provenance h r hr
  exact hauth pre r.block post hacc r.vote hv

/-! ### Canonical target inclusion and source consistency -/

/-- **Source consistency.** Python asserts that an included vote names the
state's justified checkpoint of its target epoch. -/
theorem includedVote_source {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {state : FFGBeaconState Root}
    (h : Reachable S blocks votes state) :
    ∀ r ∈ votes, r.vote.data.source =
      (if r.vote.data.target.epoch = compute_epoch_at_slot S.cfg r.pre.slot then
        r.pre.current_justified_checkpoint else r.pre.previous_justified_checkpoint) := by
  intro r hr
  obtain ⟨-, -, -, next, hnext⟩ := includedVote_provenance h r hr
  obtain ⟨flags, hflags, -⟩ := process_attestation_eq_ok hnext
  exact (get_attestation_participation_flag_indices_eq_ok hflags).1

/-- **Canonical target inclusion.** A recorded body vote counts for
justification exactly when its target root is the checkpoint root that
`get_block_root` reads on the state where `process_attestation` ran. -/
theorem targetIncluded_iff {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {state : FFGBeaconState Root}
    (h : Reachable S blocks votes state) {r : IncludedVote Root} (hr : r ∈ votes) :
    TargetIncluded S votes r ↔
      get_block_root S.cfg S.preset r.pre r.vote.data.target.epoch =
        .ok r.vote.data.target.root := by
  obtain ⟨-, -, -, next, hnext⟩ := includedVote_provenance h r hr
  obtain ⟨flags, hflags, -⟩ := process_attestation_eq_ok hnext
  have hiff := (get_attestation_participation_flag_indices_eq_ok hflags).2.2
  constructor
  · rintro ⟨-, fl, hfl, h1⟩
    have e : r.flags S = Except.ok flags := hflags
    rw [e] at hfl
    cases hfl
    exact hiff.mp h1
  · intro hread
    exact ⟨hr, flags, hflags, hiff.mpr hread⟩

/-- **Wrong target.** A recorded body vote whose target root differs from the
checkpoint root read at inclusion is accepted but does not count. -/
theorem not_targetIncluded_of_wrong_target {S : FFGSetup Root}
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    {r : IncludedVote Root} (hr : r ∈ votes) {root : Root}
    (hread : get_block_root S.cfg S.preset r.pre r.vote.data.target.epoch = .ok root)
    (hne : r.vote.data.target.root ≠ root) : ¬ TargetIncluded S votes r := by
  rw [targetIncluded_iff h hr, hread]
  intro e
  cases e
  exact hne rfl

/-! ### Invariant consequences -/

/-- **Flag provenance.** In an in-horizon reachable state, a validator has the
current-epoch timely-target flag exactly when a target-included body vote of
the current epoch names it; the previous-epoch flag likewise for the previous
epoch. -/
theorem participation_flags_iff {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) (i : ValidatorIndex) :
    (has_flag (state.current_epoch_participation.getD i 0) timelyTargetFlagIndex = true ↔
      ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
        r.vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot) ∧
    (has_flag (state.previous_epoch_participation.getD i 0) timelyTargetFlagIndex = true ↔
      ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
        r.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot) :=
  let hinv := provenanceInvariant_of_reachable hS h hH
  ⟨hinv.current_flags i, hinv.previous_flags i⟩

/-- **Exact checkpoints.** The target of a target-included vote is the
accepted-chain checkpoint of its epoch: its root is the root of the latest
accepted block at or before the epoch start slot. -/
theorem targetIncluded_target_on_chain {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    {r : IncludedVote Root} (hr : TargetIncluded S votes r) :
    r.vote.data.target.root = chainRootAt S.genesisRoot blocks
      (compute_start_slot_at_epoch S.cfg r.vote.data.target.epoch) :=
  ((provenanceInvariant_of_reachable hS h hH).target_on_chain r hr).2

/-- **Accepted history.** Accepted block slots increase, each block names its
predecessor as parent, and every successful `get_block_root` read is the
accepted-chain root of the epoch start slot. -/
theorem reachable_history {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    blocks.Pairwise (fun a b => a.slot < b.slot) ∧ ParentLinked S.genesisRoot blocks ∧
    state.latest_block_header.root = tipRoot S.genesisRoot blocks ∧
    ∀ epoch root, get_block_root S.cfg S.preset state epoch = .ok root →
      root = chainRootAt S.genesisRoot blocks (compute_start_slot_at_epoch S.cfg epoch) := by
  have hinv := provenanceInvariant_of_reachable hS h hH
  refine ⟨hinv.blocks_ordered, hinv.parent_linked, hinv.header_root, ?_⟩
  intro epoch root hread
  obtain ⟨-, hread⟩ := get_block_root_eq_ok.mp hread
  obtain ⟨-, hlt, hle, -, hcell⟩ := get_block_root_at_slot_eq_ok.mp hread
  rw [hinv.ring _ hlt hle] at hcell
  exact (Option.some.inj hcell).symm

/-- Every recorded body vote names a justified source. -/
theorem includedVote_source_justified {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    ∀ r ∈ votes, Justified S votes r.vote.data.source :=
  (provenanceInvariant_of_reachable hS h hH).source_justified

/-! ### Justification soundness -/

/-- **Justification soundness.** In an in-horizon reachable state, the
current justified, previous justified and finalized checkpoints are justified
from the genesis stub by supermajority links of included, target-matching body
votes. -/
theorem justification_soundness {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    Justified S votes state.current_justified_checkpoint ∧
    Justified S votes state.previous_justified_checkpoint ∧
    Justified S votes state.finalized_checkpoint :=
  let hinv := provenanceInvariant_of_reachable hS h hH
  ⟨hinv.current_justified, hinv.previous_justified, hinv.finalized_justified⟩

/-- The signer weight of a link is positive, so its signer set is nonempty. -/
theorem SupermajorityLink.signers_nonempty {S : FFGSetup Root} (hS : S.Admissible)
    {votes : List (IncludedVote Root)} {source target : Checkpoint Root}
    (link : SupermajorityLink S votes source target) : link.signers.Nonempty := by
  rcases Finset.eq_empty_or_nonempty link.signers with he | hne
  · have h := link.supermajority
    have hfloor := hS.balance_floor
    have hinc := S.cfg.effective_balance_increment_pos
    rw [FixedFFGScope.weight, he, Finset.sum_empty] at h
    beacon_omega
  · exact hne

/-- **Certificate extraction.** A justified checkpoint is the genesis stub, or
it has a supermajority link from a justified source whose epoch is smaller.
The link's distinct signers are nonempty, weigh at least two thirds of the
fixed active balance, and each has a target-included body vote of an
accepted block of the run with exactly this source and target. -/
theorem justified_certificate {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    {c : Checkpoint Root} (hc : Justified S votes c) :
    c = S.stub ∨
      ∃ (source : Checkpoint Root) (link : SupermajorityLink S votes source c),
        Justified S votes source ∧ source.epoch < c.epoch ∧ link.signers.Nonempty ∧
        2 * S.scope.activeBalance ≤ 3 * S.scope.weight link.signers ∧
        ∀ i ∈ link.signers, ∃ r ∈ votes, r.block ∈ blocks ∧
          r.vote ∈ r.block.attestations ∧ TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
          r.vote.data.source = source ∧ r.vote.data.target = c := by
  cases hc with
  | anchor => exact Or.inl rfl
  | link hsource link =>
    rename_i source
    refine Or.inr ⟨source, link, hsource, link.source_before_target,
      link.signers_nonempty hS, link.supermajority, ?_⟩
    intro i hi
    obtain ⟨r, hr, hri, hs, ht⟩ := link.signer_vote i hi
    obtain ⟨hb, hv, -, -⟩ := includedVote_provenance h r hr.1
    exact ⟨r, hr.1, hb, hv, hr, hri, hs, ht⟩

/-- **Justified checkpoints are exact chain checkpoints.** In an in-horizon
reachable state, a justified checkpoint is the genesis stub or the
accepted-chain checkpoint of its epoch. -/
theorem justified_checkpoint_on_chain {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    {c : Checkpoint Root} (hc : Justified S votes c) :
    c = S.stub ∨ c.root = chainRootAt S.genesisRoot blocks
      (compute_start_slot_at_epoch S.cfg c.epoch) := by
  rcases justified_certificate hS h hc with hstub | ⟨source, link, -, -, hne, -, hvote⟩
  · exact Or.inl hstub
  · obtain ⟨i, hi⟩ := hne
    obtain ⟨r, -, -, -, hr, -, -, rfl⟩ := hvote i hi
    exact Or.inr (targetIncluded_target_on_chain hS h hH hr)

omit [DecidableEq Root] in
/-- The genesis stub reads as the genesis anchor at the FFG interpretation
boundary. -/
theorem stub_reads_as_anchor (S : FFGSetup Root) :
    CheckpointReadsAs S.stub ⟨GENESIS_EPOCH, S.genesisRoot⟩ :=
  Or.inr ⟨rfl, rfl⟩

end FastConfirmation.Spec.ConcreteFFG

end
