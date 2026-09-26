module
public import FastConfirmationProofs.FFG.Concrete.CanonicalSelectors
public import FastConfirmationProofs.FFG.SelectedSource.FFGEndpointRealization
public import FastConfirmationProofs.ModelFacts.FFGState

@[expose] public section

/-! Proves the timing laws of the canonical selectors along accepted chains.
A block transition only adds included body votes. Thus each PJF pass of a
descendant sees at least the participation of its ancestor, and the epoch of
the resulting checkpoint does not decrease (`cjFormula_mono`, `cjRun_mono`).
The file defines the canonical formed-evidence relation `Formed`: the four
selector values of an accepted block and the realized checkpoints of its
slot runs. It proves the membership, maximality, monotonicity, and epoch laws
of `AcceptedBlockFFGState` for `Formed`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

section Formula

variable {Root : Type} [DecidableEq Root]

/-! ### Monotonicity of one PJF pass in the included votes -/

omit [DecidableEq Root] in
theorem chainCheckpoint_epoch (S : FFGSetup Root) (blocks : List (FFGWireBlock Root))
    (e : Epoch) : (chainCheckpoint S blocks e).epoch = e := rfl

theorem participants_mono {S : FFGSetup Root} {votes votes' : List (IncludedVote Root)}
    (hsub : ∀ v ∈ votes, v ∈ votes') (e : Epoch) :
    participants S votes e ⊆ participants S votes' e := by
  classical
  intro i hi
  unfold participants at hi ⊢
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨hr, ha, hs, r, ⟨hmem, hflags⟩, hatt, he⟩ := hi
  exact ⟨hr, ha, hs, r, ⟨hsub r hmem, hflags⟩, hatt, he⟩

theorem epochTest_mono {S : FFGSetup Root} {votes votes' : List (IncludedVote Root)}
    (hsub : ∀ v ∈ votes, v ∈ votes') {e : Epoch} (h : EpochTest S votes e) :
    EpochTest S votes' e := by
  unfold EpochTest at h ⊢
  refine h.trans (Nat.mul_le_mul_right _ (max_le_max le_rfl ?_))
  exact Finset.sum_le_sum_of_subset (participants_mono hsub e)

/-- One PJF pass with an output epoch at most the pass epoch. -/
theorem cjFormula_epoch_le {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {c : Checkpoint Root} (hc : c.epoch ≤ E - 1) :
    (cjFormula S blocks votes E c).epoch ≤ E := by
  unfold cjFormula
  split_ifs
  · beacon_omega
  · exact le_rfl
  · change E - 1 ≤ E; beacon_omega
  · beacon_omega

/-- One PJF pass does not lower a start checkpoint before the pass epoch. -/
theorem cjFormula_start_le {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {c : Checkpoint Root} (hc : c.epoch ≤ E - 1) :
    c.epoch ≤ (cjFormula S blocks votes E c).epoch := by
  unfold cjFormula
  split_ifs
  · exact le_rfl
  · change c.epoch ≤ E; beacon_omega
  · exact hc
  · exact le_rfl

/-- **Vote monotonicity of one PJF pass.** More included votes and a later
start checkpoint give a pass output that is not earlier. -/
theorem cjFormula_mono {S : FFGSetup Root} {blocks blocks' : List (FFGWireBlock Root)}
    {votes votes' : List (IncludedVote Root)} (hsub : ∀ v ∈ votes, v ∈ votes') {E : Epoch}
    {c c' : Checkpoint Root} (hcc : c.epoch ≤ c'.epoch) (hc' : c'.epoch ≤ E - 1) :
    (cjFormula S blocks votes E c).epoch ≤ (cjFormula S blocks' votes' E c').epoch := by
  unfold cjFormula
  by_cases h1 : E ≤ 1
  · rw [if_pos h1, if_pos h1]; exact hcc
  rw [if_neg h1, if_neg h1]
  by_cases hE : EpochTest S votes E
  · rw [if_pos hE, if_pos (epochTest_mono hsub hE)]
    exact le_rfl
  rw [if_neg hE]
  by_cases hP : EpochTest S votes (E - 1)
  · rw [if_pos hP]
    split_ifs
    · change E - 1 ≤ E; beacon_omega
    · exact le_rfl
    · exact absurd (epochTest_mono hsub hP) ‹_›
  · rw [if_neg hP]
    split_ifs
    · change c.epoch ≤ E; beacon_omega
    · change c.epoch ≤ E - 1; beacon_omega
    · exact hcc

/-! ### Runs of passes -/

theorem cjRun_add {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} :
    ∀ (a b : ℕ) (E : Epoch) (c : Checkpoint Root),
      cjRun S blocks votes E (a + b) c = cjRun S blocks votes (E + a) b (cjRun S blocks votes E a c)
  | 0, b, E, c => by simp [cjRun]
  | a + 1, b, E, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega, cjRun, cjRun, cjRun_add a b (E + 1),
      show E + 1 + a = E + (a + 1) by beacon_omega]

/-- A run keeps the invariant `epoch ≤ E - 1` of its start checkpoint at the
next epoch. -/
theorem cjRun_epoch_le_sub {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} :
    ∀ (n : ℕ) (E : Epoch) (c : Checkpoint Root), c.epoch ≤ E - 1 →
      (cjRun S blocks votes E n c).epoch ≤ E + n - 1
  | 0, E, c, hc => by simpa [cjRun] using hc
  | n + 1, E, c, hc => by
    rw [cjRun]
    have h1 := cjFormula_epoch_le (S := S) (blocks := blocks) (votes := votes) hc
    have := cjRun_epoch_le_sub (S := S) (blocks := blocks) (votes := votes) n (E + 1)
      (cjFormula S blocks votes E c) (by beacon_omega)
    beacon_omega

/-- A run does not lower the epoch of its start checkpoint. -/
theorem cjRun_epoch_ge {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} :
    ∀ (n : ℕ) (E : Epoch) (c : Checkpoint Root), c.epoch ≤ E - 1 →
      c.epoch ≤ (cjRun S blocks votes E n c).epoch
  | 0, _, _, _ => le_rfl
  | n + 1, E, c, hc => by
    rw [cjRun]
    have h1 := cjFormula_start_le (S := S) (blocks := blocks) (votes := votes) hc
    have h2 := cjFormula_epoch_le (S := S) (blocks := blocks) (votes := votes) hc
    exact h1.trans (cjRun_epoch_ge n (E + 1) (cjFormula S blocks votes E c) (by beacon_omega))

/-- A longer run does not give an earlier checkpoint. -/
theorem cjRun_epoch_mono_len {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {c : Checkpoint Root} (hc : c.epoch ≤ E - 1)
    {a b : ℕ} (hab : a ≤ b) :
    (cjRun S blocks votes E a c).epoch ≤ (cjRun S blocks votes E b c).epoch := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [cjRun_add]
  have ha := cjRun_epoch_le_sub (S := S) (blocks := blocks) (votes := votes) a E c hc
  exact cjRun_epoch_ge d _ _ (by beacon_omega)

/-- **Vote monotonicity of runs.** -/
theorem cjRun_mono {S : FFGSetup Root} {blocks blocks' : List (FFGWireBlock Root)}
    {votes votes' : List (IncludedVote Root)} (hsub : ∀ v ∈ votes, v ∈ votes') :
    ∀ (n : ℕ) (E : Epoch) (c c' : Checkpoint Root), c.epoch ≤ c'.epoch → c'.epoch ≤ E - 1 →
      (cjRun S blocks votes E n c).epoch ≤ (cjRun S blocks' votes' E n c').epoch
  | 0, _, _, _, hcc, _ => hcc
  | n + 1, E, c, c', hcc, hc' => by
    rw [cjRun, cjRun]
    have hle := cjFormula_epoch_le (S := S) (blocks := blocks') (votes := votes') hc'
    exact cjRun_mono hsub n (E + 1) _ _ (cjFormula_mono hsub hcc hc') (by beacon_omega)

/-- Runs from an epoch holding every recorded target: only the first two
boundaries can change the checkpoint, and from an epoch `E ≥ 2` only the
first. -/
theorem cjRun_cap {S : FFGSetup Root} (hS : S.Admissible) {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch}
    (hvotes : ∀ r ∈ votes, r.vote.data.target.epoch ≤ E) (n : ℕ) (c : Checkpoint Root) :
    cjRun S blocks votes E n c = cjRun S blocks votes E (min n 2) c ∧
      (2 ≤ E → cjRun S blocks votes E n c = cjRun S blocks votes E (min n 1) c) := by
  constructor
  · by_cases hn : n ≤ 2
    · rw [min_eq_left hn]
    · obtain ⟨d, rfl⟩ : ∃ d, n = 2 + d := ⟨n - 2, by omega⟩
      rw [min_eq_right (by omega), cjRun_add,
        cjRun_very_late hS d (E + 2) _ (fun r hr => by have := hvotes r hr; beacon_omega)]
  · intro hE
    by_cases hn : n ≤ 1
    · rw [min_eq_left hn]
    · rw [min_eq_right (by omega), cjRun_two_boundaries hS hvotes hE (by omega)]
      simp [cjRun]

/-- Runs that stay below epoch 2 keep the checkpoint. -/
theorem cjRun_early {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} :
    ∀ (n : ℕ) (E : Epoch) (c : Checkpoint Root), E + n ≤ 2 → cjRun S blocks votes E n c = c
  | 0, _, _, _ => rfl
  | n + 1, E, c, h => by
    rw [cjRun, cjRun_early n (E + 1) _ (by beacon_omega)]
    unfold cjFormula
    rw [if_pos (show E ≤ 1 by beacon_omega)]

/-! ### One block transition -/

/-- **Transition step.** A successful in-scope block transition extends the
reachable run, and every later run of the child is at least the run of the
parent. -/
theorem transition_run_mono {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {bp : List (FFGWireBlock Root)} {vp : List (IncludedVote Root)}
    {P Q : FFGBeaconState Root} {wire : FFGWireBlock Root} (hreach : Reachable S bp vp P)
    (hHP : compute_epoch_at_slot S.cfg P.slot ≤ S.scope.last_epoch)
    (h : state_transition S.cfg S.preset S.schedule S.oracle P wire = .ok Q)
    (hHQ : compute_epoch_at_slot S.cfg Q.slot ≤ S.scope.last_epoch) :
    Reachable S (bp ++ [wire]) (vp ++ blockVotes S P wire) Q ∧ P.slot < Q.slot ∧
      Q.current_justified_checkpoint =
        cjRun S bp vp (compute_epoch_at_slot S.cfg P.slot)
          (compute_epoch_at_slot S.cfg Q.slot - compute_epoch_at_slot S.cfg P.slot)
          P.current_justified_checkpoint ∧
      ∀ k, compute_epoch_at_slot S.cfg Q.slot ≤ k →
        (cjRun S bp vp (compute_epoch_at_slot S.cfg P.slot)
          (k - compute_epoch_at_slot S.cfg P.slot) P.current_justified_checkpoint).epoch ≤
        (cjRun S (bp ++ [wire]) (vp ++ blockVotes S P wire) (compute_epoch_at_slot S.cfg Q.slot)
          (k - compute_epoch_at_slot S.cfg Q.slot) Q.current_justified_checkpoint).epoch := by
  have hreachQ := Reachable.block wire hreach h
  obtain ⟨hQslot, hlt⟩ := state_transition_slot h
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  have hcjQ := (process_block_checkpoints hblock).2.2.1
  obtain ⟨next, hnext, -, -, hcj⟩ := process_slots_ok hS hnum
    (provenanceInvariant_of_reachable hS hreach hHP) (lengthsOK_of_reachable hreach) hlt
    (by rw [← hQslot]; exact hHQ)
  rw [hslots] at hnext
  cases hnext
  have hEPQ : compute_epoch_at_slot S.cfg P.slot ≤ compute_epoch_at_slot S.cfg Q.slot :=
    compute_epoch_at_slot_mono (by rw [hQslot]; exact Nat.le_of_lt hlt)
  have hCJ : Q.current_justified_checkpoint =
      cjRun S bp vp (compute_epoch_at_slot S.cfg P.slot)
        (compute_epoch_at_slot S.cfg Q.slot - compute_epoch_at_slot S.cfg P.slot)
        P.current_justified_checkpoint := by
    rw [hcjQ, hcj, hQslot]
  refine ⟨hreachQ, by rw [hQslot]; exact hlt, hCJ, ?_⟩
  intro k hk
  have hsplit : k - compute_epoch_at_slot S.cfg P.slot =
      (compute_epoch_at_slot S.cfg Q.slot - compute_epoch_at_slot S.cfg P.slot) +
        (k - compute_epoch_at_slot S.cfg Q.slot) := by beacon_omega
  rw [hsplit, cjRun_add, show compute_epoch_at_slot S.cfg P.slot +
    (compute_epoch_at_slot S.cfg Q.slot - compute_epoch_at_slot S.cfg P.slot) =
      compute_epoch_at_slot S.cfg Q.slot by beacon_omega, ← hCJ]
  exact cjRun_mono (fun v hv => List.mem_append_left _ hv) _ _ _ _ le_rfl
    (provenanceInvariant_of_reachable hS hreachQ hHQ).current_epoch_le

/-! ### Early epochs -/

/-- A reachable state of epoch at most `GENESIS_EPOCH + 2` keeps the genesis
justified epoch: the passes at epochs 0 and 1 return early. -/
theorem early_current_justified {S : FFGSetup Root} (hS : S.Admissible)
    (hnum : (S.scope.last_epoch + 1) * S.cfg.slots_per_epoch +
      S.preset.slots_per_historical_root ≤ UINT64_MAX)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {X : FFGBeaconState Root} (h : Reachable S blocks votes X) :
    compute_epoch_at_slot S.cfg X.slot ≤ S.scope.last_epoch →
      compute_epoch_at_slot S.cfg X.slot ≤ 2 → X.current_justified_checkpoint.epoch = 0 := by
  induction h with
  | genesis => intro _ _; rfl
  | @slots blocks votes state next target hreach hslots ih =>
    intro hH h2
    obtain ⟨hnext, hlt⟩ := process_slots_slot hslots
    have hle : compute_epoch_at_slot S.cfg state.slot ≤ compute_epoch_at_slot S.cfg next.slot :=
      compute_epoch_at_slot_mono (by rw [hnext]; exact Nat.le_of_lt hlt)
    obtain ⟨next', hnext', -, -, hcj⟩ := process_slots_ok hS hnum
      (provenanceInvariant_of_reachable hS hreach (hle.trans hH))
      (lengthsOK_of_reachable hreach) hlt (by rw [← hnext]; exact hH)
    rw [hslots] at hnext'
    cases hnext'
    rw [hcj, cjRun_early _ _ _ (by rw [← hnext]; beacon_omega)]
    exact ih (hle.trans hH) (hle.trans h2)
  | @block blocks votes state next blk hreach htrans ih =>
    intro hH h2
    obtain ⟨hns, hlt⟩ := state_transition_slot htrans
    have hle : compute_epoch_at_slot S.cfg state.slot ≤ compute_epoch_at_slot S.cfg next.slot :=
      compute_epoch_at_slot_mono (by rw [hns]; exact Nat.le_of_lt hlt)
    obtain ⟨-, -, hcj, -⟩ := transition_run_mono hS hnum hreach (hle.trans hH) htrans hH
    rw [hcj, cjRun_early _ _ _ (by beacon_omega)]
    exact ih (hle.trans hH) (hle.trans h2)

end Formula

section Chain

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The parent root of the genesis block is not an execution ancestor of an
accepted root. -/
theorem genesis_parent_not_descends (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.ext store) (hs : B.BridgedStore store)
    {x : Root} (hx : E.RootKnownInScheduledPrefix B.setup.cfg B.ext x)
    (hd : E.RootDescends (store.blocks B.setup.genesisRoot).parent_root x) : False := by
  have hne := hs.genesis_parent_ne
  have hun := hs.genesis_parent_unopened
  cases hd with
  | refl =>
    obtain ⟨store', -, hs', hx'⟩ := B.accepted_bridged hB hg hx
    obtain ⟨cs, -, -, -, -, -, hrest⟩ := hs'.known _ hx'
    obtain ⟨wire, ho, -⟩ := hrest hne
    rw [hun] at ho
    cases ho
  | step hedge _ =>
    obtain ⟨anchor, hroot, -, -, -, hgs⟩ := hg
    have hgmem : B.setup.genesisRoot ∈ E.genesis_store.block_roots := by
      rw [hgs, ← hroot]; simp [get_forkchoice_store]
    have hagree : store.blocks B.setup.genesisRoot = E.genesis_store.blocks B.setup.genesisRoot :=
      hwf.blocks_agree (Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.ext E hstore)
        (fun r hr => Or.inl ⟨hr, rfl⟩) hs.genesis_known hgmem
    rcases hedge with ⟨r, hr, hchild, -⟩ | ⟨w, n, b, hb, hchild, -⟩
    · rw [hgs] at hr
      simp only [get_forkchoice_store, List.mem_singleton] at hr
      exact hne (hchild.trans (hr.trans hroot))
    · exact hwf.anchor_parent_unscheduled _ hgmem w n b hb (by rw [← hagree, hchild])

/-- **Chain runs.** An accepted execution ancestor `x` of a root `r` known in a
prefix store is known in the same store. Every reachable run of the committed
state of `x` extends to a run of the committed state of `r` with more
included votes, and every later run from `r` is at least the run from `x`. -/
theorem chain_runs (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.ext store) {r x : Root}
    (hd : E.RootDescends r x) (hr : r ∈ store.block_roots)
    (hx : E.RootKnownInScheduledPrefix B.setup.cfg B.ext x) :
    x ∈ store.block_roots ∧ ∃ csx csr, B.stateOf x = some csx ∧ B.stateOf r = some csr ∧
      csx.slot ≤ csr.slot ∧
      ∀ bx vx, Reachable B.setup bx vx csx → ∃ br vr, Reachable B.setup br vr csr ∧
        (∀ v ∈ vx, v ∈ vr) ∧
        ∀ k, compute_epoch_at_slot B.setup.cfg csr.slot ≤ k →
          (cjRun B.setup bx vx (compute_epoch_at_slot B.setup.cfg csx.slot)
            (k - compute_epoch_at_slot B.setup.cfg csx.slot)
            csx.current_justified_checkpoint).epoch ≤
          (cjRun B.setup br vr (compute_epoch_at_slot B.setup.cfg csr.slot)
            (k - compute_epoch_at_slot B.setup.cfg csr.slot)
            csr.current_justified_checkpoint).epoch := by
  have hs := B.bridgedStore_prefix hB hg hstore
  have hprov := Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.ext E hstore
  induction hd with
  | refl r =>
    obtain ⟨cs, hcs, -⟩ := hs.known r hr
    exact ⟨hr, cs, cs, hcs, hcs, le_rfl, fun bx vx h => ⟨bx, vx, h, fun _ hv => hv,
      fun _ _ => le_rfl⟩⟩
  | @step child parent ancestor hedge _ ih =>
    have hpEq := E.parentEdge_parent_eq_of_store_known_for_storeReflection hwf hprov hr hedge
    by_cases hgen : child = B.setup.genesisRoot
    · subst hgen
      exfalso
      rename_i hrest
      exact B.genesis_parent_not_descends hB hg hwf hstore hs hx (hpEq ▸ hrest)
    obtain ⟨cs, hcs, -, ⟨-, hH⟩, -, -, hrest⟩ := hs.known child hr
    obtain ⟨wire, -, -, -, hpk, cp, hcp, htrans⟩ := hrest hgen
    rw [← hpEq] at hpk hcp
    obtain ⟨hxk, csx, csp, hcsx, hcsp, hle, hruns⟩ := ih hpk hx
    rw [hcp] at hcsp
    cases hcsp
    refine ⟨hxk, csx, cs, hcsx, hcs, ?_, ?_⟩
    · exact hle.trans (Nat.le_of_lt (state_transition_slot htrans).2 |>.trans
        (state_transition_slot htrans).1.symm.le)
    · intro bx vx hreach
      obtain ⟨bp, vp, hreachp, hsub, hk⟩ := hruns bx vx hreach
      have hHp' : compute_epoch_at_slot B.setup.cfg cp.slot ≤ B.setup.scope.last_epoch := by
        obtain ⟨cp', hcp', -, ⟨-, hHp''⟩, -⟩ := hs.known parent hpk
        rw [hcp] at hcp'
        cases hcp'
        exact hHp''
      obtain ⟨hreachc, -, -, hmono⟩ :=
        transition_run_mono hB.setup hB.numeric hreachp hHp' htrans hH
      refine ⟨_, _, hreachc, fun v hv => List.mem_append_left _ (hsub v hv), ?_⟩
      intro k hk'
      exact (hk k ((compute_epoch_at_slot_mono (Nat.le_of_lt
        (by have := state_transition_slot htrans; rw [this.1] ; exact this.2))).trans hk')).trans
        (hmono k hk')

/-! ### Canonical formed evidence -/

/-- A realized checkpoint of a slot run from the committed state of `x`, to an
in-scope target slot. The pre-state of every block has this form. -/
def RealizedAt (x : Root) (c : Checkpoint Root) : Prop :=
  ∃ cs target next, B.stateOf x = some cs ∧
    compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch ∧
    process_slots B.setup.cfg B.setup.preset cs target = .ok next ∧
    c = B.norm0 next.current_justified_checkpoint

/-- The canonical formed-evidence relation: at an accepted block, the four
selector values and the realized checkpoints of its slot runs. -/
def Formed (E : Execution Root) (x : Root) (c : Checkpoint Root) : Prop :=
  E.RootKnownInScheduledPrefix B.setup.cfg B.ext x ∧
    (c = B.GJ x ∨ c = B.GF x ∨ c = B.GU x ∨ c = B.GUF x ∨ B.RealizedAt x c)

omit [Inhabited Root] in
theorem gj_epoch {r : Root} {cs : FFGBeaconState Root} (hcs : B.stateOf r = some cs) :
    (B.GJ r).epoch = cs.current_justified_checkpoint.epoch := by
  rw [B.GJ_of r hcs, B.norm0_epoch]

omit [Inhabited Root] in
/-- `GU` is the one-boundary run from the committed state. -/
theorem gu_epoch (hB : B.Admissible) {r : Root} {cs : FFGBeaconState Root}
    (hcs : B.stateOf r = some cs) {bl : List (FFGWireBlock Root)}
    {vo : List (IncludedVote Root)} (hreach : Reachable B.setup bl vo cs)
    (hH : compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch) :
    (B.GU r).epoch = (cjRun B.setup bl vo (compute_epoch_at_slot B.setup.cfg cs.slot) 1
      cs.current_justified_checkpoint).epoch := by
  obtain ⟨Y, hY, hcj⟩ := eager_pjf hB.setup hB.numeric
    (provenanceInvariant_of_reachable hB.setup hreach hH) (lengthsOK_of_reachable hreach) hH
  rw [B.GU_of r (B.eagerOf_of r hcs hY), B.norm0_epoch, hcj]
  rfl

/-- A formed checkpoint is bounded by a run of at most two boundaries from
the committed state of its carrier, and of at most one boundary from an
epoch `E ≥ 2`. -/
theorem formed_run_bound (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {x : Root} {c : Checkpoint Root} (hf : B.Formed E x c) {cs : FFGBeaconState Root}
    (hcs : B.stateOf x = some cs) {bl : List (FFGWireBlock Root)}
    {vo : List (IncludedVote Root)} (hreach : Reachable B.setup bl vo cs)
    (hH : compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch) :
    ∃ j, c.epoch ≤ (cjRun B.setup bl vo (compute_epoch_at_slot B.setup.cfg cs.slot) j
      cs.current_justified_checkpoint).epoch ∧ j ≤ 2 ∧
      (2 ≤ compute_epoch_at_slot B.setup.cfg cs.slot → j ≤ 1) := by
  have hinv := provenanceInvariant_of_reachable hB.setup hreach hH
  have hraw : ∃ j, c.epoch ≤ (cjRun B.setup bl vo (compute_epoch_at_slot B.setup.cfg cs.slot) j
      cs.current_justified_checkpoint).epoch := by
    obtain ⟨hacc, h | h | h | h | h⟩ := hf
    · exact ⟨0, by rw [h, B.gj_epoch hcs]; exact le_rfl⟩
    · refine ⟨0, ?_⟩
      rw [h]
      exact (B.realized_finalized_epoch_le_realized_justified hB hg hacc).trans
        (by rw [B.gj_epoch hcs]; exact le_rfl)
    · exact ⟨1, by rw [h, B.gu_epoch hB hcs hreach hH]⟩
    · refine ⟨1, ?_⟩
      rw [h]
      exact (B.unrealized_finalized_epoch_le_unrealized_justified hB hg hacc).trans
        (by rw [B.gu_epoch hB hcs hreach hH])
    · obtain ⟨cs', target, next, hcs', htarget, hslots, rfl⟩ := h
      rw [hcs] at hcs'
      cases hcs'
      obtain ⟨hnext, hlt⟩ := process_slots_slot hslots
      obtain ⟨next', hnext', -, -, hcj⟩ := process_slots_ok hB.setup hB.numeric hinv
        (lengthsOK_of_reachable hreach) hlt htarget
      rw [hslots] at hnext'
      cases hnext'
      exact ⟨_, by rw [B.norm0_epoch, hcj]⟩
  obtain ⟨j, hj⟩ := hraw
  obtain ⟨h2, h1⟩ := cjRun_cap hB.setup hinv.target_epoch_le j cs.current_justified_checkpoint
  by_cases hE : 2 ≤ compute_epoch_at_slot B.setup.cfg cs.slot
  · exact ⟨min j 1, by rw [← h1 hE]; exact hj, by omega, fun _ => by omega⟩
  · exact ⟨min j 2, by rw [← h2]; exact hj, by omega, fun h => absurd h hE⟩

/-- A formed checkpoint is no later than the epoch of its carrier. -/
theorem formed_epoch_le (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {x : Root} {c : Checkpoint Root} (hf : B.Formed E x c) {cs : FFGBeaconState Root}
    (hcs : B.stateOf x = some cs) :
    c.epoch ≤ compute_epoch_at_slot B.setup.cfg cs.slot := by
  obtain ⟨cs', bl, vo, -, hcs', hreach, hH, -⟩ := B.accepted_state hB hg hf.1
  rw [hcs] at hcs'
  cases hcs'
  have hinv := provenanceInvariant_of_reachable hB.setup hreach hH
  obtain ⟨j, hj, -⟩ := B.formed_run_bound hB hg hf hcs hreach hH
  refine hj.trans ?_
  rcases cjRun_epoch_le hB.setup hinv.target_epoch_le j cs.current_justified_checkpoint with
    h | h
  · rw [h]; have := hinv.current_epoch_le; beacon_omega
  · exact h

omit [Inhabited Root] in
theorem known_witness {store : Store Root} (hs : B.BridgedStore store) {r : Root}
    (hr : r ∈ store.block_roots) :
    ∃ cs, B.stateOf r = some cs ∧ cs.slot = (store.blocks r).slot ∧
      compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch ∧
      ∃ bl vo, Reachable B.setup bl vo cs := by
  obtain ⟨cs, hcs, -, ⟨⟨bl, vo, hreach⟩, hH⟩, -, hslot, -⟩ := hs.known r hr
  exact ⟨cs, hcs, hslot, hH, bl, vo, hreach⟩

/-! ### The maximality and monotonicity laws -/

/-- `unrealized_justified_max`. -/
theorem unrealized_justified_max (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {r : Root}
    {b : BeaconBlock Root} {c : Checkpoint Root}
    (hb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b)
    (hE : GENESIS_EPOCH + 1 < compute_epoch_at_slot B.setup.cfg b.slot)
    (hc : ∃ carrier, E.RootDescends r carrier ∧ B.Formed E carrier c) :
    c.epoch ≤ (B.GU r).epoch := by
  obtain ⟨x, hd, hf⟩ := hc
  obtain ⟨store, hstore, hr, hbr⟩ := hb
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨hxk, csx, csr, hcsx, hcsr, hle, hruns⟩ := B.chain_runs hB hg hwf hstore hd hr hf.1
  obtain ⟨csx', hcsx', -, hHx, bx, vx, hreachx⟩ := B.known_witness hs hxk
  rw [hcsx] at hcsx'
  cases hcsx'
  obtain ⟨csr', hcsr', hslotr, hHr, -⟩ := B.known_witness hs hr
  rw [hcsr] at hcsr'
  cases hcsr'
  rw [hbr] at hslotr
  rw [← hslotr] at hE
  simp only [GENESIS_EPOCH] at hE
  obtain ⟨br, vr, hreachr, -, hk⟩ := hruns bx vx hreachx
  obtain ⟨j, hj, hj2, hj1⟩ := B.formed_run_bound hB hg hf hcsx hreachx hHx
  have hEle := compute_epoch_at_slot_mono (cfg := B.setup.cfg) hle
  have hjk : j ≤ compute_epoch_at_slot B.setup.cfg csr.slot + 1 -
      compute_epoch_at_slot B.setup.cfg csx.slot := by
    by_cases h2 : 2 ≤ compute_epoch_at_slot B.setup.cfg csx.slot
    · have := hj1 h2; beacon_omega
    · beacon_omega
  have hinvx := provenanceInvariant_of_reachable hB.setup hreachx hHx
  refine hj.trans ((cjRun_epoch_mono_len hinvx.current_epoch_le hjk).trans ?_)
  have := hk (compute_epoch_at_slot B.setup.cfg csr.slot + 1) (by beacon_omega)
  rw [show compute_epoch_at_slot B.setup.cfg csr.slot + 1 -
    compute_epoch_at_slot B.setup.cfg csr.slot = 1 by beacon_omega] at this
  rw [B.gu_epoch hB hcsr hreachr hHr]
  exact this

/-- `realized_justified_max`. -/
theorem realized_justified_max (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {r seed : Root}
    {b sb : BeaconBlock Root} {c : Checkpoint Root}
    (hb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b)
    (hsb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext seed sb)
    (hds : E.RootDescends r seed)
    (hlt : compute_epoch_at_slot B.setup.cfg sb.slot < compute_epoch_at_slot B.setup.cfg b.slot)
    (hE : GENESIS_EPOCH + 2 < compute_epoch_at_slot B.setup.cfg b.slot)
    (hc : ∃ carrier, E.RootDescends seed carrier ∧ B.Formed E carrier c) :
    c.epoch ≤ (B.GJ r).epoch := by
  obtain ⟨x, hd, hf⟩ := hc
  obtain ⟨sstore, hsstore, hsr, hsbr⟩ := hsb
  have hss := B.bridgedStore_prefix hB hg hsstore
  obtain ⟨-, csx0, css, hcsx0, hcss, hlexs, -⟩ := B.chain_runs hB hg hwf hsstore hd hsr hf.1
  obtain ⟨css', hcss', hslots, -⟩ := B.known_witness hss hsr
  rw [hcss] at hcss'
  cases hcss'
  rw [hsbr] at hslots
  obtain ⟨store, hstore, hr, hbr⟩ := hb
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨hxk, csx, csr, hcsx, hcsr, -, hruns⟩ :=
    B.chain_runs hB hg hwf hstore (Execution.RootDescends.trans E hds hd) hr hf.1
  rw [hcsx0] at hcsx
  cases hcsx
  obtain ⟨csx', hcsx', -, hHx, bx, vx, hreachx⟩ := B.known_witness hs hxk
  rw [hcsx0] at hcsx'
  cases hcsx'
  obtain ⟨csr', hcsr', hslotr, hHr, -⟩ := B.known_witness hs hr
  rw [hcsr] at hcsr'
  cases hcsr'
  rw [hbr] at hslotr
  rw [← hslotr] at hE hlt
  rw [← hslots] at hlt
  simp only [GENESIS_EPOCH] at hE
  obtain ⟨br, vr, -, -, hk⟩ := hruns bx vx hreachx
  obtain ⟨j, hj, hj2, hj1⟩ := B.formed_run_bound hB hg hf hcsx0 hreachx hHx
  have hExs := compute_epoch_at_slot_mono (cfg := B.setup.cfg) hlexs
  have hjk : j ≤ compute_epoch_at_slot B.setup.cfg csr.slot -
      compute_epoch_at_slot B.setup.cfg csx0.slot := by
    by_cases h2 : 2 ≤ compute_epoch_at_slot B.setup.cfg csx0.slot
    · have := hj1 h2; beacon_omega
    · beacon_omega
  have hinvx := provenanceInvariant_of_reachable hB.setup hreachx hHx
  refine hj.trans ((cjRun_epoch_mono_len hinvx.current_epoch_le hjk).trans ?_)
  have := hk (compute_epoch_at_slot B.setup.cfg csr.slot) le_rfl
  rw [Nat.sub_self] at this
  rw [B.gj_epoch hcsr]
  exact this

/-- `unrealized_justified_epoch_le_later_realized`. -/
theorem unrealized_justified_epoch_le_later_realized (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {seed tip : Root}
    {sb tb : BeaconBlock Root}
    (hsb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext seed sb)
    (htb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext tip tb)
    (hd : E.RootDescends tip seed)
    (hlt : compute_epoch_at_slot B.setup.cfg sb.slot < compute_epoch_at_slot B.setup.cfg tb.slot) :
    (B.GU seed).epoch ≤ (B.GJ tip).epoch := by
  obtain ⟨store, hstore, hr, hbr⟩ := htb
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨hxk, csx, csr, hcsx, hcsr, -, hruns⟩ :=
    B.chain_runs hB hg hwf hstore hd hr (Execution.BlockKnownInScheduledPrefix.acceptedRoot
      B.setup.cfg B.ext E hsb)
  obtain ⟨csx', hcsx', -, hHx, bx, vx, hreachx⟩ := B.known_witness hs hxk
  rw [hcsx] at hcsx'
  cases hcsx'
  obtain ⟨csr', hcsr', hslotr, -, -⟩ := B.known_witness hs hr
  rw [hcsr] at hcsr'
  cases hcsr'
  have hslotx := B.blockKnown_slot hB hg hsb hcsx
  rw [hbr] at hslotr
  rw [← hslotr, ← hslotx] at hlt
  obtain ⟨br, vr, -, -, hk⟩ := hruns bx vx hreachx
  have hinvx := provenanceInvariant_of_reachable hB.setup hreachx hHx
  rw [B.gu_epoch hB hcsx hreachx hHx, B.gj_epoch hcsr]
  refine (cjRun_epoch_mono_len hinvx.current_epoch_le (b := compute_epoch_at_slot B.setup.cfg
    csr.slot - compute_epoch_at_slot B.setup.cfg csx.slot) (by beacon_omega)).trans ?_
  have := hk (compute_epoch_at_slot B.setup.cfg csr.slot) le_rfl
  rw [Nat.sub_self] at this
  exact this

/-- `unrealized_justified_mono`. -/
theorem unrealized_justified_mono (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {seed tip : Root}
    (hseed : E.RootKnownInScheduledPrefix B.setup.cfg B.ext seed)
    (htip : E.RootKnownInScheduledPrefix B.setup.cfg B.ext tip)
    (hd : E.RootDescends tip seed) :
    (B.GU seed).epoch ≤ (B.GU tip).epoch := by
  obtain ⟨store, hstore, hr⟩ := htip
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨hxk, csx, csr, hcsx, hcsr, hle, hruns⟩ := B.chain_runs hB hg hwf hstore hd hr hseed
  obtain ⟨csx', hcsx', -, hHx, bx, vx, hreachx⟩ := B.known_witness hs hxk
  rw [hcsx] at hcsx'
  cases hcsx'
  obtain ⟨csr', hcsr', -, hHr, -⟩ := B.known_witness hs hr
  rw [hcsr] at hcsr'
  cases hcsr'
  have hEle := compute_epoch_at_slot_mono (cfg := B.setup.cfg) hle
  obtain ⟨br, vr, hreachr, -, hk⟩ := hruns bx vx hreachx
  have hinvx := provenanceInvariant_of_reachable hB.setup hreachx hHx
  rw [B.gu_epoch hB hcsx hreachx hHx, B.gu_epoch hB hcsr hreachr hHr]
  refine (cjRun_epoch_mono_len hinvx.current_epoch_le (b := compute_epoch_at_slot B.setup.cfg
    csr.slot + 1 - compute_epoch_at_slot B.setup.cfg csx.slot) (by beacon_omega)).trans ?_
  have := hk (compute_epoch_at_slot B.setup.cfg csr.slot + 1) (by beacon_omega)
  rw [show compute_epoch_at_slot B.setup.cfg csr.slot + 1 -
    compute_epoch_at_slot B.setup.cfg csr.slot = 1 by beacon_omega] at this
  exact this

/-- `available_checkpoint_epoch_le_block`. -/
theorem available_checkpoint_epoch_le_block (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {r : Root}
    {b : BeaconBlock Root} {c : Checkpoint Root}
    (hb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b)
    (hc : ∃ carrier, E.RootDescends r carrier ∧ B.Formed E carrier c) :
    c.epoch ≤ compute_epoch_at_slot B.setup.cfg b.slot := by
  obtain ⟨x, hd, hf⟩ := hc
  obtain ⟨store, hstore, hr, hbr⟩ := hb
  obtain ⟨-, csx, csr, hcsx, hcsr, hle, -⟩ := B.chain_runs hB hg hwf hstore hd hr hf.1
  obtain ⟨csr', hcsr', hslotr, -⟩ := B.known_witness (B.bridgedStore_prefix hB hg hstore) hr
  rw [hcsr] at hcsr'
  cases hcsr'
  rw [← hbr, ← hslotr]
  exact (B.formed_epoch_le hB hg hf hcsx).trans (compute_epoch_at_slot_mono hle)

/-! ### Realized justification -/

omit [Inhabited Root] in
/-- The last epoch boundary on the committed chain of a known root of epoch at
least 1: a block `q` on the chain whose parent `p` is in an earlier epoch,
with `q` in the epoch of the root and with its current justified checkpoint. -/
theorem last_boundary (hB : B.Admissible) {store : Store Root} (hs : B.BridgedStore store)
    (E : Execution Root)
    (hedge : ∀ r ∈ store.block_roots, E.ParentEdge r (store.blocks r).parent_root) :
    ∀ n, ∀ r ∈ store.block_roots, (store.blocks r).slot ≤ n → ∀ cr, B.stateOf r = some cr →
      1 ≤ compute_epoch_at_slot B.setup.cfg cr.slot →
      ∃ q cp cq wire, q ∈ store.block_roots ∧ (store.blocks q).parent_root ∈ store.block_roots ∧
        E.RootDescends r q ∧
        q ≠ B.setup.genesisRoot ∧
        B.stateOf (store.blocks q).parent_root = some cp ∧ B.stateOf q = some cq ∧
        state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cp wire =
          .ok cq ∧
        compute_epoch_at_slot B.setup.cfg cp.slot < compute_epoch_at_slot B.setup.cfg cr.slot ∧
        compute_epoch_at_slot B.setup.cfg cq.slot = compute_epoch_at_slot B.setup.cfg cr.slot ∧
        cq.current_justified_checkpoint = cr.current_justified_checkpoint := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hr hn cr hcr hE1
    have hgen : r ≠ B.setup.genesisRoot := by
      intro h
      subst h
      rw [B.stateOf_genesis] at hcr
      cases hcr
      change 1 ≤ compute_epoch_at_slot B.setup.cfg 0 at hE1
      simp [compute_epoch_at_slot] at hE1
    obtain ⟨cs, hcs, -, ⟨-, hH⟩, -, hslot, hrest⟩ := hs.known r hr
    rw [hcr] at hcs
    cases hcs
    obtain ⟨wire, -, -, -, hpk, cp, hcp, htrans⟩ := hrest hgen
    obtain ⟨cp', hcp', hslotp, hHp, bp, vp, hreachp⟩ := B.known_witness hs hpk
    rw [hcp] at hcp'
    cases hcp'
    obtain ⟨-, hlts, hCJ, -⟩ := transition_run_mono hB.setup hB.numeric hreachp hHp htrans hH
    have hEle : compute_epoch_at_slot B.setup.cfg cp.slot ≤
        compute_epoch_at_slot B.setup.cfg cr.slot := compute_epoch_at_slot_mono (Nat.le_of_lt hlts)
    by_cases hlt : compute_epoch_at_slot B.setup.cfg cp.slot <
        compute_epoch_at_slot B.setup.cfg cr.slot
    · exact ⟨r, cp, cr, wire, hr, hpk, .refl r, hgen, hcp, hcr, htrans, hlt, rfl, rfl⟩
    · have heq : compute_epoch_at_slot B.setup.cfg cp.slot =
          compute_epoch_at_slot B.setup.cfg cr.slot := by beacon_omega
      have hlt2 : (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot := by
        rw [← hslotp, ← hslot]; exact hlts
      obtain ⟨q, cp', cq, wire', hq, hqp, hdq, hqg, hcp', hcq, htrans', hlt', heq', hcj'⟩ :=
        ih (store.blocks (store.blocks r).parent_root).slot
          (Nat.lt_of_lt_of_le hlt2 hn) _ hpk le_rfl cp hcp (heq ▸ hE1)
      refine ⟨q, cp', cq, wire', hq, hqp, .step (hedge r hr) hdq, hqg,
        hcp', hcq, htrans', heq ▸ hlt', heq ▸ heq', ?_⟩
      rw [hcj', hCJ, heq, Nat.sub_self]
      rfl

/-- `realized_justified_realized`: a realized justification that is not the
anchor was realized by an epoch-boundary run from an accepted block of an
earlier epoch. -/
theorem realized_justified_realized (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) {r : Root} {b : BeaconBlock Root}
    (hb : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b) :
    B.GJ r = B.anchorCheckpoint ∨
      GENESIS_EPOCH + 2 < compute_epoch_at_slot B.setup.cfg b.slot ∧
        ∃ seed sb, E.BlockKnownInScheduledPrefix B.setup.cfg B.ext seed sb ∧
          E.RootDescends r seed ∧
          compute_epoch_at_slot B.setup.cfg sb.slot < compute_epoch_at_slot B.setup.cfg b.slot ∧
          ∃ carrier, E.RootDescends seed carrier ∧ B.Formed E carrier (B.GJ r) := by
  obtain ⟨store, hstore, hr, hbr⟩ := hb
  have hs := B.bridgedStore_prefix hB hg hstore
  have hprov := Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.ext E hstore
  obtain ⟨cr, hcr, hslot, hH, bl, vo, hreach⟩ := B.known_witness hs hr
  by_cases h0 : cr.current_justified_checkpoint.epoch = 0
  · left
    rw [B.GJ_of r hcr]
    unfold norm0
    rw [if_pos (by simpa [GENESIS_EPOCH] using h0)]
  right
  have h3 : 2 < compute_epoch_at_slot B.setup.cfg cr.slot := by
    by_contra hle
    exact h0 (early_current_justified hB.setup hB.numeric hreach hH (by beacon_omega))
  obtain ⟨q, cp, cq, wire, hq, hpk, hdq, -, hcp, hcq, htrans, hlt, -, hcj⟩ :=
    B.last_boundary hB hs E (fun _ hr' => E.parentEdge_of_store_known hprov hr')
      _ r hr le_rfl cr hcr (by beacon_omega)
  have hdr := hdq
  rw [hbr] at hslot
  rw [← hslot]
  refine ⟨by simpa [GENESIS_EPOCH] using h3, (store.blocks q).parent_root,
    store.blocks (store.blocks q).parent_root, ⟨store, hstore, hpk, rfl⟩,
    Execution.RootDescends.trans E hdr (.step (E.parentEdge_of_store_known hprov hq) (.refl _)),
    ?_, (store.blocks q).parent_root, .refl _, ⟨⟨store, hstore, hpk⟩, ?_⟩⟩
  · obtain ⟨cp', hcp', hslotp, -⟩ := B.known_witness hs hpk
    rw [hcp] at hcp'
    cases hcp'
    rw [← hslotp]
    exact hlt
  · obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok htrans
    obtain ⟨hqs, -⟩ := state_transition_slot htrans
    obtain ⟨cq', hcq', -, hHq, -⟩ := B.known_witness hs hq
    rw [hcq] at hcq'
    cases hcq'
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨cp, wire.slot, atSlot, hcp, by rw [← hqs]; exact hHq,
      hslots, ?_⟩)))
    rw [B.GJ_of r hcr, ← hcj, (process_block_checkpoints hblock).2.2.1]

end ConcreteBridge

end Chain

end FastConfirmation.Spec.ConcreteFFG

end

