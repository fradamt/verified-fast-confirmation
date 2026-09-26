module
public import FastConfirmationProofs.FFG.Concrete.CanonicalTiming
public import FastConfirmationProofs.FFG.Concrete.FinalizedPrefix

@[expose] public section

/-! Proves that each formed checkpoint available at an accepted root is the
checkpoint of that root's chain at its epoch, in every exact prefix store
that knows the root (`available_checkpoint_checkpoint_of_known`). A formed
checkpoint is the genesis anchor or the chain checkpoint of a reachable run
of its carrier. The committed parent chain gives a reachable run whose block
list is the store ancestor walk, and the ancestor walk composes along
execution descent. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

section Shape

variable {Root : Type} [DecidableEq Root]

/-- The checkpoint is the stub or the chain checkpoint of its epoch. -/
def OnChain (S : FFGSetup Root) (blocks : List (FFGWireBlock Root)) (c : Checkpoint Root) : Prop :=
  c = S.stub ∨ c = chainCheckpoint S blocks c.epoch

omit [DecidableEq Root] in
theorem onChain_chainCheckpoint (S : FFGSetup Root) (blocks : List (FFGWireBlock Root))
    (e : Epoch) : OnChain S blocks (chainCheckpoint S blocks e) := Or.inr rfl

theorem onChain_cjFormula {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {c : Checkpoint Root}
    (hc : OnChain S blocks c) : OnChain S blocks (cjFormula S blocks votes E c) := by
  unfold cjFormula
  split_ifs
  · exact hc
  · exact onChain_chainCheckpoint S blocks _
  · exact onChain_chainCheckpoint S blocks _
  · exact hc

theorem onChain_cjRun {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} :
    ∀ (n : ℕ) (E : Epoch) (c : Checkpoint Root), OnChain S blocks c →
      OnChain S blocks (cjRun S blocks votes E n c)
  | 0, _, _, hc => hc
  | n + 1, E, _, hc => onChain_cjRun n (E + 1) _ (onChain_cjFormula hc)

theorem onChain_of_justified {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (hR : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    {c : Checkpoint Root} (hc : Justified S votes c) : OnChain S blocks c :=
  Justified.eq_stub_or_chainCheckpoint hS hR hH hc

end Shape

section Bridge

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

omit [LinearOrder Root] [Inhabited Root] in
theorem norm0_onChain {blocks : List (FFGWireBlock Root)} {c : Checkpoint Root}
    (hc : OnChain B.setup blocks c) :
    B.norm0 c = B.anchorCheckpoint ∨
      B.norm0 c = chainCheckpoint B.setup blocks (B.norm0 c).epoch := by
  unfold norm0
  split_ifs with h0
  · exact Or.inl rfl
  · rcases hc with rfl | h
    · exact absurd rfl h0
    · exact Or.inr h

/-- **Formed shape.** A formed checkpoint is the genesis anchor or the chain
checkpoint of its epoch on every reachable run of the carrier state. -/
theorem formed_shape (hB : B.Admissible) {E : Execution Root} {x : Root} {c : Checkpoint Root}
    (hf : B.Formed E x c) {cs : FFGBeaconState Root}
    (hcs : B.stateOf x = some cs) {bl : List (FFGWireBlock Root)}
    {vo : List (IncludedVote Root)} (hreach : Reachable B.setup bl vo cs)
    (hH : compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch) :
    c = B.anchorCheckpoint ∨ c = chainCheckpoint B.setup bl c.epoch := by
  have hinv := provenanceInvariant_of_reachable hB.setup hreach hH
  have hj : ∀ {c'}, Justified B.setup vo c' → OnChain B.setup bl c' :=
    fun h => onChain_of_justified hB.setup hreach hH h
  obtain ⟨Y, hY, hcj⟩ := eager_pjf hB.setup hB.numeric hinv (lengthsOK_of_reachable hreach) hH
  have he := B.eagerOf_of x hcs hY
  obtain ⟨-, h | h | h | h | h⟩ := hf
  · rw [h, B.GJ_of x hcs]; exact B.norm0_onChain (hj hinv.current_justified)
  · rw [h, B.GF_of x hcs]; exact B.norm0_onChain (hj hinv.finalized_justified)
  · rw [h, B.GU_of x he, hcj]
    exact B.norm0_onChain (onChain_cjFormula (hj hinv.current_justified))
  · rw [h, B.GUF_of x he]
    obtain ⟨bits, pj, j, f, rfl, hout⟩ := process_justification_and_finalization_outcome hY
    apply B.norm0_onChain
    change OnChain B.setup bl f
    rcases hout with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl | rfl | rfl⟩
    · exact hj hinv.finalized_justified
    · exact hj hinv.finalized_justified
    · exact hj hinv.previous_justified
    · exact hj hinv.current_justified
  · obtain ⟨cs', target, next, hcs', htarget, hslots, rfl⟩ := h
    rw [hcs] at hcs'
    cases hcs'
    obtain ⟨-, hlt⟩ := process_slots_slot hslots
    obtain ⟨next', hnext', -, -, hrun⟩ := process_slots_ok hB.setup hB.numeric hinv
      (lengthsOK_of_reachable hreach) hlt htarget
    rw [hslots] at hnext'
    cases hnext'
    rw [hrun]
    exact B.norm0_onChain (onChain_cjRun _ _ _ (hj hinv.current_justified))

/-! ### The committed chain run -/

omit [Inhabited Root] in
/-- **Chain witness.** A known root of a bridged store has a reachable run of
its committed state whose block list is the store ancestor walk. -/
theorem chain_witness (hB : B.Admissible) {store : Store Root} (hs : B.BridgedStore store) :
    ∀ n, ∀ x ∈ store.block_roots, (store.blocks x).slot ≤ n →
      ∃ cs bl vo, B.stateOf x = some cs ∧ Reachable B.setup bl vo cs ∧
        ∀ y, chainRootAt B.setup.genesisRoot bl y =
          (get_ancestor store (ForkChoiceNode.mk x .pending) y).root := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    by_cases hgen : x = B.setup.genesisRoot
    · subst hgen
      refine ⟨_, [], [], B.stateOf_genesis, .genesis, fun y => ?_⟩
      rw [get_ancestor_stop (by rw [hs.genesis_slot]; exact Nat.zero_le _)]
      rfl
    obtain ⟨cs, hcs, -, ⟨-, hH⟩, -, hslot, hrest⟩ := hs.known x hx
    obtain ⟨wire, -, hwroot, hm, hpk, cp, hcp, htrans⟩ := hrest hgen
    obtain ⟨cp', hcp', hslotp, hHp, -⟩ := B.known_witness hs hpk
    rw [hcp] at hcp'
    cases hcp'
    obtain ⟨hwslot, hlt⟩ := state_transition_slot htrans
    have hplt : (store.blocks (store.blocks x).parent_root).slot < (store.blocks x).slot := by
      rw [← hslotp, ← hslot, hwslot]; exact hlt
    obtain ⟨cp', bp, vp, hcp', hreachp, hchain⟩ := ih _ (Nat.lt_of_lt_of_le hplt hn) _ hpk le_rfl
    rw [hcp] at hcp'
    cases hcp'
    have hinvp := provenanceInvariant_of_reachable hB.setup hreachp hHp
    refine ⟨cs, bp ++ [wire], vp ++ blockVotes B.setup cp wire, hcs,
      Reachable.block wire hreachp htrans, fun y => ?_⟩
    have hxslot : (store.blocks x).slot = wire.slot := hm.1
    by_cases hy : y < wire.slot
    · rw [chainRootAt_append_of_lt hy, hchain y,
        get_ancestor_step hs.parentSlotLt hx (by rw [hxslot]; exact hy)
          (hs.walkKnown y _ _ hpk le_rfl)]
    · rw [chainRootAt_of_forall_le, tipRoot_append, hwroot,
        get_ancestor_stop (by rw [hxslot]; exact Nat.le_of_not_lt hy)]
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · have := (hinvp.blocks_le_header b hb).trans hinvp.header_le_slot
        beacon_omega
      · rw [List.mem_singleton.mp hb]; exact Nat.le_of_not_lt hy

omit [Inhabited Root] in
/-- The only known root of slot zero is the genesis root. -/
theorem BridgedStore.slot_zero {B : ConcreteBridge Root} {store : Store Root}
    (hs : B.BridgedStore store) {a : Root} (ha : a ∈ store.block_roots)
    (h0 : (store.blocks a).slot ≤ 0) : a = B.setup.genesisRoot := by
  by_contra hne
  obtain ⟨_, -, -, -, -, -, hkn⟩ := hs.known a ha
  obtain ⟨-, -, -, -, hpa, -⟩ := hkn hne
  exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (hs.parentSlotLt a ha hpa) h0)

/-- An accepted execution ancestor is the store ancestor at its own slot. -/
theorem chain_ancestor (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.ext store) {r x : Root}
    (hd : E.RootDescends r x) (hr : r ∈ store.block_roots)
    (hx : E.RootKnownInScheduledPrefix B.setup.cfg B.ext x) :
    x ∈ store.block_roots ∧ (store.blocks x).slot ≤ (store.blocks r).slot ∧
      (get_ancestor store (ForkChoiceNode.mk r .pending) (store.blocks x).slot).root = x := by
  have hs := B.bridgedStore_prefix hB hg hstore
  have hprov := Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.ext E hstore
  induction hd with
  | refl r => exact ⟨hr, le_rfl, by rw [get_ancestor_stop le_rfl]⟩
  | @step child parent ancestor hedge hrest ih =>
    have hpEq := E.parentEdge_parent_eq_of_store_known_for_storeReflection hwf hprov hr hedge
    by_cases hgen : child = B.setup.genesisRoot
    · subst hgen
      exact (B.genesis_parent_not_descends hB hg hwf hstore hs hx (hpEq ▸ hrest)).elim
    obtain ⟨cs, -, -, -, -, -, hkn⟩ := hs.known child hr
    obtain ⟨-, -, -, -, hpk, -⟩ := hkn hgen
    rw [← hpEq] at hpk
    obtain ⟨hxk, hle, hanc⟩ := ih hpk hx
    have hplt := hs.parentSlotLt child hr (hpEq ▸ hpk)
    rw [← hpEq] at hplt
    refine ⟨hxk, hle.trans (Nat.le_of_lt hplt), ?_⟩
    rw [get_ancestor_step hs.parentSlotLt hr (Nat.lt_of_le_of_lt hle hplt)
      (by rw [← hpEq]; exact hs.walkKnown _ _ _ hpk le_rfl), ← hpEq]
    exact hanc

/-- **`available_checkpoint_checkpoint_of_known`.** -/
theorem available_checkpoint_of_known (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E) {store : Store Root}
    (hstore : E.ScheduledPrefixStore B.setup.cfg B.ext store) {r : Root}
    (hr : r ∈ store.block_roots) {c : Checkpoint Root}
    (hc : ∃ carrier, E.RootDescends r carrier ∧ B.Formed E carrier c) :
    c = get_checkpoint_for_block B.setup.cfg store r c.epoch := by
  obtain ⟨x, hd, hf⟩ := hc
  have hs := B.bridgedStore_prefix hB hg hstore
  obtain ⟨hxk, -, hanc⟩ := B.chain_ancestor hB hg hwf hstore hd hr hf.1
  obtain ⟨cs, bl, vo, hcs, hreach, hchain⟩ := B.chain_witness hB hs _ x hxk le_rfl
  obtain ⟨cs', hcs', hslot, hH, -⟩ := B.known_witness hs hxk
  rw [hcs] at hcs'
  cases hcs'
  have hle := B.formed_epoch_le hB hg hf hcs
  unfold get_checkpoint_for_block get_checkpoint_block
  have hstart : compute_start_slot_at_epoch B.setup.cfg c.epoch ≤ (store.blocks x).slot := by
    rw [← hslot]
    obtain ⟨h1, -⟩ := slot_mem_epoch (cfg := B.setup.cfg) cs.slot
    exact (Nat.mul_le_mul_right _ hle).trans h1
  have hcomp : (get_ancestor store (ForkChoiceNode.mk r .pending)
      (compute_start_slot_at_epoch B.setup.cfg c.epoch)).root =
      (get_ancestor store (ForkChoiceNode.mk x .pending)
        (compute_start_slot_at_epoch B.setup.cfg c.epoch)).root := by
    rw [← get_ancestor_comp_root hs.parentSlotLt hstart
      (hs.walkKnown _ _ r hr le_rfl), hanc]
  rcases B.formed_shape hB hf hcs hreach hH with h | h
  · subst h
    change B.anchorCheckpoint = ⟨0, (get_ancestor store (ForkChoiceNode.mk r .pending)
      (compute_start_slot_at_epoch B.setup.cfg 0)).root⟩
    have hspec := get_ancestor_spec hs.parentSlotLt (hs.walkKnown
      (compute_start_slot_at_epoch B.setup.cfg 0) _ r hr le_rfl)
    rw [hs.slot_zero hspec.1 (by simpa [compute_start_slot_at_epoch] using hspec.2)]
    rfl
  · conv_lhs => rw [h]
    unfold chainCheckpoint
    rw [hchain, hcomp]

end ConcreteBridge

end Bridge

end FastConfirmation.Spec.ConcreteFFG

end
