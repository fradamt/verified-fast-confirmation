module
public import FastConfirmationProofs.FFG.Concrete.JustificationSoundness
public import FastConfirmationInternal.FFG.ConcreteFinality

@[expose] public section

/-! Proves finalization soundness for the concrete FFG model. Each of the four
Python finalization rules of `weigh_justification_and_finalization` gives a
finalizing link from a justified checkpoint to the chain checkpoint one or two
epochs later. In the two-epoch case the chain checkpoint between them is
justified. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### The four rules as a function of the new bits -/

/-- The finalized checkpoint after the four ordered Python rules, as a
function of the new justification bits. -/
def finalizedOf (bits : List Bool) (previous current finalized : Checkpoint Root)
    (epoch : Epoch) : Checkpoint Root :=
  let f1 := if ((bits.drop 1).take 3).all id && previous.epoch + 3 == epoch then previous
    else finalized
  let f2 := if ((bits.drop 1).take 2).all id && previous.epoch + 2 == epoch then previous
    else f1
  let f3 := if (bits.take 3).all id && current.epoch + 2 == epoch then current else f2
  if (bits.take 2).all id && current.epoch + 1 == epoch then current else f3

omit [DecidableEq Root] in
/-- The new bits and the new finalized checkpoint of one weighing pass. -/
theorem weigh_justification_and_finalization_bits {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root} {total previous current : Gwei}
    (h : weigh_justification_and_finalization cfg preset state total previous current =
      .ok next) :
    ∃ b0 b1 b2 b3 : Bool, state.justification_bits = [b0, b1, b2, b3] ∧
      next.justification_bits = [decide (total * 2 ≤ current * 3),
        decide (total * 2 ≤ previous * 3) || b0, b1, b2] ∧
      next.finalized_checkpoint = finalizedOf next.justification_bits
        state.previous_justified_checkpoint state.current_justified_checkpoint
        state.finalized_checkpoint (compute_epoch_at_slot cfg state.slot) := by
  unfold weigh_justification_and_finalization at h
  rw [except_bind_eq_ok] at h
  obtain ⟨_, hg, h⟩ := h
  have hlen : state.justification_bits.length = 4 := by
    have := guard_eq_ok.mp hg
    simpa using this
  obtain ⟨b0, b1, b2, b3, hb⟩ :
      ∃ b0 b1 b2 b3, state.justification_bits = [b0, b1, b2, b3] := by
    match hbits : state.justification_bits, hlen with
    | [b0, b1, b2, b3], _ => exact ⟨b0, b1, b2, b3, rfl⟩
  refine ⟨b0, b1, b2, b3, hb, ?_⟩
  dsimp only at h
  simp only [pure_bind] at h
  rw [hb] at h
  by_cases c1 : previous * 3 ≥ total * 2
  · rw [if_pos c1] at h
    rw [except_bind_eq_ok] at h
    obtain ⟨root1, hr1, h⟩ := h
    by_cases c2 : current * 3 ≥ total * 2
    · rw [if_pos c2] at h
      rw [except_bind_eq_ok] at h
      obtain ⟨root2, hr2, h⟩ := h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨by simp [c1, c2], ?_⟩
        simp only [finalizedOf, *, ↓reduceIte, Bool.false_eq_true]
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨by simp [c1, c2], ?_⟩
        simp only [finalizedOf, *, ↓reduceIte, Bool.false_eq_true]
  · rw [if_neg c1] at h
    by_cases c2 : current * 3 ≥ total * 2
    · rw [if_pos c2] at h
      rw [except_bind_eq_ok] at h
      obtain ⟨root2, hr2, h⟩ := h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨by simp [c1, c2], ?_⟩
        simp only [finalizedOf, *, ↓reduceIte, Bool.false_eq_true]
    · rw [if_neg c2] at h
      repeat' split at h
      all_goals
        simp only [except_pure_eq_ok] at h
        subst h
        refine ⟨by simp [c1, c2], ?_⟩
        simp only [finalizedOf, *, ↓reduceIte, Bool.false_eq_true]

omit [DecidableEq Root] in
/-- The four Python rules: the finalized checkpoint is unchanged, or the last
rule whose bits and epoch test pass sets it. -/
theorem finalizedOf_cases (x0 x1 x2 x3 : Bool) (p c f : Checkpoint Root) (e : Epoch) :
    finalizedOf [x0, x1, x2, x3] p c f e = f ∨
    (x1 = true ∧ x2 = true ∧ x3 = true ∧ p.epoch + 3 = e ∧
      finalizedOf [x0, x1, x2, x3] p c f e = p) ∨
    (x1 = true ∧ x2 = true ∧ p.epoch + 2 = e ∧
      finalizedOf [x0, x1, x2, x3] p c f e = p) ∨
    (x0 = true ∧ x1 = true ∧ x2 = true ∧ c.epoch + 2 = e ∧
      finalizedOf [x0, x1, x2, x3] p c f e = c) ∨
    (x0 = true ∧ x1 = true ∧ c.epoch + 1 = e ∧
      finalizedOf [x0, x1, x2, x3] p c f e = c) := by
  unfold finalizedOf
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  split_ifs <;> tauto

omit [DecidableEq Root] in
/-- One PJF pass after the epoch 0/1 return: the two participation tests,
the shifted bits, the new previous justified checkpoint, and the four rules. -/
theorem process_justification_and_finalization_bits {cfg : Config} {preset : FFGPreset}
    {state next : FFGBeaconState Root}
    (h : process_justification_and_finalization cfg preset state = .ok next)
    (hE : 2 ≤ compute_epoch_at_slot cfg state.slot) :
    ∃ b0 b1 b2 b3 previous current,
      state.justification_bits = [b0, b1, b2, b3] ∧
      get_unslashed_participating_indices cfg state 1
        (compute_epoch_at_slot cfg state.slot - 1) = .ok previous ∧
      get_unslashed_participating_indices cfg state 1
        (compute_epoch_at_slot cfg state.slot) = .ok current ∧
      next.justification_bits =
        [decide (ConcreteFFG.get_total_active_balance cfg state * 2 ≤
            ConcreteFFG.get_total_balance cfg state current * 3),
          decide (ConcreteFFG.get_total_active_balance cfg state * 2 ≤
            ConcreteFFG.get_total_balance cfg state previous * 3) || b0, b1, b2] ∧
      next.previous_justified_checkpoint = state.current_justified_checkpoint ∧
      next.finalized_checkpoint = finalizedOf next.justification_bits
        state.previous_justified_checkpoint state.current_justified_checkpoint
        state.finalized_checkpoint (compute_epoch_at_slot cfg state.slot) := by
  rcases process_justification_and_finalization_eq_ok h with ⟨hE', -⟩ |
    ⟨-, previous, current, hp, hc, hw⟩
  · exact absurd hE (by beacon_omega)
  obtain ⟨b0, b1, b2, b3, hb, hnb, hnf⟩ := weigh_justification_and_finalization_bits hw
  obtain ⟨_, _, _, rfl, -, -⟩ := weigh_justification_and_finalization_eq_ok hw
  exact ⟨b0, b1, b2, b3, previous, current, hb, hp, hc, hnb, rfl, hnf⟩

/-! ### Links of one pass -/

/-- A passing PJF two-thirds test on a state `t` with the participation,
registry and slot of an invariant state gives a supermajority link from the
source of the tested epoch to the chain checkpoint of that epoch. -/
theorem supermajorityLink_of_participation_test {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state t : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hE2 : 2 ≤ compute_epoch_at_slot S.cfg state.slot)
    (hslot : t.slot = state.slot) (hval : t.validators = state.validators)
    (hcur : t.current_epoch_participation = state.current_epoch_participation)
    (hprev : t.previous_epoch_participation = state.previous_epoch_participation)
    {epoch : Epoch} {set : Finset ValidatorIndex}
    (hepoch : epoch = compute_epoch_at_slot S.cfg state.slot ∨
      epoch + 1 = compute_epoch_at_slot S.cfg state.slot)
    (hset : get_unslashed_participating_indices S.cfg t 1 epoch = .ok set)
    (hth : ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
      ConcreteFFG.get_total_balance S.cfg t set * 3) :
    Nonempty (SupermajorityLink S votes
      (if epoch = compute_epoch_at_slot S.cfg state.slot then
        state.current_justified_checkpoint else state.previous_justified_checkpoint)
      (chainCheckpoint S blocks epoch)) := by
  set E := compute_epoch_at_slot S.cfg state.slot with hEdef
  have hscope : t.validators = S.scope.validators := hval.trans hinv.validators_eq
  have hmem : ∀ i, i ∈ set → i < S.scope.validators.length ∧
      is_active_validator (S.scope.validators.getD i default) epoch = true ∧
      has_flag ((if epoch = E then state.current_epoch_participation
        else state.previous_epoch_participation).getD i 0) 1 = true ∧
      (S.scope.validators.getD i default).slashed = false := by
    intro i hi
    have := (get_unslashed_participating_indices_mem hset i).mp hi
    rw [hslot, hcur, hprev, hscope] at this
    exact this
  refine ⟨
    { signers := set
      source_before_target := ?_
      signer_vote := ?_
      signer_active := fun i hi => ⟨(hmem i hi).1, (hmem i hi).2.1⟩
      signer_unslashed := fun i hi => (hmem i hi).2.2.2
      supermajority := ?_ }⟩
  · have h1 := hinv.current_epoch_le
    have h2 := hinv.previous_epoch_le
    change _ < epoch
    by_cases h : epoch = E
    · rw [if_pos h]
      beacon_omega
    · rw [if_neg h]
      rcases hepoch with h' | h'
      · exact absurd h' h
      · beacon_omega
  · intro i hi
    have hflag := (hmem i hi).2.2.1
    by_cases h : epoch = E
    · rw [if_pos h] at hflag
      obtain ⟨r, hr, hri, hre⟩ := (hinv.current_flags i).mp hflag
      have hre' : r.vote.data.target.epoch = epoch := by rw [hre]; exact h.symm
      refine ⟨r, hr, hri, ?_, checkpoint_eq_of hre' ?_⟩
      · rw [if_pos h]; exact hinv.current_sources r hr hre
      · exact (hinv.target_on_chain r hr).2.trans (by rw [hre']; rfl)
    · rw [if_neg h] at hflag
      obtain ⟨r, hr, hri, hre⟩ := (hinv.previous_flags i).mp hflag
      have hre' : r.vote.data.target.epoch = epoch := by
        rcases hepoch with h' | h'
        · exact absurd h' h
        · beacon_omega
      refine ⟨r, hr, hri, ?_, checkpoint_eq_of hre' ?_⟩
      · rw [if_neg h]; exact hinv.previous_sources r hr hre
      · exact (hinv.target_on_chain r hr).2.trans (by rw [hre']; rfl)
  · rw [total_active_balance_eq hS hscope (by rw [hslot]; exact hH),
      total_balance_eq hscope set] at hth
    exact supermajority_of_threshold S.cfg.effective_balance_increment_pos hS.balance_floor hth

/-- A passing current-epoch test links the current justified checkpoint to the
chain checkpoint of the current epoch. -/
theorem current_link_of_test {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state t : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hE2 : 2 ≤ compute_epoch_at_slot S.cfg state.slot)
    (hslot : t.slot = state.slot) (hval : t.validators = state.validators)
    (hcur : t.current_epoch_participation = state.current_epoch_participation)
    (hprev : t.previous_epoch_participation = state.previous_epoch_participation)
    {set : Finset ValidatorIndex}
    (hset : get_unslashed_participating_indices S.cfg t 1
      (compute_epoch_at_slot S.cfg state.slot) = .ok set)
    (hth : ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
      ConcreteFFG.get_total_balance S.cfg t set * 3) :
    Nonempty (SupermajorityLink S votes state.current_justified_checkpoint
      (chainCheckpoint S blocks (compute_epoch_at_slot S.cfg state.slot))) := by
  have := supermajorityLink_of_participation_test hS hinv hH hE2 hslot hval hcur hprev
    (Or.inl rfl) hset hth
  rwa [if_pos rfl] at this

/-- A passing previous-epoch test links the previous justified checkpoint to
the chain checkpoint of the previous epoch. -/
theorem previous_link_of_test {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state t : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hE2 : 2 ≤ compute_epoch_at_slot S.cfg state.slot)
    (hslot : t.slot = state.slot) (hval : t.validators = state.validators)
    (hcur : t.current_epoch_participation = state.current_epoch_participation)
    (hprev : t.previous_epoch_participation = state.previous_epoch_participation)
    {set : Finset ValidatorIndex}
    (hset : get_unslashed_participating_indices S.cfg t 1
      (compute_epoch_at_slot S.cfg state.slot - 1) = .ok set)
    (hth : ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
      ConcreteFFG.get_total_balance S.cfg t set * 3) :
    Nonempty (SupermajorityLink S votes state.previous_justified_checkpoint
      (chainCheckpoint S blocks (compute_epoch_at_slot S.cfg state.slot - 1))) := by
  have := supermajorityLink_of_participation_test hS hinv hH hE2 hslot hval hcur hprev
    (Or.inr (by beacon_omega)) hset hth
  rwa [if_neg (by beacon_omega)] at this

/-! ### The four finalization rules -/

/-- Python rule 1 (`bits[1:4]`, `old_previous_justified.epoch + 3 ==
current_epoch`): a link from the finalized checkpoint over one justified
epoch. -/
theorem finalizationLink_rule1 {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {f : Checkpoint Root} {E : Epoch}
    (hf : Justified S votes f) (hfe : f.epoch + 3 = E)
    (hlink : Nonempty (SupermajorityLink S votes f (chainCheckpoint S blocks (E - 1))))
    (hmid : Justified S votes (chainCheckpoint S blocks (E - 2))) :
    FinalizationLink S blocks votes f (chainCheckpoint S blocks (E - 1)) where
  justified := hf
  link := hlink
  target_on_chain := rfl
  target_epoch := Or.inr (by change E - 1 = f.epoch + 2; beacon_omega)
  middle_justified := fun _ => by
    have : f.epoch + 1 = E - 2 := by beacon_omega
    rw [this]
    exact hmid

/-- Python rule 2 (`bits[1:3]`, `old_previous_justified.epoch + 2 ==
current_epoch`): a link from the finalized checkpoint to the next epoch. -/
theorem finalizationLink_rule2 {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {f : Checkpoint Root} {E : Epoch}
    (hf : Justified S votes f) (hfe : f.epoch + 2 = E)
    (hlink : Nonempty (SupermajorityLink S votes f (chainCheckpoint S blocks (E - 1)))) :
    FinalizationLink S blocks votes f (chainCheckpoint S blocks (E - 1)) where
  justified := hf
  link := hlink
  target_on_chain := rfl
  target_epoch := Or.inl (by change E - 1 = f.epoch + 1; beacon_omega)
  middle_justified := fun h => by
    change E - 1 = f.epoch + 2 at h
    exact absurd h (by beacon_omega)

/-- Python rule 3 (`bits[0:3]`, `old_current_justified.epoch + 2 ==
current_epoch`): a link from the finalized checkpoint over one justified
epoch. -/
theorem finalizationLink_rule3 {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {f : Checkpoint Root} {E : Epoch}
    (hf : Justified S votes f) (hfe : f.epoch + 2 = E)
    (hlink : Nonempty (SupermajorityLink S votes f (chainCheckpoint S blocks E)))
    (hmid : Justified S votes (chainCheckpoint S blocks (E - 1))) :
    FinalizationLink S blocks votes f (chainCheckpoint S blocks E) where
  justified := hf
  link := hlink
  target_on_chain := rfl
  target_epoch := Or.inr (by change E = f.epoch + 2; beacon_omega)
  middle_justified := fun _ => by
    have : f.epoch + 1 = E - 1 := by beacon_omega
    rw [this]
    exact hmid

/-- Python rule 4 (`bits[0:2]`, `old_current_justified.epoch + 1 ==
current_epoch`): a link from the finalized checkpoint to the next epoch. -/
theorem finalizationLink_rule4 {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {f : Checkpoint Root} {E : Epoch}
    (hf : Justified S votes f) (hfe : f.epoch + 1 = E)
    (hlink : Nonempty (SupermajorityLink S votes f (chainCheckpoint S blocks E))) :
    FinalizationLink S blocks votes f (chainCheckpoint S blocks E) where
  justified := hf
  link := hlink
  target_on_chain := rfl
  target_epoch := Or.inl (by change E = f.epoch + 1; beacon_omega)
  middle_justified := fun h => by
    change E = f.epoch + 2 at h
    exact absurd h (by beacon_omega)

/-! ### One PJF pass -/

/-- One PJF pass on a state `t` with the fields of an invariant state moves
the finality invariant to the next epoch. The pass result is the eager copy,
or the state before its slot increment at an epoch boundary. -/
theorem finalityInvariant_pass {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state t next : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hfin : FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hpjf : process_justification_and_finalization S.cfg S.preset t = .ok next)
    (hslot : t.slot = state.slot) (hval : t.validators = state.validators)
    (hcur : t.current_epoch_participation = state.current_epoch_participation)
    (hprev : t.previous_epoch_participation = state.previous_epoch_participation)
    (hbits : t.justification_bits = state.justification_bits)
    (hpj : t.previous_justified_checkpoint = state.previous_justified_checkpoint)
    (hcj : t.current_justified_checkpoint = state.current_justified_checkpoint)
    (hfc : t.finalized_checkpoint = state.finalized_checkpoint) :
    FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot + 1) next := by
  set E := compute_epoch_at_slot S.cfg state.slot with hEdef
  have hEt : compute_epoch_at_slot S.cfg t.slot = E := by rw [hslot]
  by_cases hE : 2 ≤ E
  · obtain ⟨b0, b1, b2, b3, prev, cur, hb, hprevset, hcurset, hnb, hnpj, hnf⟩ :=
      process_justification_and_finalization_bits hpjf (by rw [hEt]; exact hE)
    rw [hEt] at hprevset hcurset hnf
    rw [hbits] at hb
    have hP : (decide (ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
          ConcreteFFG.get_total_balance S.cfg t prev * 3) || b0) = true →
        Nonempty (SupermajorityLink S votes state.previous_justified_checkpoint
          (chainCheckpoint S blocks (E - 1))) := by
      intro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact previous_link_of_test hS hinv hH hE hslot hval hcur hprev hprevset
          (of_decide_eq_true h)
      · exact hfin.bit_link (by rw [hb]; exact h)
    have hPJ : (decide (ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
          ConcreteFFG.get_total_balance S.cfg t prev * 3) || b0) = true →
        Justified S votes (chainCheckpoint S blocks (E - 1)) := fun h =>
      let ⟨L⟩ := hP h
      .link hinv.previous_justified L
    have hQ : decide (ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
          ConcreteFFG.get_total_balance S.cfg t cur * 3) = true →
        Nonempty (SupermajorityLink S votes state.current_justified_checkpoint
          (chainCheckpoint S blocks E)) := fun h =>
      current_link_of_test hS hinv hH hE hslot hval hcur hprev hcurset (of_decide_eq_true h)
    have hQJ : decide (ConcreteFFG.get_total_active_balance S.cfg t * 2 ≤
          ConcreteFFG.get_total_balance S.cfg t cur * 3) = true →
        Justified S votes (chainCheckpoint S blocks E) := fun h =>
      let ⟨L⟩ := hQ h
      .link hinv.current_justified L
    have hcjle : state.current_justified_checkpoint.epoch ≤
        next.current_justified_checkpoint.epoch := by
      obtain ⟨bits', pj, j, f, rfl, hout⟩ := process_justification_and_finalization_outcome hpjf
      have := hinv.current_epoch_le
      rcases hout with ⟨hE1, -⟩ | ⟨-, -, hj | ⟨_, -, -, hje, -⟩ | ⟨_, -, -, hje, -⟩, -⟩
      · rw [hEt] at hE1
        exact absurd hE (by beacon_omega)
      · change _ ≤ j.epoch
        rw [hj, hcj]
      · change _ ≤ j.epoch
        rw [hje, hEt]
        beacon_omega
      · change _ ≤ j.epoch
        rw [hje, hEt]
        beacon_omega
    refine
      { bits_length := by rw [hnb]; rfl
        bit_epoch := ?_
        bit_link := ?_
        bit_justified := ?_
        finalized_certified := ?_
        finalized_le_previous := ?_
        previous_le_current := by rw [hnpj, hcj]; exact hcjle }
    · intro i hi
      rw [hnb] at hi
      match i, hi with
      | 0, _ => beacon_omega
      | 1, _ => beacon_omega
      | 2, hi =>
        have := hfin.bit_epoch 1 (by rw [hb]; exact hi)
        beacon_omega
      | 3, hi =>
        have := hfin.bit_epoch 2 (by rw [hb]; exact hi)
        beacon_omega
      | i + 4, hi => simp at hi
    · intro h0
      rw [hnb] at h0
      rw [hnpj, hcj, Nat.add_sub_cancel]
      exact hQ h0
    · intro i hi
      rw [hnb] at hi
      match i, hi with
      | 0, hi =>
        rw [show E + 1 - 1 - 0 = E by beacon_omega]
        exact hQJ hi
      | 1, hi =>
        rw [show E + 1 - 1 - 1 = E - 1 by beacon_omega]
        exact hPJ hi
      | 2, hi =>
        rw [show E + 1 - 1 - 2 = E - 1 - 1 by beacon_omega]
        exact hfin.bit_justified 1 (by rw [hb]; exact hi)
      | 3, hi =>
        rw [show E + 1 - 1 - 3 = E - 1 - 2 by beacon_omega]
        exact hfin.bit_justified 2 (by rw [hb]; exact hi)
      | i + 4, hi => simp at hi
    · rw [hnf, hnb, hpj, hcj, hfc]
      rcases finalizedOf_cases _ _ _ _ state.previous_justified_checkpoint
          state.current_justified_checkpoint state.finalized_checkpoint E with
        h | ⟨h1, h2, -, he, h⟩ | ⟨h1, -, he, h⟩ | ⟨h0, h1, -, he, h⟩ | ⟨h0, -, he, h⟩
      · rw [h]
        rcases hfin.finalized_certified with h' | ⟨target, hl, hlt⟩
        · exact Or.inl h'
        · exact Or.inr ⟨target, hl, by beacon_omega⟩
      · rw [h]
        refine Or.inr ⟨_, finalizationLink_rule1 hinv.previous_justified he (hP h1) ?_,
          by change E - 1 < E + 1; beacon_omega⟩
        have := hfin.bit_justified 1 (by rw [hb]; exact h2)
        rwa [show E - 1 - 1 = E - 2 by beacon_omega] at this
      · rw [h]
        exact Or.inr ⟨_, finalizationLink_rule2 hinv.previous_justified he (hP h1),
          by change E - 1 < E + 1; beacon_omega⟩
      · rw [h]
        exact Or.inr ⟨_, finalizationLink_rule3 hinv.current_justified he (hQ h0) (hPJ h1),
          by change E < E + 1; beacon_omega⟩
      · rw [h]
        exact Or.inr ⟨_, finalizationLink_rule4 hinv.current_justified he (hQ h0),
          by change E < E + 1; beacon_omega⟩
    · rw [hnpj, hnf, hnb, hpj, hcj, hfc]
      have h1 := hfin.finalized_le_previous
      have h2 := hfin.previous_le_current
      rcases finalizedOf_cases _ _ _ _ state.previous_justified_checkpoint
          state.current_justified_checkpoint state.finalized_checkpoint E with
        h | ⟨-, -, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] <;>
        beacon_omega
  · rcases process_justification_and_finalization_eq_ok hpjf with ⟨-, rfl⟩ | ⟨hE', -⟩
    · have hzero : ∀ i, state.justification_bits.getD i false = true → False := by
        intro i hi
        have := hfin.bit_epoch i hi
        beacon_omega
      refine
        { bits_length := hbits ▸ hfin.bits_length
          bit_epoch := fun i hi => (hzero i (hbits ▸ hi)).elim
          bit_link := fun hi => (hzero 0 (hbits ▸ hi)).elim
          bit_justified := fun i hi => (hzero i (hbits ▸ hi)).elim
          finalized_certified := ?_
          finalized_le_previous := by rw [hfc, hpj]; exact hfin.finalized_le_previous
          previous_le_current := by rw [hpj, hcj]; exact hfin.previous_le_current }
      rw [hfc]
      rcases hfin.finalized_certified with h' | ⟨target, hl, hlt⟩
      · exact Or.inl h'
      · exact Or.inr ⟨target, hl, by beacon_omega⟩
    · rw [hEt] at hE'
      exact absurd hE' hE

/-! ### Frames and transport -/

theorem FinalityInvariant.congr {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {state state' : FFGBeaconState Root}
    (h : FinalityInvariant S blocks votes E state)
    (hbits : state'.justification_bits = state.justification_bits)
    (hpj : state'.previous_justified_checkpoint = state.previous_justified_checkpoint)
    (hcj : state'.current_justified_checkpoint = state.current_justified_checkpoint)
    (hfc : state'.finalized_checkpoint = state.finalized_checkpoint) :
    FinalityInvariant S blocks votes E state' where
  bits_length := by rw [hbits]; exact h.bits_length
  bit_epoch := fun i hi => h.bit_epoch i (by rw [← hbits]; exact hi)
  bit_link := fun hi => by rw [hpj]; exact h.bit_link (by rw [← hbits]; exact hi)
  bit_justified := fun i hi => h.bit_justified i (by rw [← hbits]; exact hi)
  finalized_certified := by rw [hfc]; exact h.finalized_certified
  finalized_le_previous := by rw [hfc, hpj]; exact h.finalized_le_previous
  previous_le_current := by rw [hpj, hcj]; exact h.previous_le_current

/-- A finalizing link stays valid when votes are recorded and the chain
checkpoints up to its target do not change. -/
theorem FinalizationLink.transport {S : FFGSetup Root}
    {blocks blocks' : List (FFGWireBlock Root)} {votes votes' : List (IncludedVote Root)}
    {f target : Checkpoint Root} (hv : ∀ r, r ∈ votes → r ∈ votes')
    (hc : ∀ k, k ≤ target.epoch → chainCheckpoint S blocks k = chainCheckpoint S blocks' k)
    (h : FinalizationLink S blocks votes f target) :
    FinalizationLink S blocks' votes' f target where
  justified := h.justified.mono hv
  link := let ⟨L⟩ := h.link; ⟨L.mono hv⟩
  target_on_chain := h.target_on_chain.trans (hc _ (Nat.le_refl _))
  target_epoch := h.target_epoch
  middle_justified := fun he => by
    rw [← hc _ (by beacon_omega)]
    exact (h.middle_justified he).mono hv

theorem FinalityInvariant.transport {S : FFGSetup Root}
    {blocks blocks' : List (FFGWireBlock Root)} {votes votes' : List (IncludedVote Root)}
    {E : Epoch} {state : FFGBeaconState Root} (hv : ∀ r, r ∈ votes → r ∈ votes')
    (hc : ∀ k, k + 1 ≤ E → chainCheckpoint S blocks k = chainCheckpoint S blocks' k)
    (h : FinalityInvariant S blocks votes E state) :
    FinalityInvariant S blocks' votes' E state where
  bits_length := h.bits_length
  bit_epoch := h.bit_epoch
  bit_link := fun hi => by
    have := h.bit_epoch 0 hi
    obtain ⟨L⟩ := h.bit_link hi
    rw [← hc _ (by beacon_omega)]
    exact ⟨L.mono hv⟩
  bit_justified := fun i hi => by
    have := h.bit_epoch i hi
    rw [← hc _ (by beacon_omega)]
    exact (h.bit_justified i hi).mono hv
  finalized_certified := by
    rcases h.finalized_certified with h' | ⟨target, hl, hlt⟩
    · exact Or.inl h'
    · exact Or.inr ⟨target, hl.transport hv (fun k hk => hc k (by beacon_omega)), hlt⟩
  finalized_le_previous := h.finalized_le_previous
  previous_le_current := h.previous_le_current

omit [DecidableEq Root] in
theorem chainCheckpoint_append {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {block : FFGWireBlock Root} {k : Epoch}
    (h : compute_start_slot_at_epoch S.cfg k < block.slot) :
    chainCheckpoint S (blocks ++ [block]) k = chainCheckpoint S blocks k := by
  unfold chainCheckpoint
  rw [chainRootAt_append_of_lt h]

theorem start_lt_of_lt_epoch {cfg : Config} {k : Epoch} {x : Slot}
    (h : k + 1 ≤ compute_epoch_at_slot cfg x) : compute_start_slot_at_epoch cfg k < x := by
  unfold compute_start_slot_at_epoch
  unfold compute_epoch_at_slot at h
  have hspe := cfg.slots_per_epoch_pos
  have h1 : (k + 1) * cfg.slots_per_epoch ≤ x / cfg.slots_per_epoch * cfg.slots_per_epoch :=
    Nat.mul_le_mul_right _ h
  have h2 := Nat.div_mul_le_self x cfg.slots_per_epoch
  have h3 : (k + 1) * cfg.slots_per_epoch = k * cfg.slots_per_epoch + cfg.slots_per_epoch :=
    Nat.succ_mul k cfg.slots_per_epoch
  beacon_omega

/-! ### Slot steps -/

theorem finalityInvariant_slotStep {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} (hinv : ProvenanceInvariant S blocks votes state)
    (hfin : FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (h : slotStep S.cfg S.preset state = .ok next) :
    FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg next.slot) next := by
  obtain ⟨s1, hs1, hcase⟩ := slotStep_eq_ok h
  obtain ⟨-, -, hs1def⟩ := process_slot_eq_ok.mp hs1
  subst hs1def
  rcases hcase with ⟨hb, rfl⟩ | ⟨hb, mid, hmid, rfl⟩
  · change FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg (state.slot + 1)) _
    rw [epoch_succ_of_not_boundary hb]
    exact hfin.congr rfl rfl rfl rfl
  · change FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg (state.slot + 1)) _
    rw [epoch_succ_of_boundary hb]
    have := finalityInvariant_pass hS hinv hfin hH hmid rfl rfl rfl rfl rfl rfl rfl rfl
    exact this.congr rfl rfl rfl rfl

theorem finalityInvariant_slotFold {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)} :
    ∀ (steps : List ℕ) (state next : FFGBeaconState Root),
      ProvenanceInvariant S blocks votes state →
      FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state →
      steps.foldlM (fun s _ => slotStep S.cfg S.preset s) state = .ok next →
      compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch →
      FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg next.slot) next := by
  intro steps
  induction steps with
  | nil =>
    intro state next _ hfin h _
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact hfin
  | cons step steps ih =>
    intro state next hinv hfin h hH
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    have hle : state.slot ≤ next.slot := by
      rw [slotFold_slot _ _ _ hrest, slotStep_slot hmid]
      beacon_omega
    have hHs : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch :=
      Nat.le_trans (compute_epoch_at_slot_mono hle) hH
    exact ih mid next (provenanceInvariant_slotStep hS hinv hHs hmid).1
      (finalityInvariant_slotStep hS hinv hfin hHs hmid) hrest hH

theorem finalityInvariant_process_slots {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} {target : Slot}
    (hinv : ProvenanceInvariant S blocks votes state)
    (hfin : FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state)
    (h : process_slots S.cfg S.preset state target = .ok next)
    (hH : compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch) :
    FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg next.slot) next := by
  obtain ⟨-, -, hfold⟩ := process_slots_eq_ok.mp h
  exact finalityInvariant_slotFold hS _ _ _ hinv hfin hfold hH

/-! ### Block steps -/

theorem attestationFold_checkpoints {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {parentSlot : Slot} :
    ∀ (attestations : List (FFGWireAttestation Root)) (state next : FFGBeaconState Root),
      attestations.foldlM (fun s vote =>
        process_attestation cfg preset schedule s vote parentSlot) state = .ok next →
      next.justification_bits = state.justification_bits ∧
      next.previous_justified_checkpoint = state.previous_justified_checkpoint ∧
      next.current_justified_checkpoint = state.current_justified_checkpoint ∧
      next.finalized_checkpoint = state.finalized_checkpoint := by
  intro attestations
  induction attestations with
  | nil =>
    intro state next h
    simp only [List.foldlM_nil] at h
    cases (except_pure_eq_ok.mp h)
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons vote attestations ih =>
    intro state next h
    simp only [List.foldlM_cons, except_bind_eq_ok] at h
    obtain ⟨mid, hmid, hrest⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := ih mid next hrest
    obtain ⟨_, _, _, _, _, rfl, _, _⟩ := process_attestation_flags hmid
    exact ⟨h1, h2, h3, h4⟩

theorem process_block_checkpoints {cfg : Config} {preset : FFGPreset}
    {schedule : FixedCommitteeSchedule} {state next : FFGBeaconState Root}
    {block : FFGWireBlock Root} (h : process_block cfg preset schedule state block = .ok next) :
    next.justification_bits = state.justification_bits ∧
      next.previous_justified_checkpoint = state.previous_justified_checkpoint ∧
      next.current_justified_checkpoint = state.current_justified_checkpoint ∧
      next.finalized_checkpoint = state.finalized_checkpoint := by
  obtain ⟨paid, headed, hpaid, hheaded, hfold⟩ := process_block_eq_ok h
  obtain ⟨_, _, rfl⟩ := process_parent_execution_payload_eq_ok hpaid
  obtain ⟨-, -, -, rfl⟩ := process_block_header_eq_ok hheaded
  have := attestationFold_checkpoints _ _ _ hfold
  exact this

theorem finalityInvariant_state_transition {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state next : FFGBeaconState Root} {block : FFGWireBlock Root}
    (hinv : ProvenanceInvariant S blocks votes state)
    (hfin : FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state)
    (h : state_transition S.cfg S.preset S.schedule S.oracle state block = .ok next)
    (hH : compute_epoch_at_slot S.cfg next.slot ≤ S.scope.last_epoch) :
    FinalityInvariant S (blocks ++ [block]) (votes ++ blockVotes S state block)
      (compute_epoch_at_slot S.cfg next.slot) next := by
  obtain ⟨atSlot, hslots, hblock, -⟩ := state_transition_eq_ok h
  have hnextslot : next.slot = atSlot.slot := process_block_slot hblock
  obtain ⟨hatslot, -⟩ := process_slots_slot hslots
  have hfin1 := finalityInvariant_process_slots hS hinv hfin hslots
    (by rw [← hnextslot]; exact hH)
  obtain ⟨hb, hpj, hcj, hf⟩ := process_block_checkpoints hblock
  rw [hnextslot]
  refine (hfin1.congr hb hpj hcj hf).transport (fun r hr => List.mem_append_left _ hr) ?_
  intro k hk
  have := start_lt_of_lt_epoch hk
  rw [hatslot] at this
  exact (chainCheckpoint_append this).symm

/-! ### Reachable states -/

theorem finalityInvariant_genesis (S : FFGSetup Root) :
    FinalityInvariant S [] [] (compute_epoch_at_slot S.cfg S.genesis.slot) S.genesis := by
  have hz : ∀ i, (List.replicate 4 false).getD i false = true → False := by
    intro i hi
    match i, hi with
    | 0, hi => exact Bool.false_ne_true hi
    | 1, hi => exact Bool.false_ne_true hi
    | 2, hi => exact Bool.false_ne_true hi
    | 3, hi => exact Bool.false_ne_true hi
    | _ + 4, hi => simp at hi
  exact
    { bits_length := rfl
      bit_epoch := fun i hi => (hz i hi).elim
      bit_link := fun hi => (hz 0 hi).elim
      bit_justified := fun i hi => (hz i hi).elim
      finalized_certified := Or.inl rfl
      finalized_le_previous := Nat.le_refl _
      previous_le_current := Nat.le_refl _ }

/-- **Finality invariant of reachable states.** -/
theorem finalityInvariant_of_reachable {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    FinalityInvariant S blocks votes (compute_epoch_at_slot S.cfg state.slot) state := by
  induction h with
  | genesis => exact finalityInvariant_genesis S
  | slots hreach hslots ih =>
    obtain ⟨hnext, hlt⟩ := process_slots_slot hslots
    have hHs := Nat.le_trans (compute_epoch_at_slot_mono (Nat.le_of_lt (hnext ▸ hlt))) hH
    exact finalityInvariant_process_slots hS (provenanceInvariant_of_reachable hS hreach hHs)
      (ih hHs) hslots hH
  | block blk hreach htrans ih =>
    obtain ⟨hns, hlt⟩ := state_transition_slot htrans
    have hHs := Nat.le_trans (compute_epoch_at_slot_mono (Nat.le_of_lt (hns ▸ hlt))) hH
    exact finalityInvariant_state_transition hS (provenanceInvariant_of_reachable hS hreach hHs)
      (ih hHs) htrans hH

/-- **Finalization soundness.** The finalized checkpoint of an in-horizon
reachable state is the genesis stub, or it has a finalizing link: it is
justified, a supermajority link goes from it to the chain checkpoint one or
two epochs later, and in the two-epoch case the chain checkpoint between them
is justified. The link target is earlier than the current epoch. -/
theorem finalization_soundness {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    state.finalized_checkpoint = S.stub ∨
      ∃ target, FinalizationLink S blocks votes state.finalized_checkpoint target ∧
        target.epoch < compute_epoch_at_slot S.cfg state.slot :=
  (finalityInvariant_of_reachable hS h hH).finalized_certified

theorem finalized_certified {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    state.finalized_checkpoint = S.stub ∨
      FinalizationCertified S blocks votes state.finalized_checkpoint := by
  rcases finalization_soundness hS h hH with h' | ⟨target, hl, -⟩
  · exact Or.inl h'
  · exact Or.inr ⟨target, hl⟩

/-- **Eager finalization soundness.** The eager PJF copy of an in-horizon
reachable state has a stub or finalizing-link finalized checkpoint. The link
target is at most the current epoch. -/
theorem eager_finalization_soundness {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state eager : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hpjf : process_justification_and_finalization S.cfg S.preset state = .ok eager) :
    eager.finalized_checkpoint = S.stub ∨
      ∃ target, FinalizationLink S blocks votes eager.finalized_checkpoint target ∧
        target.epoch ≤ compute_epoch_at_slot S.cfg state.slot := by
  have := (finalityInvariant_pass hS (provenanceInvariant_of_reachable hS h hH)
    (finalityInvariant_of_reachable hS h hH) hH hpjf rfl rfl rfl rfl rfl rfl rfl
    rfl).finalized_certified
  rcases this with h' | ⟨target, hl, hlt⟩
  · exact Or.inl h'
  · exact Or.inr ⟨target, hl, by beacon_omega⟩

/-- The finalized, previous justified and current justified checkpoints of an
in-horizon reachable state have ordered epochs. -/
theorem checkpoint_epochs_ordered {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    state.finalized_checkpoint.epoch ≤ state.previous_justified_checkpoint.epoch ∧
      state.previous_justified_checkpoint.epoch ≤ state.current_justified_checkpoint.epoch :=
  ⟨(finalityInvariant_of_reachable hS h hH).finalized_le_previous,
    (finalityInvariant_of_reachable hS h hH).previous_le_current⟩

/-- The same order for the eager PJF copy. -/
theorem eager_checkpoint_epochs_ordered {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state eager : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hpjf : process_justification_and_finalization S.cfg S.preset state = .ok eager) :
    eager.finalized_checkpoint.epoch ≤ eager.previous_justified_checkpoint.epoch ∧
      eager.previous_justified_checkpoint.epoch ≤ eager.current_justified_checkpoint.epoch := by
  have := finalityInvariant_pass hS (provenanceInvariant_of_reachable hS h hH)
    (finalityInvariant_of_reachable hS h hH) hH hpjf rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨this.finalized_le_previous, this.previous_le_current⟩

/-- **Finalization lag.** The finalized checkpoint of an in-horizon reachable
state is the stub, or its epoch is at least two epochs before the current
epoch. For the post-state of a block, the current epoch is the block epoch. -/
theorem finalized_lag {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    state.finalized_checkpoint = S.stub ∨
      state.finalized_checkpoint.epoch + 2 ≤ compute_epoch_at_slot S.cfg state.slot := by
  rcases finalization_soundness hS h hH with h' | ⟨target, hl, hlt⟩
  · exact Or.inl h'
  · obtain ⟨L⟩ := hl.link
    have := L.source_before_target
    exact Or.inr (by beacon_omega)

/-- The eager finalized checkpoint is the stub, or its epoch is before the
current epoch. -/
theorem eager_finalized_lag {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state eager : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    (hpjf : process_justification_and_finalization S.cfg S.preset state = .ok eager) :
    eager.finalized_checkpoint = S.stub ∨
      eager.finalized_checkpoint.epoch + 1 ≤ compute_epoch_at_slot S.cfg state.slot := by
  rcases eager_finalization_soundness hS h hH hpjf with h' | ⟨target, hl, hlt⟩
  · exact Or.inl h'
  · obtain ⟨L⟩ := hl.link
    have := L.source_before_target
    exact Or.inr (by beacon_omega)

end FastConfirmation.Spec.ConcreteFFG

end
