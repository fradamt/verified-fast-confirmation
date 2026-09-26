module
public import FastConfirmationProofs.FFG.Concrete.Accountability

@[expose] public section

/-! Proves the generalized exact finalized-prefix result for concrete FFG
runs. A finalized checkpoint of one reachable run is the checkpoint of its
epoch on the chain of a second reachable run whose justified checkpoint is not
earlier, unless validators with one third of the fixed total active balance
signed slashable included votes. The two runs share one setup; their block
roots commit to slot and parent. The finalizing link can span one or two
epochs (Gasper `k = 2`). -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [DecidableEq Root]

/-! ### Chain agreement under root commitment -/

omit [DecidableEq Root] in
theorem parentLinked_filter_le {y : Slot} :
    ∀ (genesisRoot : Root) (blocks : List (FFGWireBlock Root)),
      blocks.Pairwise (fun a b => a.slot < b.slot) → ParentLinked genesisRoot blocks →
      ParentLinked genesisRoot (blocks.filter fun b => decide (b.slot ≤ y))
  | _, [], _, _ => trivial
  | g, a :: rest, ho, hp => by
    rw [List.pairwise_cons] at ho
    simp only [ParentLinked] at hp
    rw [List.filter_cons]
    by_cases ha : a.slot ≤ y
    · rw [if_pos (decide_eq_true ha)]
      simp only [ParentLinked]
      exact ⟨hp.1, parentLinked_filter_le a.root rest ho.2 hp.2⟩
    · rw [if_neg (by simpa using ha), List.filter_eq_nil_iff.mpr]
      · trivial
      · intro b hb
        have := ho.1 b hb
        simp only [decide_eq_true_eq]
        beacon_omega

omit [DecidableEq Root] in
/-- Under root commitment, two parent-linked chains from the genesis block
with the same tip root have the same roots and slots. -/
theorem rootSlots_eq_of_tipRoot_eq {S : FFGSetup Root} {B : List (FFGWireBlock Root)}
    (hc : RootsCommit S B) :
    ∀ (b1 b2 : List (FFGWireBlock Root)), (∀ x ∈ b1, x ∈ B) → (∀ x ∈ b2, x ∈ B) →
      ParentLinked S.genesisRoot b1 → ParentLinked S.genesisRoot b2 →
      tipRoot S.genesisRoot b1 = tipRoot S.genesisRoot b2 →
      b1.map (fun b => (b.root, b.slot)) = b2.map (fun b => (b.root, b.slot)) := by
  intro b1
  induction b1 using List.reverseRecOn with
  | nil =>
    intro b2 _ h2 _ _ htip
    rcases List.eq_nil_or_concat' b2 with rfl | ⟨L, b, rfl⟩
    · rfl
    · rw [tipRoot_append] at htip
      exact absurd htip.symm
        (hc.not_genesis b (h2 b (List.mem_append_right _ (List.mem_singleton_self _))))
  | append_singleton l a ih =>
    intro b2 h1 h2 hp1 hp2 htip
    have ha := h1 a (List.mem_append_right _ (List.mem_singleton_self _))
    rcases List.eq_nil_or_concat' b2 with rfl | ⟨L, b, rfl⟩
    · rw [tipRoot_append] at htip
      exact absurd htip (hc.not_genesis a ha)
    · rw [tipRoot_append, tipRoot_append] at htip
      have hb := h2 b (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨hslot, hparent⟩ := hc.commit a ha b hb htip
      rw [parentLinked_append] at hp1 hp2
      have := ih L (fun x hx => h1 x (List.mem_append_left _ hx))
        (fun x hx => h2 x (List.mem_append_left _ hx)) hp1.1 hp2.1
        (by rw [← hp1.2, ← hp2.2, hparent])
      rw [List.map_append, List.map_append, this]
      simp [htip, hslot]

omit [DecidableEq Root] in
theorem chainRootAt_eq_of_rootSlots_eq {g : Root} {b1 b2 : List (FFGWireBlock Root)}
    (h : b1.map (fun b => (b.root, b.slot)) = b2.map (fun b => (b.root, b.slot)))
    (y : Slot) : chainRootAt g b1 y = chainRootAt g b2 y := by
  have key : ∀ b : List (FFGWireBlock Root), chainRootAt g b y =
      ((((b.map (fun b => (b.root, b.slot))).filter fun q => decide (q.2 ≤ y)).getLast?).map
        Prod.fst).getD g := by
    intro b
    unfold chainRootAt
    rw [List.filter_map, List.getLast?_map, Option.map_map]
    rfl
  rw [key b1, key b2, h]

omit [DecidableEq Root] in
theorem chainRootAt_filter_le {g : Root} {b : List (FFGWireBlock Root)} {x y : Slot}
    (hy : y ≤ x) :
    chainRootAt g (b.filter fun c => decide (c.slot ≤ x)) y = chainRootAt g b y := by
  have : (b.filter fun c => decide (c.slot ≤ x)).filter (fun c => decide (c.slot ≤ y)) =
      b.filter (fun c => decide (c.slot ≤ y)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    by_cases h : c.slot ≤ y
    · simp [h, Nat.le_trans h hy]
    · simp [h]
  unfold chainRootAt
  rw [this]

omit [DecidableEq Root] in
/-- **Chain agreement.** Under root commitment, two ordered parent-linked
chains from the genesis block that agree at a slot agree at every earlier
slot. -/
theorem chainRootAt_agree {S : FFGSetup Root} {b1 b2 : List (FFGWireBlock Root)}
    (hc : RootsCommit S (b1 ++ b2))
    (ho1 : b1.Pairwise fun a b => a.slot < b.slot) (ho2 : b2.Pairwise fun a b => a.slot < b.slot)
    (hp1 : ParentLinked S.genesisRoot b1) (hp2 : ParentLinked S.genesisRoot b2)
    {x : Slot} (hx : chainRootAt S.genesisRoot b1 x = chainRootAt S.genesisRoot b2 x)
    {y : Slot} (hy : y ≤ x) :
    chainRootAt S.genesisRoot b1 y = chainRootAt S.genesisRoot b2 y := by
  rw [← chainRootAt_filter_le (b := b1) (x := x) hy, ← chainRootAt_filter_le (b := b2) (x := x) hy]
  apply chainRootAt_eq_of_rootSlots_eq
  exact rootSlots_eq_of_tipRoot_eq hc _ _
    (fun c hc' => List.mem_append_left _ (List.mem_filter.mp hc').1)
    (fun c hc' => List.mem_append_right _ (List.mem_filter.mp hc').1)
    (parentLinked_filter_le _ _ ho1 hp1) (parentLinked_filter_le _ _ ho2 hp2) hx

omit [DecidableEq Root] in
theorem chainCheckpoint_agree {S : FFGSetup Root} {b1 b2 : List (FFGWireBlock Root)}
    (hc : RootsCommit S (b1 ++ b2))
    (ho1 : b1.Pairwise fun a b => a.slot < b.slot) (ho2 : b2.Pairwise fun a b => a.slot < b.slot)
    (hp1 : ParentLinked S.genesisRoot b1) (hp2 : ParentLinked S.genesisRoot b2)
    {e : Epoch} (he : chainCheckpoint S b1 e = chainCheckpoint S b2 e)
    {e' : Epoch} (hle : e' ≤ e) : chainCheckpoint S b1 e' = chainCheckpoint S b2 e' := by
  have hx := congrArg Checkpoint.root he
  unfold chainCheckpoint
  rw [chainRootAt_agree hc ho1 ho2 hp1 hp2 (x := compute_start_slot_at_epoch S.cfg e) hx
    (y := compute_start_slot_at_epoch S.cfg e') (Nat.mul_le_mul_right _ hle)]

/-! ### Certificates on the chain -/

/-- The target of a link of a reachable run is the chain checkpoint of its
epoch. -/
theorem SupermajorityLink.target_eq_chainCheckpoint {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (hR : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    {s t : Checkpoint Root} (L : SupermajorityLink S votes s t) :
    t = chainCheckpoint S blocks t.epoch := by
  obtain ⟨i, hi⟩ := L.signers_nonempty hS
  obtain ⟨r, hr, -, -, hrt⟩ := L.signer_vote i hi
  have := targetIncluded_target_on_chain hS hR hH hr
  rw [hrt] at this
  exact checkpoint_eq_of rfl this

theorem Justified.eq_stub_or_chainCheckpoint {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (hR : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch)
    {c : Checkpoint Root} (hc : Justified S votes c) :
    c = S.stub ∨ c = chainCheckpoint S blocks c.epoch := by
  rcases justified_checkpoint_on_chain hS hR hH hc with h | h
  · exact Or.inl h
  · exact Or.inr (checkpoint_eq_of rfl h)

/-! ### Exact finalized prefix -/

/-- **Exact finalized prefix under accountability.** Take a finalizing link
of one reachable run and a justified checkpoint `j` of a second reachable run,
with `j` not earlier than the finalized checkpoint. If the two certificate
laws hold for the joint votes, the finalized checkpoint is the stub or the
chain checkpoint of its epoch on the second run. This is the concrete form of
`IncludedCertifiedFinalized.exact_prefix_of_accountable` with the `k = 2`
middle checkpoint. -/
theorem finalized_prefix_of_accountable {S : FFGSetup Root} (hS : S.Admissible)
    {blocks1 blocks2 : List (FFGWireBlock Root)} {votes1 votes2 : List (IncludedVote Root)}
    {state1 state2 : FFGBeaconState Root}
    (hR1 : Reachable S blocks1 votes1 state1)
    (hH1 : compute_epoch_at_slot S.cfg state1.slot ≤ S.scope.last_epoch)
    (hR2 : Reachable S blocks2 votes2 state2)
    (hH2 : compute_epoch_at_slot S.cfg state2.slot ≤ S.scope.last_epoch)
    (hc : RootsCommit S (blocks1 ++ blocks2))
    (hacc : ConcreteCertificateAccountability S (votes1 ++ votes2))
    {f target : Checkpoint Root} (hf : FinalizationLink S blocks1 votes1 f target)
    (htarget : target.epoch ≤ S.scope.last_epoch)
    {j : Checkpoint Root} (hj : Justified S votes2 j) (hjl : j.epoch ≤ S.scope.last_epoch)
    (hfj : f.epoch ≤ j.epoch) :
    f = S.stub ∨ f = chainCheckpoint S blocks2 f.epoch := by
  have V1 : ∀ r, r ∈ votes1 → r ∈ votes1 ++ votes2 := fun r hr => List.mem_append_left _ hr
  have V2 : ∀ r, r ∈ votes2 → r ∈ votes1 ++ votes2 := fun r hr => List.mem_append_right _ hr
  have hfJ := hf.justified.mono V1
  obtain ⟨Lf⟩ := hf.link
  have htJ : Justified S (votes1 ++ votes2) target := (Justified.link hf.justified Lf).mono V1
  obtain ⟨ho1, hp1, -, -⟩ := reachable_history hS hR1 hH1
  obtain ⟨ho2, hp2, -, -⟩ := reachable_history hS hR2 hH2
  have hfchain := hf.justified.eq_stub_or_chainCheckpoint hS hR1 hH1
  -- Agreement of the two chains at an epoch not before `f` places `f`.
  have hfin : ∀ e, f.epoch ≤ e → chainCheckpoint S blocks1 e = chainCheckpoint S blocks2 e →
      f = S.stub ∨ f = chainCheckpoint S blocks2 f.epoch := fun e he hce =>
    hfchain.imp id (fun h => h.trans (chainCheckpoint_agree hc ho1 ho2 hp1 hp2 hce he))
  have hft : f.epoch < target.epoch := Lf.source_before_target
  revert hjl hfj
  induction hj with
  | anchor =>
    intro _ hfj
    exact Or.inl (hf.justified.eq_stub_of_epoch_zero (by change f.epoch ≤ 0 at hfj; beacon_omega))
  | @link s j' hs L ih =>
    intro hjl hfj
    have hsj := L.source_before_target
    by_cases hsf : f.epoch ≤ s.epoch
    · exact ih (by beacon_omega) hsf
    have hjchain := L.target_eq_chainCheckpoint hS hR2 hH2
    have hjJ : Justified S (votes1 ++ votes2) j' := (Justified.link hs L).mono V2
    by_cases hje : j'.epoch = f.epoch
    · have hroot := hacc.justified_unique hfJ hjJ (by beacon_omega) hje.symm
      have hfj' : f = j' := checkpoint_eq_of hje.symm hroot
      right
      rw [hfj']
      exact hjchain
    by_cases hjt : j'.epoch = target.epoch
    · have hroot := hacc.justified_unique htJ hjJ htarget hjt.symm
      have htj : target = j' := checkpoint_eq_of hjt.symm hroot
      refine hfin target.epoch (by beacon_omega) ?_
      calc chainCheckpoint S blocks1 target.epoch = target := hf.target_on_chain.symm
        _ = j' := htj
        _ = chainCheckpoint S blocks2 j'.epoch := hjchain
        _ = chainCheckpoint S blocks2 target.epoch := by rw [hjt]
    by_cases hmid : target.epoch = f.epoch + 2 ∧ j'.epoch = f.epoch + 1
    · have hmJ := (hf.middle_justified hmid.1).mono V1
      have hroot := hacc.justified_unique hmJ hjJ (by change f.epoch + 1 ≤ _; beacon_omega)
        (by change f.epoch + 1 = _; beacon_omega)
      have hmj : chainCheckpoint S blocks1 (f.epoch + 1) = j' :=
        checkpoint_eq_of (by change f.epoch + 1 = _; beacon_omega) hroot
      refine hfin (f.epoch + 1) (by beacon_omega) ?_
      calc chainCheckpoint S blocks1 (f.epoch + 1) = j' := hmj
        _ = chainCheckpoint S blocks2 j'.epoch := hjchain
        _ = chainCheckpoint S blocks2 (f.epoch + 1) := by rw [hmid.2]
    · exfalso
      have htj : target.epoch < j'.epoch := by
        rcases hf.target_epoch with h | h <;> beacon_omega
      exact hacc.links_not_surround (L.mono V2) (Lf.mono V1) hjl ⟨by beacon_omega, htj⟩

/-- **Exact finalized prefix or slashing.** The finalized checkpoint of a
finalizing link of one reachable run is the stub or the chain checkpoint of
its epoch on a second reachable run with a not-earlier justified checkpoint,
or validators with one third of the fixed total active balance signed
slashable included, target-matching votes. -/
theorem finalized_prefix_or_slashable {S : FFGSetup Root} (hS : S.Admissible)
    {blocks1 blocks2 : List (FFGWireBlock Root)} {votes1 votes2 : List (IncludedVote Root)}
    {state1 state2 : FFGBeaconState Root}
    (hR1 : Reachable S blocks1 votes1 state1)
    (hH1 : compute_epoch_at_slot S.cfg state1.slot ≤ S.scope.last_epoch)
    (hR2 : Reachable S blocks2 votes2 state2)
    (hH2 : compute_epoch_at_slot S.cfg state2.slot ≤ S.scope.last_epoch)
    (hc : RootsCommit S (blocks1 ++ blocks2))
    {f target : Checkpoint Root} (hf : FinalizationLink S blocks1 votes1 f target)
    (htarget : target.epoch ≤ S.scope.last_epoch)
    {j : Checkpoint Root} (hj : Justified S votes2 j) (hjl : j.epoch ≤ S.scope.last_epoch)
    (hfj : f.epoch ≤ j.epoch) :
    (f = S.stub ∨ f = chainCheckpoint S blocks2 f.epoch) ∨
      SlashableQuorum S (votes1 ++ votes2) := by
  by_cases hq : SlashableQuorum S (votes1 ++ votes2)
  · exact Or.inr hq
  · exact Or.inl (finalized_prefix_of_accountable hS hR1 hH1 hR2 hH2 hc
      (ConcreteCertificateAccountability.of_not_slashableQuorum hS hq) hf htarget hj hjl hfj)

/-- The finalized checkpoint of an in-horizon reachable state is earlier than
its current epoch. -/
theorem finalized_epoch_lt {S : FFGSetup Root} (hS : S.Admissible)
    {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
    {state : FFGBeaconState Root} (h : Reachable S blocks votes state)
    (hH : compute_epoch_at_slot S.cfg state.slot ≤ S.scope.last_epoch) :
    state.finalized_checkpoint = S.stub ∨
      state.finalized_checkpoint.epoch < compute_epoch_at_slot S.cfg state.slot := by
  rcases finalization_soundness hS h hH with h' | ⟨target, hl, hlt⟩
  · exact Or.inl h'
  · obtain ⟨L⟩ := hl.link
    have := L.source_before_target
    exact Or.inr (by beacon_omega)

/-- **Concrete accountable safety for finalized checkpoints.** Take two
in-horizon reachable runs of one setup whose block roots commit to slot and
parent. If the earlier finalized checkpoint is neither the stub nor the chain
checkpoint of its epoch on the other run, then validators with at least one
third of the fixed total active balance signed slashable pairs among the
included, target-matching votes of the two runs. -/
theorem concrete_accountable_safety {S : FFGSetup Root} (hS : S.Admissible)
    {blocks1 blocks2 : List (FFGWireBlock Root)} {votes1 votes2 : List (IncludedVote Root)}
    {state1 state2 : FFGBeaconState Root}
    (hR1 : Reachable S blocks1 votes1 state1)
    (hH1 : compute_epoch_at_slot S.cfg state1.slot ≤ S.scope.last_epoch)
    (hR2 : Reachable S blocks2 votes2 state2)
    (hH2 : compute_epoch_at_slot S.cfg state2.slot ≤ S.scope.last_epoch)
    (hc : RootsCommit S (blocks1 ++ blocks2))
    (hepoch : state1.finalized_checkpoint.epoch ≤ state2.finalized_checkpoint.epoch)
    (hconflict : state1.finalized_checkpoint ≠ S.stub ∧
      state1.finalized_checkpoint ≠
        chainCheckpoint S blocks2 state1.finalized_checkpoint.epoch) :
    SlashableQuorum S (votes1 ++ votes2) := by
  rcases finalization_soundness hS hR1 hH1 with h1 | ⟨target, hl, hlt⟩
  · exact absurd h1 hconflict.1
  have hj := (justification_soundness hS hR2 hH2).2.2
  have hjl : state2.finalized_checkpoint.epoch ≤ S.scope.last_epoch := by
    rcases finalized_epoch_lt hS hR2 hH2 with h2 | h2
    · rw [h2] at hepoch ⊢
      exact Nat.zero_le _
    · beacon_omega
  rcases finalized_prefix_or_slashable hS hR1 hH1 hR2 hH2 hc hl (by beacon_omega) hj hjl hepoch with
    h | hq
  · rcases h with h | h
    · exact absurd h hconflict.1
    · exact absurd h hconflict.2
  · exact hq

end FastConfirmation.Spec.ConcreteFFG

end
