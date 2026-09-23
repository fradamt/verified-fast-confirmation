module
public import FastConfirmation.Spec.Proof.AcceptedActualFCRNextSlotSafetyFacade
public import FastConfirmation.Spec.Proof.HeadStack

@[expose] public section

/-!
# Vote and support bridges for live monotonicity

The first lemma links a recorded latest message to the honest vote that
produced it. The second isolates the full-epoch stake inequality used by
one-confirmation. Store-to-store ancestry transport and the executable
support estimate remain separate obligations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- A latest message from an honest vote in the live interval names a vote
for a descendant of that slot's honestly proposed block. The ancestry is
in the voting store; support at another store needs transport. -/
theorem latest_honest_message_extends_live_block
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v observer : ValidatorIndex} (hv : v ∈ E.honest)
    {n m : ℕ} (live : MonotonicityLiveAssumptions cfg ext E observer n m)
    {s : Slot} {k : ℕ} {a : Attestation Root}
    (hstart : E.slot_at cfg 0 ≤ s) (hend : s < E.slot_at cfg m)
    (hvote : E.vote v s = some (k, a))
    {w : ValidatorIndex} {t : ℕ} {msg : LatestMessage Root}
    (hmsg : (E.store cfg ext w t).latest_messages v = some msg)
    (hepoch : compute_epoch_at_slot cfg s = get_latest_message_epoch cfg msg) :
    ∃ r b, E.BlockAt r b ∧ b.slot = s ∧
      b.proposer_index ∈ E.honest ∧
      r ∈ (E.store cfg ext v k).block_roots ∧
      is_ancestor (E.store cfg ext v k)
        (get_node_for_root msg.root) (get_node_for_root r) = true := by
  obtain ⟨r, b, hblock, hslot, hproposer, _, hsupport⟩ :=
    live.honest_block_each_slot s hstart hend
  have hroot : msg.root = a.data.beacon_block_root := by
    have heq := E.latest_message_eq_honest_vote cfg ext hhb hec hgen
      hv hvote hmsg hepoch
    exact congrArg LatestMessage.root heq
  obtain ⟨hknown, hancestor⟩ :=
    hsupport v hv s k a (Nat.le_refl s) hend hvote
  exact ⟨r, b, hblock, hslot, hproposer, hknown, by simpa [hroot] using hancestor⟩

end Execution

/-- The configured margin makes the honest full-epoch stake exceed the
undiscounted threshold with the entire configured adversarial allowance.
The executable one-confirmation proof must identify its actual support and
threshold with these quantities. -/
theorem configured_margin_full_epoch_arith
    {total nonHonest honest allowance boost : ℕ}
    (hpart : honest + nonHonest = total)
    (hmargin : 2 * nonHonest + 2 * allowance + boost < total) :
    honest > (total + boost + 2 * allowance) / 2 := by
  omega

/-- A direct executable threshold bridge. Its premises are the support and
window bounds to be supplied by the execution proof; the discount can only
lower the threshold. -/
theorem one_confirmed_of_bounded_window
    (store : Store Root) (balanceSource : BeaconState Root) (block : Root)
    {total nonHonest honest allowance boost : ℕ}
    (hpart : honest + nonHonest = total)
    (hmargin : 2 * nonHonest + 2 * allowance + boost < total)
    (hsupport : honest ≤ get_attestation_score cfg store
      (get_node_for_root block) balanceSource)
    (hwindow : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      ((store.blocks (store.blocks block).parent_root).slot + 1)
      (get_current_slot cfg store - 1) ≤ total)
    (hboost : compute_proposer_score cfg balanceSource ≤ boost)
    (hadversarial : get_adversarial_weight cfg ext store balanceSource block ≤
      allowance) :
    is_one_confirmed cfg ext store balanceSource block = true := by
  have hbudget : estimate_committee_weight_between_slots cfg
      (get_total_active_balance cfg balanceSource)
      ((store.blocks (store.blocks block).parent_root).slot + 1)
      (get_current_slot cfg store - 1) +
      compute_proposer_score cfg balanceSource +
      2 * get_adversarial_weight cfg ext store balanceSource block ≤
      total + boost + 2 * allowance :=
    Nat.add_le_add (Nat.add_le_add hwindow hboost)
      (Nat.mul_le_mul_left 2 hadversarial)
  have hthreshold : compute_safety_threshold cfg ext store block balanceSource ≤
      (total + boost + 2 * allowance) / 2 := by
    simp only [compute_safety_threshold]
    split_ifs
    · apply Nat.div_le_div_right
      exact (Nat.sub_le _ _).trans hbudget
    · exact Nat.zero_le _
  have hfull := configured_margin_full_epoch_arith hpart hmargin
  have hscore : compute_safety_threshold cfg ext store block balanceSource <
      get_attestation_score cfg store (get_node_for_root block) balanceSource :=
    lt_of_le_of_lt hthreshold (lt_of_lt_of_le hfull hsupport)
  simpa [is_one_confirmed] using hscore

end FastConfirmation.Spec

end
