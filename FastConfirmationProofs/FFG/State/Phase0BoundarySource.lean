module
public import FastConfirmationStatements.Premises.FFG

@[expose] public section

/-!
The honest source read after one or more empty epoch boundaries.
`phase0BoundarySource st e` is the justified checkpoint after slot processing
from `st` to the first slot of epoch `e`. The Phase0 boundary laws make it the
source of every slot-processing or block-transition result in epoch `e`.
For one boundary it is the eager PJF value.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-- The justified checkpoint after slot processing to the start of epoch `e`. -/
def phase0BoundarySource (st : BeaconState Root) (e : Epoch) : Checkpoint Root :=
  (ext.process_slots st (compute_start_slot_at_epoch cfg e)).current_justified_checkpoint

theorem compute_epoch_at_start_slot (e : Epoch) :
    compute_epoch_at_slot cfg (compute_start_slot_at_epoch cfg e) = e := by
  simp only [compute_epoch_at_slot, compute_start_slot_at_epoch]
  exact Nat.mul_div_cancel e cfg.slots_per_epoch_pos

theorem slot_lt_start_of_epoch_lt {slot : Slot} {e : Epoch}
    (h : compute_epoch_at_slot cfg slot < e) :
    slot < compute_start_slot_at_epoch cfg e := by
  by_contra hnot
  have hle : compute_start_slot_at_epoch cfg e ≤ slot := Nat.le_of_not_gt hnot
  have := Nat.div_le_div_right (c := cfg.slots_per_epoch) hle
  rw [← compute_epoch_at_slot, ← compute_epoch_at_slot,
    compute_epoch_at_start_slot] at this
  exact (Nat.not_le_of_gt h) this

/-- The source that an honest vote in epoch `e` reads from head `r`: the
head state's checkpoint in the head epoch, else the boundary source. -/
def phase0HonestSourceAt (store : Store Root) (r : Root) (e : Epoch) :
    Checkpoint Root :=
  if get_block_epoch cfg store r = e then
    (store.block_states r).current_justified_checkpoint
  else phase0BoundarySource cfg ext (store.block_states r) e

namespace Phase0BoundarySourceCoherence

variable {cfg ext}

/-- The old unconditional eager equations imply the Phase0 boundary laws.
Finite witness externals that satisfy the stronger equations use this
constructor. -/
theorem of_eager
    (hslots : ∀ (st : BeaconState Root) (target : Slot),
      st.slot < target →
      compute_epoch_at_slot cfg st.slot < compute_epoch_at_slot cfg target →
      (ext.process_slots st target).current_justified_checkpoint =
        (ext.process_justification_and_finalization st).current_justified_checkpoint)
    (htransition : ∀ (pre : BeaconState Root) (sb : SignedBeaconBlock Root)
      (post : BeaconState Root),
      ext.state_transition pre sb = some post →
      compute_epoch_at_slot cfg pre.slot <
        compute_epoch_at_slot cfg sb.message.slot →
      post.current_justified_checkpoint =
        (ext.process_justification_and_finalization pre).current_justified_checkpoint)
    (hpjf : ∀ st : BeaconState Root,
      (ext.process_justification_and_finalization st).current_justified_checkpoint.epoch ≤
        compute_epoch_at_slot cfg st.slot) :
    Phase0BoundarySourceCoherence cfg ext := by
  have hlt : ∀ {st : BeaconState Root} {target : Slot},
      compute_epoch_at_slot cfg st.slot < compute_epoch_at_slot cfg target →
      st.slot < target := by
    intro st target h
    by_contra hnot
    exact (Nat.not_le_of_gt h) (Nat.div_le_div_right (Nat.le_of_not_gt hnot))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro st target hslot hnext
    exact hslots st target hslot (by rw [hnext]; exact Nat.lt_succ_self _)
  · intro st target target' hcross hsame
    rw [hslots st target (hlt hcross) hcross,
      hslots st target' (hlt (hsame ▸ hcross)) (hsame ▸ hcross)]
  · intro pre sb post h hcross
    rw [htransition pre sb post h hcross, hslots pre _ (hlt hcross) hcross]
  · intro st target hcross
    rw [hslots st target (hlt hcross) hcross]
    exact Or.inr (hpjf st)

/-- Slot processing into a later epoch reads the boundary source of that
epoch. -/
theorem process_slots_eq_boundarySource
    (h : Phase0BoundarySourceCoherence cfg ext)
    {st : BeaconState Root} {target : Slot}
    (hcross : compute_epoch_at_slot cfg st.slot <
      compute_epoch_at_slot cfg target) :
    (ext.process_slots st target).current_justified_checkpoint =
      phase0BoundarySource cfg ext st (compute_epoch_at_slot cfg target) :=
  h.process_slots_same_target_epoch st target _ hcross
    (compute_epoch_at_start_slot cfg _).symm

/-- A block transition into a later epoch reads the boundary source of the
block epoch. -/
theorem state_transition_eq_boundarySource
    (h : Phase0BoundarySourceCoherence cfg ext)
    {pre : BeaconState Root} {sb : SignedBeaconBlock Root}
    {post : BeaconState Root}
    (htransition : ext.state_transition pre sb = some post)
    (hcross : compute_epoch_at_slot cfg pre.slot <
      compute_epoch_at_slot cfg sb.message.slot) :
    post.current_justified_checkpoint =
      phase0BoundarySource cfg ext pre
        (compute_epoch_at_slot cfg sb.message.slot) :=
  (h.state_transition_process_slots pre sb post htransition hcross).trans
    (h.process_slots_eq_boundarySource hcross)

/-- Across one boundary the boundary source is the eager PJF value. -/
theorem boundarySource_eq_pjf
    (h : Phase0BoundarySourceCoherence cfg ext)
    {st : BeaconState Root} {e : Epoch}
    (hnext : e = compute_epoch_at_slot cfg st.slot + 1) :
    phase0BoundarySource cfg ext st e =
      (ext.process_justification_and_finalization st).current_justified_checkpoint :=
  h.process_slots_one_boundary st _
    (slot_lt_start_of_epoch_lt cfg (by rw [hnext]; exact Nat.lt_succ_self _))
    ((compute_epoch_at_start_slot cfg e).trans hnext)

/-- The boundary source is the start state's checkpoint or no newer than the
start epoch. -/
theorem boundarySource_eq_or_epoch_le
    (h : Phase0BoundarySourceCoherence cfg ext)
    {st : BeaconState Root} {e : Epoch}
    (hcross : compute_epoch_at_slot cfg st.slot < e) :
    phase0BoundarySource cfg ext st e = st.current_justified_checkpoint ∨
      (phase0BoundarySource cfg ext st e).epoch ≤
        compute_epoch_at_slot cfg st.slot :=
  h.process_slots_checkpoint_epoch st _
    (by rw [compute_epoch_at_start_slot]; exact hcross)

end Phase0BoundarySourceCoherence

variable [LinearOrder Root] [Inhabited Root]

/-- A current target whose block is two or more epochs old needs a known
current-epoch block below the head.  That accepted block carries the boundary
source as its `GJ`.  The call sites that use the target gate satisfy this. -/
def CurrentTargetLateBoundaryCarrierGuard (store : Store Root) : Prop :=
  get_block_epoch cfg store (get_current_target cfg store).root + 1 <
      (get_current_target cfg store).epoch →
    ∃ c ∈ store.block_roots,
      get_block_epoch cfg store c = get_current_store_epoch cfg store ∧
        is_ancestor store (get_head cfg store) (get_node_for_root c) = true

end FastConfirmation.Spec

end
