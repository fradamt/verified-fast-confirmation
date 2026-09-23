module
public import FastConfirmationModel.Weak.WeakSynchrony
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots

@[expose] public section

namespace FastConfirmation.Spec.Weak

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A successful search supplies knownness, ancestry, and its own certificate. -/
theorem certified_head_search_spec (store : Store Root) (bs : BeaconState Root)
    (fuel : Nat) (root carrier : Root)
    (h : certified_head_search cfg ext store bs fuel root = some carrier) :
    carrier ∈ store.block_roots ∧
      is_ancestor store (get_head cfg store) (get_node_for_root carrier) = true ∧
      has_broadcast_certificate cfg ext store bs carrier
        (get_block_slot store carrier) (get_current_slot cfg store - 1) = true := by
  induction fuel generalizing root with
  | zero => simp [certified_head_search] at h
  | succ fuel ih =>
    simp only [certified_head_search] at h
    split_ifs at h with hc hp
    · cases h
      exact hc
    · exact ih _ h

/-- Total fallback and successful search both name a known root. -/
theorem get_certified_head_known (store : Store Root) (bs : BeaconState Root)
    (hhead : (get_head cfg store).root ∈ store.block_roots) :
    get_certified_head cfg ext store bs ∈ store.block_roots := by
  unfold get_certified_head
  cases h : certified_head_search cfg ext store bs
      (get_block_slot store (get_head cfg store).root + 1) (get_head cfg store).root with
  | none => exact hhead
  | some r => exact (certified_head_search_spec cfg ext store bs _ _ _ h).1

/-- Selecting a carrier cannot move to a side branch. -/
theorem get_certified_head_below_head (store : Store Root) (bs : BeaconState Root) :
    is_ancestor store (get_head cfg store)
      (get_node_for_root (get_certified_head cfg ext store bs)) = true := by
  unfold get_certified_head
  cases h : certified_head_search cfg ext store bs
      (get_block_slot store (get_head cfg store).root + 1) (get_head cfg store).root with
  | none =>
      rw [is_ancestor_node_root]
      exact is_ancestor_refl _ _
  | some r => exact (certified_head_search_spec cfg ext store bs _ _ _ h).2.1

/-- If the actual head is certified, selection returns it without delay. -/
theorem get_certified_head_eq_head (store : Store Root) (bs : BeaconState Root)
    (hknown : (get_head cfg store).root ∈ store.block_roots)
    (hcert : has_broadcast_certificate cfg ext store bs (get_head cfg store).root
      (get_block_slot store (get_head cfg store).root)
      (get_current_slot cfg store - 1) = true) :
    get_certified_head cfg ext store bs = (get_head cfg store).root := by
  have hself : is_ancestor store (get_head cfg store)
      (get_node_for_root (get_head cfg store).root) = true := by
    rw [is_ancestor_node_root]
    exact is_ancestor_refl _ _
  simp [get_certified_head, certified_head_search, hknown, hself, hcert]

/-- A new uncertified head does not hide its certified parent. -/
theorem get_certified_head_eq_parent (store : Store Root) (bs : BeaconState Root)
    (parent : Root)
    (hparent : (store.blocks (get_head cfg store).root).parent_root = parent)
    (hknown : parent ∈ store.block_roots)
    (hbelow : is_ancestor store (get_head cfg store) (get_node_for_root parent) = true)
    (hlt : get_block_slot store parent < get_block_slot store (get_head cfg store).root)
    (hnew : has_broadcast_certificate cfg ext store bs (get_head cfg store).root
      (get_block_slot store (get_head cfg store).root)
      (get_current_slot cfg store - 1) = false)
    (hcert : has_broadcast_certificate cfg ext store bs parent
      (get_block_slot store parent) (get_current_slot cfg store - 1) = true) :
    get_certified_head cfg ext store bs = parent := by
  obtain ⟨fuel, hfuel⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt))
  unfold get_certified_head
  rw [certified_head_search]
  simp only [hnew, Bool.false_eq_true, and_false, if_false, hparent]
  rw [if_pos hlt, hfuel, certified_head_search]
  simp [hknown, hbelow, hcert]

end FastConfirmation.Spec.Weak

end
