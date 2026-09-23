module
public import FastConfirmation.Spec.Proof.GetLatestConfirmedTrace
public import FastConfirmation.Spec.Proof.L4Fold

@[expose] public section

/-!
# Executable gates that block live monotonicity

`MonotonicityLiveAssumptions` does not constrain when a justification becomes
visible in `store.unrealized_justifications`. The accepted paper Assumption
3.2 lets the justification of epoch `e` appear only by the start of epoch
`e + 2`. The executable selector needs it earlier. This file records the two
executable facts behind that gap:

1. In a non-start slot, if the unrealized justification of both the head and
   the previous-slot head is older than the previous epoch, the descendant
   selector returns its input. The cached root then cannot enter the current
   epoch in that slot.
2. At a call where the cached root is at least two epochs old, the observed
   checkpoint block is not from the previous epoch, and the finalized block is
   at least two epochs old, `get_latest_confirmed` returns the finalized root.

With a one-epoch lag of unrealized justification, fact 1 holds in every
non-start slot of an epoch. The cached root is then at least two epochs old at
the next epoch start, and fact 2 moves it back to the finalized root. The
facts are about the executable functions only. They are not a claim that
every accepted execution has such a lag.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- In a non-start slot, a lagging unrealized justification at both the
head and the previous-slot head closes both gates of the descendant
selector. -/
theorem find_latest_confirmed_descendant_eq_of_lagging_unrealized
    (query : FastConfirmationStore Root) (input : Root)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = false)
    (hhead : (query.store.unrealized_justifications
        (get_head cfg query.store).root).epoch + 1 <
      get_current_store_epoch cfg query.store)
    (hprev : (query.store.unrealized_justifications
        query.previous_slot_head).epoch + 1 <
      get_current_store_epoch cfg query.store) :
    find_latest_confirmed_descendant cfg ext query input = input := by
  have hheadNot : ¬ ((query.store.unrealized_justifications
      (get_head cfg query.store).root).epoch + 1 ≥
        get_current_store_epoch cfg query.store) := Nat.not_le.mpr hhead
  have hprevNot : ¬ ((query.store.unrealized_justifications
      query.previous_slot_head).epoch + 1 ≥
        get_current_store_epoch cfg query.store) := Nat.not_le.mpr hprev
  simp [find_latest_confirmed_descendant, hstart, hheadNot, hprevNot]

/-- A stale cached root reverts to the finalized root when neither the
observed restart nor the selector can move the candidate. -/
theorem get_latest_confirmed_eq_finalized_of_stale
    (query : FastConfirmationStore Root)
    (hstale : get_block_epoch cfg query.store query.confirmed_root + 1 <
      get_current_store_epoch cfg query.store)
    (hobserved : get_block_epoch cfg query.store
        query.current_epoch_observed_justified_checkpoint.root + 1 ≠
      get_current_store_epoch cfg query.store)
    (hfinalized : get_block_epoch cfg query.store
        query.store.finalized_checkpoint.root + 1 <
      get_current_store_epoch cfg query.store) :
    get_latest_confirmed cfg ext query =
      query.store.finalized_checkpoint.root := by
  have hafterFinalized : getLatestAfterFinalized cfg ext query =
      query.store.finalized_checkpoint.root := by
    simp only [getLatestAfterFinalized]
    rw [if_pos (Or.inl hstale)]
  have hguard : getLatestObservedRestartGuard cfg query
      (getLatestAfterFinalized cfg ext query) = false := by
    simp [getLatestObservedRestartGuard, hobserved]
  have hafterObserved : getLatestAfterObserved cfg ext query =
      query.store.finalized_checkpoint.root := by
    simp only [getLatestAfterObserved]
    rw [if_neg (by simp [hguard]), hafterFinalized]
  rw [← getLatestTraceResult_eq_getLatestConfirmed]
  have hselector : ¬ (get_block_epoch cfg query.store
      (getLatestAfterObserved cfg ext query) + 1 ≥
        get_current_store_epoch cfg query.store) := by
    rw [hafterObserved]
    exact Nat.not_le.mpr hfinalized
  simp only [getLatestTraceResult]
  rw [if_neg hselector, hafterObserved]

namespace Execution

variable (E : Execution Root)

/-- Execution form of `get_latest_confirmed_eq_finalized_of_stale` at an
actual FCR call. -/
theorem confirmed_succ_eq_finalized_of_stale_call
    (v : ValidatorIndex) (n : ℕ) (hcall : E.IsFCRCallAt cfg ext v n)
    (hstale : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hobserved : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root + 1 ≠
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hfinalized : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.store cfg ext v (n + 1)).finalized_checkpoint.root + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1))) :
    E.confirmed cfg ext v (n + 1) =
      (E.store cfg ext v (n + 1)).finalized_checkpoint.root := by
  rw [E.confirmed_succ_of_advance cfg ext v n hcall]
  have hstore := E.fcrStep_store cfg ext v n
  have hroot := E.fcrStep_confirmed_root cfg ext v n
  have h := get_latest_confirmed_eq_finalized_of_stale cfg ext
    (E.fcrStep cfg ext v n)
    (by rw [hstore, hroot]; exact hstale)
    (by rw [hstore]; exact hobserved)
    (by rw [hstore]; exact hfinalized)
  rw [h, hstore]

/-- At a non-start call with a lagging unrealized justification, a cached
root that is recent and canonical is carried unchanged. -/
theorem confirmed_succ_eq_of_lagging_nonstart_call
    (v : ValidatorIndex) (n : ℕ) (hcall : E.IsFCRCallAt cfg ext v n)
    (hstart : is_start_slot_at_epoch cfg
      (get_current_slot cfg (E.store cfg ext v (n + 1))) = false)
    (hrecent : ¬ get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hcanonical : is_ancestor (E.store cfg ext v (n + 1))
        (get_node_for_root (get_head cfg (E.store cfg ext v (n + 1))).root)
        (get_node_for_root (E.confirmed cfg ext v n)) = true)
    (hhead : ((E.store cfg ext v (n + 1)).unrealized_justifications
        (get_head cfg (E.store cfg ext v (n + 1))).root).epoch + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hprev : ((E.store cfg ext v (n + 1)).unrealized_justifications
        (E.fcrStep cfg ext v n).previous_slot_head).epoch + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1))) :
    E.confirmed cfg ext v (n + 1) = E.confirmed cfg ext v n := by
  rw [E.confirmed_succ_of_advance cfg ext v n hcall,
    ← getLatestTraceResult_eq_getLatestConfirmed]
  have hstore := E.fcrStep_store cfg ext v n
  have hroot := E.fcrStep_confirmed_root cfg ext v n
  set query := E.fcrStep cfg ext v n with hquery
  have hstart' : is_start_slot_at_epoch cfg
      (get_current_slot cfg query.store) = false := by
    rw [hstore]; exact hstart
  have hafterFinalized : getLatestAfterFinalized cfg ext query =
      E.confirmed cfg ext v n := by
    simp only [getLatestAfterFinalized]
    rw [if_neg, hroot]
    rw [hstore, hroot]
    simp [hrecent, hcanonical, hstart]
  have hguard : getLatestObservedRestartGuard cfg query
      (getLatestAfterFinalized cfg ext query) = false := by
    simp [getLatestObservedRestartGuard, hstart']
  have hafterObserved : getLatestAfterObserved cfg ext query =
      E.confirmed cfg ext v n := by
    simp only [getLatestAfterObserved]
    rw [if_neg (by simp [hguard]), hafterFinalized]
  have hselect := find_latest_confirmed_descendant_eq_of_lagging_unrealized
    cfg ext query (E.confirmed cfg ext v n) hstart'
    (by rw [hstore]; exact hhead) (by rw [hstore]; exact hprev)
  simp only [getLatestTraceResult]
  rw [hafterObserved]
  split_ifs
  · exact hselect
  · rfl

end Execution

end FastConfirmation.Spec

end
