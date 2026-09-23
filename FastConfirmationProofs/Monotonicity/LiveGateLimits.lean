module
public import FastConfirmationProofs.FCRRule.GetLatestConfirmedTrace
public import FastConfirmationProofs.FFG.SourceHistory.SafeFromInvariant

@[expose] public section

/-!
# Live monotonicity gate limits

Proves two executable FCR gate facts that limit live monotonicity when FFG justification arrives late.

The accepted finalization delay permits the anchor checkpoint at the first epoch boundary. It does not imply a strict later-epoch finalization bound.

In a non-start slot, stale unrealized justifications make the descendant selector return its input. At a later FCR call, a stale cached root and stale observed and finalized checkpoints make `get_latest_confirmed` return the finalized root.

The live economic bounds cover total stake. They do not make one slot's honest committee outweigh the proposer boost. A delivered honest vote can therefore leave a boosted sibling as the head.
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
    (v : ValidatorIndex) (n : ℕ) (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hstale : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.confirmed cfg ext v n) + 1 <
      get_current_store_epoch cfg (E.store cfg ext v (n + 1)))
    (hobserved : get_block_epoch cfg (E.store cfg ext v (n + 1))
        (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.root + 1 ≠
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
    (E.fcrStoreAtCall cfg ext v n)
    (by rw [hstore, hroot]; exact hstale)
    (by rw [hstore]; exact hobserved)
    (by rw [hstore]; exact hfinalized)
  rw [h, hstore]


end Execution

end FastConfirmation.Spec


end
