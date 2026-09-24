module
public import FastConfirmationStatements.Premises.Synchrony
public import FastConfirmationStatements.Traces
public import FastConfirmationProofs.Checkpoints.SlotClock

@[expose] public section

/-! Honest vote and scheduled FCR call roots have source observations by the attestation deadline. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- The honest vote itself supplies a deadline-bounded origin for every root
already in the voter's store when the vote is made. -/
theorem honest_vote_root_before_deadline
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest)
    {s n : ℕ} {a : Attestation Root} {r : Root}
    (hvote : E.vote v s = some (n, a))
    (hroot : r ∈ (E.store cfg ext v n).block_roots) :
    ∃ origin : ℕ,
      E.slot_start cfg s ≤ origin ∧
      origin ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000 ∧
      r ∈ (E.store cfg ext v origin).block_roots := by
  refine ⟨n, ?_, ?_, hroot⟩
  · exact (hhb.vote_deadline v hv s n a hvote).1
  · exact (hhb.vote_deadline v hv s n a hvote).2

/-- A scheduled FCR call that advances a slot reads the new slot at its
first whole second. This is the earlier cutoff origin for roots already in
that call's store. -/
theorem scheduled_fcr_call_at_slot_start
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {v : ValidatorIndex} {n : ℕ}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n) :
    E.slot_start cfg (E.slot_at cfg (n + 1)) = n + 1 := by
  have hslot : E.slot_at cfg n < E.slot_at cfg (n + 1) := by
    simpa only [Execution.IsScheduledFCRCallAt,
      E.store_current_slot cfg ext v (n + 1),
      E.store_current_slot cfg ext v n] using hcall
  have hbefore := (E.slot_at_lt_iff cfg hdiv hgen).mp hslot
  have hstart := E.slot_start_le_of_slot_at cfg hdiv hgen
    (show E.slot_at cfg (n + 1) = E.slot_at cfg (n + 1) from rfl)
  omega

/-- A root known at a scheduled call's new-slot second has a source
observation at or before that slot's attestation deadline. -/
theorem scheduled_fcr_call_root_before_deadline
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {v : ValidatorIndex} {n : ℕ} {r : Root}
    (hcall : E.IsScheduledFCRCallAt cfg ext v n)
    (hroot : r ∈ (E.store cfg ext v (n + 1)).block_roots) :
    ∃ origin : ℕ,
      origin = n + 1 ∧
      origin ≤ E.slot_start cfg (E.slot_at cfg origin) +
        get_attestation_due_ms cfg / 1000 ∧
      r ∈ (E.store cfg ext v origin).block_roots := by
  refine ⟨n + 1, rfl, ?_, hroot⟩
  rw [E.scheduled_fcr_call_at_slot_start cfg ext hdiv hgen hcall]
  omega

/-- A later-slot receiver is after the first second of the source's next
slot and strictly after the source observation. This is the clock gate for
applying cutoff relay to an earlier honest vote or scheduled call origin. -/
theorem past_slot_deadline_target_gate
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {source target : ℕ}
    (hslot : E.slot_at cfg source < E.slot_at cfg target) :
    E.slot_start cfg (E.slot_at cfg source + 1) ≤ target ∧
      source < target := by
  have hstart := E.slot_start_le_of_slot_at cfg hdiv hgen
    (show E.slot_at cfg target = E.slot_at cfg target from rfl)
  have hgate : E.slot_start cfg (E.slot_at cfg source + 1) ≤ target :=
    (E.slot_start_mono cfg (Nat.succ_le_of_lt hslot)).trans hstart
  have htime : source < target := by
    by_contra hnot
    have hback : target ≤ source := Nat.le_of_not_gt hnot
    have hmono := E.slot_at_mono cfg hback
    exact (Nat.not_le_of_gt hslot) hmono
  exact ⟨hgate, htime⟩

/-- Under the paper's strict millisecond bound, the last whole-second vote
time is strictly before the next slot boundary. This holds for a positive
subsecond delay and for one-second slots. -/
theorem deadline_before_next_slot
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    {s n delta_ms : ℕ}
    (hboundary : E.genesis_store.time ≤ E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000))
    (hdeadline : n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000)
    (hpositive : 0 < delta_ms)
    (hfit : get_attestation_due_ms cfg + delta_ms < cfg.slot_duration_ms) :
    n < E.slot_start cfg (s + 1) := by
  obtain ⟨seconds, hseconds⟩ := hdiv
  have hsecondsDiv : cfg.slot_duration_ms / 1000 = seconds := by
    rw [hseconds]
    exact Nat.mul_div_cancel_left seconds (by decide : 0 < (1000 : ℕ))
  have hmul (x : ℕ) :
      x * cfg.slot_duration_ms / 1000 = x * seconds := by
    rw [hseconds, Nat.mul_left_comm x 1000 seconds]
    exact Nat.mul_div_cancel_left (x * seconds) (by decide : 0 < (1000 : ℕ))
  have hslot : E.slot_start cfg (s + 1) =
      E.slot_start cfg s + seconds := by
    simp only [Execution.slot_start]
    rw [hmul (s + 1), hmul s, Nat.add_mul, one_mul]
    have hbound : E.genesis_store.time ≤
        E.genesis_store.genesis_time + s * seconds := by
      simpa only [hsecondsDiv] using hboundary
    omega
  have hA : get_attestation_due_ms cfg / 1000 < seconds := by
    rw [hseconds] at hfit
    omega
  omega

/-- The source cutoff is no later than the last second before the next tick. -/
theorem deadline_le_next_slot_pred
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    {s n delta_ms : ℕ}
    (hboundary : E.genesis_store.time ≤ E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000))
    (hdeadline : n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000)
    (hpositive : 0 < delta_ms)
    (hfit : get_attestation_due_ms cfg + delta_ms < cfg.slot_duration_ms) :
    n ≤ E.slot_start cfg (s + 1) - 1 := by
  have hlt := E.deadline_before_next_slot cfg hdiv hboundary hdeadline hpositive hfit
  omega

/-- If an excluded block stays absent, its exclusion holds at every later
second. Parent knownness follows from store monotonicity. -/
theorem permanentBlockExclusion_mono_of_not_mem
    {v w : ValidatorIndex} {n k m : ℕ} {r : Root}
    (hle : k ≤ m)
    (habsent : r ∉ (E.store cfg ext w m).block_roots)
    (hexcluded : PermanentBlockExclusion cfg ext E v n r w k) :
    PermanentBlockExclusion cfg ext E v n r w m := by
  refine ⟨habsent, (E.store_storeLE cfg ext w hle).1 hexcluded.2.1, ?_⟩
  intro t hmt hHt
  exact hexcluded.2.2 t (hle.trans hmt) hHt

/-- A refined cutoff relay also gives a later endpoint alternative. If the
root remains absent, the pre-tick exclusion persists to that endpoint. -/
theorem deadline_block_relay_at_endpoint
    (hrelay : DeadlineBlockRelay cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (n : ℕ) (r : Root)
    (hHn : E.WithinHorizon cfg n)
    (hr : r ∈ (E.store cfg ext v n).block_roots)
    (hdue : n ≤ E.slot_start cfg (E.slot_at cfg n) +
      get_attestation_due_ms cfg / 1000)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hHm : E.WithinHorizon cfg m)
    (hnext : E.slot_start cfg (E.slot_at cfg n + 1) ≤ m)
    (hlt : n < m) :
    r ∈ (E.store cfg ext w m).block_roots ∨
      PermanentBlockExclusion cfg ext E v n r w m := by
  rcases hrelay v hv n r hHn hr hdue w hw m hHm hnext hlt with hk | he
  · exact Or.inl hk
  · by_cases hk : r ∈ (E.store cfg ext w m).block_roots
    · exact Or.inl hk
    · exact Or.inr (E.permanentBlockExclusion_mono_of_not_mem cfg ext
        ((Nat.sub_le _ 1).trans hnext) hk he)

/-- The integer-second arrival argument for the refined exemption. An
accepted block remains known. An exclusion at an earlier arrival second
also holds at the last source-slot second if the block is still absent. -/
theorem deadline_block_relay_outcome_of_arrival
    {v w : ValidatorIndex} {n a boundary m : ℕ} {r : Root}
    (harrival : a < boundary) (hnext : boundary ≤ m)
    (houtcome : r ∈ (E.store cfg ext w a).block_roots ∨
      PermanentBlockExclusion cfg ext E v n r w a) :
    r ∈ (E.store cfg ext w m).block_roots ∨
      PermanentBlockExclusion cfg ext E v n r w (boundary - 1) := by
  rcases houtcome with hknown | hexcluded
  · exact Or.inl ((E.store_storeLE cfg ext w (harrival.le.trans hnext)).1 hknown)
  · by_cases hknown : r ∈ (E.store cfg ext w (boundary - 1)).block_roots
    · exact Or.inl ((E.store_storeLE cfg ext w
        ((Nat.sub_le boundary 1).trans hnext)).1 hknown)
    · exact Or.inr (E.permanentBlockExclusion_mono_of_not_mem cfg ext
        (by omega) hknown hexcluded)

/-- An honest voter's selected root reaches the next-slot receiver unless
that receiver has permanently excluded the block under `on_block`'s finalized
guard. The vote gives the source-time cutoff; the strict positive bound gives
the distinct receiver second. -/
theorem honest_vote_root_relay_or_excluded
    (hhb : HonestBehavior cfg ext E)
    (hsync : NextSlotSynchronyPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s n m : ℕ} {a : Attestation Root} {r : Root}
    (hboundary : E.genesis_store.time ≤ E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000))
    (hHn : E.WithinHorizon cfg n)
    (hHm : E.WithinHorizon cfg m)
    (hvote : E.vote v s = some (n, a))
    (hslot : E.slot_at cfg n = s)
    (hroot : r ∈ (E.store cfg ext v n).block_roots)
    (hnext : E.slot_start cfg (s + 1) ≤ m) :
    r ∈ (E.store cfg ext w m).block_roots ∨
      PermanentBlockExclusion cfg ext E v n r w
        (E.slot_start cfg (E.slot_at cfg n + 1) - 1) := by
  have hdue := (hhb.vote_deadline v hv s n a hvote).2
  have hlt : n < m :=
    (E.deadline_before_next_slot cfg hdiv hboundary hdue
      hsync.delta_pos hsync.deadline_fits).trans_le hnext
  apply hsync.deadline_block_relay v hv n r hHn hroot
  · simpa only [hslot] using hdue
  · exact hw
  · exact hHm
  · simpa only [hslot] using hnext
  · exact hlt

/-- The finalized-only exemption is impossible when both exact `on_block`
finalized guards pass in the receiver's current store. -/
theorem permanentBlockExclusion_false_of_finalized_guards
    {v w : ValidatorIndex} {n m : ℕ} {r : Root}
    (hHm : E.WithinHorizon cfg m)
    (hslot : compute_start_slot_at_epoch cfg
        (E.store cfg ext w m).finalized_checkpoint.epoch <
      ((E.store cfg ext v n).blocks r).slot)
    (hcheckpoint : (E.store cfg ext w m).finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext w m)
        ((E.store cfg ext v n).blocks r).parent_root
        (E.store cfg ext w m).finalized_checkpoint.epoch) :
    ¬ PermanentBlockExclusion cfg ext E v n r w m := by
  intro hreject
  have hguard := hreject.2.2 m (Nat.le_refl m) hHm
  rcases hguard with hbefore | hconflict
  · exact (Nat.not_le_of_gt hslot) hbefore
  · exact hconflict hcheckpoint

/-- The paper's strict `A + Δ < S` bound places a message sent by the vote
deadline in the receiver's store before the next slot's first second. The
genuine-boundary guard handles executions whose anchor begins mid-slot. -/
theorem deadline_relay_before_next_slot
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    {s n delta : ℕ}
    (hboundary : E.genesis_store.time ≤ E.genesis_store.genesis_time +
      s * (cfg.slot_duration_ms / 1000))
    (hdeadline : n ≤ E.slot_start cfg s + get_attestation_due_ms cfg / 1000)
    (hdelta : 0 < delta)
    (hfit : get_attestation_due_ms cfg / 1000 + delta <
      cfg.slot_duration_ms / 1000) :
    n + delta ≤ E.slot_start cfg (s + 1) - 1 ∧
      n < E.slot_start cfg (s + 1) - 1 := by
  obtain ⟨seconds, hseconds⟩ := hdiv
  have hsecondsDiv : cfg.slot_duration_ms / 1000 = seconds := by
    rw [hseconds]
    exact Nat.mul_div_cancel_left seconds (by decide : 0 < (1000 : ℕ))
  have hmul (x : ℕ) :
      x * cfg.slot_duration_ms / 1000 = x * seconds := by
    rw [hseconds, Nat.mul_left_comm x 1000 seconds]
    exact Nat.mul_div_cancel_left (x * seconds) (by decide : 0 < (1000 : ℕ))
  have hslot : E.slot_start cfg (s + 1) =
      E.slot_start cfg s + seconds := by
    simp only [Execution.slot_start]
    rw [hmul (s + 1), hmul s, Nat.add_mul, one_mul]
    have hbound : E.genesis_store.time ≤
        E.genesis_store.genesis_time + s * seconds := by
      simpa only [hsecondsDiv] using hboundary
    omega
  rw [hsecondsDiv] at hfit
  omega

end Execution
end FastConfirmation.Spec

end
