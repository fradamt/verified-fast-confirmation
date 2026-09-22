module
public import FastConfirmation.Spec.Proof.WeakObserverReplay

@[expose] public section

/-!
# A pure weak-FCR replay relation

`replay` is the executable relation at the zk boundary: it starts from a
trusted `Store`, consumes one event list for each relative second, and runs
the weak FCR at exactly the slot advances of the store trajectory.  It does
not inspect an `Execution`; executions enter only in the correspondence
theorems below.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- Pure replay of a timed observer log from a trusted starting store.

The list entry at index `k` is the event list at relative second `k + 1`.
Relative second zero has no log entry because `Execution.store` ignores its
schedule.  The second component carries the weak FCR state; its `store` field
is the first component. -/
def replay (cfg : Config) (ext : Externals Root) (start : Store Root)
    (log : List (List (Event Root))) : ℕ → Store Root × FastConfirmationStore Root
  | 0 => (start, get_fast_confirmation_store start)
  | n + 1 =>
      let previous := replay cfg ext start log n
      let ticked := on_tick cfg previous.1 (start.time + (n + 1))
      let next_store := (log.getD n []).foldl
        (fun store event => (apply_event cfg ext store event).getD store) ticked
      let next_fcr := { previous.2 with store := next_store }
      let next_fcr :=
        if get_current_slot cfg next_store > get_current_slot cfg previous.1 then
          Weak.on_fast_confirmation cfg ext next_fcr
        else next_fcr
      (next_store, next_fcr)

private def replayExecution (start : Store Root)
    (log : List (List (Event Root))) : Execution Root where
  verification_horizon := 0
  genesis_store := start
  schedule := fun _ k => log.getD (k - 1) []
  honest := ∅
  committee := fun _ => ∅
  vote := fun _ _ => none

private theorem replay_eq_replayExecution
    (cfg : Config) (ext : Externals Root) (start : Store Root)
    (log : List (List (Event Root))) (v : ValidatorIndex) :
    ∀ n : ℕ,
      replay cfg ext start log n =
        ((replayExecution start log).store cfg ext v n,
          (replayExecution start log).weakFcr cfg ext v n) := by
  intro n
  induction n with
  | zero =>
      simp [replay, replayExecution, Execution.store, Execution.weakFcr]
  | succ n ih =>
      have hstore := congrArg Prod.fst ih
      have hfcr := congrArg Prod.snd ih
      simp only [replay, Execution.store, Execution.weakFcr]
      rw [hstore, hfcr]
      simp [replayExecution, Execution.time_at]

private theorem replay_correspondence
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (v : ValidatorIndex) (log : List (List (Event Root))) (n : ℕ)
    (hlog : ∀ k : ℕ, 0 < k → k ≤ n → log.getD (k - 1) [] = E.schedule v k) :
    (replay cfg ext E.genesis_store log n).1 = E.store cfg ext v n ∧
      (replay cfg ext E.genesis_store log n).2 = E.weakFcr cfg ext v n ∧
      (replay cfg ext E.genesis_store log n).2.confirmed_root =
        E.weakConfirmed cfg ext v n := by
  let F := replayExecution E.genesis_store log
  have hanchor : E.genesis_store = F.genesis_store := by
    rfl
  have hschedule : ∀ k : ℕ, 0 < k → k ≤ n → E.schedule v k = F.schedule v k := by
    intro k hk hkN
    simpa [F, replayExecution] using (hlog k hk hkN).symm
  have hstore := Execution.store_eq_of_local_log_prefix cfg ext hanchor v v n hschedule
  have hfcr := Execution.weakFcr_eq_of_local_log_prefix cfg ext hanchor v v n hschedule
  have hconfirmed :=
    Execution.weakConfirmed_eq_of_local_log_prefix cfg ext hanchor v v n hschedule
  have hreplay := replay_eq_replayExecution cfg ext E.genesis_store log v n
  have hreplayStore :
      (replay cfg ext E.genesis_store log n).1 = F.store cfg ext v n := by
    simpa [F] using congrArg Prod.fst hreplay
  have hreplayFcr :
      (replay cfg ext E.genesis_store log n).2 = F.weakFcr cfg ext v n := by
    simpa [F] using congrArg Prod.snd hreplay
  have hreplayConfirmed :
      (replay cfg ext E.genesis_store log n).2.confirmed_root =
        F.weakConfirmed cfg ext v n := by
    simpa [F, Execution.weakConfirmed] using
      congrArg FastConfirmationStore.confirmed_root hreplayFcr
  exact ⟨hreplayStore.trans hstore.symm, hreplayFcr.trans hfcr.symm,
    hreplayConfirmed.trans hconfirmed.symm⟩

/-- The pure replay store agrees with the execution store on the supplied
relative-second log prefix. -/
theorem replay_eq_weakStore
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (v : ValidatorIndex) (log : List (List (Event Root))) (n : ℕ)
    (hlog : ∀ k : ℕ, 0 < k → k ≤ n → log.getD (k - 1) [] = E.schedule v k) :
    (replay cfg ext E.genesis_store log n).1 = E.store cfg ext v n := by
  exact (replay_correspondence cfg ext E v log n hlog).1

/-- The pure replay FCR state agrees with the execution's weak FCR state on
the supplied relative-second log prefix. -/
theorem replay_eq_weakFcr
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (v : ValidatorIndex) (log : List (List (Event Root))) (n : ℕ)
    (hlog : ∀ k : ℕ, 0 < k → k ≤ n → log.getD (k - 1) [] = E.schedule v k) :
    (replay cfg ext E.genesis_store log n).2 = E.weakFcr cfg ext v n := by
  exact (replay_correspondence cfg ext E v log n hlog).2.1

/-- The pure replay confirmed root agrees with `Execution.weakConfirmed` on
the supplied relative-second log prefix. -/
theorem replay_eq_weakConfirmed
    (cfg : Config) (ext : Externals Root) (E : Execution Root)
    (v : ValidatorIndex) (log : List (List (Event Root))) (n : ℕ)
    (hlog : ∀ k : ℕ, 0 < k → k ≤ n → log.getD (k - 1) [] = E.schedule v k) :
    (replay cfg ext E.genesis_store log n).2.confirmed_root =
      E.weakConfirmed cfg ext v n := by
  exact (replay_correspondence cfg ext E v log n hlog).2.2

/-- Replay output at relative second `n` depends only on log entries at
indices `0` through `n - 1`, which are the timed events at seconds `1` through
`n`.  Thus appending or changing entries after second `n` has no effect. -/
theorem replay_bounded_witness
    (cfg : Config) (ext : Externals Root) (start : Store Root)
    (log₁ log₂ : List (List (Event Root))) (n : ℕ)
    (hlog : ∀ k : ℕ, k < n → log₁.getD k [] = log₂.getD k []) :
    replay cfg ext start log₁ n = replay cfg ext start log₂ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hprefix : ∀ k : ℕ, k < n → log₁.getD k [] = log₂.getD k [] := by
        intro k hk
        exact hlog k (Nat.lt_succ_of_lt hk)
      have hlast := hlog n (Nat.lt_succ_self n)
      simp only [replay]
      rw [ih hprefix]
      change List.getD log₁ n [] = List.getD log₂ n [] at hlast
      simp only [List.getD] at hlast ⊢
      rw [hlast]

end FastConfirmation.Spec

end
