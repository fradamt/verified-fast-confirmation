module
public import FastConfirmation.Spec.Proof.WeakFCRCallContracts

@[expose] public section

/-!
# Local replay determines the weak confirmation output

These equalities require no network, honesty, or protocol-safety assumptions.
For fixed configuration and external functions, the trusted starting store and
the observer's finite event-log prefix determine its store and weak FCR output.
Other nodes' logs, the honest set, the ground vote record, and the verification
horizon do not enter the computation. Time is logical: the anchor time plus
the relative second index.

This is a dependence theorem, not a safety theorem for arbitrary input data.
Safety still requires the replay's authenticated inputs and model assumptions.
-/

namespace FastConfirmation.Spec.Execution

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- Matching local input prefixes produce matching fork-choice stores.
The execution model ignores events at relative second zero. -/
theorem store_eq_of_local_log_prefix {E F : Execution Root}
    (hanchor : E.genesis_store = F.genesis_store) (v w : ValidatorIndex) :
    ∀ n : ℕ,
      (∀ k : ℕ, 0 < k → k ≤ n → E.schedule v k = F.schedule w k) →
      E.store cfg ext v n = F.store cfg ext w n := by
  intro n
  induction n with
  | zero =>
      intro _
      exact hanchor
  | succ n ih =>
      intro hlog
      have hprevious := ih (fun k hk hkn => hlog k hk (hkn.trans (Nat.le_succ n)))
      have hevents := hlog (n + 1) (Nat.succ_pos n) (le_refl _)
      simp only [Execution.store, hprevious, hevents, Execution.time_at, hanchor]

/-- Matching local input prefixes produce matching weak FCR stores. -/
theorem weakFcr_eq_of_local_log_prefix {E F : Execution Root}
    (hanchor : E.genesis_store = F.genesis_store) (v w : ValidatorIndex) :
    ∀ n : ℕ,
      (∀ k : ℕ, 0 < k → k ≤ n → E.schedule v k = F.schedule w k) →
      E.weakFcr cfg ext v n = F.weakFcr cfg ext w n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [Execution.weakFcr, Execution.store, hanchor]
  | succ n ih =>
      intro hlog
      have hprefix : ∀ k : ℕ, 0 < k → k ≤ n → E.schedule v k = F.schedule w k :=
        fun k hk hkn => hlog k hk (hkn.trans (Nat.le_succ n))
      have hprevious := ih hprefix
      have hstorePrevious := store_eq_of_local_log_prefix cfg ext hanchor v w n hprefix
      have hstoreNext := store_eq_of_local_log_prefix cfg ext hanchor v w (n + 1) hlog
      simp only [Execution.weakFcr, hprevious, hstorePrevious, hstoreNext]

/-- The confirmed root depends only on the anchor and the finite local log.
No synchrony or observer-honesty hypothesis is needed for this equality. -/
theorem weakConfirmed_eq_of_local_log_prefix {E F : Execution Root}
    (hanchor : E.genesis_store = F.genesis_store) (v w : ValidatorIndex)
    (n : ℕ)
    (hlog : ∀ k : ℕ, 0 < k → k ≤ n → E.schedule v k = F.schedule w k) :
    E.weakConfirmed cfg ext v n = F.weakConfirmed cfg ext w n := by
  exact congrArg FastConfirmationStore.confirmed_root
    (weakFcr_eq_of_local_log_prefix cfg ext hanchor v w n hlog)

end FastConfirmation.Spec.Execution

end
