module
public import FastConfirmation.Spec.Proof.DynamicsClosure
public import FastConfirmation.Spec.Proof.EngineStore
public import FastConfirmation.Spec.Proof.FilterViability
public import FastConfirmation.Spec.Proof.FCRCallContracts
public import FastConfirmation.Spec.TheoremStatements
public import FastConfirmation.Spec.Internal.Legacy.Vocabulary

public import FastConfirmation.Spec.Statements.Premises.Execution
@[expose] public section

/-!
# Spec / Proof / L4Fold: the algorithm fold and reset branches

This module combines the head-safety engine
(`HeadSafetyEngine.spec_head_safety_engine`, fed through
`ChainInput.ledgerChainInput_of_certificates`) with
`EngineStore.head_ge_of_justified_ge`. It first proves safety of the block
returned by `get_latest_confirmed`, then follows the confirmed root along the FCR
trajectory to obtain `Spec_Safety`.

* **Section 1 — `SafeFrom` and engine composition.** `SafeFrom E b n` means that
  from second `n` onward every honest head descends from `b`.
  `safeFrom_of_certificates` composes `spec_head_safety_engine` with
  `ledgerChainInput_of_certificates` and converts `EngineInv` to `SafeFrom`.

* **Section 2 — reset anchors.** If an anchor `r₀` lies on every honest store's
  justified chain, `head_ge_of_justified_ge` puts every honest head above `r₀`.
  `safeFrom_of_justified_dom` lifts this fact to `SafeFrom`, while
  `head_ge_finalized_of_interface` handles a store's finalized checkpoint using
  `finalized_justified_ancestry`.

* **Section 3 — loop inversions.** Theorems for the two
  `find_latest_confirmed_descendant` loops, their wrapper, and
  `get_latest_confirmed` show that a result is either a reset anchor or a block
  that passed `is_one_confirmed`.

* **Section 4 — trajectory induction.** Between slot updates `E.confirmed` is
  constant; at a slot update it is `get_latest_confirmed`. `L4Residual` supplies
  safety for the reset anchors and for blocks that pass `is_one_confirmed`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — `SafeFrom` and the engine composition

`SafeFrom E b n` states that from second `n` on, `b` is an ancestor of every
honest node's fork-choice head.
`EngineInv cfg ext E b n k` (`EngineInduction.lean`) is the same statement *capped
at cutoff slot `k`*; `spec_head_safety_engine` produces it for **every** `k`, so
`SafeFrom` is the `∀ k` collapse — instantiate `k := E.slot_at cfg m` at each
endpoint second `m`. -/

/-- **`EngineInv` (all cutoffs) ⟹ `SafeFrom`.** Each endpoint second `m` sits at
cutoff slot `E.slot_at cfg m`; the engine invariant at that cutoff, applied with
`E.slot_at cfg m ≤ E.slot_at cfg m`, gives head descent. The slot-slice collapse. -/
theorem safeFrom_of_engineInv {b : Root} {n₀ : ℕ}
    (heng : ∀ k : Slot, EngineInv cfg ext E b n₀ k) :
    E.SafeFrom cfg ext b n₀ :=
  fun w hw m hm hH => heng (E.slot_at cfg m) w hw m hm (le_refl _) hH


/-! ## Section 2 — finalized and observed-justified reset anchors

The finalized / observed-justified reset branches of `get_latest_confirmed`
(`get_latest_confirmed_spec`'s left disjuncts) need no engine: once the anchor
`r₀` is on every honest store's justified chain, the FFG-takeover head lemma
`EngineStore.head_ge_of_justified_ge` puts every honest head above `r₀` with no
LMD margin. `safeFrom_of_justified_dom` lifts that per-store lemma to `SafeFrom`.
`head_ge_finalized_of_interface` derives the single-store finalized direction
from `finalized_justified_ancestry`. -/



end Execution

/-! ## Section 3 — loop inversions

Structural characterizations of the two `find_latest_confirmed_descendant` loops,
their wrapper, and `get_latest_confirmed`. The invariant every inversion exposes:
the returned root is the input accumulator `r₀`, or a block that **passed
`is_one_confirmed`** at the querying store with `get_current_balance_source`.
These results follow by recursion on `canonical_roots`. -/

/-- Cons-case unfold of the prev-epoch loop (`rfl`; `let`s zeta-reduce). An
explicit equation lemma so the inversion uses `by_cases` + `if_pos`/`if_neg`
rather than `split_ifs`, which would split both sides of the disjunctive goal. -/
private theorem prev_epoch_loop_cons_eq (fcr_store : FastConfirmationStore Root)
    (ce : Epoch) (b : Root) (rest : List Root) (acc : Root) :
    find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b = ce then acc
       else if ¬ is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
              (get_node_for_root b) then acc
       else if ¬ is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce rest b) :=
  rfl

/-- **Prev-epoch loop inversion.** The first `find_latest_confirmed_descendant`
loop returns the input accumulator `acc`, or a list element `r` that passed
`is_one_confirmed` at `fcr_store.store` with `get_current_balance_source`. Structural
recursion: every advance step is guarded by the `is_one_confirmed` gate, so the
final root — reached by advancing — carries the gate's witness. -/
theorem prev_epoch_loop_spec (fcr_store : FastConfirmationStore Root)
    (ce : Epoch) :
    ∀ (roots : List Root) (acc : Root),
      find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc = acc ∨
      ∃ r, r ∈ roots ∧
        find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc = r ∧
        is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) r = true := by
  intro roots
  induction roots with
  | nil => intro acc; left; rfl
  | cons b rest ih =>
    intro acc
    rw [prev_epoch_loop_cons_eq]
    by_cases h1 : get_block_epoch cfg fcr_store.store b = ce
    · rw [if_pos h1]; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h2 : is_ancestor fcr_store.store (get_node_for_root fcr_store.previous_slot_head)
          (get_node_for_root b) = true
      · rw [if_neg (not_not_intro h2)]
        by_cases h3 : is_one_confirmed cfg ext fcr_store.store
            (get_current_balance_source fcr_store) b = true
        · rw [if_neg (not_not_intro h3)]
          rcases ih b with hacc | ⟨r, hr, heq, hrc⟩
          · exact Or.inr ⟨b, List.mem_cons_self, hacc, h3⟩
          · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, heq, hrc⟩
        · rw [if_pos h3]; exact Or.inl rfl
      · rw [if_pos h2]; exact Or.inl rfl

/-- Cons-case unfold of the tentative loop (`rfl`; `let`s zeta-reduce). -/
private theorem tentative_loop_cons_eq (fcr_store : FastConfirmationStore Root)
    (b : Root) (rest : List Root) (acc : Root) :
    find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store (b :: rest) acc =
      (if get_block_epoch cfg fcr_store.store b > get_block_epoch cfg fcr_store.store acc ∧
            ¬ will_current_target_be_justified cfg ext fcr_store.store then acc
       else if ¬ is_one_confirmed cfg ext fcr_store.store
              (get_current_balance_source fcr_store) b then acc
       else find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store rest b) :=
  rfl

/-- **Tentative loop inversion.** The second `find_latest_confirmed_descendant`
loop returns the input accumulator `acc`, or a list element `r` that passed
`is_one_confirmed`. Same structure as `prev_epoch_loop_spec`; the extra
`will_current_target_be_justified` gate only *blocks* an advance,
never manufactures one, so the `is_one_confirmed` witness on the result is
unaffected. -/
theorem tentative_loop_spec (fcr_store : FastConfirmationStore Root) :
    ∀ (roots : List Root) (acc : Root),
      find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc = acc ∨
      ∃ r, r ∈ roots ∧
        find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc = r ∧
        is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) r = true := by
  intro roots
  induction roots with
  | nil => intro acc; left; rfl
  | cons b rest ih =>
    intro acc
    rw [tentative_loop_cons_eq]
    by_cases h1 : get_block_epoch cfg fcr_store.store b >
          get_block_epoch cfg fcr_store.store acc ∧
        ¬ will_current_target_be_justified cfg ext fcr_store.store
    · rw [if_pos h1]; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h2 : is_one_confirmed cfg ext fcr_store.store
          (get_current_balance_source fcr_store) b = true
      · rw [if_neg (not_not_intro h2)]
        rcases ih b with hacc | ⟨r, hr, heq, hrc⟩
        · exact Or.inr ⟨b, List.mem_cons_self, hacc, h2⟩
        · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, heq, hrc⟩
      · rw [if_pos h2]; exact Or.inl rfl



/-! ## Section 4 — trajectory induction

`SafeFrom` threaded across seconds to `∀ v n, SafeFrom (E.confirmed v n) n` — the
core of `Spec_Safety`. The FCR handler runs once per slot: between slot updates
`E.confirmed` is constant, so a `SafeFrom` witness persists; at a slot update
`E.confirmed` is `get_latest_confirmed`, whose result (`get_latest_confirmed_spec`)
is a reset anchor or an advance-confirmed block. The reset-to-previous-confirmed
case uses the trajectory IH (`SafeFrom.mono`); the finalized and
observed-justified anchors and the advance are supplied by `L4Residual`. -/

namespace Execution

variable (E : Execution Root)

/-- `SafeFrom` is monotone forward in the base second: a witness from `n` still
holds from any `n' ≥ n` (the endpoint interval only shrinks). -/
theorem SafeFrom.mono {b : Root} {n n' : ℕ} (h : E.SafeFrom cfg ext b n) (hn : n ≤ n') :
    E.SafeFrom cfg ext b n' :=
  fun w hw m hm hH => h w hw m (le_trans hn hm) hH

/-- Genesis confirmed root: `get_fast_confirmation_store` seeds it at the anchor's
finalized root. -/
theorem confirmed_zero (v : ValidatorIndex) :
    E.confirmed cfg ext v 0 = (E.store cfg ext v 0).finalized_checkpoint.root := rfl

/-- Between slot updates the confirmed root is constant: if the wall clock has not
advanced a slot at second `n+1`, `on_fast_confirmation` does not run and
`E.confirmed` carries over. -/
theorem confirmed_succ_of_no_advance (v : ValidatorIndex) (n : ℕ)
    (h : ¬ get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    E.confirmed cfg ext v (n + 1) = E.confirmed cfg ext v n := by
  simp only [Execution.confirmed, Execution.fcr]
  rw [if_neg h]

/-- At a slot update the confirmed root is `get_latest_confirmed` of `fcrStep`. -/
theorem confirmed_succ_of_advance (v : ValidatorIndex) (n : ℕ)
    (h : get_current_slot cfg (E.store cfg ext v (n + 1)) >
      get_current_slot cfg (E.store cfg ext v n)) :
    E.confirmed cfg ext v (n + 1) = get_latest_confirmed cfg ext (E.fcrStep cfg ext v n) := by
  simp only [Execution.confirmed, Execution.fcr]
  rw [if_pos h]
  rfl




end Execution

/-! ## Section 5 — `Spec_Safety` from `L4Residual`

`Spec_Safety`'s conclusion at `(E, v, n, w, m)` is exactly
`E.SafeFrom (E.confirmed v n) n` applied at `(w, m)`. `confirmed_safeFrom_of_residual`
provides it for every honest `(v, n)` under `L4Residual`. -/




end FastConfirmation.Spec

end
