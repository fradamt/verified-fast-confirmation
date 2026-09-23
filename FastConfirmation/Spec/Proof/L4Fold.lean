module
public import FastConfirmation.Spec.Proof.DynamicsClosure
public import FastConfirmation.Spec.Proof.EngineStore
public import FastConfirmation.Spec.Proof.FilterViability
public import FastConfirmation.Spec.Proof.FCRCallContracts
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

/-- **`SafeFrom` from the certificate functional.** The full engine composition:
the cert-level chain functional `LedgerChainInputCert` (`ChainInput.lean`) lifts to
`LedgerChainInput` (`ledgerChainInput_of_certificates`), which
`spec_head_safety_engine` turns into `EngineInv` at every cutoff and hence
`SafeFrom`. -/
theorem safeFrom_of_certificates {b : Root} {n₀ : ℕ}
    (hcert : LedgerChainInputCert cfg ext E b n₀) :
    E.SafeFrom cfg ext b n₀ :=
  E.safeFrom_of_engineInv cfg ext
    (spec_head_safety_engine cfg ext (ledgerChainInput_of_certificates cfg ext hcert))

/-! ## Section 2 — finalized and observed-justified reset anchors

The finalized / observed-justified reset branches of `get_latest_confirmed`
(`get_latest_confirmed_spec`'s left disjuncts) need no engine: once the anchor
`r₀` is on every honest store's justified chain, the FFG-takeover head lemma
`EngineStore.head_ge_of_justified_ge` puts every honest head above `r₀` with no
LMD margin. `safeFrom_of_justified_dom` lifts that per-store lemma to `SafeFrom`.
`head_ge_finalized_of_interface` derives the single-store finalized direction
from `finalized_justified_ancestry`. -/

/-- **`SafeFrom` from justified dominance.** If at every honest `(w, m)` past
`n₀` the store's fork-choice domain conditions hold (`parent_slot_lt` `hwf`, the
`WalkKnown` domain `hwalk`, justified-known `hjust`) and `r₀` is on the store's
justified chain (`hjb : justified ⪰ r₀`), then `r₀` is on every honest head from
`n₀` on. Per store this is `head_ge_of_justified_ge`. -/
theorem safeFrom_of_justified_dom {r₀ : Root} {n₀ : ℕ}
    (hdom : ∀ w ∈ E.honest, ∀ m : ℕ, n₀ ≤ m →
      E.WithinHorizon cfg m →
      (∀ r ∈ (E.store cfg ext w m).block_roots,
          ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
            ((E.store cfg ext w m).blocks
                ((E.store cfg ext w m).blocks r).parent_root).slot
              < ((E.store cfg ext w m).blocks r).slot) ∧
        (∀ t r : Root, r ∈ (E.store cfg ext w m).block_roots →
          WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r) ∧
        (E.store cfg ext w m).justified_checkpoint.root ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root r₀) = true) :
    E.SafeFrom cfg ext r₀ n₀ := by
  intro w hw m hm hH
  obtain ⟨hwf, hwalk, hjust, hjb⟩ := hdom w hw m hm hH
  exact head_ge_of_justified_ge cfg hwf hwalk hjust hjb

/-- **Finalized takeover at a single honest store.** At any
honest `(w, m)` with the fork-choice domain conditions and both checkpoints known,
`finalized_justified_ancestry` puts the finalized block on the justified chain, so
`head_ge_of_justified_ge` puts it on the head. A `SafeFrom` statement for a fixed
root additionally requires cross-store tracking of that finalized root. -/
theorem head_ge_finalized_of_interface (hji : JustificationInterface cfg ext E)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ)
    (hH : E.WithinHorizon cfg m)
    (hwf : ∀ r ∈ (E.store cfg ext w m).block_roots,
        ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
          ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot
            < ((E.store cfg ext w m).blocks r).slot)
    (hwalk : ∀ t r : Root, r ∈ (E.store cfg ext w m).block_roots →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks t).slot r)
    (hjust : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hfin : (E.store cfg ext w m).finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots) :
    is_ancestor (E.store cfg ext w m) (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.store cfg ext w m).finalized_checkpoint.root) = true :=
  head_ge_of_justified_ge cfg hwf hwalk hjust
    (hji.finalized_justified_ancestry w hw m hH hfin hjust)

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

/-- **`find_latest_confirmed_descendant` inversion.** The wrapper
returns the input `latest_confirmed_root` or a block that passed `is_one_confirmed`
at the querying store. Both advancement stages preserve the "is `lcr` or confirmed"
predicate: the prev-epoch stage advances only through the first loop
(`prev_epoch_loop_spec`), the tentative stage only through the second
(`tentative_loop_spec`) followed by a gate that either keeps its accumulator or
selects the loop's confirmed output; every leaf lands in the predicate. -/
theorem find_latest_confirmed_descendant_spec (fcr_store : FastConfirmationStore Root)
    (lcr : Root) :
    find_latest_confirmed_descendant cfg ext fcr_store lcr = lcr ∨
    is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store)
      (find_latest_confirmed_descendant cfg ext fcr_store lcr) = true := by
  -- "is `lcr`, or confirmed at (store, current balance source)"
  set P : Root → Prop := fun r => r = lcr ∨
    is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) r = true
    with hP
  -- closure of `P` under each advancing loop
  have hprev : ∀ (ce : Epoch) (roots : List Root) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_prev_epoch_loop cfg ext fcr_store ce roots acc) := by
    intro ce roots acc hacc
    rcases prev_epoch_loop_spec cfg ext fcr_store ce roots acc with h | ⟨_, _, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ hc)
  have htent : ∀ (roots : List Root) (acc : Root), P acc →
      P (find_latest_confirmed_descendant_tentative_loop cfg ext fcr_store roots acc) := by
    intro roots acc hacc
    rcases tentative_loop_spec cfg ext fcr_store roots acc with h | ⟨_, _, heq, hc⟩
    · rw [hP]; rw [h]; exact hacc
    · exact Or.inr (heq ▸ hc)
  change P (find_latest_confirmed_descendant cfg ext fcr_store lcr)
  generalize hX : find_latest_confirmed_descendant cfg ext fcr_store lcr = X
  rw [find_latest_confirmed_descendant] at hX
  simp only at hX
  -- both advancement stages preserve `P` from the `P lcr` base
  split_ifs at hX with hc1 hc2 hc3 hc4 hc5 <;>
    subst hX <;>
      first
      | exact Or.inl rfl
      | (apply htent; first | exact Or.inl rfl | exact hprev _ _ _ (Or.inl rfl))
      | exact hprev _ _ _ (Or.inl rfl)

/-- **`get_latest_confirmed` inversion.** The block the FCR
returns is one of the three reset anchors — the previous confirmed root, the
finalized root, or the current-epoch observed-justified root — or a block that
passed `is_one_confirmed` through `find_latest_confirmed_descendant`. -/
theorem get_latest_confirmed_spec (fcr_store : FastConfirmationStore Root) :
    (get_latest_confirmed cfg ext fcr_store = fcr_store.confirmed_root ∨
      get_latest_confirmed cfg ext fcr_store = fcr_store.store.finalized_checkpoint.root ∨
      get_latest_confirmed cfg ext fcr_store =
        fcr_store.current_epoch_observed_justified_checkpoint.root) ∨
    is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store)
      (get_latest_confirmed cfg ext fcr_store) = true := by
  -- "is a reset anchor, or confirmed at (store, current balance source)"
  set Q : Root → Prop := fun r =>
    (r = fcr_store.confirmed_root ∨ r = fcr_store.store.finalized_checkpoint.root ∨
      r = fcr_store.current_epoch_observed_justified_checkpoint.root) ∨
    is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) r = true
    with hQ
  -- the advance keeps a reset-anchor input inside `Q`
  have hadv : ∀ lcr : Root,
      (lcr = fcr_store.confirmed_root ∨ lcr = fcr_store.store.finalized_checkpoint.root ∨
        lcr = fcr_store.current_epoch_observed_justified_checkpoint.root) →
      Q (find_latest_confirmed_descendant cfg ext fcr_store lcr) := by
    intro lcr hlcr
    rcases find_latest_confirmed_descendant_spec cfg ext fcr_store lcr with h | hc
    · exact Or.inl (by rw [h]; exact hlcr)
    · exact Or.inr hc
  change Q (get_latest_confirmed cfg ext fcr_store)
  generalize hX : get_latest_confirmed cfg ext fcr_store = X
  simp only [get_latest_confirmed] at hX
  split_ifs at hX <;>
    subst hX <;>
      first
      | exact Or.inl (Or.inl rfl)
      | exact Or.inl (Or.inr (Or.inl rfl))
      | exact Or.inl (Or.inr (Or.inr rfl))
      | exact hadv _ (Or.inl rfl)
      | exact hadv _ (Or.inr (Or.inl rfl))
      | exact hadv _ (Or.inr (Or.inr rfl))

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

/-- **`SafeFrom` of `get_latest_confirmed`.** If the input
confirmed root, the store's finalized root, the observed-justified anchor are all
`SafeFrom n`, and every `is_one_confirmed` block is `SafeFrom n`, then the block
`get_latest_confirmed` returns is `SafeFrom n`. Pure case split on
`get_latest_confirmed_spec`: each reset anchor routes to its `SafeFrom` witness, the
advance routes to the engine one. -/
theorem safeFrom_get_latest_confirmed {fcr_store : FastConfirmationStore Root} {n : ℕ}
    (hprev : E.SafeFrom cfg ext fcr_store.confirmed_root n)
    (hfin : E.SafeFrom cfg ext fcr_store.store.finalized_checkpoint.root n)
    (hobs : E.SafeFrom cfg ext
      fcr_store.current_epoch_observed_justified_checkpoint.root n)
    (heng : ∀ b : Root,
      is_one_confirmed cfg ext fcr_store.store (get_current_balance_source fcr_store) b = true →
      E.SafeFrom cfg ext b n) :
    E.SafeFrom cfg ext (get_latest_confirmed cfg ext fcr_store) n := by
  rcases get_latest_confirmed_spec cfg ext fcr_store with (h | h | h) | h
  · rw [h]; exact hprev
  · rw [h]; exact hfin
  · rw [h]; exact hobs
  · exact heng _ h

/-- **Inputs for the trajectory induction.** The named store-dynamics facts
the trajectory skeleton cannot discharge internally, in existing shapes:

* `genesis_safe` — the anchor's finalized root is `SafeFrom 0`;
* `finalized_safe` — at each slot update the current finalized root is safe;
* `observed_safe` — at each slot update the rotated observed-justified anchor is
  safe;
* `advance_safe` — every `is_one_confirmed` block at the update store is safe (the
  input supplied by `safeFrom_of_certificates` from a
  `LedgerChainInputCert`). -/
structure L4Residual (E : Execution Root) : Prop where
  /-- The anchor's finalized root is safe from second 0. -/
  genesis_safe : ∀ v ∈ E.honest,
    E.SafeFrom cfg ext (E.store cfg ext v 0).finalized_checkpoint.root 0
  /-- The finalized reset anchor is safe at every slot-update second. -/
  finalized_safe : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.SafeFrom cfg ext (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1)
  /-- The observed-justified restart anchor is safe at every slot update. -/
  observed_safe : ∀ v ∈ E.honest, ∀ n : ℕ,
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root (n + 1)
  /-- engine: any block that passes `is_one_confirmed` at a slot-update store is
      safe (the `LedgerChainInputCert` discharge per confirmed chain block). -/
  advance_safe : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.SafeFrom cfg ext b (n + 1)

/-- **The trajectory induction.** Under `L4Residual`, every honest
node's confirmed root at every second is `SafeFrom` that second. Induction on the
second `n`: the genesis root rides `genesis_safe`; at a non-update second the
confirmed root is unchanged (`confirmed_succ_of_no_advance`) so the IH carries
forward; at a slot update it is `get_latest_confirmed` of `fcrStep`, handled by
`safeFrom_get_latest_confirmed` — the previous confirmed root from the IH (its
`SafeFrom n` widened to `n+1`), the reset anchors and the advance from the
residual. -/
theorem confirmed_safeFrom_of_residual (hres : E.L4Residual cfg ext)
    (v : ValidatorIndex) (hv : v ∈ E.honest) :
    ∀ n : ℕ, E.SafeFrom cfg ext (E.confirmed cfg ext v n) n := by
  intro n
  induction n with
  | zero => rw [E.confirmed_zero]; exact hres.genesis_safe v hv
  | succ n ih =>
    by_cases h : get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n)
    · rw [E.confirmed_succ_of_advance cfg ext v n h]
      refine E.safeFrom_get_latest_confirmed cfg ext ?_
        (hres.finalized_safe v hv n) (hres.observed_safe v hv n) (hres.advance_safe v hv n)
      rw [E.fcrStep_confirmed_root]
      exact fun w hw m hm hH => ih w hw m (le_trans (Nat.le_succ n) hm) hH
    · rw [E.confirmed_succ_of_no_advance cfg ext v n h]
      exact fun w hw m hm hH => ih w hw m (le_trans (Nat.le_succ n) hm) hH

end Execution

/-! ## Section 5 — `Spec_Safety` from `L4Residual`

`Spec_Safety`'s conclusion at `(E, v, n, w, m)` is exactly
`E.SafeFrom (E.confirmed v n) n` applied at `(w, m)`. `confirmed_safeFrom_of_residual`
provides it for every honest `(v, n)` under `L4Residual`. -/

/-- **`Spec_Safety` from the fold residual.** Under a proof that `SpecAssumptions`
supplies `L4Residual` for every execution,
the FCR's safety guarantee holds. The trajectory fold (`confirmed_safeFrom_of_residual`)
turns the per-execution residual into per-`(v, n)` `SafeFrom`, whose unfolding is
`Spec_Safety`'s conclusion. -/
theorem spec_safety_of_residual
    (hres : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.L4Residual cfg ext) :
    Spec_Safety cfg ext := by
  intro E hSA v hv n w hw m hm hH
  exact E.confirmed_safeFrom_of_residual cfg ext (hres E hSA) v hv n w hw m hm hH

/-- The pinned current-moment guarantee implies the weaker next-slot corollary.
This direction is deliberately one-way: proving the corollary alone does not
discharge the same-slot cases required by `Spec_Safety`. -/
theorem spec_safety_next_slot_of_safety (hsafe : Spec_Safety cfg ext) :
    Spec_Safety_next_slot cfg ext := by
  intro E hSA v hv n w hw m hm _hnext hH
  exact hsafe E hSA v hv n w hw m hm hH

/-- The current-moment residual proof immediately yields the separately named
next-slot corollary by discarding its additional timing premise. -/
theorem spec_safety_next_slot_of_residual
    (hres : ∀ E : Execution Root, SpecAssumptions cfg ext E → E.L4Residual cfg ext) :
    Spec_Safety_next_slot cfg ext :=
  spec_safety_next_slot_of_safety cfg ext (spec_safety_of_residual cfg ext hres)

end FastConfirmation.Spec

end
