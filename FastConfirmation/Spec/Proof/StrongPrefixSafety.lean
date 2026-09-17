import FastConfirmation.Spec.Proof.ShellInstantiation
import FastConfirmation.Spec.Proof.AheadFacade
import FastConfirmation.Spec.Proof.ExportWiring
import FastConfirmation.Spec.Proof.FinalWiring
import FastConfirmation.Spec.Proof.Remainder

/-!
# Strong-prefix safety interfaces

Same-slot availability vocabulary and the safety-to-monotonicity bridge for `Spec_Safety`, the
stronger statement that quantifies over every later completed whole-second execution state,
including later states inside the same slot. The accepted public result is instead
`acceptedSpec_safety_next_slot`, exported by `FastConfirmation.Spec.ProvenTheorems`.

What survives here is the part with no dependence on the ahead regime:
`SameSlotFinalizedRootKnown` / `SameSlotFinalizedRootKnownNonGenesis` and their genesis
reduction, the ancestor-comparability lemmas, and `spec_monotonicity_of_safety`
(`Spec_Monotonicity` from `Spec_Safety` plus confirmed-root knownness).

The conditional reductions that stood here — `shellResiduals_of_strongPrefixSafetyInputs`,
`Spec_Safety_of_strongPrefix_inputs`, `Spec_Safety_of_sameSlot_inputs` and the two
`Spec_Monotonicity_of_strongPrefix_inputs*` companions — are deleted with the rest of the
legacy `SpecAssumptions` observed-anchor cone (P-6; see the section notes below). They routed
the observed anchor through `AheadFacade`'s unproduced ahead-regime head-tracking
premise; none of them was an audited witness.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- Additional inputs for the conditional all-prefix `Spec_Safety` reduction. -/
structure StrongPrefixSafetyInputs (E : Execution Root) : Prop where
  /-- The confirming node's finalized root is already known at every honest
      endpoint considered later in the same slot, before next-slot block relay
      applies. -/
  finalized_dom_sameslot : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots
  /-- Every `is_one_confirmed` block carries the parent-linked ancestry chain
      from the justified root required by the fork-choice argument. -/
  dynamics_struct : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.DynamicsChainStruct cfg ext b (n + 1)
  /-- Every parent edge in a confirmed chain satisfies the fork-choice input
      used by the head-safety induction. -/
  fork_edges : ∀ v ∈ E.honest, ∀ n : ℕ, ∀ b : Root,
    is_one_confirmed cfg ext (E.fcrStep cfg ext v n).store
      (get_current_balance_source (E.fcrStep cfg ext v n)) b = true →
    E.ForkEdgeSupply cfg ext b (n + 1)

/-! ### Deleted: `shellResiduals_of_strongPrefixSafetyInputs`

This assembled `ShellInstantiation.ShellResiduals` from `StrongPrefixSafetyInputs`, wiring the
observed-anchor leg through `ExportWiring.observedFilterResiduals_of_interface` and carrying
the ahead-regime head-tracking premise `htracks` explicitly.

It is deleted with the whole legacy `SpecAssumptions` observed-anchor cone (38 declarations,
14 of them unconsumed roots). Nothing ever produced that premise, and the audited
route does not need it: `AcceptedObservedRestartDynamicSafety` proves
`obs.epoch ≤ jc(w, n+1).epoch` at every honest `w`, so the observed anchor never enters the
ahead regime and `E5Filter.head_ge_of_justified_ge_K` closes its `SafeFrom` on its own. See
`docs/p6-justified-descends-derivation.md` §8 and `docs/plumbing-spec-citations.md` P-6. -/

/-- Same-slot availability of the finalized root read at the confirming
update. The premise covers the interval before the next-slot block-relay
deadline. -/
def SameSlotFinalizedRootKnown (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots

/-- Same-slot finalized-root availability restricted to roots not already in
the receiving node's genesis store. -/
def SameSlotFinalizedRootKnownNonGenesis (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ, ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
    E.WithinHorizon cfg m →
    ¬ (E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1)) →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∉ (E.store cfg ext w 0).block_roots →
    (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈ (E.store cfg ext w m).block_roots

/-- Derive full same-slot finalized-root availability. Roots present in the
shared genesis store persist by within-node store monotonicity; all others are
covered by `SameSlotFinalizedRootKnownNonGenesis`. -/
theorem sameSlotFinalizedRootKnown_of_nonGenesis (h : E.SameSlotFinalizedRootKnownNonGenesis cfg ext) :
    E.SameSlotFinalizedRootKnown cfg ext := by
  intro v hv n w hw m hm hH hgate
  by_cases hg : (E.store cfg ext v (n + 1)).finalized_checkpoint.root ∈
      (E.store cfg ext w 0).block_roots
  · exact (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hg
  · exact h v hv n w hw m hm hH hgate hg

end Execution

/-! ## Deleted: the conditional strong-prefix theorems

`Spec_Safety_of_strongPrefix_inputs` and `Spec_Safety_of_sameSlot_inputs` stood here. Each
derived the all-prefix `Spec_Safety` from `StrongPrefixSafetyInputs` while carrying the
unproduced ahead-regime premise `htracks`, and each was an unconsumed root (or fed one) of the
legacy `SpecAssumptions` observed-anchor cone. See the note in place of
`shellResiduals_of_strongPrefixSafetyInputs` above. -/

/-! ## Monotonicity from safety

`Spec_Monotonicity` is the ancestry-comparability of an honest node's confirmed roots at two
times, in the node's own later store. It does **not** need its own weight machinery: safety
already forces every confirmed root onto the honest node's current head-chain, and two
ancestors of one node are comparable. The only genuine input beyond `Spec_Safety` is that the
confirmed roots are *known blocks* — and, since `Spec_Monotonicity` is a **same-node**
statement (`store v m` throughout), that knownness needs only within-node `StoreLE`
monotonicity (`hkc_of_confirmed_known` below), reducing to the single-store confirmed-root
knownness premise `hck` (`E.confirmed v k ∈ (store v k).block_roots`). -/

omit [Inhabited Root] in
/-- **Two ancestors of a common node, the lower slot below.** If `a` and `b` are both
ancestors of `x` and `(blocks a).slot ≤ (blocks b).slot`, then `a` is an ancestor of `b`
(`b ⪰ a`). The walk from `x` down to `b`'s slot lands on `b` (`hb`); continuing it to `a`'s
slot lands on `a` (`ha`) by walk composition (`get_ancestor_comp`) — so the walk from `b` to
`a`'s slot is `a`. Purely the `get_ancestor` composition law; the `WalkKnown` witness is the
walk of `x` down to `a`'s slot. -/
theorem ancestor_comparable_of_common {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a b : Root} (hle : (store.blocks a).slot ≤ (store.blocks b).slot)
    (hwa : WalkKnown store (store.blocks a).slot x)
    (ha : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk a) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk b) = true) :
    is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk a) = true := by
  simp only [is_ancestor, decide_eq_true_eq] at ha hb ⊢
  have hcomp := get_ancestor_comp hwf hle hwa
  rw [hb, ha] at hcomp
  exact hcomp

omit [Inhabited Root] in
/-- **Ancestor comparability.** Two ancestors `a`, `b` of a common node `x` are
ancestry-ordered (`b ⪰ a` or `a ⪰ b`) — the confirmed-root chain is linear. Symmetric
wrapper over `ancestor_comparable_of_common`, dispatching on which slot is lower. -/
theorem ancestor_comparable {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {x a b : Root}
    (hwa : WalkKnown store (store.blocks a).slot x)
    (hwb : WalkKnown store (store.blocks b).slot x)
    (ha : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk a) = true)
    (hb : is_ancestor store (ForkChoiceNode.mk x) (ForkChoiceNode.mk b) = true) :
    is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk a) = true ∨
    is_ancestor store (ForkChoiceNode.mk a) (ForkChoiceNode.mk b) = true := by
  rcases le_total (store.blocks a).slot (store.blocks b).slot with hle | hle
  · exact Or.inl (ancestor_comparable_of_common hwf hle hwa ha hb)
  · exact Or.inr (ancestor_comparable_of_common hwf hle hwb hb ha)

/-- **Confirmed-root knownness over a time span, from the single-store fact.** The
`Spec_Monotonicity` premise `hkc` — an honest node's confirmed root at time `k` is a known
block in its **own** store at every later time `m ≥ k` — reduces, with **no** cross-node
`block_relay`, to the single-store confirmed-root knownness `hck` (`confirmed v k ∈
(store v k).block_roots`) by within-node `StoreLE` monotonicity (`store_storeLE`, the
`block_roots ⊆` leg). This is tighter than the cross-node relay: `Spec_Monotonicity` is a
same-node statement, so the confirmed root never has to gossip anywhere. `hck` is a
`get_latest_confirmed` store invariant (its result is `confirmed_root`,
the finalized root, or an `is_one_confirmed` balance-source descendant — all in `block_roots`),
in the same knownness family as `JustificationInterface.checkpoint_known`. -/
theorem hkc_of_confirmed_known
    (hck : ∀ F : Execution Root, SpecAssumptions cfg ext F → ∀ v ∈ F.honest, ∀ k : ℕ,
      F.WithinHorizon cfg k →
      F.confirmed cfg ext v k ∈ (F.store cfg ext v k).block_roots) :
    ∀ F : Execution Root, SpecAssumptions cfg ext F → ∀ v ∈ F.honest, ∀ k m : ℕ, k ≤ m →
      F.WithinHorizon cfg m →
      F.confirmed cfg ext v k ∈ (F.store cfg ext v m).block_roots :=
  fun F hSA v hv k _m hkm hH =>
    (F.store_storeLE cfg ext v hkm).1
      (hck F hSA v hv k (F.withinHorizon_mono cfg hkm hH))

/-- **`Spec_Monotonicity` from `Spec_Safety` and confirmed-root knownness.**

Given the safety guarantee and the knownness premise `hkc` (an honest node's confirmed
root at time `k` is a known block at every later store `m ≥ k` — the block-relay-family fact
`checkpoint_known` covers for realized checkpoints), `Spec_Monotonicity` follows with **no**
extra weight argument: at store `(v, m)` both `confirmed(v, n)` and `confirmed(v, m)` are
ancestors of the current head (safety, applied at `n ≤ m` and at `m ≤ m`), and
`ancestor_comparable` orders them. The fork-choice walk domain (`hwf`/`hwalkK`) and head
knownness come Layer-0 from `SpecAssumptions` (`store_domainK` + `get_head_root_mem_or`). -/
theorem spec_monotonicity_of_safety (hsafe : Spec_Safety cfg ext)
    (hkc : ∀ E : Execution Root, SpecAssumptions cfg ext E → ∀ v ∈ E.honest, ∀ k m : ℕ, k ≤ m →
      E.WithinHorizon cfg m →
      E.confirmed cfg ext v k ∈ (E.store cfg ext v m).block_roots) :
    Spec_Monotonicity cfg ext := by
  intro E hSA v hv n m hnm hH
  obtain ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩ := hSA
  have hSA : SpecAssumptions cfg ext E := ⟨hgen, hwfE, hdiv, hhb, hsync, hec, hsv, hbb, hji⟩
  obtain ⟨hwf, hwalkK, hjust⟩ :=
    E.store_domainK cfg ext hwfE hec hgen hji v hv m hH
  have hhead : (get_head cfg (E.store cfg ext v m)).root ∈ (E.store cfg ext v m).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v m) with h | h
    · exact h
    · rw [h]; exact hjust
  have ha : E.confirmed cfg ext v n ∈ (E.store cfg ext v m).block_roots :=
    hkc E hSA v hv n m hnm hH
  have hb : E.confirmed cfg ext v m ∈ (E.store cfg ext v m).block_roots :=
    hkc E hSA v hv m m (le_refl _) hH
  have hA := hsafe E hSA v hv n v hv m hnm hH
  have hB := hsafe E hSA v hv m v hv m (le_refl _) hH
  exact ancestor_comparable hwf
    (hwalkK _ ha _ hhead) (hwalkK _ hb _ hhead) hA hB

/-! ### Deleted: `Spec_Monotonicity_of_strongPrefix_inputs` and
`Spec_Monotonicity_of_strongPrefix_inputs_of_confirmed_known`

Both composed `spec_monotonicity_of_safety` on `Spec_Safety_of_strongPrefix_inputs`, and both
carried the ahead-regime head-tracking premise `htracks`. They go with the rest of the
legacy `SpecAssumptions` observed-anchor cone; see the note in place of
`shellResiduals_of_strongPrefixSafetyInputs` above. -/

end FastConfirmation.Spec
