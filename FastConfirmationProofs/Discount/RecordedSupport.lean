module
public import FastConfirmationProofs.ForkChoice.Head.HeadMembership
public import FastConfirmationProofs.Execution.Delivery.Delivery
public import FastConfirmationProofs.ForkChoice.Head.SupportTransport
public import FastConfirmationProofs.FFG.Certificates.QuorumAccounting

@[expose] public section

/-!
# Spec / Proof / EngineSupport

This module contains `mem_AttSupporters_of`, `supports_of_ge_b`, `mem_AttSupporters_honest` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The supporter-list membership constructor -/

omit [Inhabited Root] in
/-- Reverse of `QuorumAccounting.mem_AttSupporters`: a validator that is active
in the balance source, unslashed, non-equivocating, and whose recorded latest
message supports `node` sits in the supporter list. -/
theorem mem_AttSupporters_of {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex} {lm : LatestMessage Root}
    (hact : i ∈ get_active_validator_indices state (get_current_epoch cfg state))
    (huns : (state.validators.getD i default).slashed = false)
    (hlm : store.latest_messages i = some lm)
    (hne : i ∉ store.equivocating_indices)
    (hsupp : is_ancestor store (get_supported_node store lm) node = true) :
    i ∈ AttSupporters cfg store node state := by
  simp only [AttSupporters, List.mem_filter]
  refine ⟨⟨hact, ?_⟩, ?_⟩
  · rw [huns]; rfl
  · simp only [hlm, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hne, hsupp⟩

/-! ## Active / unslashed projections out of a supporter membership -/



/-! ## Reconciliation (b): active / unslashed transport across balance sources

Two balance sources on the ground registry (`StaticValidatorSet`) agree on the
active-validator list — the range length is the registry length on both, and
activity is epoch-independent (`registry_activity_constant`), so the per-index
filter predicates coincide even at different current epochs. Slashed status is
read off the same registry entry. This moves the confirmation-time activity
facts of `HS₀` (extracted from its `v/n₀` supporter membership) to the later
store `(w, m)`'s balance source. -/





/-! ## The `SupportTransport` bridge: `⪰ b` supports every chain child `c ≼ b` -/

omit [Inhabited Root] in
/-- A recorded latest message whose root descends from `b` (`lm.root ⪰ b`, the
engine IH's conclusion) supports every chain child `c` of `b` (`c ≼ b`), via
`SupportTransport.supporter_of_ancestor`. The `WalkKnown` witnesses pin both
parent-walks down to `c`'s slot. -/
theorem supports_of_ge_b {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {b c : Root} {lm : LatestMessage Root}
    (hwa : WalkKnown store (store.blocks c).slot lm.root)
    (hwb : WalkKnown store (store.blocks c).slot b)
    (hge : is_ancestor store (ForkChoiceNode.mk lm.root .pending) (ForkChoiceNode.mk b .pending) = true)
    (hcb : is_ancestor store (ForkChoiceNode.mk b .pending) (ForkChoiceNode.mk c .pending) = true) :
    is_ancestor store (get_supported_node store lm) (get_node_for_root c) = true := by
  unfold get_supported_node
  rw [is_ancestor_pending_root_eq store lm.root c _ .pending]
  exact supporter_of_ancestor hwf hwa hwb hge hcb

/-! ## Honest supporter membership at the later store -/

/-- **Honest membership.** At an honest store `(w, m)`, an honest validator `i`
that is active and unslashed in the balance source and whose recorded latest
message supports `node` sits in `AttSupporters`. Non-equivocation is discharged
by `Execution.honest_not_equivocating` (honest validators never enter
`equivocating_indices`); the other three facts are supplied by the caller. -/
theorem mem_AttSupporters_honest {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {bs : BeaconState Root} {node : ForkChoiceNode Root}
    {i : ValidatorIndex} {lm : LatestMessage Root}
    (hi : i ∈ E.honest)
    (hact : i ∈ get_active_validator_indices bs (get_current_epoch cfg bs))
    (huns : (bs.validators.getD i default).slashed = false)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) node = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    i ∈ AttSupporters cfg (E.store cfg ext w m) node bs := by
  have hne : i ∉ (E.store cfg ext w m).equivocating_indices :=
    Execution.honest_not_equivocating cfg ext hhb hec hgen hi w m hw hmH
  exact mem_AttSupporters_of cfg hact huns hlm hne hsupp

/-! ## The headline: recorded-support lower bound for a validator set

`MajorityPersists.recorded_support_lower` lower-bounds the attestation score by
the ground-truth weight of any validator set all of whose members support the
node at the store. Combined with `mem_AttSupporters_honest`, an honest set whose
members carry the active/unslashed/recorded-`node`-support facts lower-bounds
`node`'s score at `(w, m)`. Instantiated with `node = get_node_for_root c` and
`HS = HS₀ ∪ NewVoters` this is the ledger's `hscore` input (the two sets'
weights sum to `E.weight HS` when disjoint by slot range — provenance provides
the disjointness where the split is wanted). -/


end FastConfirmation.Spec

end
