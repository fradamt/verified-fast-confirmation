module
public import FastConfirmation.Spec.Proof.Engine
public import FastConfirmation.Spec.Proof.Delivery
public import FastConfirmation.Spec.Proof.SupportTransport
public import FastConfirmation.Spec.Proof.QuorumAccounting

@[expose] public section

/-!
# Spec / Proof / EngineSupport: recorded-support membership

The head-safety engine's *recorded-support lower bound* is established at a
later honest store `(w, m)` in slot
`k ≥ s`, the block `b`'s recorded attestation score for a fork child `c` on
`b`'s chain must cover the old honest supporter set `HS₀` **plus** the new
honest voters of slots `[s, k)`. This module supplies the membership half: each
such validator sits in `AttSupporters cfg store_wm (get_node_for_root c) bs`,
so `MajorityPersists.recorded_support_lower` lower-bounds the score by their
ground-truth weight — the ledger's `hscore` input.

The construction uses the following proved components:

* **`mem_AttSupporters_of`** — the reverse of `QuorumAccounting.mem_AttSupporters`:
  active + unslashed + a recorded non-equivocating message supporting the node
  gives supporter-list membership.
* **`AttSupporters_active` / `AttSupporters_unslashed`** — the active/unslashed
  projections out of an existing supporter membership (the confirmation-time
  facts of `HS₀`).
* **`active_indices_congr` / `mem_active_congr` / `unslashed_congr`** —
  active/unslashed transport across two balance sources
  on the ground registry (`StaticValidatorSet.registry_activity_constant`),
  moving `HS₀`'s confirmation-time activity to the later store.
* **`supports_of_ge_b`** — the `SupportTransport.supporter_of_ancestor` bridge:
  a recorded root `⪰ b` supports every chain child `c ≼ b`.
* **`mem_AttSupporters_honest`** — honest + active + unslashed + a recorded
  `c`-supporting message gives membership at `(w, m)` (non-equivocation from
  `Execution.honest_not_equivocating`).
* **`recorded_support_lower_HS`** — a validator set all of whose
  members carry those facts lower-bounds `c`'s score at `(w, m)` by its weight.

The two explicit inputs are the *exact-message identification* (that
`vote_ubiquity`'s recorded
message root equals the honest vote-block — `vote_ubiquity` delivers only the
epoch bound) and the *new-voter activity* at the balance source.
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

omit [Inhabited Root] in
/-- A supporter is active in its balance source. -/
theorem AttSupporters_active {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg store node state) :
    i ∈ get_active_validator_indices state (get_current_epoch cfg state) := by
  simp only [AttSupporters, List.mem_filter] at hi
  exact hi.1.1

omit [Inhabited Root] in
/-- A supporter is unslashed in its balance source. -/
theorem AttSupporters_unslashed {store : Store Root} {node : ForkChoiceNode Root}
    {state : BeaconState Root} {i : ValidatorIndex}
    (hi : i ∈ AttSupporters cfg store node state) :
    (state.validators.getD i default).slashed = false := by
  simp only [AttSupporters, List.mem_filter] at hi
  simpa using hi.1.2

/-! ## Reconciliation (b): active / unslashed transport across balance sources

Two balance sources on the ground registry (`StaticValidatorSet`) agree on the
active-validator list — the range length is the registry length on both, and
activity is epoch-independent (`registry_activity_constant`), so the per-index
filter predicates coincide even at different current epochs. Slashed status is
read off the same registry entry. This moves the confirmation-time activity
facts of `HS₀` (extracted from its `v/n₀` supporter membership) to the later
store `(w, m)`'s balance source. -/

omit [LinearOrder Root] [Inhabited Root] in
/-- The active-validator list is the same on any two ground-registry balance
sources (despite possibly different current epochs). -/
theorem active_indices_congr {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {bs bs' : BeaconState Root} (hval : bs.validators = E.registry)
    (hval' : bs'.validators = E.registry)
    (hbs : get_current_epoch cfg bs < E.verification_horizon)
    (hbs' : get_current_epoch cfg bs' < E.verification_horizon) :
    get_active_validator_indices bs (get_current_epoch cfg bs)
      = get_active_validator_indices bs' (get_current_epoch cfg bs') := by
  unfold get_active_validator_indices
  rw [hval, hval']
  apply List.filter_congr
  intro i _
  exact hsv.registry_activity_constant i _ _ hbs hbs'

omit [LinearOrder Root] [Inhabited Root] in
/-- Active membership transports across two ground-registry balance sources. -/
theorem mem_active_congr {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {bs bs' : BeaconState Root} (hval : bs.validators = E.registry)
    (hval' : bs'.validators = E.registry)
    (hbs : get_current_epoch cfg bs < E.verification_horizon)
    (hbs' : get_current_epoch cfg bs' < E.verification_horizon) {i : ValidatorIndex}
    (hact : i ∈ get_active_validator_indices bs (get_current_epoch cfg bs)) :
    i ∈ get_active_validator_indices bs' (get_current_epoch cfg bs') :=
  active_indices_congr cfg hsv hval hval' hbs hbs' ▸ hact

omit [LinearOrder Root] [Inhabited Root] in
/-- Unslashed status transports across two ground-registry balance sources
(the same registry entry is read on both). -/
theorem unslashed_congr {E : Execution Root} {bs bs' : BeaconState Root}
    (hval : bs.validators = E.registry) (hval' : bs'.validators = E.registry)
    {i : ValidatorIndex} (huns : (bs.validators.getD i default).slashed = false) :
    (bs'.validators.getD i default).slashed = false := by
  rw [hval'] ; rw [hval] at huns ; exact huns

omit [Inhabited Root] in
/-- Reconciliation (b), applied to `HS₀`: a confirmation-time supporter (member
of `AttSupporters` at `v/n₀`, `hi`) is active and unslashed in the later store's
balance source `bs`. Both balance sources are on the ground registry, so the
active/unslashed facts extracted from `hi` transport (`mem_active_congr`,
`unslashed_congr`). This feeds the active/unslashed inputs of
`mem_AttSupporters_honest` for the old honest supporter set. -/
theorem old_supporter_active_unslashed {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {store0 : Store Root} {bs0 bs : BeaconState Root} {node0 : ForkChoiceNode Root}
    {i : ValidatorIndex} (hval0 : bs0.validators = E.registry)
    (hval : bs.validators = E.registry)
    (hbs0 : get_current_epoch cfg bs0 < E.verification_horizon)
    (hbs : get_current_epoch cfg bs < E.verification_horizon)
    (hi : i ∈ AttSupporters cfg store0 node0 bs0) :
    i ∈ get_active_validator_indices bs (get_current_epoch cfg bs) ∧
      (bs.validators.getD i default).slashed = false :=
  ⟨mem_active_congr cfg hsv hval0 hval hbs0 hbs (AttSupporters_active cfg hi),
    unslashed_congr hval0 hval (AttSupporters_unslashed cfg hi)⟩

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
    (hge : is_ancestor store (ForkChoiceNode.mk lm.root) (ForkChoiceNode.mk b) = true)
    (hcb : is_ancestor store (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true) :
    is_ancestor store (get_supported_node store lm) (get_node_for_root c) = true := by
  simp only [get_supported_node, get_node_for_root]
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

/-- Recorded-support lower bound (headline). For a validator set `HS` all of
whose members are honest, active, unslashed, and record a `node`-supporting
latest message at `(w, m)`, the ground-truth weight of `HS` is at most `node`'s
attestation score at `(w, m)`. -/
theorem recorded_support_lower_HS {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {bs : BeaconState Root} {node : ForkChoiceNode Root}
    (hval : bs.validators = E.registry)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      i ∈ get_active_validator_indices bs (get_current_epoch cfg bs) ∧
      (bs.validators.getD i default).slashed = false ∧
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) node = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    E.weight HS ≤ get_attestation_score cfg (E.store cfg ext w m) node bs := by
  refine recorded_support_lower cfg hval HS (fun i hi => ?_)
  obtain ⟨hih, hact, huns, lm, hlm, hsupp⟩ := hHS i hi
  exact mem_AttSupporters_honest cfg ext (hw := hw) (hmH := hmH) hhb hec hgen hih hact huns hlm hsupp

end FastConfirmation.Spec

end
