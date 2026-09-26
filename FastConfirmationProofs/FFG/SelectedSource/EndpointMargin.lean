module
public import FastConfirmationProofs.Handlers.SupportClasses
public import FastConfirmationProofs.FFG.State.PayloadAwareHead
public import FastConfirmationProofs.Execution.Delivery.VoteDeliveryMargin
public import FastConfirmationProofs.ForkChoice.Ancestry.Forks

@[expose] public section

/-!
# Spec / Proof / Endpoint

Bounds recorded competing support at the selected FFG endpoint.

This module contains `recorded_bside_ge`, `recorded_sibling_le`, `ghost_arith` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

/-! ## The `b′`-side child's recorded score dominates `Sval`

Set-weight subadditivity over a union (`EngineWindows.weight_union_le`, reused for
the sibling bound below) and the recorded-support machinery of `MajorityPersists`
are the only ingredients. -/

/-- **Recorded `b′`-side lower bound.** At a registry-constant balance source `bs`,
the fork child `c`'s attestation score at `store` is at least `Sval σ` — the
ground weight of the honest window members whose newest vote supports
`subtree(b′)` — provided every such member records a `c`-supporting latest message
at `store` (`hSmem`, the transport fact the shell supplies via
`EngineTransport.HS0_in_AttSupporters` / `NewVoters_in_AttSupporters`). Direct
`MajorityPersists.recorded_support_lower` with `HS := Sclass`. -/
theorem recorded_bside_ge {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c : Root} {lo σ : Slot}
    (hSmem : ∀ i ∈ E.Sclass cfg ext v₀ n₀ b' lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs) :
    E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c) bs := by
  rw [Execution.Sval]
  exact recorded_support_lower cfg hval (E.Sclass cfg ext v₀ n₀ b' lo σ) hSmem

/-! ## A sibling's recorded score is at most `Xval + Bval` -/

/-- **Recorded sibling upper bound.** At a registry-constant balance source `bs`,
the recorded attestation score of a sibling `cc` (of `parent(b′)`, `cc ≠` the
`b′`-side child) is at most `Xval σ + Bval σ`. Its supporter set splits into an
honest part confined to `Xclass` (recorded supporters of a sibling neither support
`subtree(b′)` nor are `b′`-ancestors — `Bridge` + `Forks.siblings_incompatible`,
supplied as `hHon`) and a byz part confined to the window enemy set `Bwin`
(window confinement, supplied as `hByz`);
`MajorityPersists.attestation_score_eq_weight` turns the score into that supporter
set's weight and `weight_union_le` weighs the confinement. -/
theorem recorded_sibling_le {E : Execution Root} {store : Store Root}
    {bs : BeaconState Root} (hval : bs.validators = E.registry)
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' cc : Root} {lo σ : Slot}
    (hHon : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∈ E.honest → i ∈ E.Xclass cfg ext v₀ n₀ b' lo σ)
    (hByz : ∀ i ∈ AttSupporters cfg store (get_node_for_root cc) bs,
      i ∉ E.honest → i ∈ E.Bwin lo σ) :
    get_attestation_score cfg store (get_node_for_root cc) bs ≤
      E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ := by
  rw [attestation_score_eq_weight cfg hval, Execution.Xval, Execution.Bval]
  refine le_trans (E.weight_mono ?_) (weight_union_le _ _)
  intro i hi
  rw [List.mem_toFinset] at hi
  rw [Finset.mem_union]
  by_cases hh : i ∈ E.honest
  · exact Or.inl (hHon i hi hh)
  · exact Or.inr (hByz i hi hh)

/-! ## The ancestor slice of the opposite payload branch -/















/-! ## The GHOST step favours the `b′`-side child -/

/-- Pure-ℕ core of the GHOST step (`Gwei` weights are opaque to `omega`, so the
linear arithmetic is discharged over plain ℕ and `exact`-ed). -/
private theorem ghost_arith {sc scc X B P S : ℕ}
    (hbside : S ≤ sc) (hledger : X + B + P + 1 ≤ S) (hsib : scc ≤ X + B) :
    scc + P < sc := by omega






/-- The resolved parent status selected by a child receives every vote that
supports the child's pending node.  This is a score lower bound at the same
store, with Gloas payload ancestry preserved. -/
theorem selected_parent_score_ge_child_score {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {b : Root}
    (hval : bs.validators = E.registry)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root b) bs →
        WalkKnown store (store.blocks (store.blocks b).parent_root).slot lm.root) :
    get_attestation_score cfg store (get_node_for_root b) bs ≤
      get_attestation_score cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root
          (get_parent_payload_status store (store.blocks b))) bs := by
  rw [attestation_score_eq_weight cfg hval,
    attestation_score_eq_weight cfg hval]
  apply E.weight_mono
  exact attSupporters_subset_resolved_ancestor cfg hwf
    (child_pending_descends_required_parent_status hwf hb hp) hwalk
    (WalkKnown.step hb (hwf b hb hp) (WalkKnown.stop hp (le_refl _)))

/-- The pending parent's payload contest. A strict margin pays the complete
proposer score. If Gloas gives both previous-slot payload decisions zero
weight, the status tie breaker supplies the second route. -/
def PendingStatusMargin (store : Store Root) (blocks : List Root)
    (h : Root) (status : PayloadStatus) : Prop :=
  let selected := ForkChoiceNode.mk h status
  selected ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending) ∧
  ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
    other ≠ selected →
    (get_attestation_score cfg store other
          (store.checkpoint_states store.justified_checkpoint) +
          get_proposer_score cfg store <
        get_attestation_score cfg store selected
          (store.checkpoint_states store.justified_checkpoint) ∧
      is_previous_slot_payload_decision cfg store selected = false) ∨
      (get_weight cfg store other = get_weight cfg store selected ∧
        get_payload_status_tiebreaker cfg store other <
          get_payload_status_tiebreaker cfg store selected)


/-- The payload ledger margin selects the required status with Gloas's full
weight, root, and payload-status key. -/
theorem pending_status_selected_of_margin {store : Store Root} {blocks : List Root}
    {h : Root} {status : PayloadStatus}
    (hmargin : PendingStatusMargin cfg store blocks h status) :
    (get_node_children store blocks (ForkChoiceNode.mk h .pending)).argmax
      (fun child => toLex (get_weight cfg store child,
        toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
      some (ForkChoiceNode.mk h status) := by
  let selected := ForkChoiceNode.mk h status
  have hmem := hmargin.1
  have hkey : ∀ other ∈ get_node_children store blocks (ForkChoiceNode.mk h .pending),
      other ≠ selected →
      (toLex (get_weight cfg store other,
        toLex (other.root, get_payload_status_tiebreaker cfg store other)) :
          Gwei ×ₗ (Root ×ₗ ℕ)) <
      toLex (get_weight cfg store selected,
        toLex (selected.root, get_payload_status_tiebreaker cfg store selected)) := by
    intro other hm hne
    rcases hmargin.2 other hm hne with ⟨hscore, hnotrecent⟩ | ⟨heq, htie⟩
    · rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (lt_of_le_of_lt (get_weight_le cfg store other)
        (lt_of_lt_of_le hscore
          (get_weight_ge_of_not_payload_decision cfg store selected hnotrecent)))
    · have hroot : other.root = h := ((mem_get_node_children_pending rfl).mp hm).1
      rw [Prod.Lex.toLex_lt_toLex]
      right
      constructor
      · exact heq
      · rw [Prod.Lex.toLex_lt_toLex]
        right
        exact ⟨hroot, htie⟩
  rw [List.argmax_eq_some_iff]
  refine ⟨hmem, fun other hm => ?_, fun other hm hle => ?_⟩
  · by_cases hsame : other = selected
    · subst hsame; exact le_refl _
    · exact le_of_lt (hkey other hm hsame)
  · by_cases hsame : other = selected
    · subst hsame; exact le_refl _
    · exact absurd (lt_of_lt_of_le (hkey other hm hsame) hle) (lt_irrefl _)

/-- **The GHOST step dominates.** From the ledger inequality
`Xval + Bval + get_proposer_score + 1 ≤ Sval`, the `b′`-side lower bound `hbside`
and a sibling upper bound `hsib`, the sibling `cc`
loses to the `b′`-side child `c` in `get_weight` — the boost is charged to the
sibling in full (`MajorityPersists.fork_weight_lt`) yet the winner's bare score
already exceeds sibling-plus-boost. -/
theorem ghost_step_dominates {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' c cc : Root} {lo σ : Slot}
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : get_attestation_score cfg store (get_node_for_root cc)
        (store.checkpoint_states store.justified_checkpoint)
      ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    get_weight cfg store (ForkChoiceNode.mk cc .pending) < get_weight cfg store (ForkChoiceNode.mk c .pending) := by
  simp only [get_node_for_root] at hbside hsib
  exact fork_weight_lt cfg (ghost_arith hbside hledger hsib)

/-- **A ledger certificate builds one `DescendStep`.** At a fork with parent `h`,
the status margin selects the payload status required by `c`. Within that
resolved branch the ledger inequality, selected lower bound, and every sibling
upper bound select `c`. The shell must derive `hstatus` from confirmation. -/
theorem ledger_descendStep {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot}
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
    (hstatus : PendingStatusMargin cfg store (get_filtered_block_tree cfg store)
      h (get_parent_payload_status store (store.blocks c)))
    (hbside : E.Sval cfg ext v₀ n₀ b' lo σ ≤
      get_attestation_score cfg store (get_node_for_root c)
        (store.checkpoint_states store.justified_checkpoint))
    (hledger : E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ + get_proposer_score cfg store + 1
      ≤ E.Sval cfg ext v₀ n₀ b' lo σ)
    (hsib : ∀ c' : Root,
      ForkChoiceNode.mk c' .pending ∈
        get_node_children store (get_filtered_block_tree cfg store)
          (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))) →
        c' ≠ c →
        get_attestation_score cfg store (get_node_for_root c')
            (store.checkpoint_states store.justified_checkpoint)
          ≤ E.Xval cfg ext v₀ n₀ b' lo σ + E.Bval lo σ) :
    DescendStep cfg store (get_filtered_block_tree cfg store) h c :=
  descendStep_of_dom cfg hchild
    (fun c' hc' hne => ghost_step_dominates cfg ext hbside hledger (hsib c' hc' hne))
    (pending_status_selected_of_margin cfg hstatus)

/-! ## The head descends from `b` along the confirmed chain -/







end FastConfirmation.Spec

end
