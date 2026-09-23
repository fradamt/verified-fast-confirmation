# Historical G2 proof obligations

> **History.** This record applies to the upstream discount rule before the
> payload-aware change in [the spec deviation](../gloas-spec-deviation.md).
> The current Gloas proof constructs the pending-parent status margin in
> `FastConfirmationProofs/Discount/StatusMarginConstruction.lean`. The G2b port
> archive was removed after commit `28faf6d`.

This is the preserved G2b record. The G3 lane is allowed to strengthen payload
envelope relay. The statements below describe the earlier assumptions.

# Gloas proof obligations

The Gloas proof port is blocked. No public theorem statement or safety assumption was changed to remove either obligation. The active library retains the last buildable pre-port baseline. The patches preserve the candidate for further work. They do not prove Gloas safety.

The public theorem declaration is unchanged:

```lean
theorem acceptedSpec_safety_next_slot :
    AcceptedSpec_Safety_next_slot cfg ext
```

Its full meaning depends on the model and assumption records. Keeping the text while adding a payload-delivery premise to an assumption record would weaken the claim. That change was not made.

## G2-003: receiver payload delivery

The local delivery proof has this statement. Section parameters are `{Root : Type*} [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root) (E : Execution Root)`.

```lean
theorem honestVoteTarget_cached_at_delivery
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    {v w : ValidatorIndex} (hv : v ∈ E.honest) (hw : w ∈ E.honest)
    {s : Slot} {n : Nat} {index : CommitteeIndex}
    (hn : E.slot_at cfg n = s)
    (hHn : E.WithinHorizon cfg n)
    (hHdeliver : E.WithinHorizon cfg (E.slot_start cfg (s + 1)))
    (hvote : E.vote v s = some
      (n, honest_attestation cfg ext (E.store cfg ext v n) s index v))
    (hheadKnown :
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root ∈
          (E.store cfg ext v n).block_roots)
    (hheadWalk : WalkKnown (E.store cfg ext v n)
      (compute_start_slot_at_epoch cfg
        (honest_attestation cfg ext
          (E.store cfg ext v n) s index v).data.target.epoch)
      (honest_attestation cfg ext
        (E.store cfg ext v n) s index v).data.beacon_block_root) :
    (honest_attestation cfg ext
      (E.store cfg ext v n) s index v).data.target ∈
        (E.store cfg ext w
          (E.slot_start cfg (s + 1))).checkpoint_state_keys
```

Its call to `validate_at_extension` lacks this final argument:

```lean
a.data.index = 1 →
  is_payload_verified
    (pre.foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      ticked)
    a.data.beacon_block_root = true
```

`PaperSafetySynchrony` puts the vote in the receiver schedule and relays beacon roots. It does not require a verified envelope before the vote. Local payload persistence needs an earlier verification fact at the same receiver. The FULL-parent acceptance lemma verifies the parent payload, not the block's own payload. The indexed-attestation validity contract does not imply payload verification.

The candidate fixture `scripts/GloasPayloadDeliveryObstacle.lean` proves that the former local validation interface is false. Both stores have the same blocks. The source has the envelope; the receiver does not. The index-1 vote is rejected. At the same receiver clock, retaining the source payload makes validation pass.

```text
("GLOAS_PAYLOAD_DELIVERY_OBSTACLE", 2, 3, 2, 2, true, false, false)
```

The pinned-source experiment can be run from the active tree:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/conformance/python/gloas_payload_delivery_obstacle.py --consensus-repo /home/fradamt/lean/consensus-specs
```

It reports this obstruction and exits 0 because the expected checks pass:

```text
OBSTACLE: delivered honest index-1 votes can be rejected without payload relay
```

The experiment rejects all 400 delivered index-1 votes at the receiver. It is an exact-source projection, not a full accepted Lean execution.

## G2-004: payload branch selection

The local endpoint statement is:

```lean
theorem ledger_descendStep {E : Execution Root} {store : Store Root}
    {v₀ : ValidatorIndex} {n₀ : ℕ} {b' h c : Root} {lo σ : Slot}
    (hchild : ForkChoiceNode.mk c .pending ∈
      get_node_children store (get_filtered_block_tree cfg store)
        (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c))))
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
    DescendStep cfg store (get_filtered_block_tree cfg store) h c
```

After beacon-child dominance, `descendStep_of_dom` still requires:

```lean
(get_node_children store (get_filtered_block_tree cfg store)
    (ForkChoiceNode.mk h .pending)).argmax
    (fun child => toLex (get_weight cfg store child,
      toLex (child.root, get_payload_status_tiebreaker cfg store child))) =
  some (ForkChoiceNode.mk h (get_parent_payload_status store (store.blocks c)))
```

The sibling bound covers only the required resolved branch. It gives no bound on the other branch. The support partition separates same-root and other-root weight, but it does not show which status wins. Payload persistence proves availability, not selection.

The candidate fixture `scripts/GloasPayloadBranchObstacle.lean` proves the local obstruction. FULL child 2 has weight 100 and FULL sibling 3 has weight 0. Parent FULL has weight 100, while parent EMPTY has weight 200. The parent payload is verified, and all four roots survive filtering. The pending parent selects EMPTY and the head reaches child 4.

```text
("GLOAS_PAYLOAD_BRANCH_OBSTACLE", 100, 0, 100, 200, 4)
```

This is a kernel-checked local fork-choice counterexample. It does not refute the complete accepted safety theorem. A complete proof would need a derived invariant for payload-status history and branch scores. The existing scalar root ledger does not supply that invariant.

## Kernel checks and scope

After reconstructing the candidate as stated in the archived README (`archive/gloas-port/README.md` at commit `28faf6d`), run:

```sh
flock /home/fradamt/lean/orch/g2-lean-slot.lock lake env lean scripts/GloasPayloadDeliveryObstacle.lean
flock /home/fradamt/lean/orch/g2-lean-slot.lock lake env lean scripts/GloasPayloadBranchObstacle.lean
```

Both commands passed in lane g2b. Their listed axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`. They import the executable model, so they do not use stale proof-module artifacts.

The separate source branch FCR experiment reproduces a threshold gap, but its child-vote run violates honest head voting. Its control removes child support when voters follow the actual head. It is not an accepted safety counterexample. No public theorem is claimed false on the basis of that experiment.

## Full compiler confirmation

The final candidate check reaches G2-004 at `Endpoint.ledger_descendStep`.
Command:

```sh
flock /home/fradamt/lean/orch/g2-lean-slot.lock scripts/validate.sh --consensus-repo /home/fradamt/lean/consensus-specs
```

Full check 07 exits 1 with this first error:

```text
error: FastConfirmationProofs/FFG/SelectedSource/EndpointMargin.lean:156:2: Type mismatch
  descendStep_of_dom cfg hchild fun c' hc' hne ↦ ghost_step_dominates cfg ext hbside hledger (hsib c' hc' hne)
has type
  List.argmax
        (fun child ↦
          toLex (get_weight cfg store child, toLex (child.root, get_payload_status_tiebreaker cfg store child)))
        (get_node_children store (get_filtered_block_tree cfg store) { root := h }) =
      some { root := h, payload_status := get_parent_payload_status store (store.blocks c) } →
    DescendStep cfg store (get_filtered_block_tree cfg store) h c
but is expected to have type
  DescendStep cfg store (get_filtered_block_tree cfg store) h c
```

The payload partition and persistence modules compile. They do not supply
the missing branch-selection equality. Adding that equality as a new safety
premise would change the assumption surface, so no such premise was added.

Full check 08 has the same first error and only Endpoint as a direct failed
target. The 12 resumed mechanical proof repairs all pass targeted builds.
The dependent safety proof and its witness audit remain blocked.
