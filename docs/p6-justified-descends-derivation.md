# P-6 — deriving `JustificationInterface.justified_descends` at the spec layer

> **W0 EXECUTED — the field is deleted.** See **§7, "W0 outcome"**, at the end of this
> document for the reachability computation, the site-by-site resolution, and the one residual.
> Sections 0-6 below are the original analysis, kept verbatim; §7 records where it was right,
> where it overshot, and what actually landed.

**Status:** analysis only. No `.lean` file was touched, nothing was built, nothing committed.
**Snapshot:** branch `centaur/weak-synchrony-202609150824`, working tree at 2026-09-16
(`git pull --ff-only` → already up to date).
**Pinned spec:** consensus-specs `30aa65fc21cf7f7c7dd1f7d6b686d0250462d04f`; `fork-choice.md`
quoted from blob `275b36991f108f165a1aa919fb65839bdcede6ac` (the blob recorded in
`spec_source/manifest.json`), line numbers 1-based into that blob, consistent with
`docs/plumbing-spec-citations.md`.

The flag under study is `docs/plumbing-spec-citations.md` §13 **P-6** (row 14 of §2), against
`FastConfirmation/Spec/TheoremStatements.lean:279-292`:

```lean
  justified_descends : ∀ w ∈ E.honest, ∀ m : ℕ, ∀ c : Checkpoint Root,
    E.WithinHorizon cfg m →
    JustifiedIn (E.store cfg ext w m) c →
    c.root ∈ (E.store cfg ext w m).block_roots →
    (E.store cfg ext w m).justified_checkpoint.epoch < c.epoch →
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m)) (get_node_for_root c.root) = true
```

The owner's ruling is that the paper derives this content (Paper/LMDGhost's weight engine) and
that the spec layer must therefore not assume it. This document asks, adversarially, **how** it
would be derived here and **what it would cost** — and reaches a negative headline result that
changes the shape of the answer.

---

## 0. Headline

1. There are **two** consumption sites, not three. The third alleged site is a name collision.
2. Both real sites instantiate `c` (or `c.root`) at exactly **one** value: an honest FCR's
   `current_epoch_observed_justified_checkpoint`. The unconditional `∀ c. JustifiedIn …` surface
   is ~80 % dead weight.
3. The fork-choice **filter provably cannot** deliver the ahead regime; the weight engine is
   genuinely required. The module docstring at `AheadFacade.lean:59-70` already says this, and it
   is correct.
4. The spec layer **already owns** every piece of the weight engine — a real executable
   `get_head` argmax, real `get_weight` with proposer boost, the `DescendStep`→`DescendsTo`→
   `get_head` fold, the per-fork ledger, latest-message provenance in both directions.
5. **The crux fails arithmetically, not for lack of machinery.** An FFG 2/3 quorum implies LMD
   head-domination only when `β < 1/6 − pb/2 ≈ 0.1604`. The spec's own design point is
   `β ≤ 0.25` (`Config.lean:35-39,66`). At `β = 0.25` the honest-only ledger reads `5/12` against
   `7/12` — the sibling wins. The paper's own Lemma 4 threshold says the same thing. The
   docstring's "2/3 ⟹ dominates" and `AheadFacade.lean:70`'s "2/3 exceeds the confirmation bar"
   are **false at the spec's design point**.
6. Therefore neither "derive it here" nor "transplant the paper's Lemma 3/4" closes P-6 as
   stated. The honest endpoint is a **narrowed, relocated, disclosed premise** (waves 0-2), with
   a genuine derivation (wave 3) available only under a strengthened Byzantine bound.

---

## 1. What the consumers actually need

### 1.1 Site A — `ExportWiring.lean:70-72`, the AheadFacade ahead regime

```lean
theorem headTracksJustified_of_interface (hji : JustificationInterface cfg ext E) :
    E.HeadTracksJustified cfg ext :=
  hji.justified_descends
```

`HeadTracksJustified` (`AheadFacade.lean:128-135`) is binder-identical to the field. It is
consumed exactly once, by `observed_head_ahead_of_headTracks` (`AheadFacade.lean:143-166`), at

```
c := (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint
```

for an honest `v` and `n + 1 ≤ m`. That instance is the `observed_head_ahead` field of
`E5Filter.ObservedFilterResiduals` (`E5Filter.lean:205-211`), and the whole bundle is assembled
at `ExportWiring.lean:120-129` / `AheadFacade.lean:168-196`.

**Provenance of `c` at this site.** `JustifiedIn (store w m) c` is not free: it is produced by
`ObservedDom.fcrStep_observed_justifiedIn` from `hji.observed_justified`
(`TheoremStatements.lean:157-162`) plus the boundary-corner carry `prev_greatest_justifiedIn`.
So `c` is always a checkpoint that some honest node's FCR published as *observed justified* —
fast-confirmation.md:94's "observed by all honest nodes at the beginning of the current epoch
assuming synchrony". A justification quorum for it is in scope via
`justified_requires_targets` (`TheoremStatements.lean:139-155`) **modulo two epoch gates**
(§3.1).

**Does it need the full field?** No. It needs one instance, at the observed family.

### 1.2 Site B — `AnchorClose.lean:927`, case (iii) of the anchor-close geometry

```lean
        have hhead_r₀ : is_ancestor S (get_head cfg S) (get_node_for_root r₀) = true :=
          hjcb_root ▸ hji.justified_descends w hw m jcb hH hjust hjcb_known hep2
```

inside `head_ge_glc_endpoint` (`AnchorClose.lean:860-947`). The four cases are documented at
`AnchorClose.lean:845-859`; (i), (ii) and (iv) are filter-mechanical
(`head_ge_of_justified_ge_K` + `justified_ancestry`), only (iii) calls the field.

**Provenance of `jcb`.** `jcb` is existentially supplied by the third (observed) disjunct of
`AnchorClose.AnchorCovSupply` (`AnchorClose.lean:644-690`), whose guard is

```
r₀ = (E.fcrStep cfg ext v n).current_epoch_observed_justified_checkpoint.root
```

with `jcb.root = r₀`. So again: the observed family, root-wise. Two riders:

* The conclusion actually consumed is only `head ⪰ r₀`, i.e. only `c.root` matters, not `c`.
* `AnchorCovSupply` is **itself an open flag**: it is carried as the hypothesis `hcov` at
  `AnchorClose.lean:967, 1248, 1279, 1319, 1348`, never produced. Its observed route is
  documented (`AnchorClose.lean:626-643`) as awaiting the *same* quorum argument
  (`justified_requires_targets` → an honest quorum member's earlier-slot head via the
  head-safety IH → `Delivery.honest_attestation_data_target_root`). `Nucleus.lean:222-267`
  exposes the residual half of that as the explicit predicate `CurrentEpochCoveringBridge`
  rather than asserting it — the in-tree precedent for how this development handles exactly
  this kind of fact.

Consequence: site B is behind an unproduced supply. Whatever we do to the field, site B is not
today a load-bearing consumer of anything that is proved.

### 1.3 Site C — `AcceptedCurrentSameEndpointSource.lean:429` / `:528` — **not a consumer**

Both lines read `h.justified_descends_candidate`, which is the field of

```lean
structure AcceptedPastJustifiedFallbackAt (v : ValidatorIndex) (q : Nat) (candidate : Root) where
  past : E.AcceptedHonestPastHeadBelowAt cfg ext v q candidate
  justified_descends_candidate : is_ancestor
    (E.store cfg ext past.validator past.second)
    (get_node_for_root (E.store cfg ext past.validator past.second).justified_checkpoint.root)
    (get_node_for_root candidate) = true
```

(`AcceptedCurrentSameSourceHistory.lean:2331-2339`). This is the **opposite orientation** — the
past store's *realized* justified root descends from the candidate — and it is produced
mechanically, with no interface field, by
`AcceptedHonestPastHeadBelowAt.directJustified_or_pathLocal`
(`AcceptedCurrentSameSourceHistory.lean:272-296`, via `queryHead_direct_or_viableLeafBelow`),
and consumed at `AcceptedCurrentSameSourceHistory.lean:2402-2406` /
`WeakCandidateSourceHistory.lean:1906-1910`. **Pure name collision.**

A repo-wide grep for `.justified_descends` finds exactly two projection sites: `ExportWiring.lean:72`
and `AnchorClose.lean:927`.

### 1.4 Q1 verdict

| | site A | site B | site C |
|---|---|---|---|
| real consumer of the field | yes | yes, behind an open flag | **no** |
| `c` at | `(fcrStep v n).current_epoch_observed_justified_checkpoint` | `jcb`, `jcb.root = ` the same root | — |
| quorum in scope | yes, via `justified_requires_targets` + 2 gates | same | — |
| needs unconditional `∀ c`? | no | no (needs only `head ⪰ c.root`) | — |

**A gated form suffices at every real site.** The gate "an FFG justification quorum for `c` is in
hand" is available at both; so is the much narrower gate "`c` is an honest FCR's observed
justified checkpoint at an earlier second".

---

## 2. What the spec-side engine already has

### 2.1 The filter gives nothing in the ahead regime — confirmed against the pinned text

What the filter *does* give is already proved, with no weight:

* `E5Filter.head_ge_of_justified_ge_K` (`E5Filter.lean:449-459`) and its blanket-domain twin
  `EngineStore.head_ge_of_justified_ge` (`EngineStore.lean:307-317`): once
  `jc.root ⪰ b` on the chain, `head ⪰ b`, because every root emitted by `filter_block_tree_aux`
  from the base `store.justified_checkpoint.root` descends from that base
  (`E5Filter.filtered_through_justified_K`, `:429-442`).
* `E5Filter.head_ge_of_justifiedIn_le_K` (`E5Filter.lean:492-510`): the `c.epoch ≤ jc.epoch`
  complement of P-6, closed by `justified_ancestry` + the above. **Only the strictly-ahead case
  is open.**

Why the filter cannot reach the ahead case, from the pinned blob:

```python
def get_filtered_block_tree(store: Store) -> Dict[Root, BeaconBlock]:
    base = store.justified_checkpoint.root          # fork-choice.md:453
```
```python
    correct_justified = (                            # fork-choice.md:419-423
        store.justified_checkpoint.epoch == GENESIS_EPOCH
        or voting_source.epoch == store.justified_checkpoint.epoch
        or voting_source.epoch + 2 >= current_epoch
    )
```
```python
def get_head(store: Store) -> ForkChoiceNode:        # fork-choice.md:473-484
    blocks = get_filtered_block_tree(store)
    head = ForkChoiceNode(root=store.justified_checkpoint.root)
    while True:
        children = get_node_children(store, blocks, head)
        if len(children) == 0: return head
        head = max(children, key=lambda child: (get_weight(store, child), child.root))
```

A sibling branch that forks off *below* `c.root` and never contains `c`'s justifying
attestations carries `voting_source.epoch` around `c.epoch − 1`; with `current_epoch` at
`c.epoch` or `c.epoch + 1` the clause `voting_source.epoch + 2 >= current_epoch` holds, so the
branch survives `filter_block_tree` and competes in the `max`. This is exactly the analysis
already written at `AheadFacade.lean:59-70`, and it is right. **Filter structure is not the
route; weight is.**

The spec model transcribes all of this literally — `filter_block_tree_aux`
(`Model/ForkChoice.lean:259-289`), `get_filtered_block_tree` (`:301-303`), `get_voting_source`
(`:215-223`).

### 2.2 The model has a real weight engine — and a real proposer boost

* `Store.latest_messages : ValidatorIndex → Option (LatestMessage Root)`
  (`Model/ForkChoice.lean:49`), written by `update_latest_messages`
  (`Model/Handlers.lean:238-256`).
* `get_attestation_score` sums effective balances over unslashed, active, non-equivocating
  validators whose recorded latest message descends the node (`Model/ForkChoice.lean:148-159`).
* `get_head` is a genuine fuel-bounded GHOST descent, `List.argmax` over the lexicographic key
  `(get_weight store child, child.root)` (`Model/ForkChoice.lean:329-349`).
* **Proposer boost is in the model, not prose.** `Config.proposer_score_boost` (`Config.lean:32`,
  mainnet `40` at `:65`), `Store.proposer_boost_root` (`ForkChoice.lean:35`),
  `compute_proposer_score = total_active/32 · 40/100` (`ForkChoice.lean:166-168`),
  `get_weight`'s boost arm (`ForkChoice.lean:192-201`), set by `update_proposer_boost_root`
  (`Handlers.lean:313-321`, called from `on_block` at `:385`), reset per slot (`:113-116`).
  It is charged **adversarially in full** in every margin lemma
  (`MajorityPersists.get_weight_le` / `get_weight_ge` / `fork_weight_lt`,
  `MajorityPersists.lean:62-96`). So the field docstring's "plus the
  proposer boost" (`TheoremStatements.lean:284`) names a real term worth `1.25 %` of total stake.

### 2.3 The "enough weight ⟹ head descends" chain already exists, spec-native

| layer | declaration | file:line |
|---|---|---|
| GHOST descent relation | `Descent.DescendsTo` | `Descent.lean:44-55` |
| descent ⟹ head | `Descent.is_ancestor_get_head` | `Descent.lean:138-147` |
| one dominant fork | `EngineStore.DescendStep` | `EngineStore.lean:51-55` |
| chain fold | `EngineStore.is_ancestor_get_head_of_chain` | `EngineStore.lean:145-156` |
| score = set weight | `QuorumAccounting.AttSupporters`, `get_attestation_score_eq_sum` | `QuorumAccounting.lean:53-70` |
| support lower bound | `EngineSupport.recorded_support_lower_HS` | `EngineSupport.lean:213-228` |
| vote classes | `Ledger.Sclass/Xclass/Bwin`, `Sval/Xval/Bval` | `Ledger.lean:83-139` |
| **the per-fork ledger** | `Endpoint.ghost_step_dominates` | `Endpoint.lean:113-128` |
| boost bridge | `MajorityPersists.fork_weight_lt`, `fork_majority` | `MajorityPersists.lean:90-130` |
| covered/margin disjunction | `CoveredMargin.head_ge_of_covered_or_descend_chain` | `CoveredMargin.lean:78-95` |
| honest vote ⟹ recorded everywhere | `Delivery.vote_lands`, `Delivery.vote_ubiquity` | `Delivery.lean:565-590`, `:733-765` |
| recorded ⟹ real past attestation | `Execution.latestMessageProvenance` | `Provenance.lean:360-366` |
| honest target = head's boundary block | `Delivery.honest_attestation_data_target_root` (by `rfl`) | `Delivery.lean:266-270` |
| Byzantine fraction per span | `ByzantineBound.span_fraction` | `Model/Assumptions.lean:529-533` |
| every validator re-votes each epoch | `ExternalsCoherence.committee_coverage` | `Model/Assumptions.lean:442-446` |
| justified ⟹ honest causal vote | `Execution.globalJustified_honestTarget` | `AcceptedCurrentSameEndpointSource.lean:71-80` |

The canonical spec-layer statement of "enough weight ⟹ head descends X" is `Endpoint.lean:113-128`:

```
Xval + Bval + get_proposer_score + 1 ≤ Sval    (at every fork on X's chain)
  ⟹ get_weight sibling < get_weight chain-child ⟹ DescendStep ⟹ head ⪰ X
```

with `Sval` = **honest** window members supporting `subtree(X)`, `Xval` = honest but
sibling-stuck, `Bval` = non-honest window members.

Note in passing: `AheadFacade.lean:70` cites `fork_majority_of_windows`, which no longer exists;
the live name is `MajorityPersists.fork_majority` (`MajorityPersists.lean:118-130`). Stale
citation, worth fixing whatever else happens.

### 2.4 Q2 verdict

The filter constrains the head **only** relative to the *realized* justified checkpoint; it says
nothing about unrealized justifications, exactly as P-6 charges. The weight engine needed to say
more is already present in spec-native form. What is missing is not machinery — it is an input.

---

## 3. The crux, step by step, adversarially

Target: honest `w`, in-horizon `m`, `c` `JustifiedIn (store w m)`, `c.root` known,
`jc(w,m).epoch < c.epoch` ⟹ `head(w,m) ⪰ c.root`.

### 3.1 Step 1 — quorum. Sound, but two gates must be discharged first

`justified_requires_targets` (`TheoremStatements.lean:139-155`) yields
`S ⊆ E.span_committee (c.epoch · slots_per_epoch) (c.epoch · slots_per_epoch + slots_per_epoch − 1)`
with `2 · total_active ≤ 3 · weight S`, every member witnessed by an attestation event with
`a.data.target = c`. Committees: **`c.epoch`'s own**, the full 32-slot span.

It is gated on `E.genesis_store.justified_checkpoint.epoch < c.epoch` and
`c.epoch < E.verification_horizon`; `justified_descends` has neither gate. Both look
dischargeable:

* genesis gate ← `jc(w,m).epoch < c.epoch` + `Execution.store_justified_epoch_mono`
  (`AcceptedActualFCRContractScaffold.lean:272-275`, unconditional) + `store w 0 = genesis_store`;
* horizon gate ← `WithinHorizon m` unfolds to
  `compute_epoch_at_slot cfg (E.slot_at cfg m) < E.verification_horizon`
  (`Model/Execution.lean:78-81`), so it needs `c.epoch ≤ epoch(slot_at m)` — the checkpoint-epoch
  bound family in `Proof/CausalCheckpointEpochBound.lean`, `Proof/CheckpointDomain.lean`.

Also worth noting: `JustifiedIn` (`TheoremStatements.lean:44-49`) has a fifth disjunct
`∃ r ∈ block_roots, unrealized_justifications r = c`, so `c` can be the unrealized justification
of an adversarial block. `justified_requires_targets` covers that disjunct too, so step 1 is
uniform.

### 3.2 Step 2 — honest share. `(2/3 − β)` in the worst case

`ByzantineBound.span_fraction` gives `100·byz(span) ≤ C·W(span)` with
`C = cfg.confirmation_byzantine_threshold`, `C ≤ 25` structurally (`Config.lean:35-39`), `= 25`
on mainnet (`:66`). The adversary is free to put **all** of its weight inside the quorum, so the
worst-case honest quorum share is `2/3 − β`, not `2/3`.

### 3.3 Step 3 — latest messages. One good surprise, one fatal obstruction

**Good surprise.** The pinned validator gate makes every *recorded* target-`c` attestation an LMD
vote inside `c`'s subtree, Byzantine ones included:

```python
    # LMD vote must be consistent with FFG vote target        # fork-choice.md:804-807
    assert target.root == get_checkpoint_block(store, attestation.data.beacon_block_root,
                                               target.epoch)
```

and the model keeps it: `Delivery.honest_attestation_data_target_root` (`Delivery.lean:266-270`)
is literally `rfl`, and `latest_messages` is written only through `on_attestation`
(`Handlers.lean:238-256`). So at the instant just after the quorum is recorded and before any
epoch-`(c.epoch+1)` vote lands, the *recorded* support for `c`'s subtree is `≥ 2/3` against
`≤ 1/3` — and the boost is `1.25 %` of total. **Instantaneous dominance holds.**

**Fatal obstruction.** The instant does not persist, and the spec's ledger is honest-only for
exactly that reason. Plug the quorum into `Endpoint.ghost_step_dominates`:

```
Sval ≥ (2/3 − β)·W            (honest quorum share)
Xval ≤ J − Sval = (1 − β) − (2/3 − β) = 1/3 · W     (honest, sibling-stuck)
Bval ≤ β·W
boost = pb·W, pb = 40/100/32 = 0.0125
```
The required `Xval + Bval + boost + 1 ≤ Sval` becomes

```
        1/3 + β + pb  <  2/3 − β        ⟺        β < 1/6 − pb/2 ≈ 0.1604
```

At the spec's own design point `β = 0.25` this reads **`0.5958 < 0.4167` — false.** The honest
quorum share `5/12` loses to `7/12`.

**Independent confirmation from the paper.** `Paper/LMDGhost/Proof/Quorum.lean:88-92`
(Lemma 4, `P_base_of_Q`) requires

```lean
    (hQ : Q A cm V b s > (1 / 2) * (1 + Wp A pb / W A cm b s) + fm.β)
```

i.e. `Q > 1/2·(1 + pb) + β`. With `Q = 2/3` and `pb = 0.0125` that is `β < 0.1604` — the same
number, derived independently. And `FaultModel.hβ : β < 1/3` (Paper `Core/Model/Validators.lean`)
is *not* what makes Lemma 4 apply: the threshold does.

**Does the inductive route rescue it?** No, not in the ahead window. Running the head-safety
strong induction over slots (the IH shape already used at `CoveredMargin.lean:209-214`,
`AnchorClose.lean:416-419`): honest validators who re-vote after the quorum land in `c`'s
subtree, but Byzantine committee members who re-vote leave it, at `≤ β/32` of total per slot by
`span_fraction` at `[t,t]`. Worst case (all honest re-voters were already in the quorum, so they
add nothing), dominance survives `k` slots only while `2/3 − βk/32 > 1/3 + βk/32 + pb`, i.e.
`k < 32·(1/3 − pb)/(2β) ≈ 20.5` at `β = 0.25`. The ahead window is up to a **full** epoch — the
store's realized `jc` only advances at `update_checkpoints`/pull-up, so an unrealized
justification can sit ahead for the rest of the epoch. Roughly the last third of the window is
uncovered.

**So the crux outcome is a genuine gap, and it is quantitative, not an engineering shortfall.**
The precise missing input is: *no spec-side premise bounds how much recorded LMD support has
migrated off a justified checkpoint's subtree since its quorum.* `Synchrony.latest_message_relay`
(`Model/Assumptions.lean:173-180`) propagates latest messages with **monotone epochs only** — it
says nothing about where they point.

Two in-tree claims are wrong at `β = 25` and should be corrected whatever route is taken:

* `TheoremStatements.lean:281-292` — "2/3 of an epoch's attesters named it as target; honest
  ones' newest messages keep descending from it".
* `AheadFacade.lean:68-70` — "the 2/3 bound feeds the same … descent used by the confirmation
  engine, with no boost/discount arms **because 2/3 exceeds the confirmation bar**".

### 3.4 The weakest gate that closes it — candidates, honestly assessed

* **G1, β-gate.** Add `cfg.confirmation_byzantine_threshold ≤ 16` as a hypothesis of the derived
  lemma. Mathematically closes it; a real change to the design point, and `Config.lean:66` pins 25.
* **G2, drift/freshness gate.** "At `(w,m)` the recorded support that has moved off `c`'s subtree
  since the quorum is `< (1/3 − pb)/2` of total." True by definition of what is needed, not
  derivable from anything present, and unnatural at the use sites.
* **G3, coverage gate.** Drive `Xval`/`Unrec` to zero with `committee_coverage`
  (`Assumptions.lean:442-446`, cf. `LedgerV2.Uval_eq_zero_of_coverage`) — needs a full epoch of
  honest re-voting *after* the quorum, which is precisely what the ≤1-epoch ahead window does not
  provide.
* **G4, ubiquity/certified-evidence gate.** "`c` was observed by all honest nodes"
  (fast-confirmation.md:94) plus the FCR's certified-evidence delta. This is available at both
  real sites — but it buys *delivery*, which was never the problem; the arithmetic obstruction is
  untouched. G4 collapses into G2.

**No free gate exists.** The smallest sound premise is the head-safety conclusion itself, named
honestly as an LMD premise rather than an FFG export.

---

## 4. The paper-transplant option

* **The arithmetic core is model-agnostic.** `Model/Weights.lean` (72 LOC) + `Proof/Weights.lean`
  (85) + `Proof/Positivity.lean` (88) + `Proof/Quorum.lean` (218) + `Proof/Monotone.lean` (139)
  = **602 LOC / 31 theorems**, and they see the view only through an opaque
  `V.supportsLMD b i s : Bool` inside `Finset.filter`s. `Proof/Quorum.lean:70-73`
  (`g_mono_helper`) has no model type at all. `CommitteeHonestMajority`
  (`Paper/LMDGhost/Model/Assumptions.lean:21-24`) is pure Finset/weight arithmetic and is the
  exact analogue of `ByzantineBound.span_fraction`.
* **The engine proper does not transplant.** `Proof/HeadSafety.lean` (617),
  `Proof/Canonical.lean` (433), `Proof/Support.lean` (218), `Proof/Propagation.lean` (37) all
  carry `Synchrony`, `HonestNoForgery`, `HonestBehavior`, `τ.AfterGST` and `ViewValid` — bound to
  the paper's `View`/`ViewFamily` model (`Paper/Core/Model/View.lean:22-63, 82-140`).
* **Half the transplant has already been done, and the other half was already rejected for this
  exact reason.** `Spec/Proof/Fraction.lean` (188 LOC) says in its header (`:8-11`) that it is a
  port of `Paper/LMDGhost/Model/Weights.lean` + `Proof/Monotone.lean` into ℕ, cross-multiplied,
  with an abstract supporter predicate `sup : ValidatorIndex → Prop` replacing `supportsLMD`.
  Lines `:31-41` record that the **absolute-margin endpoint (`Hmargin_of_fraction` /
  `Hmargin_of_confirmed`) was removed because the spec's `β ≤ 1/4` mismatched the `β = 1/3` used
  there.** That is P-6's obstruction, already discovered once, in-tree.
  `Spec/Proof/HeadSafetyEngine.lean` (283 LOC) similarly mirrors `head_safety_at_slot` /
  `head_safety_engine` natively.
* **No bridge exists and none is planned:** no `Spec` file imports `FastConfirmation.Paper.*` or
  vice versa; `FastConfirmation.lean:14-15` states outright that the repository "claims no formal
  refinement theorem between them".

**Q4 verdict:** there is nothing to transplant that the spec layer does not already have in
native form. A transplant would import the paper's `β < 1/6 − pb/2` threshold along with the
arithmetic — i.e. it delivers G1, not a proof at `β = 25`.

---

## 5. Recommendation, waves, blast radius

**Verdict: a gated, narrowed, relocated field is the right endpoint.** The unconditional field is
not derivable at the spec's design point, and the paper does not derive it there either.

**Blast-radius facts that make this cheap.**

* `JustificationInterface` is **never constructed** anywhere in the repo: a grep for
  `justified_descends :=` returns nothing, and the record appears only as a hypothesis (97
  occurrences of `JustificationInterface cfg ext E`). So weakening a field is free except at its
  projection sites — of which there are **two**.
* The **accepted public theorem is unaffected**. `acceptedSpec_safety_next_slot`
  (`AcceptedActualFCRNextSlotSafetyFacade.lean:269-272`) is stated over
  `AcceptedActualFCRNextSlotSafetyAssumptions` (`:33-47`), which does not mention
  `JustificationInterface` — and since the record has no constructor, a theorem that does not
  assume it cannot use it. P-6 rides only the **weak/strong headline** premise surface, via the
  explicit `hji` binder at e.g. `WeakObservedResetSeedSafety.lean:179-181, 207-209` and
  `WeakTrajectorySafety.lean:611, 684`.

### Wave 0 — reachability check (≈ half a day)

Delete the field, build, and see which of the two sites actually breaks. Specifically: is
`justified_descends` in the *proof terms* of the weak headlines, or only in their *premise
surface* via `hji`? (`ObservedFilterResiduals` is consumed at `INVstarTrack.lean:413`,
`StrongPrefixSafety.lean:65`, `AnchorThread.lean:340`, `Suppliers.lean:205` — all
`Spec_Safety`/L4-residual routes; the weak fold's own path uses `head_ge_of_justified_ge_K`
at `WeakObservedRestartDynamicSafety.lean:244, 678`.) If the weak headlines never project the
field, P-6's honest resolution is **deletion plus an explicit premise on the two routes that use
it** — the cheapest possible outcome, and it must be checked first.

### Wave 1 — narrow the field to what is consumed (≈ 1-2 days, ~80-120 lines)

Replace `∀ c. JustifiedIn (store w m) c → …` by the observed family actually instantiated, and add
the two `justified_requires_targets` gates so the field is at least *quorum-shaped*:

```
∀ v ∈ honest, ∀ n, ∀ w ∈ honest, ∀ m, n + 1 ≤ m → WithinHorizon m →
  let c := (fcrStep v n).current_epoch_observed_justified_checkpoint
  genesis_store.justified_checkpoint.epoch < c.epoch → c.epoch < verification_horizon →
  (store w m).justified_checkpoint.epoch < c.epoch →
    is_ancestor (store w m) (get_head (store w m)) (get_node_for_root c.root) = true
```

Gates discharged at the sites by `store_justified_epoch_mono`
(`AcceptedActualFCRContractScaffold.lean:272`) and the checkpoint-epoch bound family
(`CausalCheckpointEpochBound.lean`). Site A becomes a direct instance; site B needs
`AnchorCovSupply`'s observed route to pin `jcb := obs` (it already pins `jcb.root = obs.root`).
Blast radius: 2 proof sites, 2 docstrings, 1 row of `plumbing-spec-citations.md`.

### Wave 2 — relocate it out of the FFG interface (≈ 3-5 days, ~100-150 lines)

Move the narrowed statement from `JustificationInterface` into a named predicate next to
`AheadFacade.HeadTracksJustified` (e.g. `LMDHeadTracksObservedJustified`), carried explicitly by
the routes that consume it — the precedent is `Nucleus.CurrentEpochCoveringBridge`
(`Nucleus.lean:222-267`), which is "deliberately exposed as a predicate, not asserted as a
theorem", with its non-circularity argument written out. Effect: `JustificationInterface`
14 → **13** fields, all of them genuinely FFG; the LMD fact becomes a disclosed, separately-named
premise on the four weak headlines (+1 explicit premise there). This is what actually discharges
P-6 as an audit finding: the claim stops being presented as an FFG export with a spec citation it
does not have. Simultaneously fix the two false docstrings (§3.3) and the stale
`fork_majority_of_windows` citation (`AheadFacade.lean:70`).

### Wave 3 — the genuine derivation (≈ 2-4 weeks, ~800-1200 lines) — **only under G1**

If and only if the owner accepts a strengthened Byzantine bound for this lemma
(`C ≤ 16`, or a paper-Assumption-4-shaped `β < 1/6 − pb/2` premise), the derivation is
constructible from parts that all exist:

1. quorum from `justified_requires_targets` + the two gates (wave 1);
2. honest share `(2/3 − β)` from `span_fraction` over `c.epoch`'s 32-slot span;
3. quorum members' votes ⟹ recorded at every honest store from slot+1 on
   (`Delivery.vote_lands` / `vote_ubiquity`), and their LMD votes lie in `subtree(c.root)`
   (`honest_attestation_data_target_root` + fork-choice.md:804-807);
4. sibling upper bound from `latestMessageProvenance` slot-confinement + sibling disjointness
   (`Endpoint.recorded_sibling_le`, `Endpoint.lean:81-100`);
5. the per-fork inequality `Xval + Bval + proposer_score + 1 ≤ Sval` — **this is the step that
   needs G1**;
6. fold along `[jc.root, c.root]` via `descendStep_of_dom` → `is_ancestor_get_head_of_chain`,
   reusing `CoveredMargin.head_ge_of_covered_or_descend_chain` for the covered edges.

Estimate: ~300 lines for (1)-(4) (mostly adapting `EngineTransport`'s `HS0_in_AttSupporters`
shapes to an FFG-quorum window instead of a confirmation window), ~200 for (5)-(6), ~300 for the
walk/domain plumbing at both sites, plus the config-premise threading. It does **not** remove a
premise — it trades an unmotivated LMD assertion for a tighter, motivated Byzantine bound.

---

## 6. One-paragraph summary for the owner

P-6 is not a plumbing omission; it is a real mathematical gap at the spec's own design point. The
fork-choice filter demonstrably cannot deliver the ahead regime, the spec layer already owns the
entire LMD weight engine needed to try, and the try fails: converting an FFG 2/3 quorum into
LMD head-domination needs `β < 1/6 − pb/2 ≈ 16 %`, while `CONFIRMATION_BYZANTINE_THRESHOLD = 25`.
The paper's Lemma 4 carries exactly that threshold in its hypothesis, so transplanting it imports
the constraint rather than removing it — and `Spec/Proof/Fraction.lean:31-41` records that this
development already hit, and retreated from, the same β mismatch once. The honest endpoint is to
narrow the field to the single observed-checkpoint instance both consumers use, gate it on the
quorum conditions, and move it out of `JustificationInterface` into a named LMD premise in the
style of `Nucleus.CurrentEpochCoveringBridge` — after first checking (wave 0) whether the weak
headlines project the field at all, since the accepted public theorem provably does not.

---

## 7. W0 outcome — executed, the field is deleted

**Status:** landed on `centaur/weak-synchrony-202609150824` in `fe724fd` (code) and the docs
commit that follows it. `bash scripts/check_build.sh` green; `lake env lean scripts/Audit.lean`
passes with **21 witnesses** (10237 declarations, 6404 theorems, 26 generated partials,
sorry-free, `[propext, Classical.choice, Quot.sound]` only).
`JustificationInterface` is **14 → 13 fields**.

### 7.1 The reachability computation

Computed from the compiled environment (a throwaway `lake env lean` script, not committed):
forward closure of the 21 `scripts/Audit.lean` `publicWitnesses` over the constants appearing in
each declaration's **type and proof term**, transitively, then intersected against the
projection-site set.

| quantity | value |
|---|---|
| declarations in the whole project mentioning `justified_descends` | **2** (`ExportWiring.headTracksJustified_of_interface`, `AnchorClose.head_ge_glc_endpoint`) — a fresh `rg '\.justified_descends'` agrees, and §1.3's name-collision finding is confirmed |
| forward closure of the 21 witnesses | **19251** constants, **5353** of them from `FastConfirmation.*` modules |
| `JustificationInterface.justified_descends` in that closure | **no** |
| either projection site in that closure | **no** |
| `JustificationInterface` (the structure) in that closure | **yes** — it is a binder on W20–W23, which is why deleting a field weakens audited witnesses |

**The control that makes this decisive.** The same pass was run for all 14 fields. Exactly one
is reachable:

| field | project decls mentioning it | reachable ones | field in closure |
|---|---|---|---|
| `checkpoint_known` | 21 | **1** (`Execution.head_root_known`) | **yes** |
| `justified_descends` | 2 | 0 | no |
| the other 12 | 0–6 each | 0 | no |

So the method discriminates: it finds the one field the audited witnesses really do project, and
it says `justified_descends` is not one of them. **Verdict: UNREACHABLE from all 21 witnesses.**

### 7.2 Where §5's plan was right, and where it overshot

§5 predicted "deletion plus an explicit premise on the two routes that use it". Half of that is
what landed; the other half was a **mechanization overshoot**, and the correction came from the
owner's observation that the rule's own banking already carries the ancestry.

**Site B (`AnchorClose:927`) did not need a premise — the fold was redundant.** §1.2 correctly
noted that site B is behind the unproduced `AnchorCovSupply` flag, but missed that the flag's
observed disjunct is *tagged*: its first conjunct is
`r₀ = (fcrStep v n).current_epoch_observed_justified_checkpoint.root`, and
`safeFromGlc_of_covSupply` already threads `hobs : SafeFrom obs.root (n+1)` — whose unfolding
*is* `head(w,m) ⪰ obs.root` for every honest `w` and `m ≥ n+1`. The proof's own pre-deadline
branch had always used exactly that (`simpa only [hobserved] using hobs w hw m hm hH`); only the
post-deadline branch detoured through the 4-case fold. The post-deadline branch now finishes
through `finishDirect` like the confirmed and finalized kinds, and `head_ge_glc_endpoint` is
deleted as dead code. No weight arithmetic, no β gate, no new hypothesis.

**The accepted/actual route never needed it either.** `get_latest_confirmed`
(`Model/Confirmation.lean`) computes
`is_head_unrealized_justified_ok := decide (fcr_store.current_epoch_observed_justified_checkpoint
= store.unrealized_justifications head)` — a **runtime re-check** that the observed checkpoint is
the head's *own* unrealized justification. That is the executable form of the owner's point, and
it is why `AcceptedObservedRestartDynamicSafety.safeFrom_of_acceptedDynamics` proves the observed
anchor's `SafeFrom` with no head-tracking premise at all, and why
`StrictSelectorAdvanceGeometryAt.descends_input` gets `result ⪰ afterObserved` mechanically.

**Site A (`ExportWiring`) does still need it, and the transitivity route provably cannot close
it.** Two independent reasons, both citable in-tree:

1. *It is the base of the transitivity, not a step in it.* Site A produces
   `ObservedFilterResiduals.observed_head_ahead`, which is what
   `AnchorFacade.safeFrom_observed_of_filter_K` turns into `SafeFrom obs.root` — i.e. into `hobs`
   itself. Deriving `hobs` from "head ⪰ candidate, candidate ⪰ obs" is circular: `hobs` is one of
   the three reset anchors the fold consumes *in order to* establish the candidate's safety. (At
   site B the orientation is the same but harmless, because there `hobs` arrives threaded.)
2. *The strong rule has no chain-intrinsic banking to lean on.* Rule delta 5's
   `Weak.headUnrealizedJustification_known_and_below` works because the **weak** rule banks
   `store.unrealized_justifications (get_head store).root` — a read off the head's own chain. The
   **strong** rule's `update_fast_confirmation_variables` (`Model/Confirmation.lean`) rotates in
   `store.unrealized_justified_checkpoint` / `previous_epoch_greatest_unrealized_checkpoint` —
   *store-global running maxima*, confirmed by `MicroSteps.fcrStep_observed_boundary`. And the
   claim that a store-global running maximum lies on the certified head's chain is recorded in
   this repository as **false in general**: the branch-switch hole, written out in
   `Model/WeakSynchrony.lean`'s and `Proof/WeakBankedJustification.lean`'s headers (and
   `docs/weak-synchrony.md`) — "between the second at which the running maximum was captured …
   and the boundary at which the gate fires, the store's checkpoints may move to a different
   branch, so the certified head need not descend from the banked root at all". That is exactly
   the `banked_below_supplier` field Francesco's revision *removed* rather than assumed. There is
   no non-`Weak` counterpart of `auCheckpoint_known_and_below_tip`, and its hypotheses
   (`ExactPrefixAcceptedFFGSemantics`) are not available from `SpecAssumptions` anyway.

So the residual is not a β-conditional lemma and not a general assumption — it is **one premise
on one legacy route**, the `SpecAssumptions` observed-anchor bundle, which is precisely the route
that lacks the runtime guard the actual algorithm performs.

### 7.3 What landed

* **`TheoremStatements.lean`** — field deleted, 14 → 13. A comment in its place records why, and
  the module header no longer presents the claim as an FFG export.
* **`AheadFacade.HeadTracksJustified`** — already binder-identical to the old field, this is now
  the fact's only home. Its docstring carries the finding: the `β < 1/6 − pb/2` arithmetic with
  the `Endpoint.ghost_step_dominates` ledger, the `β = 1/4` counter-reading `5/12` vs `7/12`, the
  paper's Lemma 4 threshold (`Paper/LMDGhost/Proof/Quorum.lean:88-92`), the `Fraction.lean:31-41`
  precedent, where the fact survives and where it does not, and the reachability numbers.
* **`AnchorClose.lean`** — observed route rewired to `hobs`; `head_ge_glc_endpoint` deleted, with
  a section note in its place. `AnchorCovSupply` keeps its `jcb` covering payload unchanged (the
  flag is never produced in-tree and `Nucleus.covering_comparability` /
  `CurrentEpochCoveringBridge` are still stated in that field shape), so its observed payload is
  now unused — a candidate for a later, separate narrowing.
* **`ExportWiring.lean`** — `headTracksJustified_of_interface` deleted;
  `observedFilterResiduals_of_interface` takes `htracks : E.HeadTracksJustified cfg ext`.
* **premise threading** — `htracks` is carried explicitly by
  `shellResiduals_of_strongPrefixSafetyInputs`, `soundResidualsGround_of_split`,
  `l4Residual_of_advance`, `Spec_Safety_of_anchored` and the `Spec_Safety_*` /
  `Spec_Monotonicity_*` conditional theorems downstream of them (`StrongPrefixSafety`,
  `INVstarTrack`, `LastCruxes`, `Suppliers`, `ShellCompose`, `Definitive`, `Shrink`, `Compose`,
  `Closing`, `Knownness`, `AnchorThread`, `AnchorClose`). None of these is an audited witness.
* **false claims fixed** — the deleted field's docstring ("2/3 of an epoch's attesters named it
  as target; honest ones' newest messages keep descending from it") is gone with the field;
  `AheadFacade`'s "with no boost/discount arms because 2/3 exceeds the confirmation bar" is
  replaced by the arithmetic that refutes it; the stale `fork_majority_of_windows` citation now
  reads `MajorityPersists.fork_majority`. Stale prose in `HeadReroot`, `HeadRerootChain`,
  `SelectedFilterBridge` and `AnchorClose`'s own header is updated.

### 7.4 Effect on the premise surface

* `hji` shrinks from 14 to 13 fields on **every** witness carrying it — W20–W23, the four weak
  trajectory headlines. This is a strict premise weakening: no witness gained anything.
* The accepted public theorem is unaffected, as §5 predicted (it is stated over
  `AcceptedActualFCRNextSlotSafetyAssumptions`, which never mentioned
  `JustificationInterface`).
* The unproven content now appears in exactly one place — `HeadTracksJustified` — visible in the
  signature of every legacy route that uses it, and in none of the 21 audited witnesses.

### 7.5 What is *not* closed

W1 (narrowing to the observed family), W2 (the relocation, now done) and W3 (the full derivation
under `β ≤ 1/6`) are superseded as stated. The live question is narrower and better posed:

> Can the legacy `SpecAssumptions` observed-anchor route be given the same runtime guard the
> actual algorithm has (`obs = store.unrealized_justifications head`), so that
> `HeadTracksJustified` is discharged there the way
> `AcceptedObservedRestartDynamicSafety` already discharges it on the accepted route?

If yes, the premise disappears entirely rather than being weakened. If no — because the legacy
route quantifies over rotated checkpoints with no such guard — then the honest conclusion is that
the legacy `SpecAssumptions` route is strictly weaker than the accepted one and should be
retired rather than repaired, since the accepted route already proves the fact outright.
