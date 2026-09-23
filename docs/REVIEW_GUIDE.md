# Review guide

## Weak observer premises after the main merge

`Execution.WeakObserverAssumptions` has this exact four-field declaration:

```lean
structure WeakObserverAssumptions (obs : ValidatorIndex) : Prop where
  base : SelectedMarginAssumptions cfg ext E
  genesis : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
    anchorState.slot = anchorBlock.message.slot ∧
    ext.AnchorCommitsToState anchorBlock.message anchorState ∧
    anchorBlock.message.parent_root ≠ anchorBlock.root
  validity : E.ObserverValidity cfg ext obs
  committees_agree : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s
```

The `validity` field uses this record:

```lean
structure ObserverValidity (E : Execution Root) (obs : ValidatorIndex) : Prop where
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot
```

`ObserverValidationState` means a keyed block or checkpoint state in the
observer's genesis store or a scheduled handler prefix at that observer. This
is a smaller domain than the pre-merge unconditional attestation laws. It
does not require the observer to be honest. The weak proofs derive observer
non-equivocation and latest-message provenance from this field.

The direct one-shot forms keep their separate margin and coherence premises.
They are not the full-rule premise bundle above.

## Known scope limits

Pending user decision:

- Optimistic-sync `VALID` status is not modelled. The normative `MUST` in
  `is_one_confirmed` is not implemented in the Python function body either.
- Execution, envelope, and bid checks are opaque Boolean externals with no
  source-soundness law.
- The paper-model Algorithm-1 monotonicity witness assumes future confirmation
  of honest-view-safe blocks.
- Live monotonicity needs an FFG timing premise. See
  [Missing FFG timing premise](#missing-ffg-timing-premise).

### Missing FFG timing premise

The proposed live premises do not bound when unrealized justification reaches
the selector. A live proof needs an FFG timing premise for that update.

## Trust and architecture

The repository publishes two independent developments. `FastConfirmation.Spec`
models the executable Ethereum consensus specification and contains the primary
accepted theorem. `FastConfirmation.Paper` formalizes the companion paper. There
is no refinement theorem between them, and cross-imports are prohibited.

All Lean modules must be reachable through their own public facade and then
through `FastConfirmation.lean`. This keeps internal experiments, historical
audits, and countermodels out of the publication unless they are deliberately
made part of a reviewed import cone.

Imports are checked using the parser from the repository's pinned Lean
toolchain (`lean --deps-json`), not a duplicate header grammar.

The accepted Spec result is next-slot stored-output safety. The literal
mandatory boundary-call result is also proved. Optional calls at arbitrary
in-slot action prefixes are not covered; the two exported strict-prefix
counterexamples are required regression results, not ancillary examples.

The primary assumption surface is the GST-0 specialization. Public safety
endpoints and static-set laws use a finite verification horizon.
`HorizonVoteDeliveryLookahead` can also require the mandated receipt at the
first second of the following slot, just outside the endpoint cutoff. Legacy
or exact-current statement vocabularies are diagnostic surfaces, not
substitutes for the accepted theorem.

## Consensus source

The authoritative public source is `ethereum/consensus-specs` commit
`6b9bd532cca16555e2f3282d757622ebff29743e`. The manifest in
`spec_source/manifest.json` records the exact six source and configuration
objects consumed by the model. The local Gloas payload-aware discount is a
documented deviation. The weak Python branch `fcr-weak-synchrony-gloas` at
`353eb0dc4` is a further overlay.

The manifest proves byte identity and provenance only. A pin change must also
be reviewed against:

- `docs/spec-model-design.md`
- `docs/spec-annotation.md`
- `FastConfirmation/Spec/Model/`
- the accepted assumption surface and theorem statement

Regenerating hashes never establishes semantic faithfulness by itself.

## Deterministic gates

`scripts/validate.sh --fast` checks:

- the pinned consensus-source Git objects and content hashes;
- fail-closed exact strings for proof placeholders, native decision shortcuts,
  implementation overrides, and `#exit` are absent from project Lean sources
  (including comments and strings);
- whitespace errors in the pending Git diff and project text.

`scripts/validate.sh` additionally runs:

- facade reachability and Spec/Paper independence using Lean's own parser;
- `scripts/check_build.sh`, elaborating the complete import graph and rejecting
  Lean's proof-placeholder diagnostic even for non-persistent commands;
- `scripts/Audit.lean`, which inspects declarations originating in project
  modules and checks an exact public theorem witness set.

The Lean build and environment audit are authoritative for elaborated
declarations. Lake promotes Lean's named `hasSorry` diagnostic and the build
wrapper independently rejects its diagnostic text, including for
non-persistent commands such as `example`. The audit rejects `sorryAx`, unsafe,
source-authored partial, axiom, constant, opaque, extern, and `implemented_by`
project declarations.
Equation-compiler partial implementation details are recognized generically
through Lean's declaration-range metadata and must have safe public parents.
The audit permits only `propext`, `Classical.choice`, and `Quot.sound` in
project declaration dependencies.

GitHub CI runs the same deterministic gates with a checksum-pinned Elan
bootstrap. It uses no model API and receives read-only repository permissions.
The bundled `leanchecker` is intentionally not a blocking gate: on this
295-module environment it fans out replay work across matching modules, is not
an external verifier, and showed an unsuitable runtime/memory profile for
routine hosted CI.
