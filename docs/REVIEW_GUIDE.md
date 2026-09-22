# Review guide

G3 Gloas status: **STOP-false at G2-004**. Full validation fails at payload
branch selection. The new synchrony field closes G2-003; it does not close
G2-004. See [the exact-source negative result](gloas-negative-result.md).
The public witness declaration texts are unchanged, but there is no completed
Gloas proof or full trust-audit result.

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
`477321355d48d527e7e1e4d572f6a40a0b41072a`. The manifest in
`spec_source/manifest.json` records the exact twelve source and configuration
objects consumed by the model.

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

## Gloas synchrony strengthening (22 September 2026)

`PaperSafetySynchrony` gains one field. This strengthens the assumptions of
the accepted theorem even though its public declaration text is unchanged.
The field is verbatim:

```lean
  /-- Verified payload envelopes known to an honest node reach every honest
      node by the last second of the same slot. As in `block_relay`, the
      receiving state is horizon-scoped; `m + 1` only locates its deadline. -/
  payload_envelope_relay : ∀ v ∈ E.honest, ∀ n r,
    E.WithinHorizon cfg n →
    is_payload_verified (E.store cfg ext v n) r = true →
    ∀ w ∈ E.honest, ∀ m,
      E.WithinHorizon cfg m →
      E.slot_at cfg n + 1 ≤ E.slot_at cfg (m + 1) →
      is_payload_verified (E.store cfg ext w m) r = true
```

The bound is the same as `block_relay`: a verified envelope must be present
at every honest receiver by the last second of the sender's slot. The
receiving state, rather than its successor, is within the horizon. Payload
persistence carries this fact through the tick and every event prefix at
the next slot boundary. Thus an honest index-1 vote finds a verified payload
before validation. No other assumption record gains a field. The legacy
`Synchrony` conversion now needs explicit evidence for this new field.

Payload availability alone does not compare FULL and EMPTY branch weights.
The local experiment in `scripts/GloasPayloadBranchObstacle.lean` is not an
accepted execution. The new [negative result](gloas-negative-result.md) uses
honest singleton votes and the new relay field. See also
[the historical obligations](gloas-proof-obligations-history.md).
