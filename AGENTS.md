# Repository guidance

This repository is the canonical public `verified-fast-confirmation` project.
Do not transplant files or source metadata from the pre-publication
`fast-confirmation-spec` development worktree.

## Architecture

- `FastConfirmation/Spec/` is the primary consensus-spec development.
- `FastConfirmation/Paper/` is an independent companion formalization.
- Neither tree may import the other. Only `FastConfirmation.lean` composes
  their public facades.
- Every Lean module must remain reachable from the appropriate facade. Add
  audit or counterexample modules to that facade deliberately; do not leave
  publication-orphaned modules.

## Source and theorem scope

- The public consensus-spec source pin is
  `30aa65fc21cf7f7c7dd1f7d6b686d0250462d04f`.
- `acceptedSpec_safety_next_slot` is the primary accepted guarantee.
- The mandatory boundary-call theorem and both strict-prefix counterexamples
  are part of the public disposition; do not broaden the theorem to arbitrary
  in-slot queries.
- A source-pin or model-semantics change requires human correspondence review
  of `docs/spec-annotation.md`. Passing the byte-level manifest check is not a
  semantic review.

## Validation

Run the fast deterministic checks while editing:

```sh
scripts/validate.sh --fast
```

Before committing, run the full suite:

```sh
scripts/validate.sh
```

The full suite builds the entire project and audits project declarations and
public theorem axioms. Lake promotes Lean's named `hasSorry` diagnostic, and
the build wrapper checks it independently, including in non-persistent
commands such as `example`. Do not weaken, skip, or silently reclassify a gate.
