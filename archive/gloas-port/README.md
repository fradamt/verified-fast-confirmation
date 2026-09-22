# Gloas port preservation

These patches preserve the Gloas port from WIP snapshot `33a8bf9`, plus the compiler repairs from lane g2b. Their base is `fe652f4`. They are review artifacts. They do not establish the Gloas safety theorem.

G2-003 needs receiver payload verification before an index-1 vote. G2-004 needs a proof that the pending parent selects the payload branch used by the chosen beacon child. The current assumption surface does not supply these proof steps. Public statement texts and the 13 witness declaration texts are unchanged.

The groups are path limited:

- `model.patch`: Gloas model types, helpers, handlers, execution, and local handler effects.
- `proofs.patch`: proof migration, local payload lemmas, and the Spec facade. This group contains unresolved proofs.
- `harness.patch`: schema v2, Python export, interpreted Lean comparison, and finite checks.
- `docs.patch`: the port's README and source/conformance documentation. These describe the candidate port, not a proved result.

The patches use zero context to avoid trailing spaces in stored diff context lines. Apply them only at the exact base, with `--unidiff-zero`.

`manifest.json` lists each path and its candidate SHA-256. It also gives a hash for each patch. The 918 MB partial generated trace in the WIP snapshot is excluded. The original file remains a local artifact; it is not a complete conformance result.

To inspect the complete candidate, use a disposable checkout at `fe652f4` and apply the four patches together. The patch set is not a sequence of independently buildable implementation changes: the node type change and proof migration are coupled, and the proof gaps remain. Do not apply only the model patch to a proved tree and claim a Gloas safety result.

```sh
git apply --unidiff-zero model.patch proofs.patch harness.patch docs.patch
```

The executable model and its conformance runner can be built and checked separately from the unresolved proof modules. All Lean commands on this machine must use the shared lock:

```sh
flock /home/fradamt/lean/orch/g2-lean-slot.lock lake build FastConfirmation.Spec.Model.Execution FastConfirmation.Spec.Model.Assumptions
flock /home/fradamt/lean/orch/g2-lean-slot.lock lake env lean --run scripts/conformance/lean/Conformance.lean TRACE.jsonl
```

Use no network, install, push, or `lake clean`. See [proof-obligations.md](proof-obligations.md) for the exact missing goals and the local kernel checks. See [conformance-result.json](conformance-result.json) and [the conformance guide](../../docs/conformance.md) for the complete trace result. The external lane report records validation and the final commit list.

The restored active baseline passed full validation after preservation:
3,592 build jobs, no proof placeholders, and 13 public witnesses under the
standard-axiom trust audit. This validates the retained pre-port proof; it
does not validate the Gloas candidate in these patches.
