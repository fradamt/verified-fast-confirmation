# Lean file conventions

- Start each new library `.lean` file with `module`.
- Use `public import` to preserve the library's transitive imports.
- After the import header, put declarations in an `@[expose] public section`.
  Close all inner namespaces and sections, then close the public section
  with `end`. Use the scope name when closing a named scope.
- An import-only file does not need a public section.
- Keep proof helpers private. The module system also keeps public theorem
  proof bodies private. Definitions used by public statements or exposed
  definitions must be public; keep other local helpers private where valid.
- Do not put public-section commands inside comments. Check scope closures
  when a file has nested sections or namespaces.
- Keep `scripts/Audit.lean` as a non-module script so its ordinary imports
  load proof bodies. A module-based audit would need `import all`.
- Run `scripts/validate.sh --fast` before a commit. Run
  `scripts/validate.sh` for library or import changes; it includes the build,
  import check, and trust audit. Do not change proof statements to fix a
  module visibility error.
