module
public import FastConfirmation.Spec
public import FastConfirmation.Paper

/-!
# Fast Confirmation Rule — repository facade

Root facade for the repository's two independent Lean developments:

* `FastConfirmation.Spec` models the Ethereum consensus specification and
  contains the primary accepted safety theorem.
* `FastConfirmation.Paper` contains the independent companion formalization of
  Sections 3.1 and 4 of arXiv:2405.00549.

The spec proof does not import the paper model, and this repository currently
claims no formal refinement theorem between them. See `README.md` for the
entry points and `docs/spec-annotation.md` / `docs/model-annotation.md` for the
two source mappings.
-/
