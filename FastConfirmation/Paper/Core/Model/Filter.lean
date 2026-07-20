import FastConfirmation.Paper.Core.Model.View

/-!
# Core / Model / Filter

The block-eligibility filter that parameterizes the fork choice. Plain
LMD-GHOST uses `trivialFilter`; the §4 HFC layer instantiates the same seam with
its FFG checkpoint filter, so the §3.1 weight machinery is filter-agnostic.
-/

namespace FastConfirmation

/-- A block-eligibility filter, as seen in a view at a time. -/
abbrev BlockFilter (n : ℕ) (P : Type) := View n P → Time → Block n → Prop

/-- The trivial filter (everything eligible) — plain LMD-GHOST. -/
def trivialFilter {n : ℕ} {P : Type} : BlockFilter n P := fun _ _ _ => True

end FastConfirmation
