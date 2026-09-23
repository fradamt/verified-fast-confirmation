module
public import FastConfirmationPaper.Core
public import FastConfirmationPaper.LMDGhost
public import FastConfirmationPaper.HFC.Model
public import FastConfirmationPaper.HFC.Claims
public import FastConfirmationPaper.HFC.ReviewTheorem

/-!
# HFC

Root facade for the §4 **LMD-GHOST-HFC / FFG-Casper** layer of the Fast
Confirmation Rule (arXiv:2405.00549 §4). It builds additively on the §3.1
LMD-GHOST module (`Core` + `LMDGhost`), instantiating `Payload := FFGVote n` and
the eligibility seam at `flt := ffgFilter`, and reusing the filter-generic engine
`HeadFutureAgreement`.

§4 definitions include the Algorithm-1 rule-shaped predicate
`isConfirmedNoCaching`, the wrapper `isConfirmedAlg1`, and the block-contained
AU vote surface. The theorem facade discharges the gate-free Algorithm-1
theorems `HFC_Safety_Alg1` and `HFC_Monotonicity_Alg1` alongside the underlying
gate-based proof interfaces.

Import `FastConfirmation.Paper.HFC` for the complete Section 4 development, or
`FastConfirmation.Paper` for the whole paper companion.

See `docs/paper-model-design.md` (§4 HFC seam), `docs/algorithm1-gate-discharge.md` (the
semantic-gate elimination), and `docs/model-annotation.md` (paper↔Lean) for the design
and the paper mapping.
-/
