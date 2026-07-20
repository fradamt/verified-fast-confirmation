import FastConfirmation.Paper.LMDGhost.Model.Weights
import FastConfirmation.Paper.LMDGhost.Model.Confirm
import FastConfirmation.Paper.LMDGhost.Model.Rule
import FastConfirmation.Paper.LMDGhost.Model.Assumptions

/-!
# LMDGhost / Model

Model-only facade for the §3.1 LMD-GHOST confirmation rule: the weights
(`S`, `W`, `Wp`, `Q`, `safetyThreshold`), the Definition 8 predicate
(`isOneConfirmed`, `isLMDGHOSTSafe`), and Algorithm 4 (`isConfirmed`,
`highestConfirmedSinceEpoch`, `sg`).
-/
