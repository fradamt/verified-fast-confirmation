module
public import FastConfirmationPaper.LMDGhost.Model.Weights
public import FastConfirmationPaper.LMDGhost.Model.OneBlockConfirmation
public import FastConfirmationPaper.LMDGhost.Model.ConfirmationRule
public import FastConfirmationPaper.LMDGhost.Model.Assumptions

/-!
# LMDGhost / Model

Model-only facade for the §3.1 LMD-GHOST confirmation rule: the weights
(`S`, `W`, `Wp`, `Q`, `safetyThreshold`), the Definition 8 predicate
(`isOneConfirmed`, `isLMDGHOSTSafe`), and Algorithm 4 (`isConfirmed`,
`highestConfirmedSinceEpoch`, `sg`).
-/
