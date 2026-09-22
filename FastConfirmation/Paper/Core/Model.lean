module
public import FastConfirmation.Paper.Core.Model.Time
public import FastConfirmation.Paper.Core.Model.Blocks
public import FastConfirmation.Paper.Core.Model.Validators
public import FastConfirmation.Paper.Core.Model.Vote
public import FastConfirmation.Paper.Core.Model.View
public import FastConfirmation.Paper.Core.Model.Filter
public import FastConfirmation.Paper.Core.Model.ForkChoice
public import FastConfirmation.Paper.Core.Model.Honest

/-!
# Core / Model

Model-only facade for the shared FCR vocabulary (time, blocks, validators,
votes, views + synchrony, the eligibility filter, and the LMD-GHOST head).
No checkpoints / FFG / justification—those live in the separate HFC layer.
-/
