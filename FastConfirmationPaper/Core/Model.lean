module
public import FastConfirmationPaper.Core.Model.Time
public import FastConfirmationPaper.Core.Model.BlockAncestry
public import FastConfirmationPaper.Core.Model.Validators
public import FastConfirmationPaper.Core.Model.GhostVote
public import FastConfirmationPaper.Core.Model.ValidatorView
public import FastConfirmationPaper.Core.Model.ForkChoice
public import FastConfirmationPaper.Core.Model.HonestVoting

/-!
# Core / Model

Model-only facade for the shared FCR vocabulary (time, blocks, validators,
votes, views + synchrony, the eligibility filter, and the LMD-GHOST head).
No checkpoints / FFG / justification—those live in the separate HFC layer.
-/
