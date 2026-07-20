import FastConfirmation.Paper.Core.Model.Time
import FastConfirmation.Paper.Core.Model.Blocks
import FastConfirmation.Paper.Core.Model.Validators
import FastConfirmation.Paper.Core.Model.Vote
import FastConfirmation.Paper.Core.Model.View
import FastConfirmation.Paper.Core.Model.Filter
import FastConfirmation.Paper.Core.Model.ForkChoice
import FastConfirmation.Paper.Core.Model.Honest

/-!
# Core / Model

Model-only facade for the shared FCR vocabulary (time, blocks, validators,
votes, views + synchrony, the eligibility filter, and the LMD-GHOST head).
No checkpoints / FFG / justification—those live in the separate HFC layer.
-/
