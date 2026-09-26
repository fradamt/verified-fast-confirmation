import FastConfirmationWitnesses.Counterexamples.CheckpointSyncFilter

/-! Kernel audit for the raw checkpoint-sync filter regression. -/

open FastConfirmation.Spec.CheckpointSyncFilterWitness

#print axioms votes_match_honest_data
#print axioms child_import_accepted
#print axioms checkpoint_sync_filter_counterexample
#print axioms raw_source_filter_boundary
#print axioms normalized_source_changes_head
