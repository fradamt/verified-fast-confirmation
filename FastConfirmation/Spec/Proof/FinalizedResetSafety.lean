module
public import FastConfirmation.Spec.Proof.ActualResetCheckpointRealization
public import FastConfirmation.Spec.Proof.FFGSelectedDomainRealization
public import FastConfirmation.Spec.Proof.FFGAccountability
public import FastConfirmation.Spec.Proof.ExactCheckpointLinks
public import FastConfirmation.Spec.Proof.SelectedTraceFFGRealizationPipeline
public import FastConfirmation.Spec.Proof.ModelFacts

@[expose] public section

/-!
# Finalized-reset safety from the common FFG trajectory

This file separates three logically different facts used by the finalized
reset branch of the exact-current-moment safety statement:

* the reset checkpoint has carrier-local concrete finalization evidence;
* accountable safety puts it below every weakly newer certified justified
  checkpoint in the execution parent graph;
* execution-parent reflection reconstructs every concrete ancestor inside a
  reachable foreign store, after which the FFG filter forces the head above
  it.

All root knownness and ancestry obligations are proved below, including an
independent certificate-plus-synchrony propagation proof.  The strongest
`SafeFrom` constructor leaves one operational fact explicit: a causally later
honest endpoint has adopted a justified epoch at least as new as the reset
finalized epoch.  A root/ancestry/head-free cross-view propagation property is
isolated for this fact.  No `JustificationInterface` field is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)


/-! ## Execution-parent graph reflection -/

omit [LinearOrder Root] [Inhabited Root] in
/-- Two concrete messages at one execution root agree.  This is the semantic
counterpart of cross-store block agreement. -/
theorem blockAt_unique
    (hwf : WellFormedExecution E)
    {r : Root} {b b' : BeaconBlock Root}
    (hb : E.BlockAt r b) (hb' : E.BlockAt r b') :
    b = b' := by
  rcases hb with ⟨hr, rfl⟩ | ⟨w, n, sb, hs, hroot, rfl⟩
  · rcases hb' with ⟨_hr', rfl⟩ | ⟨w', n', sb', hs', hroot', rfl⟩
    · rfl
    · have hagree := hwf.genesis_blocks_agree w' n' sb' hs'
          (by simpa only [hroot'] using hr)
      simpa only [hroot'] using hagree.symm
  · rcases hb' with ⟨hr', rfl⟩ | ⟨w', n', sb', hs', hroot', rfl⟩
    · have hagree := hwf.genesis_blocks_agree w n sb hs
          (by simpa only [hroot] using hr')
      simpa only [hroot] using hagree
    · apply hwf.blocks_root_injective w n sb hs w' n' sb' hs'
      exact hroot.trans hroot'.symm







/-! ## Concrete reset certificates -/








/-! ## Independent reset-root propagation -/


/-! ## Accountable prefix and endpoint-store realization -/











end Execution

end FastConfirmation.Spec

end
