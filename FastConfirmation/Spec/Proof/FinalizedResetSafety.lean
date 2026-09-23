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

/-- Minimal cross-view Gasper propagation law used by finalized-reset safety.
If an honest view has adopted a finalized epoch, every causally later
honest view has adopted at least that epoch as justified.

This says nothing about roots, ancestry, fork-choice heads, or `SafeFrom`.
The current `Synchrony` record does not imply it at the same second: block
relay has an end-of-slot gate, and delivery of honest attestations does not
force delivery or processing of the carrier whose state advances finality. -/
def FinalizedEpochPropagation : Prop :=
  ∀ v ∈ E.honest, ∀ k : Nat, E.WithinHorizon cfg k →
    ∀ w ∈ E.honest, ∀ m : Nat, k ≤ m → E.WithinHorizon cfg m →
      (E.store cfg ext v k).finalized_checkpoint.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch

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

omit [LinearOrder Root] [Inhabited Root] in
/-- Every semantic parent edge out of a root known in a reachable store uses
the same parent pointer as that store's concrete block message. -/
theorem parentEdge_parent_eq_of_store_known
    (hwf : WellFormedExecution E)
    {store : Store Root}
    (hprovenance : BlockProvenance E store)
    {child parent : Root}
    (hchild : child ∈ store.block_roots)
    (hedge : E.ParentEdge child parent) :
    parent = (store.blocks child).parent_root := by
  have hstoreAt : E.BlockAt child (store.blocks child) := by
    rcases hprovenance child hchild with hgen | hsched
    · exact Or.inl hgen
    · obtain ⟨sb, ⟨w, n, hs⟩, hroot, hblock⟩ := hsched
      exact Or.inr ⟨w, n, sb, hs, hroot, hblock.symm⟩
  rcases hedge with hgen | hsched
  · obtain ⟨r, hr, hchildEq, hparentEq⟩ := hgen
    subst child
    subst parent
    have heq := E.blockAt_unique hwf
      (show E.BlockAt r (E.genesis_store.blocks r) from Or.inl ⟨hr, rfl⟩)
      hstoreAt
    exact congrArg BeaconBlock.parent_root heq
  · obtain ⟨w, n, sb, hs, hchildEq, hparentEq⟩ := hsched
    subst child
    subst parent
    have heq := E.blockAt_unique hwf
      (show E.BlockAt sb.root sb.message from
        Or.inr ⟨w, n, sb, hs, rfl, rfl⟩)
      hstoreAt
    exact congrArg BeaconBlock.parent_root heq

omit [LinearOrder Root] [Inhabited Root] in
/-- The child of every concrete execution-parent edge is an execution root. -/
theorem ParentEdge.source_executionRoot
    {source parent : Root}
    (h : E.ParentEdge source parent) :
    E.ExecutionRoot source := by
  rcases h with ⟨r, hr, hsource, _⟩ | ⟨w, n, sb, hs, hsource, _⟩
  · refine ⟨E.genesis_store.blocks source, Or.inl ⟨?_, rfl⟩⟩
    simpa only [hsource] using hr
  · exact ⟨sb.message, Or.inr ⟨w, n, sb, hs, hsource.symm, rfl⟩⟩

omit [LinearOrder Root] [Inhabited Root] in
/-- The source of a nontrivial execution-parent descent is an execution root;
in the reflexive case this follows from the target being an execution root. -/
theorem RootDescends.source_executionRoot
    {source target : Root}
    (h : E.RootDescends source target)
    (htarget : E.ExecutionRoot target) :
    E.ExecutionRoot source := by
  cases h with
  | refl => exact htarget
  | step hedge _ => exact ParentEdge.source_executionRoot (E := E) hedge

/-- The dangling parent of the single trusted anchor is not a concrete
execution root.  This is exactly the hash-commitment side condition already
carried by `WellFormedExecution`. -/
theorem anchorParent_not_executionRoot
    (hwf : WellFormedExecution E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hparent : ablk.message.parent_root ≠ ablk.root) :
    ¬ E.ExecutionRoot ablk.message.parent_root := by
  intro hroot
  obtain ⟨b, hb⟩ := hroot
  rcases hb with hgenBlock | hsched
  · have hmem : ablk.message.parent_root ∈
        (get_forkchoice_store cfg ast ablk).block_roots := by
      simpa only [hgen] using hgenBlock.1
    simp only [get_forkchoice_store, List.mem_singleton] at hmem
    exact hparent hmem
  · obtain ⟨w, n, sb, hs, hrootEq, _⟩ := hsched
    have hgenBlock : E.genesis_store.blocks ablk.root = ablk.message := by
      rw [hgen]
      simp [get_forkchoice_store]
    have hgenParent : (E.genesis_store.blocks ablk.root).parent_root =
        ablk.message.parent_root := congrArg BeaconBlock.parent_root hgenBlock
    exact hwf.anchor_parent_unscheduled ablk.root
      (by rw [hgen]; simp only [get_forkchoice_store, List.mem_singleton])
      w n sb hs (by rw [hrootEq, hgenParent])

/-- A semantic execution ancestor of a known tip is itself known in that
reachable store, and the semantic descent is represented by executable
`is_ancestor`.  The target only needs to be a concrete execution root;
membership is a conclusion.

The proof follows unique execution parent pointers. `NonAnchorParentKnown`
supplies every intermediate parent. The only exceptional edge is the trusted
anchor's dangling parent, which cannot start a descent to a concrete execution
root. -/
theorem store_known_ancestor_of_rootDescends
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {w : ValidatorIndex} {m : Nat}
    {tip ancestor : Root}
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (hancestorRoot : E.ExecutionRoot ancestor)
    (hdesc : E.RootDescends tip ancestor) :
    ancestor ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root tip) (get_node_for_root ancestor) = true := by
  let store := E.store cfg ext w m
  have hpsl : ParentSlotLt store :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgen, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ store.block_roots, ∀ r ∈ store.block_roots,
      WalkKnown store (store.blocks t).slot r :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgen, hslot, hparent⟩ w m
  have hnonAnchor : NonAnchorParentKnown ablk.root store :=
    E.store_nonAnchorParentKnown cfg ext hgen w m
  have hprovenance : BlockProvenance E store := E.blockProvenance cfg ext w m
  have hreflect : ∀ {a b : Root}, E.RootDescends a b →
      a ∈ store.block_roots → E.ExecutionRoot b →
      b ∈ store.block_roots ∧
        is_ancestor store (get_node_for_root a) (get_node_for_root b) = true := by
    intro a b hab
    induction hab with
    | refl r =>
        intro hr _
        exact ⟨hr, is_ancestor_refl store (get_node_for_root r)⟩
    | @step child parent target hedge hrest ih =>
        intro hchild htargetRoot
        have hparentRoot : E.ExecutionRoot parent :=
          RootDescends.source_executionRoot (E := E) hrest htargetRoot
        have hpEq : parent = (store.blocks child).parent_root :=
          E.parentEdge_parent_eq_of_store_known hwf hprovenance hchild hedge
        have hchildNeAnchor : child ≠ ablk.root := by
          intro hchildAnchor
          subst child
          have hanchorBlock := E.store_anchor_block cfg ext hwf hgen w m hchild
          have hpEq' : parent = ablk.message.parent_root := by
            change parent =
              ((E.store cfg ext w m).blocks ablk.root).parent_root at hpEq
            rw [hanchorBlock] at hpEq
            exact hpEq
          apply E.anchorParent_not_executionRoot cfg hwf hgen hparent
          rwa [← hpEq']
        have hparentKnown : parent ∈ store.block_roots := by
          have hp := (hnonAnchor child hchild).resolve_left hchildNeAnchor
          rwa [← hpEq] at hp
        have hstep : is_ancestor store (get_node_for_root child)
            (get_node_for_root parent) = true := by
          apply is_ancestor_of_parent hpsl hchild hparentKnown
          exact hpEq.symm
        obtain ⟨htargetKnown, hrestAncestor⟩ :=
          ih hparentKnown htargetRoot
        exact ⟨htargetKnown, is_ancestor_trans (a := get_node_for_root child) (b := get_node_for_root parent)
            (c := get_node_for_root target) hpsl
          (hwalkK target htargetKnown child hchild)
          (hwalkK target htargetKnown parent hparentKnown)
          hstep hrestAncestor⟩
  exact hreflect hdesc htip hancestorRoot

/-- Converse of `rootDescends_of_store_ancestor` on the actual reachable-store
domain, specialized to callers which already know both endpoints. -/
theorem store_ancestor_of_rootDescends
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    {ast : BeaconState Root} {ablk : SignedBeaconBlock Root}
    (hgen : E.genesis_store = get_forkchoice_store cfg ast ablk)
    (hslot : ast.slot = ablk.message.slot)
    (hparent : ablk.message.parent_root ≠ ablk.root)
    {w : ValidatorIndex} {m : Nat}
    {tip ancestor : Root}
    (htip : tip ∈ (E.store cfg ext w m).block_roots)
    (hancestor : ancestor ∈ (E.store cfg ext w m).block_roots)
    (hdesc : E.RootDescends tip ancestor) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root tip) (get_node_for_root ancestor) = true := by
  exact (E.store_known_ancestor_of_rootDescends cfg ext hwf hec
    hgen hslot hparent htip
    ⟨(E.store cfg ext w m).blocks ancestor,
      E.blockAt_of_store_known cfg ext hancestor⟩ hdesc).2

/-! ## Concrete reset certificates -/

/-- Strongest global-finalized origin fact: a non-anchor realized finalized
checkpoint retains the known selector carrier and its carrier-local included
finalization certificate. -/
theorem globalFinalized_anchor_or_includedCertificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : Nat) :
    (E.store cfg ext w m).finalized_checkpoint = anchor ∨
      ∃ carrier ∈ (E.store cfg ext w m).block_roots,
        Nonempty (IncludedCertifiedFinalized cfg E
          S.includedAttestations.Included anchor carrier
          (E.store cfg ext w m).finalized_checkpoint) := by
  rcases (E.globalCheckpointOrigins cfg ext hcoh hgen hanchor w m).finalized with
    hanchorEq | ⟨carrier, hcarrier, hgf | hguf⟩
  · exact Or.inl hanchorEq
  · have hroot : E.ExecutionRoot carrier :=
      ⟨(E.store cfg ext w m).blocks carrier,
        E.blockAt_of_store_known cfg ext hcarrier⟩
    rcases S.gf_evidence carrier hroot with hlocalAnchor | hcertificate
    · exact Or.inl (hgf.trans hlocalAnchor)
    · right
      refine ⟨carrier, hcarrier, ?_⟩
      rwa [hgf]
  · have hroot : E.ExecutionRoot carrier :=
      ⟨(E.store cfg ext w m).blocks carrier,
        E.blockAt_of_store_known cfg ext hcarrier⟩
    rcases S.guf_evidence carrier hroot with hlocalAnchor | hcertificate
    · exact Or.inl (hguf.trans hlocalAnchor)
    · right
      refine ⟨carrier, hcarrier, ?_⟩
      rwa [hguf]

/-- Strongest global-justified certificate fact.  A non-anchor checkpoint
retains both the known installing tip and the formation carrier below it;
neither carrier is erased to the ordinary global certificate API. -/
theorem globalJustified_anchor_or_includedCertificateCarrier
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : Nat) :
    (E.store cfg ext w m).justified_checkpoint = anchor ∨
      ∃ tip ∈ (E.store cfg ext w m).block_roots,
        ∃ carrier : Root,
          E.RootDescends tip carrier ∧
            Nonempty (IncludedCertifiedJustified cfg E
              S.includedAttestations.Included anchor carrier
              (E.store cfg ext w m).justified_checkpoint) := by
  rcases E.globalJustified_anchor_or_known_AU cfg ext hcoh hgen hanchor w m with
    hanchorEq | ⟨tip, htip, hAU⟩
  · exact Or.inl hanchorEq
  · right
    obtain ⟨carrier, htipCarrier, hevidence⟩ :=
      ChainFFGState.AU.evidence (cfg := cfg) S hAU
    exact ⟨tip, htip, carrier, htipCarrier, hevidence.certified⟩

/-- Every reachable store-global justified checkpoint has an included,
carrier-local certificate.  The trusted anchor constructor is valid on an
arbitrary carrier and introduces no link obligation. -/
theorem globalJustified_includedCertificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : Nat) :
    ∃ carrier : Root,
      Nonempty (IncludedCertifiedJustified cfg E
        S.includedAttestations.Included anchor carrier
        (E.store cfg ext w m).justified_checkpoint) := by
  rcases E.globalJustified_anchor_or_includedCertificateCarrier cfg ext
      hcoh hgen hanchor w m with hanchorEq |
      ⟨_tip, _htip, carrier, _hdesc, hcertificate⟩
  · refine ⟨anchor.root, ?_⟩
    rw [hanchorEq]
    exact ⟨IncludedCertifiedJustified.anchor⟩
  · exact ⟨carrier, hcertificate⟩

/-- Forgetting carrier-local inclusion yields the ordinary concrete
finalization certificate used by accountable safety. -/
theorem globalFinalized_anchor_or_certificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : Nat) :
    (E.store cfg ext w m).finalized_checkpoint = anchor ∨
      Nonempty (CertifiedFinalized cfg E anchor
        (E.store cfg ext w m).finalized_checkpoint) := by
  rcases E.globalFinalized_anchor_or_includedCertificate cfg ext hcoh hgen hanchor
      w m with hanchorEq | ⟨carrier, _hcarrier, hcertificate⟩
  · exact Or.inl hanchorEq
  · right
    obtain ⟨hcertificate⟩ := hcertificate
    exact ⟨IncludedCertifiedFinalized.toCertifiedFinalized
      (cfg := cfg) S.includedAttestations hcertificate⟩

/-- The actual finalized checkpoint read by `fcrStep` has the same concrete
anchor-or-certificate provenance. -/
theorem finalizedReset_anchor_or_certificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (v : ValidatorIndex) (n : Nat) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint = anchor ∨
      Nonempty (CertifiedFinalized cfg E anchor
        (E.fcrStep cfg ext v n).store.finalized_checkpoint) := by
  rw [E.fcrStep_store]
  exact E.globalFinalized_anchor_or_certificate cfg ext hcoh hgen hanchor v (n + 1)

/-- The actual finalized checkpoint read by `fcrStep`, without forgetting its
included carrier-local finalization certificate. -/
theorem finalizedReset_anchor_or_includedCertificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (v : ValidatorIndex) (n : Nat) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint = anchor ∨
      ∃ carrier ∈ (E.store cfg ext v (n + 1)).block_roots,
        Nonempty (IncludedCertifiedFinalized cfg E
          S.includedAttestations.Included anchor carrier
          (E.fcrStep cfg ext v n).store.finalized_checkpoint) := by
  rw [E.fcrStep_store]
  exact E.globalFinalized_anchor_or_includedCertificate cfg ext hcoh hgen
    hanchor v (n + 1)

/-- Every reachable store-global justified checkpoint is concretely
certified. -/
theorem globalJustified_certificate
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (w : ValidatorIndex) (m : Nat) :
    Nonempty (CertifiedJustified cfg E anchor
      (E.store cfg ext w m).justified_checkpoint) := by
  rcases E.globalJustified_anchor_or_known_AU cfg ext hcoh hgen hanchor w m with
    hanchorEq | ⟨carrier, _hcarrier, hAU⟩
  · rw [hanchorEq]
    exact ⟨CertifiedJustified.anchor⟩
  · exact S.certifiedJustified_of_AU cfg hAU

/-! ## Independent reset-root propagation -/

/-- Carrier-local finality gives an *older honest origin* for the finalized
root.  If the finalized checkpoint is not the trusted anchor, the last link
of its included justification certificate has an honest signer.  That
signer's genuine target vote knew the checkpoint root before the including
carrier block.  Block synchrony therefore reaches every honest endpoint at
the reset time, including another endpoint in the same slot.

This theorem is independent of endpoint justified-checkpoint adoption.  It is
not needed by the stronger parent-graph reflection route below, but records
that root delivery itself is not the final reset-safety seam. -/
theorem finalizedReset_known_of_includedCertificateAndSynchrony
    (hwf : WellFormedExecution E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (hsync : Synchrony cfg ext E)
    {v : ValidatorIndex} (_hv : v ∈ E.honest) (n : Nat)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hnm : n + 1 ≤ m)
    (hHm : E.WithinHorizon cfg m) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots := by
  rw [E.fcrStep_store]
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hgenShort : ∃ (ast : BeaconState Root)
      (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot :=
    ⟨ast, ablk, hgenEq, hslot⟩
  have hHn1 : E.WithinHorizon cfg (n + 1) :=
    E.withinHorizon_mono cfg hnm hHm
  have hanchorRoot : anchor.root = ablk.root := by
    have hr := congrArg Checkpoint.root hanchor
    rw [hgenEq] at hr
    simpa only [get_forkchoice_store] using hr
  have hanchorKnown0 : anchor.root ∈ E.genesis_store.block_roots := by
    rw [hgenEq, hanchorRoot]
    simp only [get_forkchoice_store, List.mem_singleton]
  have hanchorKnownM : anchor.root ∈
      (E.store cfg ext w m).block_roots :=
    (E.store_storeLE cfg ext w (Nat.zero_le m)).1 hanchorKnown0
  have hslotZero : E.slot_at cfg 0 = ast.slot := by
    have hcurrent0 := E.store_current_slot cfg ext w 0
    change get_current_slot cfg E.genesis_store = E.slot_at cfg 0 at hcurrent0
    rw [hgenEq, get_current_slot_get_forkchoice_store cfg hacc.whole_seconds]
      at hcurrent0
    exact hcurrent0.symm
  have hanchorEpoch : anchor.epoch = compute_epoch_at_slot cfg ast.slot := by
    have he := congrArg Checkpoint.epoch hanchor
    rw [hgenEq] at he
    simpa only [get_forkchoice_store, get_current_epoch] using he
  have hboundary' : ablk.message.slot ≤
      compute_start_slot_at_epoch cfg anchor.epoch := by
    simpa only [TrustedAnchorBoundaryAligned, hgenEq, hanchorRoot,
      get_forkchoice_store, Function.update_self] using hboundary
  have hwalkDomain : E.PostAnchorHonestVoteTargetWalkDomain cfg ext :=
    E.postAnchorHonestVoteTargetWalkDomain_of_globalTrajectory cfg ext
      hwf hacc.externals_coherence hacc.whole_seconds
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary
  let reset := (E.store cfg ext v (n + 1)).finalized_checkpoint
  change reset.root ∈ (E.store cfg ext w m).block_roots
  rcases E.globalFinalized_anchor_or_includedCertificate cfg ext hcoh
      hgenShort hanchor v (n + 1) with hresetAnchor |
      ⟨carrier, hcarrier, hcertificate⟩
  · change reset = anchor at hresetAnchor
    rw [hresetAnchor]
    exact hanchorKnownM
  · obtain ⟨F⟩ := hcertificate
    cases F.justified with
    | anchor => exact hanchorKnownM
    | @link source _target hsource link =>
        let globalLink : SupermajorityLink cfg E source reset :=
          IncludedSupermajorityLink.toSupermajorityLink
            (cfg := cfg) S.includedAttestations link
        obtain ⟨i, hiGlobal, _hiGlobal', hiHonest⟩ :=
          E.links_intersect_honest cfg ext hacc globalLink globalLink
        have hiLink : i ∈ link.signers := by
          change i ∈ link.signers at hiGlobal
          exact hiGlobal
        obtain ⟨a, ⟨containing, hcarrierContaining, hincluded⟩,
            hiAttests, _haSource, haTarget⟩ :=
          link.signer_attestation i hiLink
        have hevidence := S.includedAttestations.evidence hincluded
        obtain ⟨sender, sentAt, hscheduled⟩ :=
          hevidence.received_from_block
        obtain ⟨_groundTime, groundVote, hvoteGround, hdataGround⟩ :=
          hacc.honest_behavior.no_forgery sender sentAt a true hscheduled
            i hiHonest hiAttests
        have hcommittee : i ∈ E.committee a.data.slot :=
          hevidence.attesters_in_committee i hiAttests
        have hsourceCertified : CertifiedJustified cfg E anchor source :=
          IncludedCertifiedJustified.toCertifiedJustified
            (cfg := cfg) S.includedAttestations hsource
        have hanchorLtTarget : anchor.epoch < reset.epoch :=
          lt_of_le_of_lt
            (CertifiedJustified.anchor_epoch_le (cfg := cfg) hsourceCertified)
            link.source_before_target
        have htargetEpoch : reset.epoch =
            compute_epoch_at_slot cfg a.data.slot := by
          change a.data.target = reset at haTarget
          rw [← haTarget]
          exact hevidence.target_epoch
        have hstartMono : compute_start_slot_at_epoch cfg anchor.epoch ≤
            compute_start_slot_at_epoch cfg reset.epoch :=
          Nat.mul_le_mul_right cfg.slots_per_epoch hanchorLtTarget.le
        have hstartVote : compute_start_slot_at_epoch cfg reset.epoch ≤
            a.data.slot := by
          have hmulDiv := Nat.div_mul_le_self a.data.slot cfg.slots_per_epoch
          have hdiv : a.data.slot / cfg.slots_per_epoch = reset.epoch := by
            simpa only [compute_epoch_at_slot] using htargetEpoch.symm
          rw [hdiv] at hmulDiv
          simpa only [compute_start_slot_at_epoch] using hmulDiv
        have hfromZero : E.slot_at cfg 0 ≤ a.data.slot := by
          calc
            E.slot_at cfg 0 = ast.slot := hslotZero
            _ = ablk.message.slot := hslot
            _ ≤ compute_start_slot_at_epoch cfg anchor.epoch := hboundary'
            _ ≤ compute_start_slot_at_epoch cfg reset.epoch := hstartMono
            _ ≤ a.data.slot := hstartVote
        obtain ⟨k, index, hHk, hkSlot, hvoteHead⟩ :=
          hacc.honest_behavior.votes_head i hiHonest a.data.slot hcommittee
            hevidence.slot_within_horizon hfromZero
        rw [hvoteHead] at hvoteGround
        simp only [Option.some.injEq, Prod.mk.injEq] at hvoteGround
        obtain ⟨_, hgroundVote⟩ := hvoteGround
        have hdata : a.data =
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data :=
          hdataGround.trans
            (congrArg (fun x : Attestation Root => x.data)
              hgroundVote.symm)
        have htargetExact :
            (honest_attestation cfg ext (E.store cfg ext i k)
              a.data.slot index i).data.target = reset := by
          rw [← hdata]
          exact haTarget
        have htargetWalk : WalkKnown (E.store cfg ext i k)
            (compute_start_slot_at_epoch cfg reset.epoch)
            (get_head cfg (E.store cfg ext i k)).root := by
          simpa only [htargetExact] using
            hwalkDomain i hiHonest a.data.slot k index hfromZero hHk
              hkSlot hvoteHead
        have hparentSlotsK : ParentSlotLt (E.store cfg ext i k) :=
          E.store_parentSlotLt cfg ext hwf
            hacc.externals_coherence
            ⟨ast, ablk, hgenEq, hslot, hparent⟩
            hwf.anchor_parent_unscheduled i k
        have htargetRoot : reset.root = get_checkpoint_block cfg
            (E.store cfg ext i k)
            (get_head cfg (E.store cfg ext i k)).root reset.epoch := by
          have hr := honest_attestation_data_target_root cfg ext
            (E.store cfg ext i k) a.data.slot index
          have htargetData : (honest_attestation_data cfg ext
              (E.store cfg ext i k) a.data.slot index).target = reset := by
            simpa only [honest_attestation_data_eq] using htargetExact
          rw [htargetData] at hr
          exact hr
        have htargetKnown : reset.root ∈
            (E.store cfg ext i k).block_roots := by
          rw [htargetRoot]
          exact (get_ancestor_spec hparentSlotsK htargetWalk).1
        have hcontainingRoot : E.ExecutionRoot containing :=
          ⟨hevidence.carrier_message, hevidence.carrier_at⟩
        have hcontainingKnown : containing ∈
            (E.store cfg ext v (n + 1)).block_roots :=
          (E.store_known_ancestor_of_rootDescends cfg ext
            hwf hacc.externals_coherence hgenEq hslot hparent
            hcarrier hcontainingRoot hcarrierContaining).1
        have hcontainingAgreement : hevidence.carrier_message =
            (E.store cfg ext v (n + 1)).blocks containing :=
          E.blockAt_unique hwf hevidence.carrier_at
            (E.blockAt_of_store_known cfg ext hcontainingKnown)
        have hvoteBeforeUpdate : a.data.slot < E.slot_at cfg (n + 1) := by
          calc
            a.data.slot < hevidence.carrier_message.slot :=
              hevidence.slot_before_carrier
            _ = ((E.store cfg ext v (n + 1)).blocks containing).slot :=
              congrArg BeaconBlock.slot hcontainingAgreement
            _ ≤ get_current_slot cfg (E.store cfg ext v (n + 1)) :=
              E.store_blocks_slot_le_current cfg ext hacc.whole_seconds
                hgenShort v (n + 1) containing hcontainingKnown
            _ = E.slot_at cfg (n + 1) :=
              E.store_current_slot cfg ext v (n + 1)
        apply hsync.block_relay i hiHonest k reset.root hHk
          htargetKnown w hw m hHm
        calc
          E.slot_at cfg k + 1 = a.data.slot + 1 := by rw [hkSlot]
          _ ≤ E.slot_at cfg (n + 1) := Nat.succ_le_of_lt hvoteBeforeUpdate
          _ ≤ E.slot_at cfg (m + 1) :=
            E.slot_at_mono cfg (hnm.trans (Nat.le_succ m))

/-! ## Accountable prefix and endpoint-store realization -/

/-- Certificate/carrier-preserving exact prefix for the current migration
trajectory.  Unlike `finalizedReset_semanticPrefix_of_justifiedEpoch` below,
this theorem does not erase included certificates to the ordinary global API
and does not substitute `RootDescends` for checkpoint descent.

`Accepted` remains a generic positive domain until the accepted global-
checkpoint trajectory replaces this legacy endpoint producer. -/
theorem finalizedReset_exactPrefix_of_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    {Accepted : Root → Prop}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection anchor Accepted S.C)
    (V : ExactIncludedLinkValidity cfg E
      S.includedAttestations.Included anchor S.C Accepted)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (v : ValidatorIndex) (n : Nat)
    (w : ValidatorIndex) (m : Nat)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    ExactCheckpointPrefix S.C
      (E.fcrStep cfg ext v n).store.finalized_checkpoint
      (E.store cfg ext w m).justified_checkpoint := by
  obtain ⟨justifiedCarrier, hjustified⟩ :=
    E.globalJustified_includedCertificate cfg ext hcoh hgen hanchor w m
  obtain ⟨hjustified⟩ := hjustified
  rcases E.finalizedReset_anchor_or_includedCertificate cfg ext hcoh
      hgen hanchor v n with hresetAnchor |
      ⟨finalizedCarrier, _hcarrier, hfinalized⟩
  · rw [hresetAnchor]
    exact IncludedCertifiedJustified.anchor_prefix
      (cfg := cfg) P V hanchorExact hjustified
  · obtain ⟨hfinalized⟩ := hfinalized
    exact IncludedCertifiedFinalized.exact_prefix_of_accountable
      (cfg := cfg) S.includedAttestations P V hanchorExact
      (CheckpointCertificateAccountability.of_assumptions cfg hacc)
      hfinalized hjustified hepoch

/-- Immediate executable consumer of the exact certificate prefix.  Knownness
of the endpoint justified root lets transition coherence reflect `S.C` into
that endpoint store.  No selected tip, filter membership, AU-on-tip premise,
or takeover conclusion occurs. -/
theorem finalizedReset_checkpointRootAtJustified_of_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    {Accepted : Root → Prop}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (P : AcceptedEpochCheckpointProjection anchor Accepted S.C)
    (V : ExactIncludedLinkValidity cfg E
      S.includedAttestations.Included anchor S.C Accepted)
    (hanchorExact : anchor = S.C anchor.root anchor.epoch)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hjustifiedKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint.root =
      get_checkpoint_block cfg (E.store cfg ext w m)
        (E.store cfg ext w m).justified_checkpoint.root
        (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch := by
  have hprefix := E.finalizedReset_exactPrefix_of_justifiedEpoch cfg ext
    hcoh hgen hanchor P V hanchorExact hacc v n w m hepoch
  have hreflect := hcoh.checkpoint_of_known w hw m hHm
    (E.store cfg ext w m).justified_checkpoint.root hjustifiedKnown
    (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch
  exact exactCheckpointPrefix_root_eq_of_reflection cfg hprefix hreflect

/-- The actual reset finalized checkpoint is a semantic prefix of an arbitrary
endpoint's realized justified checkpoint as soon as the endpoint epoch has
caught up. -/
theorem finalizedReset_semanticPrefix_of_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    (v : ValidatorIndex) (n : Nat)
    (w : ValidatorIndex) (m : Nat)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.RootDescends (E.store cfg ext w m).justified_checkpoint.root
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root := by
  obtain ⟨hjustified⟩ := E.globalJustified_certificate cfg ext hcoh hgen hanchor w m
  rcases E.finalizedReset_anchor_or_certificate cfg ext hcoh hgen hanchor v n with
    hresetAnchor | hresetCertificate
  · rw [hresetAnchor]
    exact hjustified.descends_anchor cfg
  · obtain ⟨hfinalized⟩ := hresetCertificate
    exact E.certified_finalized_prefix cfg ext hacc hfinalized hjustified hepoch

/-- Once the actual reset root is known to be a concrete execution root,
accountability and endpoint justified-epoch adoption make both its foreign
store membership and its concrete ancestry consequences. -/
theorem finalizedReset_storeKnownAncestor_of_executionRoot_and_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hresetRoot : E.ExecutionRoot
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root
          (E.store cfg ext w m).justified_checkpoint.root)
        (get_node_for_root
          (E.fcrStep cfg ext v n).store.finalized_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hjustifiedKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justifiedRootKnown_of_globalTrajectory cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary hw m hHm
  apply E.store_known_ancestor_of_rootDescends cfg ext hwf hec
    hgenEq hslot hparent hjustifiedKnown hresetRoot
  exact E.finalizedReset_semanticPrefix_of_justifiedEpoch cfg ext hcoh
    ⟨ast, ablk, hgenEq, hslot⟩ hanchor hacc v n w m hepoch

/-- Accountable prefix is represented by concrete `is_ancestor` in an
arbitrary honest endpoint once the reset root is present there. -/
theorem finalizedReset_storeAncestor_of_known_and_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hresetKnown : (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
      (get_node_for_root
        (E.fcrStep cfg ext v n).store.finalized_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hjustifiedKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justifiedRootKnown_of_globalTrajectory cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary hw m hHm
  apply E.store_ancestor_of_rootDescends cfg ext hwf hec hgenEq hslot hparent
    hjustifiedKnown hresetKnown
  exact E.finalizedReset_semanticPrefix_of_justifiedEpoch cfg ext hcoh
    ⟨ast, ablk, hgenEq, hslot⟩ hanchor hacc v n w m hepoch

/-- Per-endpoint finalized-reset takeover from a concrete reset root and the
one ordering fact certificate accountability needs: the foreign endpoint has
adopted a justified epoch at least as new as the reset. Root membership is a
conclusion of parent-graph reflection. -/
theorem finalizedReset_head_of_executionRoot_and_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hresetRoot : E.ExecutionRoot
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (E.fcrStep cfg ext v n).store.finalized_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hjustifiedKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justifiedRootKnown_of_globalTrajectory cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary hw m hHm
  have hparentSlots : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
  obtain ⟨hresetKnown, hdom⟩ :=
    E.finalizedReset_storeKnownAncestor_of_executionRoot_and_justifiedEpoch
      cfg ext hwf hec ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh
      hanchor hboundary hacc hw hHm hresetRoot hepoch
  exact head_ge_of_justified_ge_K cfg hparentSlots hwalkK
    hjustifiedKnown hresetKnown hdom

theorem finalizedReset_head_of_known_and_justifiedEpoch
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} {n : Nat}
    {w : ValidatorIndex} (hw : w ∈ E.honest) {m : Nat}
    (hHm : E.WithinHorizon cfg m)
    (hresetKnown : (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
      (E.store cfg ext w m).block_roots)
    (hepoch : (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
      (E.store cfg ext w m).justified_checkpoint.epoch) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root
        (E.fcrStep cfg ext v n).store.finalized_checkpoint.root) = true := by
  obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hgen
  have hjustifiedKnown : (E.store cfg ext w m).justified_checkpoint.root ∈
      (E.store cfg ext w m).block_roots :=
    E.justifiedRootKnown_of_globalTrajectory cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary hw m hHm
  have hparentSlots : ParentSlotLt (E.store cfg ext w m) :=
    E.store_parentSlotLt cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩
      hwf.anchor_parent_unscheduled w m
  have hwalkK : ∀ t ∈ (E.store cfg ext w m).block_roots,
      ∀ r ∈ (E.store cfg ext w m).block_roots,
        WalkKnown (E.store cfg ext w m)
          ((E.store cfg ext w m).blocks t).slot r :=
    E.store_walkKnownK cfg ext hwf hec
      ⟨ast, ablk, hgenEq, hslot, hparent⟩ w m
  apply head_ge_of_justified_ge_K cfg hparentSlots hwalkK
    hjustifiedKnown hresetKnown
  exact E.finalizedReset_storeAncestor_of_known_and_justifiedEpoch cfg ext
    hwf hec ⟨ast, ablk, hgenEq, hslot, hparent⟩ hcoh hanchor hboundary
    hacc hw hHm hresetKnown hepoch

/-- Strongest direct `SafeFrom` reduction obtained from the common trajectory:
root delivery and justified-epoch adoption remain as explicit endpoint-local
operational premises. -/
theorem finalizedReset_safeFrom_of_visibility
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧
      ablk.message.parent_root ≠ ablk.root)
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hacc : FFGAccountabilityAssumptions cfg ext E)
    {v : ValidatorIndex} (n : Nat)
    (hknown : ∀ w ∈ E.honest, ∀ m : Nat, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
        (E.store cfg ext w m).block_roots)
    (hadopted : ∀ w ∈ E.honest, ∀ m : Nat, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1) := by
  intro w hw m hnm hHm
  exact E.finalizedReset_head_of_known_and_justifiedEpoch cfg ext
    hwf hec hgen hcoh hanchor hboundary hacc hw hHm
    (hknown w hw m hnm hHm) (hadopted w hw m hnm hHm)

/-- Strongest reset-safety theorem from the common trajectory.  Concrete
reset realization supplies an execution root at the querying honest view;
accountable semantic prefix plus parent-graph reflection then derives foreign
root delivery.  The sole remaining operational premise is cross-view
justified-epoch adoption. -/
theorem finalizedReset_safeFrom_of_crossViewAdoption
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    {v : ValidatorIndex} (hv : v ∈ E.honest) (n : Nat)
    (hadopted : ∀ w ∈ E.honest, ∀ m : Nat, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1) := by
  intro w hw m hnm hHm
  have hHn1 : E.WithinHorizon cfg (n + 1) :=
    E.withinHorizon_mono cfg hnm hHm
  have hrealized :=
    E.finalizedCheckpoint_resetRealizedAt_of_globalTrajectory cfg ext
      hA hcoh hanchor hboundary hv hHn1
  have hresetKnown :
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root ∈
        (E.store cfg ext v (n + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hrealized.root_known
  have hresetRoot : E.ExecutionRoot
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root :=
    ⟨(E.store cfg ext v (n + 1)).blocks
        (E.fcrStep cfg ext v n).store.finalized_checkpoint.root,
      E.blockAt_of_store_known cfg ext hresetKnown⟩
  exact E.finalizedReset_head_of_executionRoot_and_justifiedEpoch cfg ext
    hA.wellFormed hA.externals_coherence hA.genesis hcoh hanchor hboundary
    (SelectedMarginAssumptions.toFFGAccountabilityAssumptions cfg ext E hA)
    hw hHm hresetRoot (hadopted w hw m hnm hHm)

/-- Paper-native facade: the isolated root-free/ancestry-free cross-view
finalized-epoch propagation law is sufficient for exact-current reset safety. -/
theorem finalizedReset_safeFrom_of_finalizedEpochPropagation
    (hA : SelectedMarginAssumptions cfg ext E)
    {anchor : Checkpoint Root}
    {S : ChainFFGState cfg E anchor}
    (hcoh : FFGTransitionCoherence cfg ext S)
    (hanchor : anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := anchor))
    (hpropagation : E.FinalizedEpochPropagation cfg ext)
    {v : ValidatorIndex} (hv : v ∈ E.honest) (n : Nat) :
    E.SafeFrom cfg ext
      (E.fcrStep cfg ext v n).store.finalized_checkpoint.root (n + 1) := by
  apply E.finalizedReset_safeFrom_of_crossViewAdoption cfg ext hA hcoh
    hanchor hboundary hv n
  intro w hw m hnm hHm
  have hHn1 : E.WithinHorizon cfg (n + 1) :=
    E.withinHorizon_mono cfg hnm hHm
  simpa only [E.fcrStep_store] using
    hpropagation v hv (n + 1) hHn1 w hw m hnm hHm

end Execution

end FastConfirmation.Spec

end
