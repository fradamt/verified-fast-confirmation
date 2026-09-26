module
public import FastConfirmationProofs.FFG.SelectedSource.EndpointMargin
public import FastConfirmationProofs.FFG.SourceHistory.LaterStoreSupport
public import FastConfirmationProofs.Handlers.HandlerVoteClasses

@[expose] public section

/-! Proves that recorded vote windows and observed checkpoint ancestry remain valid when an execution window is shortened. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-- Epoch maximality over a longer window restricts to an earlier cutoff. -/
theorem WindowRecordedEpochMax_mono_end
    {w : ValidatorIndex} {m : ℕ} {lo es σ : Slot}
    (hesσ : es ≤ σ)
    (hmax : E.WindowRecordedEpochMax cfg ext w m lo σ) :
    E.WindowRecordedEpochMax cfg ext w m lo es := by
  intro i hi hiSpan lm hlm t k a ht hvote
  exact hmax i hi (E.span_committee_mono lo hesσ hiSpan)
    lm hlm t k a (ht.trans hesσ) hvote

/-- A message recorded at the confirming store has a slot in its completed
vote window. This is the validation gate in latest-message provenance. -/
theorem recorded_slot_le_completed_cutoff
    {v i : ValidatorIndex} {n : ℕ} {es : Slot} {lm : LatestMessage Root}
    (hes : es = get_current_slot cfg (E.store cfg ext v n) - 1)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    (hlm : (E.store cfg ext v n).latest_messages i = some lm) :
    lm.slot ≤ es := by
  obtain ⟨a, _, _, _, _, hgate, _, _, _, hslot⟩ := hprov i lm hlm
  rw [hslot, hes]
  exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hgate)








/-- An endpoint ancestor-class member whose genuine votes stop by `es`
belongs to the same class at the old cutoff. -/
theorem Aclass_old_cutoff_of_no_late_vote
    {w i : ValidatorIndex} {m : ℕ} {b : Root} {lo es σ : Slot}
    (hesσ : es ≤ σ)
    (hiOldSpan : i ∈ E.span_committee lo es)
    (hAσ : i ∈ E.Aclass cfg ext w m b lo σ)
    (hNoLate : ∀ t : Slot, es < t → t ≤ σ → E.vote i t = none) :
    i ∈ E.Aclass cfg ext w m b lo es := by
  simp only [Execution.Aclass, Finset.mem_filter] at hAσ ⊢
  refine ⟨⟨hiOldSpan, hAσ.1.2⟩, ?_, ?_⟩
  · intro hSes
    apply hAσ.2.1
    obtain ⟨t, k, a, ht, hvote, hnew, hanc⟩ := hSes
    refine ⟨t, k, a, ht.trans hesσ, hvote, ?_, hanc⟩
    intro t' htt htσ
    by_cases hte : t' ≤ es
    · exact hnew t' htt hte
    · exact hNoLate t' (Nat.lt_of_not_le hte) htσ
  · rcases hAσ.2.2 with hvoteless | ⟨t, k, a, htσ, hvote, hnew, hanc⟩
    · exact Or.inl (fun t ht => hvoteless t (ht.trans hesσ))
    · have ht : t ≤ es := by
        by_contra hnot
        have hzero := hNoLate t (Nat.lt_of_not_le hnot) htσ
        rw [hvote] at hzero
        contradiction
      exact Or.inr ⟨t, k, a, ht, hvote,
        (fun t' htt hte => hnew t' htt (hte.trans hesσ)), hanc⟩












/-- Endpoint child recording lifts the selected honest class into the
resolved parent status. This is the `hselected` input of the status margin. -/
theorem selected_parent_score_ge_Sval
    {store : Store Root} {bs : BeaconState Root}
    (hval : bs.validators = E.registry)
    {v : ValidatorIndex} {n : ℕ} {b c : Root} {lo σ : Slot}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hc : c ∈ store.block_roots)
    (hp : (store.blocks c).parent_root ∈ store.block_roots)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root c) bs →
        WalkKnown store (store.blocks (store.blocks c).parent_root).slot lm.root)
    (hSmem : ∀ i ∈ E.Sclass cfg ext v n b lo σ,
      i ∈ AttSupporters cfg store (get_node_for_root c) bs) :
    E.Sval cfg ext v n b lo σ ≤
      get_attestation_score cfg store
        (ForkChoiceNode.mk (store.blocks c).parent_root
          (get_parent_payload_status store (store.blocks c))) bs := by
  exact le_trans (recorded_bside_ge cfg ext hval hSmem)
    (selected_parent_score_ge_child_score cfg hval hwf hc hp hwalk)

/-- The required status appears in the pending parent's fork-choice children
when it is empty or its full payload has been verified at this store. -/
theorem selected_parent_status_mem_pending
    {store : Store Root} {blocks : List Root} {h : Root}
    {status : PayloadStatus}
    (havailable : status = .empty ∨
      (status = .full ∧ is_payload_verified store h = true)) :
    ForkChoiceNode.mk h status ∈
      get_node_children store blocks (ForkChoiceNode.mk h .pending) := by
  exact (mem_get_node_children_pending rfl).mpr ⟨rfl, havailable⟩




private theorem ancestor_strip_survives_growth
    {x0 B0 P s0 xg Bg sg dJ dB : ℕ}
    (hstrip : x0 + B0 + P + 1 ≤ s0) (hs : s0 + dJ ≤ sg)
    (hx : xg ≤ x0) (hB : Bg ≤ B0 + dB) (hbudget : dB ≤ dJ) :
    xg + Bg + P + 1 ≤ sg := by omega

private theorem ancestor_strip_transports
    {x0 x1 B P O s0 s1 : ℕ}
    (hsource : x0 + B + P + O + 1 ≤ s0)
    (hX : x1 ≤ x0) (hS : s0 ≤ s1) :
    x1 + B + (P + O) + 1 ≤ s1 := by omega

private theorem ancestor_le_add_tsub (a b : ℕ) : a ≤ b + (a - b) := by omega

/-- A fixed opposite-ancestor debt survives the complete-window growth
argument. The source strip comes from actual confirmation; the two honest
class movements, honest growth, and window capacity are the existing engine
transport and induction inputs. -/
theorem opposite_ancestor_strip_window_uniform
    {v w : ValidatorIndex} {n m : ℕ} {b : Root}
    {lo es σ : Slot} {P O : ℕ}
    (hSt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.SupportsDesc cfg ext v n b es i → E.SupportsDesc cfg ext w m b es i)
    (hAt : ∀ i, i ∈ E.honest → i ∈ E.span_committee lo es →
      E.AncestorOrVoteless cfg ext v n b es i →
        E.AncestorOrVoteless cfg ext w m b es i)
    (hsource : E.Xval cfg ext v n b lo es + E.Bval lo es + P + O + 1
      ≤ E.Sval cfg ext v n b lo es)
    (hgrowS : E.Sval cfg ext w m b lo es + (E.Jspec lo σ - E.Jspec lo es)
      ≤ E.Sval cfg ext w m b lo σ)
    (hgrowX : E.Xval cfg ext w m b lo σ ≤ E.Xval cfg ext w m b lo es)
    (hbudget : (100 - cfg.confirmation_byzantine_threshold) *
        (E.Bval lo σ - E.Bval lo es) ≤
      cfg.confirmation_byzantine_threshold * (E.Jspec lo σ - E.Jspec lo es)) :
    E.Xval cfg ext w m b lo σ + E.Bval lo σ + P + O + 1
      ≤ E.Sval cfg ext w m b lo σ := by
  have hSbase : E.Sval cfg ext v n b lo es ≤ E.Sval cfg ext w m b lo es := by
    apply E.weight_mono
    intro i hi
    simp only [Execution.Sclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hSt i hi.1.2 hi.1.1 hi.2⟩
  have hXbase : E.Xval cfg ext w m b lo es ≤ E.Xval cfg ext v n b lo es := by
    apply E.weight_mono
    intro i hi
    simp only [Execution.Xclass, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1,
      fun hs => hi.2.1 (hSt i hi.1.2 hi.1.1 hs),
      fun ha => hi.2.2 (hAt i hi.1.2 hi.1.1 ha)⟩
  have hbase : E.Xval cfg ext w m b lo es + E.Bval lo es +
      (P + O) + 1 ≤ E.Sval cfg ext w m b lo es :=
    ancestor_strip_transports hsource hXbase hSbase
  have hDpos : 0 < 100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le
    omega
  have hCD : cfg.confirmation_byzantine_threshold ≤
      100 - cfg.confirmation_byzantine_threshold := by
    have := cfg.confirmation_byzantine_threshold_le
    omega
  have hbud : E.Bval lo σ - E.Bval lo es ≤
      E.Jspec lo σ - E.Jspec lo es :=
    Nat.le_of_mul_le_mul_left
      (le_trans hbudget (Nat.mul_le_mul hCD (le_refl _))) hDpos
  have hB : E.Bval lo σ ≤ E.Bval lo es +
      (E.Bval lo σ - E.Bval lo es) :=
    ancestor_le_add_tsub _ _
  have hfinal := ancestor_strip_survives_growth hbase hgrowS hgrowX hB hbud
  simpa only [add_assoc] using hfinal


end Execution
end FastConfirmation.Spec

end
