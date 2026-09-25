module
public import FastConfirmationStatements.Weak.ObserverLocalFFG

/-! FFG content unions preserve certificate formation and selector maxima. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root} {anchor : Checkpoint Root}
namespace ObserverFFGContent

def link_map {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {r source target}
    (L : IncludedSupermajorityLink cfg E I r source target) :
    IncludedSupermajorityLink cfg E J r source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, ⟨carrier, hd, ha⟩, hs⟩ := L.signer_attestation i hi
    exact ⟨a, ⟨carrier, hd, h ha⟩, hs⟩
  supermajority := L.supermajority

theorem cert_map {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {r c}
    (hc : IncludedCertifiedJustified cfg E I anchor r c) :
    IncludedCertifiedJustified cfg E J anchor r c := by
  induction hc with
  | anchor => exact .anchor
  | link _ L ih => exact .link ih (link_map h L)

def final_map {I J : Root → Attestation Root → Prop}
    (h : ∀ {r a}, I r a → J r a) {r c}
    (F : IncludedCertifiedFinalized cfg E I anchor r c) :
    IncludedCertifiedFinalized cfg E J anchor r c where
  justified := cert_map h F.justified
  child := F.child
  child_epoch := F.child_epoch
  finalizing_link := link_map h F.finalizing_link

private theorem desc_trans {a b c : Root}
    (h : E.RootDescends a b) (h' : E.RootDescends b c) : E.RootDescends a c := by
  induction h with
  | refl => exact h'
  | step hp _ ih => exact .step hp (ih h')

private theorem cert_epoch {I : Root → Attestation Root → Prop} {r c}
    (hc : IncludedCertifiedJustified cfg E I anchor r c) : anchor.epoch ≤ c.epoch := by
  induction hc with
  | anchor => exact le_rfl
  | link _ L ih => exact ih.trans L.source_before_target.le

/-- Conditions used to combine two content domains. They concern shared block
content, common selectors, and closure of each accepted chain. -/
structure Compatible (S T : ObserverFFGContent cfg ext E anchor) : Prop where
  blocks : ∀ {r}, S.domain r → T.domain r → S.blocks r = T.blocks r
  gj : ∀ {r}, S.domain r → T.domain r → S.GJ r = T.GJ r
  gu : ∀ {r}, S.domain r → T.domain r → S.GU r = T.GU r
  gf : ∀ {r}, S.domain r → T.domain r → S.GF r = T.GF r
  guf : ∀ {r}, S.domain r → T.domain r → S.GUF r = T.GUF r
  left_closed : ∀ {r carrier}, S.domain r → T.domain carrier →
    E.RootDescends r carrier → S.domain carrier
  right_closed : ∀ {r carrier}, T.domain r → S.domain carrier →
    E.RootDescends r carrier → T.domain carrier
  left_epoch_mono : ∀ {r carrier}, S.domain r → S.domain carrier →
    E.RootDescends r carrier →
    compute_epoch_at_slot cfg (S.blocks carrier).slot ≤
      compute_epoch_at_slot cfg (S.blocks r).slot
  right_epoch_mono : ∀ {r carrier}, T.domain r → T.domain carrier →
    E.RootDescends r carrier →
    compute_epoch_at_slot cfg (T.blocks carrier).slot ≤
      compute_epoch_at_slot cfg (T.blocks r).slot

def Compatible.symm {S T : ObserverFFGContent cfg ext E anchor}
    (h : Compatible S T) : Compatible T S where
  blocks := fun ht hs => (h.blocks hs ht).symm
  gj := fun ht hs => (h.gj hs ht).symm
  gu := fun ht hs => (h.gu hs ht).symm
  gf := fun ht hs => (h.gf hs ht).symm
  guf := fun ht hs => (h.guf hs ht).symm
  left_closed := h.right_closed
  right_closed := h.left_closed
  left_epoch_mono := h.right_epoch_mono
  right_epoch_mono := h.left_epoch_mono

private theorem lift_au (S : ObserverFFGContent cfg ext E anchor)
    {r carrier c} (hd : E.RootDescends r carrier) (ha : S.AU carrier c) : S.AU r c := by
  obtain ⟨d, hcd, hf⟩ := ha
  exact ⟨d, desc_trans hd hcd, hf⟩

/-- A foreign formed entry is bounded by the common carrier's GU selector. -/
theorem Compatible.cross_gu_max {S T : ObserverFFGContent cfg ext E anchor}
    (h : Compatible S T) {r carrier c} (hr : S.domain r)
    (hd : E.RootDescends r carrier) (hf : T.formed carrier c) :
    c.epoch ≤ (S.GU r).epoch := by
  have ht := T.formed_domain hf
  have hs := h.left_closed hr ht hd
  have hc := T.gu_max ht ⟨carrier, .refl _, hf⟩
  rw [← h.gu hs ht] at hc
  exact hc.trans (S.gu_max hr (lift_au S hd (S.gu_mem carrier hs)))

/-- A foreign formed entry cannot exceed the receiving tip's block epoch. -/
theorem Compatible.cross_epoch_max {S T : ObserverFFGContent cfg ext E anchor}
    (h : Compatible S T) {r carrier c} (hr : S.domain r)
    (hd : E.RootDescends r carrier) (hf : T.formed carrier c) :
    c.epoch ≤ compute_epoch_at_slot cfg (S.blocks r).slot := by
  exact (h.cross_gu_max hr hd hf).trans (S.au_epoch_le_block hr (S.gu_mem r hr))

/-- GJ comparison uses GJ on an older checkpoint and GU at the carrier epoch. -/
theorem Compatible.cross_gj_max {S T : ObserverFFGContent cfg ext E anchor}
    (h : Compatible S T) {r carrier c} (hr : S.domain r)
    (hd : E.RootDescends r carrier) (hf : T.formed carrier c)
    (hbefore : c.epoch < compute_epoch_at_slot cfg (S.blocks r).slot) :
    c.epoch ≤ (S.GJ r).epoch := by
  have ht := T.formed_domain hf
  have hs := h.left_closed hr ht hd
  have hau : T.AU carrier c := ⟨carrier, .refl _, hf⟩
  by_cases hc : c.epoch < compute_epoch_at_slot cfg (T.blocks carrier).slot
  · have hle := T.gj_max ht hau hc
    rw [← h.gj hs ht] at hle
    apply hle.trans (S.gj_max hr (lift_au S hd (S.gj_mem carrier hs)) ?_)
    rcases S.gj_anchor_or_before carrier hs with ha | hb
    · rw [ha]
      exact (cert_epoch (T.formed_certificate hf)).trans_lt hbefore
    · exact hb.trans_le (h.left_epoch_mono hr hs hd)
  · have hle := T.gu_max ht hau
    have hupper := T.au_epoch_le_block ht (T.gu_mem carrier ht)
    rw [← h.gu hs ht] at hle hupper
    apply hle.trans (S.gj_max hr (lift_au S hd (S.gu_mem carrier hs)) ?_)
    exact hupper.trans_lt ((Nat.le_of_not_gt hc).trans_lt hbefore)

/-- The complete union of both content relations. -/
noncomputable def union (S T : ObserverFFGContent cfg ext E anchor)
    (h : Compatible S T) : ObserverFFGContent cfg ext E anchor := by
  classical
  let choose := fun {α : Type _} (f g : Root → α) r => if S.domain r then f r else g r
  refine {
    domain := fun r => S.domain r ∨ T.domain r
    blocks := choose S.blocks T.blocks
    included := fun r a => S.included r a ∨ T.included r a
    formed := fun r c => S.formed r c ∨ T.formed r c
    C := choose S.C T.C
    GJ := choose S.GJ T.GJ
    GU := choose S.GU T.GU
    GF := choose S.GF T.GF
    GUF := choose S.GUF T.GUF
    checkpoint_epoch := ?_
    formed_domain := ?_
    formed_certificate := ?_
    formed_on_chain := ?_
    gj_mem := ?_
    gu_mem := ?_
    gf_mem := ?_
    guf_mem := ?_
    gj_anchor_or_before := ?_
    gj_max := ?_
    gu_max := ?_
    au_epoch_le_block := ?_
    gf_evidence := ?_
    guf_evidence := ?_
    gf_epoch_le_gj := ?_
    guf_epoch_le_gu := ?_
    gf_epoch_le_guf := ?_ }
  · intro r e; dsimp only [choose]; split_ifs
    · exact S.checkpoint_epoch r e
    · exact T.checkpoint_epoch r e
  · intro r c hf; exact hf.elim (fun hs => Or.inl (S.formed_domain hs))
      (fun ht => Or.inr (T.formed_domain ht))
  · intro r c hf; exact hf.elim (fun hs => cert_map Or.inl (S.formed_certificate hs))
      (fun ht => cert_map Or.inr (T.formed_certificate ht))
  · intro r c hf; exact hf.elim S.formed_on_chain T.formed_on_chain
  all_goals
    first
    | (intro r hr; dsimp only [choose]; by_cases hs : S.domain r
       · simp only [if_pos hs]
         first
         | (obtain ⟨d, hd, hf⟩ := S.gj_mem r hs; exact ⟨d, hd, Or.inl hf⟩)
         | (obtain ⟨d, hd, hf⟩ := S.gu_mem r hs; exact ⟨d, hd, Or.inl hf⟩)
         | (obtain ⟨d, hd, hf⟩ := S.gf_mem r hs; exact ⟨d, hd, Or.inl hf⟩)
         | (obtain ⟨d, hd, hf⟩ := S.guf_mem r hs; exact ⟨d, hd, Or.inl hf⟩)
       · simp only [if_neg hs]
         have ht := hr.resolve_left hs
         first
         | (obtain ⟨d, hd, hf⟩ := T.gj_mem r ht; exact ⟨d, hd, Or.inr hf⟩)
         | (obtain ⟨d, hd, hf⟩ := T.gu_mem r ht; exact ⟨d, hd, Or.inr hf⟩)
         | (obtain ⟨d, hd, hf⟩ := T.gf_mem r ht; exact ⟨d, hd, Or.inr hf⟩)
         | (obtain ⟨d, hd, hf⟩ := T.guf_mem r ht; exact ⟨d, hd, Or.inr hf⟩))
    | skip
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact S.gj_anchor_or_before r hs
    · exact T.gj_anchor_or_before r (hr.resolve_left hs)
  · intro r c hr ⟨carrier, hd, hf⟩ hc
    dsimp only [choose] at hc ⊢
    split_ifs at hc ⊢ with hs
    · rcases hf with hf | hf
      · exact S.gj_max hs ⟨carrier, hd, hf⟩ hc
      · exact h.cross_gj_max hs hd hf hc
    · have ht := hr.resolve_left hs
      rcases hf with hf | hf
      · exact h.symm.cross_gj_max ht hd hf hc
      · exact T.gj_max ht ⟨carrier, hd, hf⟩ hc
  · intro r c hr ⟨carrier, hd, hf⟩; dsimp only [choose]; split_ifs with hs
    · exact hf.elim (fun hf => S.gu_max hs ⟨carrier, hd, hf⟩)
        (fun hf => h.cross_gu_max hs hd hf)
    · exact hf.elim (fun hf => h.symm.cross_gu_max (hr.resolve_left hs) hd hf)
        (fun hf => T.gu_max (hr.resolve_left hs) ⟨carrier, hd, hf⟩)
  · intro r c hr ⟨carrier, hd, hf⟩; dsimp only [choose]; split_ifs with hs
    · exact hf.elim (fun hf => S.au_epoch_le_block hs ⟨carrier, hd, hf⟩)
        (fun hf => h.cross_epoch_max hs hd hf)
    · exact hf.elim (fun hf => h.symm.cross_epoch_max (hr.resolve_left hs) hd hf)
        (fun hf => T.au_epoch_le_block (hr.resolve_left hs) ⟨carrier, hd, hf⟩)
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact (S.gf_evidence r hs).imp_right (fun ⟨F⟩ => ⟨final_map Or.inl F⟩)
    · exact (T.gf_evidence r (hr.resolve_left hs)).imp_right
        (fun ⟨F⟩ => ⟨final_map Or.inr F⟩)
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact (S.guf_evidence r hs).imp_right (fun ⟨F⟩ => ⟨final_map Or.inl F⟩)
    · exact (T.guf_evidence r (hr.resolve_left hs)).imp_right
        (fun ⟨F⟩ => ⟨final_map Or.inr F⟩)
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact S.gf_epoch_le_gj r hs
    · exact T.gf_epoch_le_gj r (hr.resolve_left hs)
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact S.guf_epoch_le_gu r hs
    · exact T.guf_epoch_le_gu r (hr.resolve_left hs)
  · intro r hr; dsimp only [choose]; split_ifs with hs
    · exact S.gf_epoch_le_guf r hs
    · exact T.gf_epoch_le_guf r (hr.resolve_left hs)

end ObserverFFGContent
end Execution
end FastConfirmation.Spec
end
