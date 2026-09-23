module
public import FastConfirmation.Spec.Model.Assumptions

@[expose] public section

/-!
# Assumptions model facts

Proofs about Model/Assumptions. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)
end Execution
omit [LinearOrder Root] [Inhabited Root] in
/-- **No new assumption content.** The conjunction of the old receipt-gated
delivery clause and the old `HorizonVoteDeliveryLookahead.attestation_delivery`
is exactly the merged `attestation_delivery` field: the gated conjunct is the
merged clause with a hypothesis discarded, and the boundary conjunct is the
merged clause verbatim. -/
theorem attestation_delivery_pair_iff (E : Execution Root) :
    ((∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1))) ∧
      (∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1)))) ↔
      (∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
        E.SlotWithinHorizon cfg s →
        E.WithinHorizon cfg n →
        E.vote v s = some (n, a) →
        ∀ w ∈ E.honest,
          Event.attestation a false ∈
            E.schedule w (E.slot_start cfg (s + 1))) := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun v hv s n a hs hn hvote _ => h v hv s n a hs hn hvote, h⟩

/-- The old receipt-gated delivery clause, derived from the merged one by
discarding the receipt-side horizon hypothesis. -/
theorem PaperSafetySynchrony.toHorizonScopedDelivery
    {E : Execution Root} (h : PaperSafetySynchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  fun v hv s n a hs hn hvote _ => h.attestation_delivery v hv s n a hs hn hvote

/-- The old `HorizonVoteDeliveryLookahead` boundary clause — now a special
case of the merged delivery field rather than a separate assumption. -/
theorem PaperSafetySynchrony.toDeliveryLookahead
    {E : Execution Root} (h : PaperSafetySynchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  h.attestation_delivery

/-- The old receipt-gated delivery clause, from the full synchrony bundle. -/
theorem Synchrony.toHorizonScopedDelivery
    {E : Execution Root} (h : Synchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      E.WithinHorizon cfg (E.slot_start cfg (s + 1)) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  fun v hv s n a hs hn hvote _ => h.attestation_delivery v hv s n a hs hn hvote

/-- The old boundary clause, from the full synchrony bundle. -/
theorem Synchrony.toDeliveryLookahead
    {E : Execution Root} (h : Synchrony cfg ext E) :
    ∀ v ∈ E.honest, ∀ s n (a : Attestation Root),
      E.SlotWithinHorizon cfg s →
      E.WithinHorizon cfg n →
      E.vote v s = some (n, a) →
      ∀ w ∈ E.honest,
        Event.attestation a false ∈ E.schedule w (E.slot_start cfg (s + 1)) :=
  h.attestation_delivery

/-- Horizon-bounded activity constancy specialized to epochs no later than
execution-clock epochs. The caller-supplied clock bounds put both epochs below
`E.verification_horizon`. -/
theorem StaticValidatorSet.activity_constant_of_epoch_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {e e' : Epoch} {n n' : ℕ}
    (he : e ≤ compute_epoch_at_slot cfg (E.slot_at cfg n))
    (he' : e' ≤ compute_epoch_at_slot cfg (E.slot_at cfg n'))
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) e =
      is_active_validator (E.registry.getD i default) e' := by
  exact hsv.activity_constant i e e'
    (lt_of_le_of_lt he hn) (lt_of_le_of_lt he' hn')

/-- Slot form of `activity_constant_of_epoch_le`: slots bounded by execution
clock slots have activity-equivalent epochs. -/
theorem StaticValidatorSet.activity_constant_of_slot_le
    {E : Execution Root} (hsv : StaticValidatorSet cfg E)
    {i : ValidatorIndex} {s s' : Slot} {n n' : ℕ}
    (hs : s ≤ E.slot_at cfg n) (hs' : s' ≤ E.slot_at cfg n')
    (hn : compute_epoch_at_slot cfg (E.slot_at cfg n) < E.verification_horizon)
    (hn' : compute_epoch_at_slot cfg (E.slot_at cfg n') < E.verification_horizon) :
    is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s) =
      is_active_validator (E.registry.getD i default) (compute_epoch_at_slot cfg s') :=
  hsv.activity_constant_of_epoch_le (cfg := cfg)
    (Nat.div_le_div_right hs) (Nat.div_le_div_right hs') hn hn'

end FastConfirmation.Spec

end
