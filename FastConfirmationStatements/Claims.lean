module
public import FastConfirmationModel
public import FastConfirmationStatements.Premises.ConcreteSafety

@[expose] public section

/-! Defines the public next-slot safety proposition over runs with the
concrete bridge. -/

section
namespace FastConfirmation.Spec
variable (Root : Type) [LinearOrder Root] [Inhabited Root]
/-- Whole-output safety of runs with the concrete bridge: for every bridge `B`
and run `E` that satisfy `B.SafetyPremises E`, every stored FCR output of an
honest node is in the observer's block store and is an ancestor of its head
from the next slot on, within the verification horizon. The run uses the
configuration `B.setup.cfg` and the state functions `B.interface`.

The global `NextSlotSynchronyPremises` in the premise makes this the current
model's GST-0 specialization. Its delivery contracts cover honest votes,
cutoff block paths, verified payloads before boundary votes, and cutoff
equivocation evidence. Each contract states its timing in slot boundaries
and attestation deadlines. -/
def ConfirmedRootSafeFromNextSlot : Prop :=
  ∀ (B : ConcreteFFG.ConcreteBridge Root) (E : Execution Root),
    B.SafetyPremises E →
      ∀ v ∈ E.honest, ∀ n : ℕ,
        ∀ w ∈ E.honest, ∀ m : ℕ, n ≤ m →
          E.slot_at B.setup.cfg n + 1 ≤ E.slot_at B.setup.cfg m →
          E.WithinHorizon B.setup.cfg m →
            E.confirmed B.setup.cfg B.interface v n ∈
                (E.store B.setup.cfg B.interface w m).block_roots ∧
              is_ancestor (E.store B.setup.cfg B.interface w m)
                (get_head B.setup.cfg (E.store B.setup.cfg B.interface w m))
                (get_node_for_root (E.confirmed B.setup.cfg B.interface v n)) = true

end FastConfirmation.Spec
end

end
