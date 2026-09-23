module
public import FastConfirmationModel.Spec.Handlers

@[expose] public section

/-!
# Payload handler preservation

Proves that Gloas envelope and PTC handlers preserve every store field outside the payload maps. Python: `specs/gloas/fork-choice.md`, Payload envelope and PTC handlers.

The envelope and PTC handlers change only the three payload maps. The frame
relation below records every other field without an assumption about payload
validity or delivery. Block PTC notification preserves the same relation.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- Remove the three fields that payload handlers can change. -/
def Store.withoutPayloadFields (store : Store Root) : Store Root :=
  { store with
    payloads := fun _ => none
    payload_timeliness_vote := fun _ => none
    payload_data_availability_vote := fun _ => none }

/-- Every non-payload field is equal in the two stores. -/
def PayloadFrame (old new : Store Root) : Prop :=
  new.withoutPayloadFields = old.withoutPayloadFields

namespace PayloadFrame

end PayloadFrame

variable [LinearOrder Root] (cfg : Config) (ext : Externals Root)

end FastConfirmation.Spec

end
