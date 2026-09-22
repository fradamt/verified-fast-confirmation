module
public import FastConfirmation.Spec.Proof.Provenance

@[expose] public section

/-!
An observer outside `Execution.honest` still has the structural part of
latest-message provenance. The attestation handler accepts a message only
when its block root is already known. This invariant uses no indexed
attestation validity law and therefore does not need an honest observer.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

def LatestMessageRootKnown (store : Store Root) : Prop :=
  ∀ i m, store.latest_messages i = some m → m.root ∈ store.block_roots

theorem latestMessageRootKnown_on_tick (store : Store Root) (time : Nat)
    (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown (on_tick cfg store time) := by
  intro i m hm
  rw [on_tick_latest cfg store time] at hm
  exact (on_tick_sameBlocks cfg store time).1 ▸ h i m hm

theorem latestMessageRootKnown_on_block {store store' : Store Root}
    {block : SignedBeaconBlock Root} (h : LatestMessageRootKnown store)
    (hsuccess : on_block cfg ext store block = some store') :
    LatestMessageRootKnown store' := by
  intro i m hm
  rw [on_block_latest cfg ext hsuccess] at hm
  exact (on_block_storeLE cfg ext hsuccess).1 (h i m hm)

theorem latestMessageRootKnown_on_attestation {store store' : Store Root}
    {a : Attestation Root} {fromBlock : Bool} (h : LatestMessageRootKnown store)
    (hsuccess : on_attestation cfg ext store a fromBlock = some store') :
    LatestMessageRootKnown store' := by
  have hsb := on_attestation_sameBlocks cfg ext hsuccess
  simp only [on_attestation] at hsuccess
  split_ifs at hsuccess with hv hvi
  cases hsuccess
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hroot⟩, _⟩, _⟩, _⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨_, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    exact hsb.1 ▸ h i m hold
  · rw [hmeq]
    exact hsb.1 ▸ hroot

theorem latestMessageRootKnown_on_attester_slashing {store store' : Store Root}
    {slashing : AttesterSlashing Root} (h : LatestMessageRootKnown store)
    (hsuccess : on_attester_slashing ext store slashing = some store') :
    LatestMessageRootKnown store' := by
  intro i m hm
  rw [on_attester_slashing_latest ext hsuccess] at hm
  exact (on_attester_slashing_sameBlocks ext hsuccess).1 ▸ h i m hm

theorem latestMessageRootKnown_apply_event (store : Store Root) (event : Event Root)
    (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown ((apply_event cfg ext store event).getD store) := by
  cases event with
  | block block =>
    simp only [apply_event]
    cases hresult : on_block cfg ext store block with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_block cfg ext h hresult
  | attestation a fromBlock =>
    simp only [apply_event]
    cases hresult : on_attestation cfg ext store a fromBlock with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_attestation cfg ext h hresult
  | attester_slashing slashing =>
    simp only [apply_event]
    cases hresult : on_attester_slashing ext store slashing with
    | none => exact h
    | some result => exact latestMessageRootKnown_on_attester_slashing ext h hresult

theorem latestMessageRootKnown_foldl {α : Type*} (f : Store Root → α → Store Root)
    (hf : ∀ store event, LatestMessageRootKnown store →
      LatestMessageRootKnown (f store event))
    (events : List α) (store : Store Root) (h : LatestMessageRootKnown store) :
    LatestMessageRootKnown (events.foldl f store) := by
  induction events generalizing store with
  | nil => exact h
  | cons event events ih => exact ih _ (hf store event h)

theorem Execution.latestMessageRootKnown {E : Execution Root}
    (hgen : ∃ state block, E.genesis_store = get_forkchoice_store cfg state block)
    (node : ValidatorIndex) (second : Nat) :
    LatestMessageRootKnown (E.store cfg ext node second) := by
  induction second with
  | zero =>
    obtain ⟨state, block, hgen⟩ := hgen
    change LatestMessageRootKnown E.genesis_store
    rw [hgen]
    intro i m hm
    simp [get_forkchoice_store] at hm
  | succ second ih =>
    exact latestMessageRootKnown_foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      (latestMessageRootKnown_apply_event cfg ext) _ _
      (latestMessageRootKnown_on_tick cfg _ _ ih)

end FastConfirmation.Spec

end
