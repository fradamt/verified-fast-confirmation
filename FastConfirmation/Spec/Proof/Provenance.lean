module
public import FastConfirmation.Spec.Proof.BlockAgreement
public import FastConfirmation.Spec.Proof.Preservation
public import FastConfirmation.Spec.Proof.Clock

@[expose] public section

/-!
# Spec / Proof / Provenance

`LatestMessageProvenance` is a trajectory invariant recording, for every
recorded LMD message, the applied
attestation that set it and the `validate_on_attestation` facts that guard it.

Concretely `LatestMessageProvenance E cfg sl store` says: whenever
`store.latest_messages i = some m`, there is an attestation `a` with

* `i ∈ a.attesting_indices` — `i` is one of `a`'s attesters;
* `a.data.target.epoch = (get_latest_message_epoch cfg m)`, `a.data.beacon_block_root = m.root` — the
  recorded message is exactly `a`'s FFG target epoch and LMD block;
* `compute_epoch_at_slot cfg a.data.slot = (get_latest_message_epoch cfg m)` — `a`'s slot sits in the
  message's epoch (the `validate_on_attestation` target/slot match);
* `a.data.slot + 1 ≤ sl` — `a` was applied at a store whose current slot was at
  least `a.data.slot + 1` (the `validate_on_attestation` fork-choice gate),
  bounded by the ambient slot `sl`;
* `i ∈ E.committee a.data.slot` — `i` is in `a`'s slot committee (the span
  confinement `ByzantineBound` budgets), from
  `ExternalsCoherence.valid_attestation_committee`;
* `m.root ∈ store.block_roots` and `(store.blocks m.root).slot ≤ a.data.slot` —
  the voted block is known and no later than `a`'s slot (the
  `validate_on_attestation` known-block / not-future gates).
* `m.slot = a.data.slot` — the handler stores the exact attestation slot, so a
  resolved payload vote at a root belongs to a later committee slot.

This is the span-confinement input to L2's accounting half: an honest recorded
supporter's message is confined to the committee of a slot in `[m.root's slot,
sl - 1]`.

The slot bound `sl` is an external upper bound (weakenable, `LatestMessageProvenance.mono_sl`);
the trajectory theorem instantiates it with `E.slot_at cfg n`. The genesis base
takes the sanctioned `∃`-form `E.genesis_store = get_forkchoice_store …`
(latest messages start empty). `WellFormedExecution` (wire-root injectivity,
already in `SpecAssumptions`) preserves the known-block slot fact across
`on_block` (block records are stable at commonly-known roots — `BlockAgreement`),
and `ExternalsCoherence` supplies committee confinement on reachable validation
states. The trajectory theorem requires an honest node and an in-horizon
second.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-! ## The provenance predicate -/

/-- Latest-message provenance of a store relative to an execution and an ambient
slot bound `sl`: every recorded LMD message was set by an applied attestation
whose `validate_on_attestation`/committee facts are recorded. See the module
docstring for the meaning of each conjunct. -/
def LatestMessageProvenance (E : Execution Root) (cfg : Config) (sl : Slot)
    (store : Store Root) : Prop :=
  ∀ (i : ValidatorIndex) (m : LatestMessage Root),
    store.latest_messages i = some m →
    ∃ a : Attestation Root,
      i ∈ a.attesting_indices ∧
      a.data.target.epoch = (get_latest_message_epoch cfg m) ∧
      a.data.beacon_block_root = m.root ∧
      compute_epoch_at_slot cfg a.data.slot = (get_latest_message_epoch cfg m) ∧
      a.data.slot + 1 ≤ sl ∧
      i ∈ E.committee a.data.slot ∧
      m.root ∈ store.block_roots ∧
      (store.blocks m.root).slot ≤ a.data.slot ∧
      m.slot = a.data.slot

namespace LatestMessageProvenance

/-- The ambient slot bound is an upper bound: a larger bound is weaker. -/
theorem mono_sl {E : Execution Root} {cfg : Config} {sl sl' : Slot} {store : Store Root}
    (hle : sl ≤ sl') (h : LatestMessageProvenance E cfg sl store) :
    LatestMessageProvenance E cfg sl' store := by
  intro i m hm
  obtain ⟨a, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i m hm
  exact ⟨a, h1, h2, h3, h4, h5.trans hle, h6, h7, h8, h9⟩

/-- Transfer provenance across a store update that only grows the block set and
whose recorded messages come from the source, keeping the block slot at every
known root (the shape every non-attestation handler produces). The bound `sl`
is untouched. -/
theorem of_transfer {E : Execution Root} {cfg : Config} {sl : Slot}
    {store store' : Store Root} (h : LatestMessageProvenance E cfg sl store)
    (hbr : store.block_roots ⊆ store'.block_roots)
    (hlm : ∀ i m, store'.latest_messages i = some m → store.latest_messages i = some m)
    (hblk : ∀ r ∈ store.block_roots, (store'.blocks r).slot = (store.blocks r).slot) :
    LatestMessageProvenance E cfg sl store' := by
  intro i m hm
  obtain ⟨a, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i m (hlm i m hm)
  exact ⟨a, h1, h2, h3, h4, h5, h6, hbr h7, (hblk m.root h7) ▸ h8, h9⟩

/-- Transfer provenance across a `SameBlocks`-related store that leaves
`latest_messages` untouched (`on_tick`, `on_attester_slashing`, and the
block-identity-preserving helpers). -/
theorem of_sameBlocks {E : Execution Root} {cfg : Config} {sl : Slot}
    {store store' : Store Root} (h : LatestMessageProvenance E cfg sl store)
    (hsb : SameBlocks store store')
    (hlm : store'.latest_messages = store.latest_messages) :
    LatestMessageProvenance E cfg sl store' :=
  h.of_transfer (fun _ hx => hsb.1 ▸ hx) (fun _ _ hh => hlm ▸ hh)
    (fun r _ => by rw [hsb.2.1])

end LatestMessageProvenance

/-! ## `update_latest_messages` membership characterization -/

/-- Fold-membership for the `update_latest_messages` step: any surviving
`some m` after folding the per-index update over `l` was either present before
the fold or is `⟨target, beacon⟩` set at an index of `l`. -/
private theorem update_lm_foldl_mem (slot : Slot) (beacon : Root) (payload_present : Bool) :
    ∀ (l : List ValidatorIndex) (s : Store Root) (i : ValidatorIndex)
      (m : LatestMessage Root),
      (l.foldl (fun st j =>
        if (match st.latest_messages j with
            | none => true
            | some lm => decide (slot > lm.slot)) then
          { st with latest_messages :=
              Function.update st.latest_messages j (some (LatestMessage.mk slot beacon payload_present)) }
        else st) s).latest_messages i = some m →
      s.latest_messages i = some m ∨ (i ∈ l ∧ m = LatestMessage.mk slot beacon payload_present) := by
  intro l
  induction l with
  | nil => intro s i m hm; exact Or.inl hm
  | cons j l ih =>
    intro s i m hm
    rw [List.foldl_cons] at hm
    rcases ih _ i m hm with hstep | ⟨hmem, hnew⟩
    · split_ifs at hstep with hupd
      · simp only [Function.update_apply] at hstep
        split_ifs at hstep with hij
        · exact Or.inr ⟨by rw [hij]; exact List.mem_cons_self,
            by injection hstep with h; exact h.symm⟩
        · exact Or.inl hstep
      · exact Or.inl hstep
    · exact Or.inr ⟨List.mem_cons_of_mem j hmem, hnew⟩

/-- `update_latest_messages` sets `latest_messages i` only for `i` among the
non-equivocating attesting indices, always to `⟨target.epoch, beacon_block_root⟩`;
so any surviving `some m` was either already present or is that message at an
attesting index. -/
theorem update_latest_messages_mem (store : Store Root)
    (attesting_indices : List ValidatorIndex) (a : Attestation Root)
    (i : ValidatorIndex) (m : LatestMessage Root)
    (hm : (update_latest_messages store attesting_indices a).latest_messages i = some m) :
    store.latest_messages i = some m ∨
      (i ∈ attesting_indices ∧
        m = LatestMessage.mk a.data.slot a.data.beacon_block_root (decide (a.data.index = 1))) := by
  simp only [update_latest_messages] at hm
  rcases update_lm_foldl_mem a.data.slot a.data.beacon_block_root (decide (a.data.index = 1)) _ store i m hm with
    hs | ⟨hmem, hnew⟩
  · exact Or.inl hs
  · exact Or.inr ⟨List.mem_of_mem_filter hmem, hnew⟩

/-! ## `get_current_slot` congruence -/

/-- `get_current_slot` reads only `time` and `genesis_time`, so it agrees across
stores agreeing on those. -/
theorem get_current_slot_congr (cfg : Config) {s t : Store Root}
    (ht : s.time = t.time) (hg : s.genesis_time = t.genesis_time) :
    get_current_slot cfg s = get_current_slot cfg t := by
  simp only [get_current_slot, get_slots_since_genesis, ht, hg]

/-! ## `latest_messages` preservation by the block/tick handlers

Every handler except `on_attestation` leaves `latest_messages` untouched — the
reverse-implication input to `LatestMessageProvenance.of_transfer`. -/

variable [LinearOrder Root] [Inhabited Root] (cfg : Config) (ext : Externals Root)

omit [Inhabited Root] in
theorem record_block_timeliness_latest (store : Store Root) (root : Root) :
    (record_block_timeliness cfg store root).latest_messages = store.latest_messages := rfl

theorem update_proposer_boost_root_latest (store : Store Root) (head root : Root) :
    (update_proposer_boost_root cfg store head root).latest_messages =
      store.latest_messages := by
  simp only [update_proposer_boost_root]; split_ifs <;> rfl

omit [Inhabited Root] in
theorem store_target_checkpoint_state_latest (store : Store Root) (target : Checkpoint Root) :
    (store_target_checkpoint_state cfg ext store target).latest_messages =
      store.latest_messages := by
  simp only [store_target_checkpoint_state]; split_ifs <;> rfl

omit [Inhabited Root] in
theorem compute_pulled_up_tip_latest (store : Store Root) (block_root : Root) :
    (compute_pulled_up_tip cfg ext store block_root).latest_messages =
      store.latest_messages := by
  simp only [compute_pulled_up_tip]; split_ifs <;> simp

omit [LinearOrder Root] in
theorem on_tick_per_slot_latest (store : Store Root) (time : ℕ) :
    (on_tick_per_slot cfg store time).latest_messages = store.latest_messages := by
  simp only [on_tick_per_slot]; split_ifs <;> simp

omit [LinearOrder Root] in
theorem on_tick_aux_latest (tick_slot fuel : ℕ) (store : Store Root) :
    (on_tick_aux cfg tick_slot fuel store).latest_messages = store.latest_messages := by
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
    rw [on_tick_aux]
    split_ifs
    · rw [ih, on_tick_per_slot_latest]
    · rfl

omit [LinearOrder Root] in
theorem on_tick_latest (store : Store Root) (time : ℕ) :
    (on_tick cfg store time).latest_messages = store.latest_messages := by
  simp only [on_tick]; rw [on_tick_per_slot_latest, on_tick_aux_latest]

theorem on_block_latest {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (h : on_block cfg ext store sb = some store') :
    store'.latest_messages = store.latest_messages := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp [on_block, hknown] at h
    cases h
    rfl
  · simp only [on_block, if_neg hknown] at h
    split_ifs at h
    all_goals try contradiction
    cases hst : ext.state_transition (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at h; cases h
    | some state =>
      rw [hst] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i notified hnotify
        cases h
        rw [compute_pulled_up_tip_latest, update_checkpoints_latest_messages,
          update_proposer_boost_root_latest, record_block_timeliness_latest]
        exact (notify_ptc_messages_frame cfg ext hnotify).latest_messages

omit [Inhabited Root] in
theorem on_attester_slashing_latest {store store' : Store Root}
    {sl : AttesterSlashing Root} (h : on_attester_slashing ext store sl = some store') :
    store'.latest_messages = store.latest_messages := by
  simp only [on_attester_slashing] at h
  split_ifs at h
  cases h
  rfl

/-! ## Handler-level provenance preservation

`on_tick` / `on_attester_slashing` ride across by `of_sameBlocks`; `on_block`
grows the block set but keeps every commonly-known block record fixed
(`WellFormedExecution.blocks_agree`), so the known-block slot fact survives. -/

omit [LinearOrder Root] in
theorem on_tick_LMP {E : Execution Root} {sl : Slot} (store : Store Root) (time : ℕ)
    (h : LatestMessageProvenance E cfg sl store) :
    LatestMessageProvenance E cfg sl (on_tick cfg store time) :=
  h.of_sameBlocks (on_tick_sameBlocks cfg store time) (on_tick_latest cfg store time)

omit [Inhabited Root] in
theorem on_attester_slashing_LMP {E : Execution Root} {sl : Slot}
    {store store' : Store Root} {asl : AttesterSlashing Root}
    (h : LatestMessageProvenance E cfg sl store)
    (hh : on_attester_slashing ext store asl = some store') :
    LatestMessageProvenance E cfg sl store' :=
  h.of_sameBlocks (on_attester_slashing_sameBlocks ext hh) (on_attester_slashing_latest ext hh)

theorem on_block_LMP {E : Execution Root} {sl : Slot} (hwf : WellFormedExecution E)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hsched : IsScheduledBlock E sb) (hprov : BlockProvenance E store)
    (h : LatestMessageProvenance E cfg sl store)
    (hh : on_block cfg ext store sb = some store') :
    LatestMessageProvenance E cfg sl store' := by
  have hprov' : BlockProvenance E store' := on_block_blockProvenance cfg ext hsched hprov hh
  have hle : StoreLE store store' := on_block_storeLE cfg ext hh
  refine h.of_transfer hle.1 (fun i m hm => ?_) (fun r hr => ?_)
  · rw [on_block_latest cfg ext hh] at hm; exact hm
  · rw [hwf.blocks_agree hprov hprov' hr (hle.1 hr)]

/-- Updating LMD messages leaves the checkpoint cache unchanged. -/
private theorem update_latest_messages_checkpointData
    (store : Store Root) (indices : List ValidatorIndex) (a : Attestation Root) :
    ((update_latest_messages store indices a).checkpoint_state_keys,
      (update_latest_messages store indices a).checkpoint_states) =
      (store.checkpoint_state_keys, store.checkpoint_states) := by
  simp only [update_latest_messages]
  generalize hindices :
    indices.filter (fun i => decide (i ∉ store.equivocating_indices)) = remaining
  clear hindices
  induction remaining generalizing store with
  | nil => rfl
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      split_ifs <;> rfl

/-- `on_attestation` records the applied attestation's provenance for the freshly
set messages (via `update_latest_messages_mem` + the `validate_on_attestation`
conjuncts + `ExternalsCoherence.valid_attestation_committee`) and transports the
pre-existing ones (the block set and clock are unchanged). The successful
post-store supplies the reachable checkpoint state. `hcur` bounds the store's
current slot by `sl`. -/
theorem on_attestation_LMP {E : Execution Root} {sl : Slot}
    (hec : ExternalsCoherence cfg ext E) {store store' : Store Root}
    {a : Attestation Root} {ifb : Bool} (hcur : get_current_slot cfg store ≤ sl)
    (h : LatestMessageProvenance E cfg sl store)
    (hh : on_attestation cfg ext store a ifb = some store')
    (hpost : E.HonestCausalStore cfg ext store') :
    LatestMessageProvenance E cfg sl store' := by
  have hsb := on_attestation_sameBlocks cfg ext hh
  simp only [on_attestation] at hh
  split_ifs at hh with hv hvi
  cases hh
  have hcache := update_latest_messages_checkpointData
    (store_target_checkpoint_state cfg ext store a.data.target) a.attesting_indices a
  have hkeys := congrArg Prod.fst hcache
  have hstates := congrArg Prod.snd hcache
  dsimp only at hkeys hstates
  have htarget : a.data.target ∈
      (store_target_checkpoint_state cfg ext store a.data.target).checkpoint_state_keys := by
    by_cases hcached : a.data.target ∈ store.checkpoint_state_keys
    · simp [store_target_checkpoint_state, hcached]
    · simp [store_target_checkpoint_state, hcached]
  have hreachable : E.ReachableValidationState cfg ext
      ((store_target_checkpoint_state cfg ext store a.data.target).checkpoint_states
        a.data.target) := by
    have hkey : a.data.target ∈
        (update_latest_messages
          (store_target_checkpoint_state cfg ext store a.data.target)
          a.attesting_indices a).checkpoint_state_keys := by
      rw [hkeys]
      exact htarget
    simpa only [hstates] using hpost.checkpointState cfg ext hkey
  simp only [validate_on_attestation, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hB⟩, _⟩, hD⟩, hE⟩, _⟩, _⟩, _⟩, _⟩, hG⟩ := hv
  intro i m hm
  rcases update_latest_messages_mem _ _ _ _ _ hm with hold | ⟨hi, hmeq⟩
  · rw [store_target_checkpoint_state_latest] at hold
    obtain ⟨a', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i m hold
    exact ⟨a', h1, h2, h3, h4, h5, h6, hsb.1 ▸ h7, hsb.2.1 ▸ h8, h9⟩
  · exact ⟨a, hi, by rw [hmeq]; exact hB, by rw [hmeq], by rw [hmeq]; rfl,
      le_trans hG hcur, hec.valid_attestation_committee _ a hreachable hvi i hi,
      by rw [hmeq]; exact hsb.1 ▸ hD, by rw [hmeq]; exact hsb.2.1 ▸ hE,
      by rw [hmeq]⟩

/-! ## Event dispatch, the event fold, and the trajectory invariant -/

/-- `apply_event` preserves the store's current slot (every handler preserves
`time` and `genesis_time`). -/
theorem apply_event_get_current_slot {store store' : Store Root} {e : Event Root}
    (he : apply_event cfg ext store e = some store') :
    get_current_slot cfg store' = get_current_slot cfg store :=
  get_current_slot_congr cfg (apply_event_time cfg ext he)
    (apply_event_storeLE cfg ext he).2.1.symm

/-- One dispatched event preserves provenance: block events use `on_block_LMP`
(needing the block to be scheduled + `BlockProvenance`), attestations
`on_attestation_LMP` (needing the slot bound `hcur`), attester slashings ride
across by `of_sameBlocks`. -/
theorem apply_event_LMP {E : Execution Root} {sl : Slot} (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E) {store store' : Store Root} {e : Event Root}
    (hsched : ∀ b, e = Event.block b → IsScheduledBlock E b)
    (hprov : BlockProvenance E store) (hcur : get_current_slot cfg store ≤ sl)
    (h : LatestMessageProvenance E cfg sl store)
    (he : apply_event cfg ext store e = some store')
    (hpost : E.HonestCausalStore cfg ext store') :
    LatestMessageProvenance E cfg sl store' := by
  cases e with
  | block b =>
    simp only [apply_event] at he
    exact on_block_LMP cfg ext hwf (hsched b rfl) hprov h he
  | attestation a ifb =>
    simp only [apply_event] at he
    exact on_attestation_LMP cfg ext hec hcur h he hpost
  | attester_slashing asl =>
    simp only [apply_event] at he
    exact h.of_sameBlocks (on_attester_slashing_sameBlocks ext he)
      (on_attester_slashing_latest ext he)
  | execution_payload_envelope envelope observation =>
    have hf := on_execution_payload_envelope_frame ext he
    exact h.of_transfer (by rw [hf.block_roots]; exact List.Subset.refl _)
      (fun _ _ hh => hf.latest_messages ▸ hh) (fun r _ => by rw [hf.blocks])
  | payload_attestation_message message fromBlock =>
    have hf := on_payload_attestation_message_frame cfg ext he
    exact h.of_transfer (by rw [hf.block_roots]; exact List.Subset.refl _)
      (fun _ _ hh => hf.latest_messages ▸ hh) (fun r _ => by rw [hf.blocks])

/-- Folding the second's scheduled events preserves provenance: every block
event is scheduled, so `BlockProvenance` (fed to `on_block`'s block-slot
stability) and the slot bound are re-established at each step. Every prefix
store must belong to the honest, in-horizon causal domain. -/
theorem LMP_foldl {E : Execution Root} {sl : Slot} (hwf : WellFormedExecution E)
    (hec : ExternalsCoherence cfg ext E) :
    ∀ (l : List (Event Root)) (s : Store Root),
      (∀ b, Event.block b ∈ l → IsScheduledBlock E b) →
      BlockProvenance E s → get_current_slot cfg s ≤ sl →
      LatestMessageProvenance E cfg sl s →
      (∀ k, k ≤ l.length → E.HonestCausalStore cfg ext
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store) s)) →
      LatestMessageProvenance E cfg sl
        (l.foldl (fun store event => (apply_event cfg ext store event).getD store) s) := by
  intro l
  induction l with
  | nil => intro s _ _ _ h _; exact h
  | cons e l ih =>
    intro s hl hprov hcur h hcausal
    have htail : ∀ k, k ≤ l.length → E.HonestCausalStore cfg ext
        ((l.take k).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ((apply_event cfg ext s e).getD s)) := by
      intro k hk
      simpa only [List.take_succ_cons, List.foldl_cons] using
        hcausal (k + 1) (by simpa using Nat.succ_le_succ hk)
    have hstep : E.HonestCausalStore cfg ext
        ((apply_event cfg ext s e).getD s) := by
      simpa using htail 0 (Nat.zero_le _)
    rw [List.foldl_cons]
    have hbsched : ∀ b, e = Event.block b → IsScheduledBlock E b :=
      fun b hbe => hl b (by rw [← hbe]; exact List.mem_cons_self)
    cases he : apply_event cfg ext s e with
    | none =>
      simp only [Option.getD_none]
      exact ih _ (fun b hb => hl b (List.mem_cons_of_mem e hb)) hprov hcur h
        (by simpa only [he, Option.getD_none] using htail)
    | some s' =>
      simp only [Option.getD_some]
      refine ih _ (fun b hb => hl b (List.mem_cons_of_mem e hb)) ?_ ?_ ?_ ?_
      · exact apply_event_blockProvenance cfg ext hbsched hprov he
      · rw [apply_event_get_current_slot cfg ext he]; exact hcur
      · exact apply_event_LMP cfg ext hwf hec hbsched hprov hcur h he
          (by simpa only [he, Option.getD_some] using hstep)
      · simpa only [he, Option.getD_some] using htail

/-- Latest-message provenance holds at every honest node and in-horizon second
of a well-formed execution whose genesis store is a `get_forkchoice_store`
(empty latest messages), with ambient bound the wall-clock slot `E.slot_at cfg
n`. Base: genesis has no recorded messages; step: weaken the bound by
`slot_at_mono`, push through `on_tick`, then fold the second's events. -/
theorem Execution.latestMessageProvenance {E : Execution Root}
    (hwf : WellFormedExecution E) (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    (v : ValidatorIndex) (n : ℕ) (hv : v ∈ E.honest)
    (hn : E.WithinHorizon cfg n) :
    LatestMessageProvenance E cfg (E.slot_at cfg n) (E.store cfg ext v n) := by
  revert hn
  induction n with
  | zero =>
    intro _hn
    obtain ⟨ast, ablk, hg⟩ := hgen
    intro i m hm
    have hm' : E.genesis_store.latest_messages i = some m := hm
    rw [hg] at hm'
    simp [get_forkchoice_store] at hm'
  | succ n ih =>
    intro hn
    change LatestMessageProvenance E cfg (E.slot_at cfg (n + 1))
      ((E.schedule v (n + 1)).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
    have hontickgen :
        (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))).genesis_time =
          E.genesis_store.genesis_time := by
      rw [← (on_tick_storeLE cfg (E.store cfg ext v n) (E.time_at (n + 1))).2.1,
        E.store_genesis_time cfg ext v n]
    have hslot :
        get_current_slot cfg (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))) =
          E.slot_at cfg (n + 1) := by
      rw [get_current_slot, get_slots_since_genesis, on_tick_time, hontickgen,
        Execution.slot_at]
    refine LMP_foldl cfg ext hwf hec _ _ (fun b hb => ⟨v, n + 1, hb⟩) ?_ ?_ ?_ ?_
    · exact on_tick_blockProvenance cfg _ _ (E.blockProvenance cfg ext v n)
    · rw [hslot]
    · exact on_tick_LMP cfg _ _
        ((ih (E.withinHorizon_mono cfg (Nat.le_succ n) hn)).mono_sl
          (E.slot_at_mono cfg (Nat.le_succ n)))
    · intro k hk
      exact .scheduledPrefix ⟨v, n, k, hk⟩ hv hn

end FastConfirmation.Spec

end
