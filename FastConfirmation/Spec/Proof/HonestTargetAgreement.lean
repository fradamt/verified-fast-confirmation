import FastConfirmation.Spec.Proof.SelectedA32Support
import FastConfirmation.Spec.Proof.L4Fold
import FastConfirmation.Spec.Proof.AcceptedPathLocalFinalizedTransport

/-!
# Spec / Proof / HonestTargetAgreement

Wave 2 of `docs/proviso-discharge-map.md` §6: the **first constructor** for
`HonestVotesSupportTarget` in the development.

Every previous occurrence of `HonestVotesSupportTarget` in this repository is
either a hypothesis or a record field (`SelectedHelperProvisosAt.current_target`,
`SelectedHelperProvisosAt.selected_previous_result_no_conflict`, and the two
dead `JustificationInterface` gates).  Nothing builds one.  This module builds
one, from a trajectory-level `Execution.SafeFrom` witness plus an explicit list
of store-geometry side conditions, and so turns a *carried* normative proviso
into a statement whose residual content is exactly those side conditions.

## The route

`get_current_target` is `get_checkpoint_for_block store (get_head store).root
(get_current_store_epoch store)` (`Model/FCRStore.lean`), and an honest vote's
FFG target is `Checkpoint (get_current_epoch head_state)
(get_checkpoint_block store head.root …)` (`Model/Validator.lean`).  Both sides
are therefore an epoch-boundary walk from a fork-choice head.  The argument is:

1. `honest_vote_eq_honestAttestation` — an honest recorded vote *is* the
   validator-spec attestation built from that validator's own store at the cast
   second, and that second lies in the voted slot
   (`HonestBehavior.votes_assigned` + `votes_head`).
2. `honest_vote_castSecond_ge_of_slotStart` — when the query second `q` is the
   first second of its slot, every vote of a slot at or after `slot_at q` is
   cast at a second `≥ q`.  This is what makes a `SafeFrom … q` witness apply at
   the cast second, and it is the three-line lemma the map's §3(iii) asks for:
   the "same-slot earlier cast" worry is vacuous at genuine call sites, where
   `slot_start (slot_at (n+1)) = n+1`.
3. `honestVoteTarget_eq_checkpoint_of_head_ancestor` — with `SafeFrom b q` the
   voter's head descends from `b`, so by `get_checkpoint_block_of_ancestor` the
   voter's own boundary walk factors through `b`: the target root is `b`'s
   boundary block, *computed in the voter's store*.
4. `honestVotesSupportTarget_of_safeFrom_currentEpochCandidate` — the packaging.
   `current_target_eq_checkpoint_of_current_epoch_ancestor` puts the query
   store's target on the same footing, and
   `get_checkpoint_block_eq_of_paired_walks` equates the voter-store and
   query-store walks from `b`.

## What is *not* discharged

The conclusion is only as strong as its hypotheses, and the hypotheses are
deliberately explicit rather than folded into a weaker conclusion.  The residual
content is:

* `b` must be a **current-epoch** block of the query store which the query head
  descends from (`hbEpoch`, `hqueryHead`).  Per the map's §5.1 this is exactly
  the configuration the live proviso sites do *not* enjoy: there the `SafeFrom`
  root is a previous-epoch block and the current-epoch boundary block sits
  strictly above it.  So this constructor does not by itself discharge
  `Execution.SelectedHelperProvisosAt.current_target`; it pins down precisely
  what would.
* the voter's store must know the boundary walk from its head and from `b`, and
  must agree with the query store on the blocks both know (`hvoterHeadWalk`,
  `hvoterWalk`, `hagree`).  These are the standard cross-store transport
  premises used throughout `AcceptedPathLocalFinalizedTransport.lean`.
* the honest head state must not run ahead of the voted slot (`hvoterHeadSlot`),
  the `ext.process_slots` clock law (`hps`), and whole-second slots plus a
  genesis-ordered anchor store (`hdiv`, `hgen`) — the usual `Clock.lean` pair.

Nothing here is floor-classified: every hypothesis is a derivable store fact
under the accepted bundles, and none of them is a new normative assumption.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

omit [LinearOrder Root] [Inhabited Root] in
/-- Structure equality for `Checkpoint` from its two fields. -/
private theorem checkpoint_eq_of_fields {c : Checkpoint Root} {e : Epoch}
    {r : Root} (he : c.epoch = e) (hr : c.root = r) :
    c = Checkpoint.mk e r := by
  cases c
  simp only [Checkpoint.mk.injEq]
  exact ⟨he, hr⟩

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — the cast second of an honest vote -/

/-- An honest recorded vote is the validator-spec attestation built from the
voter's own store at the cast second, and that second lies in the voted slot.

`HonestBehavior.votes_assigned` turns "a vote is recorded" into committee
membership, which is exactly the premise `votes_head` needs; `votes_head` then
pins both the cast second and the attestation itself. -/
theorem honest_vote_eq_honestAttestation
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot}
    (hsH : E.SlotWithinHorizon cfg s) (hs0 : E.slot_at cfg 0 ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a)) :
    ∃ index : CommitteeIndex,
      E.WithinHorizon cfg k ∧ E.slot_at cfg k = s ∧
        a = honest_attestation cfg ext (E.store cfg ext v k) s index v := by
  have hcommittee : v ∈ E.committee s :=
    hhb.votes_assigned v hv s (by rw [hvote]; simp)
  obtain ⟨n, index, hnH, hnSlot, hnVote⟩ :=
    hhb.votes_head v hv s hcommittee hsH hs0
  rw [hvote] at hnVote
  have hpair := Option.some.inj hnVote
  have hk : k = n := congrArg Prod.fst hpair
  have ha : a = honest_attestation cfg ext (E.store cfg ext v n) s index v :=
    congrArg Prod.snd hpair
  subst hk
  exact ⟨index, hnH, hnSlot, ha⟩

/-- **Map §6 wave 2, lemma 1.**  An honest vote for slot `s` is cast at a second
lying in slot `s`. -/
theorem honest_vote_castSecond_slot
    (hhb : HonestBehavior cfg ext E)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {s : Slot}
    (hsH : E.SlotWithinHorizon cfg s) (hs0 : E.slot_at cfg 0 ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a)) :
    E.slot_at cfg k = s :=
  let ⟨_, _, hkSlot, _⟩ :=
    E.honest_vote_eq_honestAttestation cfg ext hhb hv hsH hs0 hvote
  hkSlot

/-- **Map §6 wave 2, lemma 2.**  When the query second `q` is the first second
of its own slot, every honest vote of a slot at or after `slot_at q` is cast at
a second at or after `q`.

This is what lets a `SafeFrom … q` witness be applied at the cast second, and it
is why the "same-slot earlier cast" case is vacuous at genuine FCR call sites:
there `q = n + 1` and `slot_start (slot_at (n+1)) = n+1`
(`Execution.slot_start_eq_succ_of_advance_minimal`). -/
theorem honest_vote_castSecond_ge_of_slotStart
    (hhb : HonestBehavior cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {q : ℕ} {s : Slot}
    (hqStart : E.slot_start cfg (E.slot_at cfg q) = q)
    (hsH : E.SlotWithinHorizon cfg s) (hs0 : E.slot_at cfg 0 ≤ s)
    (hqs : E.slot_at cfg q ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a)) :
    q ≤ k := by
  have hkSlot : E.slot_at cfg k = s :=
    E.honest_vote_castSecond_slot cfg ext hhb hv hsH hs0 hvote
  refine Nat.le_of_not_gt ?_
  intro hlt
  have hlt' : k < E.slot_start cfg (E.slot_at cfg q) := by rw [hqStart]; exact hlt
  have hslotLt : E.slot_at cfg k < E.slot_at cfg q :=
    (E.slot_at_lt_iff cfg hdiv hgen).2 hlt'
  rw [hkSlot] at hslotLt
  exact absurd hqs (Nat.not_le_of_gt hslotLt)

/-! ## Section 2 — the honest target is `b`'s boundary block -/

/-- **Map §6 wave 2, lemma 3.**  An honest vote's FFG target is the vote-epoch
checkpoint of any `SafeFrom`-safe block `b` whose epoch is the vote slot's,
computed in the voter's own store.

The head of the voter at the cast second descends from `b` (`SafeFrom`, applied
at `k ≥ q` by `honest_vote_castSecond_ge_of_slotStart`), so its epoch-boundary
walk factors through `b` (`get_checkpoint_block_of_ancestor`).  The epoch
conjunct is `Delivery.honest_attestation_data_target_epoch`, the root conjunct
`Delivery.honest_attestation_data_target_root`. -/
theorem honestVoteTarget_eq_checkpoint_of_head_ancestor_capped
    (hhb : HonestBehavior cfg ext E)
    (hps : ∀ (st : BeaconState Root) (t : Slot), st.slot < t →
      (ext.process_slots st t).slot = t)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {b : Root} {q : ℕ} {s : Slot}
    {cap : Slot}
    (heng : EngineInv cfg ext E b q cap)
    (hscap : s ≤ cap)
    (hqStart : E.slot_start cfg (E.slot_at cfg q) = q)
    (hsH : E.SlotWithinHorizon cfg s) (hs0 : E.slot_at cfg 0 ≤ s)
    (hqs : E.slot_at cfg q ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a))
    (hvoterHeadSlot : ((E.store cfg ext v k).block_states
      (get_head cfg (E.store cfg ext v k)).root).slot ≤ s)
    (hvoterParent : ParentSlotLt (E.store cfg ext v k))
    (hbEpoch : get_block_epoch cfg (E.store cfg ext v k) b =
      compute_epoch_at_slot cfg s)
    (hvoterHeadWalk : WalkKnown (E.store cfg ext v k)
      (compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg s))
      (get_head cfg (E.store cfg ext v k)).root) :
    a.data.target =
      Checkpoint.mk (compute_epoch_at_slot cfg s)
        (get_checkpoint_block cfg (E.store cfg ext v k) b
          (compute_epoch_at_slot cfg s)) := by
  have hqk : q ≤ k :=
    E.honest_vote_castSecond_ge_of_slotStart cfg ext hhb hdiv hgen hv hqStart
      hsH hs0 hqs hvote
  obtain ⟨index, hkH, hkSlot, rfl⟩ :=
    E.honest_vote_eq_honestAttestation cfg ext hhb hv hsH hs0 hvote
  have hanc := heng v hv k hqk (by rw [hkSlot]; exact hscap) hkH
  have hepoch :
      (honest_attestation_data cfg ext (E.store cfg ext v k) s index).target.epoch =
        compute_epoch_at_slot cfg s :=
    honest_attestation_data_target_epoch cfg ext (E.store cfg ext v k) s index
      hps hvoterHeadSlot
  have hslot : compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg s) ≤
      ((E.store cfg ext v k).blocks b).slot := by
    rw [← hbEpoch]
    exact start_slot_at_block_epoch_le cfg (E.store cfg ext v k) b
  have hwalkEq := get_checkpoint_block_of_ancestor cfg hvoterParent hanc hslot
    hvoterHeadWalk
  rw [honest_attestation_data_eq]
  refine checkpoint_eq_of_fields hepoch ?_
  rw [honest_attestation_data_target_root, hepoch]
  exact hwalkEq

/-- `SafeFrom` is `EngineInv` with the cutoff cap removed, so it weakens to
`EngineInv` at *every* cap.  This is the only direction the capped
target-agreement twins need. -/
theorem engineInv_of_safeFrom {b : Root} {n₀ : ℕ} {cap : Slot}
    (hsafe : E.SafeFrom cfg ext b n₀) : EngineInv cfg ext E b n₀ cap :=
  fun w hw m hm _ hH => hsafe w hw m hm hH

/-- The uncapped form, unchanged: instantiate the cap at the vote slot. -/
theorem honestVoteTarget_eq_checkpoint_of_head_ancestor
    (hhb : HonestBehavior cfg ext E)
    (hps : ∀ (st : BeaconState Root) (t : Slot), st.slot < t →
      (ext.process_slots st t).slot = t)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {v : ValidatorIndex} (hv : v ∈ E.honest) {b : Root} {q : ℕ} {s : Slot}
    (hsafe : E.SafeFrom cfg ext b q)
    (hqStart : E.slot_start cfg (E.slot_at cfg q) = q)
    (hsH : E.SlotWithinHorizon cfg s) (hs0 : E.slot_at cfg 0 ≤ s)
    (hqs : E.slot_at cfg q ≤ s)
    {k : ℕ} {a : Attestation Root} (hvote : E.vote v s = some (k, a))
    (hvoterHeadSlot : ((E.store cfg ext v k).block_states
      (get_head cfg (E.store cfg ext v k)).root).slot ≤ s)
    (hvoterParent : ParentSlotLt (E.store cfg ext v k))
    (hbEpoch : get_block_epoch cfg (E.store cfg ext v k) b =
      compute_epoch_at_slot cfg s)
    (hvoterHeadWalk : WalkKnown (E.store cfg ext v k)
      (compute_start_slot_at_epoch cfg (compute_epoch_at_slot cfg s))
      (get_head cfg (E.store cfg ext v k)).root) :
    a.data.target =
      Checkpoint.mk (compute_epoch_at_slot cfg s)
        (get_checkpoint_block cfg (E.store cfg ext v k) b
          (compute_epoch_at_slot cfg s)) :=
  E.honestVoteTarget_eq_checkpoint_of_head_ancestor_capped cfg ext hhb hps
    hdiv hgen hv (E.engineInv_of_safeFrom cfg ext hsafe) (le_refl s) hqStart
    hsH hs0 hqs hvote hvoterHeadSlot hvoterParent hbEpoch hvoterHeadWalk

/-! ## Section 3 — the packaging -/

/-- **Map §6 wave 2, lemma 4** — the first constructor for
`HonestVotesSupportTarget`.

Given a `SafeFrom b q` witness whose root `b` is a **current-epoch** block of
the query store that the query head descends from, together with the cross-store
transport premises listed in the module docstring, every honest vote of a
current-target-epoch slot at or after `slot_at q` carries the query store's
`get_current_target` as its FFG target.

The hypothesis list is deliberately long and explicit: per
`docs/proviso-discharge-map.md` §5.1 the *current-epoch* placement of `b` is
exactly what the live `helper_provisos` sites cannot supply (there the safe
root is one epoch too low), so this lemma makes the residual gap precise
rather than hiding it.  All remaining hypotheses are ordinary derivable store
facts.

* `hqH`, `hqStart` — the query second is in horizon and is the first second of
  its slot (true at every FCR call by
  `Execution.slot_start_eq_succ_of_advance_minimal`);
* `hsafe` — the trajectory invariant at `b`;
* `hqueryParent`, `hqueryHead`, `hbEpoch`, `hqueryHeadWalk`, `hqueryWalk` —
  query-store geometry: parent-slot discipline, the head descends from `b`, `b`
  is current-epoch, and both boundary walks are known;
* `hvoterHeadSlot`, `hvoterParent`, `hvoterHeadWalk`, `hvoterWalk`, `hagree` —
  the same data in each honest voter's store at its cast second, plus block
  agreement with the query store on commonly known roots;
* `hps`, `hdiv`, `hgen` — the `ext.process_slots` clock law and the whole-second
  slot / genesis-ordered anchor pair from `Clock.lean`. -/
theorem honestVotesSupportTarget_of_engineInv_currentEpochCandidate
    (hhb : HonestBehavior cfg ext E)
    (hps : ∀ (st : BeaconState Root) (t : Slot), st.slot < t →
      (ext.process_slots st t).slot = t)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {query : FastConfirmationStore Root} {b : Root} {q : ℕ} {cap : Slot}
    (hqH : E.WithinHorizon cfg q)
    (hqStart : E.slot_start cfg (E.slot_at cfg q) = q)
    (heng : EngineInv cfg ext E b q cap)
    (hcap : compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg query.store + 1) ≤ cap)
    (hqueryParent : ParentSlotLt query.store)
    (hqueryHead : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root b) = true)
    (hbEpoch : get_block_epoch cfg query.store b =
      get_current_store_epoch cfg query.store)
    (hqueryHeadWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (hqueryWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store))
      b)
    (hvoterHeadSlot : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ((E.store cfg ext v k).block_states
        (get_head cfg (E.store cfg ext v k)).root).slot ≤ E.slot_at cfg k)
    (hvoterParent : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ParentSlotLt (E.store cfg ext v k))
    (hvoterHeadWalk : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext v k)
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store))
        (get_head cfg (E.store cfg ext v k)).root)
    (hvoterWalk : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext v k)
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store))
        b)
    (hagree : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ∀ r : Root, r ∈ (E.store cfg ext v k).block_roots →
        r ∈ query.store.block_roots →
        (E.store cfg ext v k).blocks r = query.store.blocks r) :
    HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q := by
  have hbMem : b ∈ query.store.block_roots := hqueryWalk.root_mem
  have hT : get_current_target cfg query.store =
      get_checkpoint_for_block cfg query.store b
        (get_block_epoch cfg query.store b) :=
    current_target_eq_checkpoint_of_current_epoch_ancestor cfg hqueryParent
      hqueryHead hbEpoch hqueryHeadWalk
  refine ⟨hqH, ?_⟩
  intro v hv s hsH hsEpoch hqs k a hvote
  -- the vote slot's epoch is the query store's current epoch
  have hepochT : (get_current_target cfg query.store).epoch =
      get_current_store_epoch cfg query.store := by
    rw [hT, hbEpoch]
    rfl
  have heq : compute_epoch_at_slot cfg s =
      get_current_store_epoch cfg query.store := by
    rw [hsEpoch, hepochT]
  -- the cast second
  have hs0 : E.slot_at cfg 0 ≤ s := (E.slot_at_mono cfg (Nat.zero_le q)).trans hqs
  have hqk : q ≤ k :=
    E.honest_vote_castSecond_ge_of_slotStart cfg ext hhb hdiv hgen hv hqStart
      hsH hs0 hqs hvote
  obtain ⟨_, hkH, hkSlot, _⟩ :=
    E.honest_vote_eq_honestAttestation cfg ext hhb hv hsH hs0 hvote
  have hvParent := hvoterParent v hv k hqk hkH
  have hvHeadWalk := hvoterHeadWalk v hv k hqk hkH
  have hvWalk := hvoterWalk v hv k hqk hkH
  have hvAgree := hagree v hv k hqk hkH
  -- `b` has the vote slot's epoch in the voter's own store
  have hblockEq : (E.store cfg ext v k).blocks b = query.store.blocks b :=
    hvAgree b hvWalk.root_mem hbMem
  have hbEpochVoter : get_block_epoch cfg (E.store cfg ext v k) b =
      compute_epoch_at_slot cfg s := by
    simp only [get_block_epoch, hblockEq]
    rw [heq, ← hbEpoch]
    rfl
  -- the voter's target is `b`'s boundary block in the voter's store
  -- the vote slot is in the query store's current epoch, hence strictly below
  -- that epoch's successor boundary, hence inside the cap
  have hslt : s < compute_start_slot_at_epoch cfg
      (get_current_store_epoch cfg query.store + 1) := by
    rw [← heq]
    simp only [compute_start_slot_at_epoch, compute_epoch_at_slot]
    simpa only [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (b := cfg.slots_per_epoch) s
        cfg.slots_per_epoch_pos)
  have hscap : s ≤ cap := Nat.le_of_lt (Nat.lt_of_lt_of_le hslt hcap)
  have hvoteTarget := E.honestVoteTarget_eq_checkpoint_of_head_ancestor_capped
    cfg ext hhb hps hdiv hgen hv heng hscap hqStart hsH hs0 hqs hvote
    (hkSlot ▸ hvoterHeadSlot v hv k hqk hkH)
    hvParent hbEpochVoter (by rw [heq]; exact hvHeadWalk)
  -- and the two stores compute the same boundary block from `b`
  have hpaired := get_checkpoint_block_eq_of_paired_walks cfg (source := E.store cfg ext v k)
    (target := query.store) hvParent hqueryParent hvAgree hvWalk hqueryWalk
  rw [hvoteTarget, heq, hpaired, hT, hbEpoch]
  rfl

/-- The uncapped form, unchanged: `SafeFrom` weakens to `EngineInv` at the
successor epoch boundary, where the cap hypothesis is reflexive.

Every existing consumer uses this shape; the capped twin above exists only so
that the lazy crossing-call reconstruction
(`docs/crossing-call-support-residue.md` §2.3) can feed it the *capped* safety
its endpoint induction already carries. -/
theorem honestVotesSupportTarget_of_safeFrom_currentEpochCandidate
    (hhb : HonestBehavior cfg ext E)
    (hps : ∀ (st : BeaconState Root) (t : Slot), st.slot < t →
      (ext.process_slots st t).slot = t)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgen : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {query : FastConfirmationStore Root} {b : Root} {q : ℕ}
    (hqH : E.WithinHorizon cfg q)
    (hqStart : E.slot_start cfg (E.slot_at cfg q) = q)
    (hsafe : E.SafeFrom cfg ext b q)
    (hqueryParent : ParentSlotLt query.store)
    (hqueryHead : is_ancestor query.store (get_head cfg query.store)
      (get_node_for_root b) = true)
    (hbEpoch : get_block_epoch cfg query.store b =
      get_current_store_epoch cfg query.store)
    (hqueryHeadWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store))
      (get_head cfg query.store).root)
    (hqueryWalk : WalkKnown query.store
      (compute_start_slot_at_epoch cfg (get_current_store_epoch cfg query.store))
      b)
    (hvoterHeadSlot : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ((E.store cfg ext v k).block_states
        (get_head cfg (E.store cfg ext v k)).root).slot ≤ E.slot_at cfg k)
    (hvoterParent : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ParentSlotLt (E.store cfg ext v k))
    (hvoterHeadWalk : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext v k)
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store))
        (get_head cfg (E.store cfg ext v k)).root)
    (hvoterWalk : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      WalkKnown (E.store cfg ext v k)
        (compute_start_slot_at_epoch cfg
          (get_current_store_epoch cfg query.store))
        b)
    (hagree : ∀ v ∈ E.honest, ∀ k : ℕ, q ≤ k → E.WithinHorizon cfg k →
      ∀ r : Root, r ∈ (E.store cfg ext v k).block_roots →
        r ∈ query.store.block_roots →
        (E.store cfg ext v k).blocks r = query.store.blocks r) :
    HonestVotesSupportTarget cfg E (get_current_target cfg query.store) q :=
  E.honestVotesSupportTarget_of_engineInv_currentEpochCandidate cfg ext hhb
    hps hdiv hgen hqH hqStart (E.engineInv_of_safeFrom cfg ext hsafe)
    (le_refl _) hqueryParent hqueryHead hbEpoch hqueryHeadWalk hqueryWalk
    hvoterHeadSlot hvoterParent hvoterHeadWalk hvoterWalk hagree

end Execution

end FastConfirmation.Spec
