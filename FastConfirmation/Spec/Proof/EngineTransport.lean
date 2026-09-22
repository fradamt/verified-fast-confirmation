module
public import FastConfirmation.Spec.Proof.EngineInduction
public import FastConfirmation.Spec.Proof.BlockAgreement

@[expose] public section

/-!
# Spec / Proof / EngineTransport (package facts at later stores)

This module carries the confirmation-time support package `ConfirmedSupport`
(`EngineInduction.lean`)
forward to a *later* honest store `(w, m)` in slot `k ≥ s`, phrasing the facts in
the **exact hypothesis shapes** `EngineWindows.fork_majority_of_windows` and
`EngineSupport.recorded_support_lower_HS` consume.

`fork_majority_of_windows` reads its recorded-support lower bound `hscore` against
the justified-checkpoint balance source and needs, for the fork child `c` on `b`'s
chain, that both the frozen old honest supporter set `HS₀` and the new-window
honest committee sit in `AttSupporters cfg store_wm (get_node_for_root c) bs`. Two
facts per supporter feed that membership (`EngineSupport.mem_AttSupporters_honest`):

* **active + unslashed** in the balance source `bs` (registry-constant), and
* a **recorded latest message supporting `c`** at `(w, m)`.

This module proves the first component — active and unslashed membership via
`committee_members_active` + `registry_activity_constant`, unslashed via
`honest_unslashed`" — from bare **honest + committee membership**, uniformly for
`HS₀` and the new-window voters. An honest committee member of any slot `t` is
active in the ground registry at that slot's epoch (`committee_members_active`),
hence at every epoch (`registry_activity_constant`), hence in the active list of
any registry-constant balance source (`mem_active_of_active`, using that the
`Inhabited` `Validator` default is inactive so activity forces an in-range index);
its slashed flag is `false` on the ground registry (`honest_unslashed`). These
compose (`honest_active_unslashed`) into the active/unslashed inputs of
`mem_AttSupporters_honest`.

The two assembly lemmas package the result:

* **`mem_AttSupporters_of_honest_committee`** — honest + committee membership + a
  recorded `c`-supporting message ⟹ `AttSupporters` membership at `(w, m)`.
* **`recorded_support_lower_of_honest_committee`** — a validator set all of whose
  members carry (honest + committee membership + recorded `c`-support) lower-bounds
  `c`'s attestation score at `(w, m)` by its ground-truth weight: the ledger's
  `hscore` producer, in `recorded_support_lower_HS`'s shape.

The genuinely-hard input left as a per-member hypothesis is the **recorded
`c`-supporting message** itself — the epoch-cased root identification
(`vote_ubiquity` gives only the epoch bound; the displacement case needs the
engine IH and a slot-confinement of the displacing vote).
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## The `Inhabited` validator is inactive, and active-list membership -/

/-- The `Inhabited` `Validator` default is never active: its `exit_epoch` is `0`,
so `epoch < exit_epoch` is unsatisfiable. Used to turn "active at `e`" into an
in-range index (the active list filters `List.range validators.length`). -/
private theorem is_active_validator_default_false (e : Epoch) :
    is_active_validator (default : Validator) e = false := by
  simp only [is_active_validator, decide_eq_false_iff_not, not_and, not_lt]
  intro _
  exact Nat.zero_le _

omit [LinearOrder Root] [Inhabited Root] in
/-- Membership in the active-validator list from a positive activity check: the
index is in range (activity of the out-of-range `default` is false) and passes
the list's activity filter. -/
theorem mem_active_of_active {bs : BeaconState Root} {i : ValidatorIndex} {e : Epoch}
    (hact : is_active_validator (bs.validators.getD i default) e = true) :
    i ∈ get_active_validator_indices bs e := by
  simp only [get_active_validator_indices, List.mem_filter, List.mem_range]
  refine ⟨?_, hact⟩
  by_contra hge
  rw [not_lt] at hge
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none,
    is_active_validator_default_false] at hact
  exact absurd hact (by decide)

/-! ## Active / unslashed from honest + committee membership

The uniform active/unslashed derivation for both `HS₀` and the new-window voters.
An honest committee member of slot `t` is active in the ground registry at that
slot's epoch (`ExternalsCoherence.committee_members_active`), hence at every epoch
(`StaticValidatorSet.registry_activity_constant`), hence in the active list of any
registry-constant balance source (`mem_active_of_active`). Its slashed flag is
`false` on the ground registry (`HonestBehavior.honest_unslashed`). These are the
active/unslashed inputs `EngineSupport.mem_AttSupporters_honest` consumes. -/

/-- **Active + unslashed from honest + committee membership.** For an honest
validator `i` assigned to some slot `t` and a registry-constant balance source
`bs`, `i` is active in `bs` at `bs`'s current epoch and unslashed in `bs`. -/
theorem honest_active_unslashed {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E) {bs : BeaconState Root} (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    {i : ValidatorIndex} {t : Slot} (hi : i ∈ E.honest)
    (htH : E.SlotWithinHorizon cfg t) (hcomm : i ∈ E.committee t) :
    i ∈ get_active_validator_indices bs (get_current_epoch cfg bs) ∧
      (bs.validators.getD i default).slashed = false := by
  refine ⟨mem_active_of_active ?_, by rw [hval]; exact hhb.honest_unslashed i hi⟩
  have hactt : is_active_validator (E.registry.getD i default)
      (compute_epoch_at_slot cfg t) = true := hec.committee_members_active i t htH hcomm
  rw [hval]
  exact (hsv.registry_activity_constant i (compute_epoch_at_slot cfg t)
    (get_current_epoch cfg bs) htH.2 hbsH).symm.trans hactt

/-! ## Cross-store ancestor transport

The package's `is_ancestor` fact lives at the confirming store `(v₀, n₀)`; the
supporter-membership goal is at a *different* node/second `(w, m)`. `get_ancestor`
reads only `blocks` along the parent walk, so on the walk known at `(v₀, n₀)` the
two stores compute the same ancestor once they agree on `(v₀, n₀)`'s blocks
(`BlockAgreement.is_ancestor_congr`). Provenance pins the recorded block at every
commonly-known root (`WellFormedExecution.blocks_agree`), so the agreement follows
from `(v₀, n₀)`'s roots being known at `(w, m)` — the cross-node block-relay
containment `hsub`, taken as a hypothesis (`Synchrony.block_relay`'s output, the
usual domain-condition shape). This carries the package's `⪰ b` fact to `(w, m)`. -/

/-- **Cross-store `is_ancestor` transport.** An `is_ancestor r ⪰ b` fact on a walk
known at `(v, n)`, with `r`/`b` known at `(v, n)` and all of `(v, n)`'s roots known
at `(w, m)` (`hsub`), holds identically at `(w, m)`. Cross-node analogue of
`Execution.is_ancestor_mono`; the block agreement is `WellFormedExecution.blocks_agree`
between the two provenance-respecting stores. -/
theorem is_ancestor_transport {E : Execution Root} (hwf : WellFormedExecution E)
    {v w : ValidatorIndex} {n m : ℕ} {r b : Root}
    (hsub : (E.store cfg ext v n).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hr : r ∈ (E.store cfg ext v n).block_roots)
    (hb : b ∈ (E.store cfg ext v n).block_roots)
    (hw : WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot r)
    (hanc : is_ancestor (E.store cfg ext v n)
      (ForkChoiceNode.mk r) (ForkChoiceNode.mk b) = true) :
    is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk r) (ForkChoiceNode.mk b) = true := by
  have hagree : ∀ x ∈ (E.store cfg ext v n).block_roots,
      (E.store cfg ext v n).blocks x = (E.store cfg ext w m).blocks x := fun x hx =>
    hwf.blocks_agree (E.blockProvenance cfg ext v n) (E.blockProvenance cfg ext w m) hx (hsub hx)
  rwa [← is_ancestor_congr hagree hr hb hw]

/-- **The recorded message supports `c` at `(w, m)`.** Composing the cross-store
transport with `EngineSupport.supports_of_ge_b`: if the recorded message's root
descends from `b` at the confirming store `(v, n)` (the package fact) and `b`
chain-descends to the fork child `c` at `(w, m)`, then the message supports
`get_node_for_root c` at `(w, m)`. The `(v, n)`-side inputs are the package's
`⪰ b` witness and its walk; the `(w, m)`-side inputs are `parent_slot_lt`
(`hwf_wm`) and the `b ≼ c` chain walks — all the usual domain-condition shapes.
The single fact this does *not* discharge is the epoch-cased identification of
the recorded `lm.root` with the package vote block. -/
theorem recorded_supports_c {E : Execution Root} (hwf : WellFormedExecution E)
    {v w : ValidatorIndex} {n m : ℕ} {b c : Root} {lm : LatestMessage Root}
    (hsub : (E.store cfg ext v n).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hr_vn : lm.root ∈ (E.store cfg ext v n).block_roots)
    (hb_vn : b ∈ (E.store cfg ext v n).block_roots)
    (hw_vn : WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks b).slot lm.root)
    (hge_vn : is_ancestor (E.store cfg ext v n)
      (ForkChoiceNode.mk lm.root) (ForkChoiceNode.mk b) = true)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwa_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root)
    (hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true) :
    is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true := by
  have hge_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk lm.root) (ForkChoiceNode.mk b) = true :=
    is_ancestor_transport cfg ext hwf hsub hr_vn hb_vn hw_vn hge_vn
  exact supports_of_ge_b hwf_pl hwa_wm hwb_wm hge_wm hbc_wm

/-! ## Supporter membership at the later store from honest + committee membership

Folding the active/unslashed derivation into `EngineSupport.mem_AttSupporters_honest`:
at the later honest store `(w, m)`, an honest committee member whose recorded latest
message supports `node` sits in `AttSupporters`. This is the per-member membership
`fork_majority_of_windows` needs for both `HS₀` and the new-window voters, once the
recorded `node`-supporting message is supplied. -/

/-- **Supporter membership from honest + committee membership.** At an honest store
`(w, m)`, an honest validator `i` assigned to some slot `t` whose recorded latest
message supports `node` sits in `AttSupporters cfg store_wm node bs` for any
registry-constant balance source `bs`. Active/unslashed are discharged internally
(`honest_active_unslashed`); non-equivocation by `honest_not_equivocating` inside
`mem_AttSupporters_honest`. -/
theorem mem_AttSupporters_of_honest_committee {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {bs : BeaconState Root} {node : ForkChoiceNode Root}
    {i : ValidatorIndex} {t : Slot} {lm : LatestMessage Root}
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (hi : i ∈ E.honest) (htH : E.SlotWithinHorizon cfg t)
    (hcomm : i ∈ E.committee t)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hsupp : is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) node = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    i ∈ AttSupporters cfg (E.store cfg ext w m) node bs := by
  obtain ⟨hact, huns⟩ :=
    honest_active_unslashed cfg ext hhb hec hsv hval hbsH hi htH hcomm
  exact mem_AttSupporters_honest cfg ext (hw := hw) (hmH := hmH) hhb hec hgen hi hact huns hlm hsupp

/-! ## The recorded-support lower bound: the ledger's `hscore` producer

`EngineSupport.recorded_support_lower_HS` lower-bounds `node`'s attestation score
by the weight of any validator set all of whose members are honest, active,
unslashed, and record a `node`-supporting message. Folding in
`honest_active_unslashed`, the active/unslashed clauses collapse to bare committee
membership: an honest set whose members are each committee-assigned and record a
`node`-supporting message at `(w, m)` lower-bounds the score. Instantiated with
`node = get_node_for_root c` and `HS = HS₀ ∪ NewVoters` this is the ledger's
`hscore` input of `fork_majority_of_windows` (the two sets' weights sum to
`E.weight HS` when disjoint by slot range; provenance provides the required
disjointness. -/

/-- **Recorded-support lower bound from honest + committee membership.** For a
validator set `HS` all of whose members are honest, assigned to some slot, and
record a `node`-supporting latest message at `(w, m)`, the ground-truth weight of
`HS` is at most `node`'s attestation score at `(w, m)` against any registry-constant
balance source `bs`. -/
theorem recorded_support_lower_of_honest_committee {E : Execution Root}
    (hhb : HonestBehavior cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {bs : BeaconState Root} {node : ForkChoiceNode Root}
    (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (HS : Finset ValidatorIndex)
    (hHS : ∀ i ∈ HS, i ∈ E.honest ∧
      (∃ t : Slot, E.SlotWithinHorizon cfg t ∧ i ∈ E.committee t) ∧
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        is_ancestor (E.store cfg ext w m)
          (get_supported_node (E.store cfg ext w m) lm) node = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    E.weight HS ≤ get_attestation_score cfg (E.store cfg ext w m) node bs := by
  refine recorded_support_lower_HS cfg ext (hw := hw) (hmH := hmH) hhb hec hgen hval HS (fun i hi => ?_)
  obtain ⟨hih, ⟨t, htH, hcomm⟩, lm, hlm, hsupp⟩ := hHS i hi
  obtain ⟨hact, huns⟩ :=
    honest_active_unslashed cfg ext hhb hec hsv hval hbsH hih htH hcomm
  exact ⟨hih, hact, huns, lm, hlm, hsupp⟩

/-! ## `EngineTransport`: the epoch-cased recorded-support closer

The recorded latest message of a package supporter *still supports the fork child `c`*
at the later store `(w, m)`. This follows using `LatestMessageProvenance`
carries `a.data.slot + 1 ≤ sl` (the `validate_on_attestation` gate captured at
application). For a message recorded at second `m` in slot `k = slot_at m`, the
setting attestation's slot is `< k`.

The recorded message `lm` for a supporter `i` sits, by ubiquity, at epoch
`≥ epochOf t` (`t` its newest pre-`s` vote slot). Two cases:

* **equality** (`lm.epoch = epochOf t`): the recorded root is *exactly* `i`'s
  pre-`s` vote block (`Execution.latest_message_root`), which descends from `b`
  at the confirming store (the package fact); `recorded_supports_c` transports
  that to `c`-support at `(w, m)`.
* **displacement** (`lm.epoch > epochOf t`): the setting attestation's slot `sl`
  has `epochOf sl = lm.epoch > epochOf t`, so `sl > t`; the "no vote in `(t, s)`"
  clause of the package forbids `t < sl < s`, so `sl ≥ s`; and `sl < k` from the
  provenance gate — hence `sl ∈ [s, k)` and the engine IH (`hIH`, `EngineInduction` shape)
  puts `i`'s slot-`sl` vote block `⪰ b` at `(w, m)` directly, which
  `supports_of_ge_b` carries to `c`-support. The setting attestation is pinned to
  `i`'s own vote by `SchedLMProv` + `no_forgery`; its slot to the provenance slot
  by `committee_assignment_unique` (both `i`-assigned, same epoch). -/

/-- Epoch monotonicity of `compute_epoch_at_slot` (it is `· / slots_per_epoch`). -/
private theorem compute_epoch_at_slot_mono {x y : Slot} (h : x ≤ y) :
    compute_epoch_at_slot cfg x ≤ compute_epoch_at_slot cfg y := by
  simp only [compute_epoch_at_slot]; exact Nat.div_le_div_right h

/-- **The recorded message of a package supporter supports `c` at `(w, m)`.**
For honest `i` whose newest pre-`s` vote (slot `t < s`, block `a`, no vote in
`(t, s)`) descends from `b` at the confirming store `(v₀, n₀)`, and a recorded
latest message `lm` at `(w, m)` (slot `k = slot_at m`) with `epochOf t ≤ lm.epoch`
(ubiquity), the message supports the fork child `c` on `b`'s chain — under the
engine IH `hIH` (every honest `[s, k)`-vote block `⪰ b` at `(w, m)`) and the
cross-store / walk domain conditions. Closes `EngineTransport`'s blocker 1. -/
theorem recorded_supports_c_of_IH {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {v₀ w : ValidatorIndex} {n₀ m : ℕ} {b c : Root} {i : ValidatorIndex}
    {t : Slot} {kk : ℕ} {a : Attestation Root} {s k : Slot} {lm : LatestMessage Root}
    (hi : i ∈ E.honest) (_hts : t < s)
    (hvt : E.vote i t = some (kk, a))
    (hmid : ∀ t' : Slot, t < t' → t' < s → E.vote i t' = none)
    (hgvn : is_ancestor (E.store cfg ext v₀ n₀)
      (get_node_for_root a.data.beacon_block_root) (get_node_for_root b) = true)
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hepge : compute_epoch_at_slot cfg t ≤ lm.epoch)
    (hslot_m : E.slot_at cfg m = k)
    (hIH : ∀ j ∈ E.honest, ∀ t' : Slot, s ≤ t' → t' < k →
      ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hsub : (E.store cfg ext v₀ n₀).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hbbr_vn : a.data.beacon_block_root ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hb_vn : b ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hwa_vn : WalkKnown (E.store cfg ext v₀ n₀)
      ((E.store cfg ext v₀ n₀).blocks b).slot a.data.beacon_block_root)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwa_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root)
    (hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true := by
  rcases eq_or_lt_of_le hepge with heq | hlt
  · -- equality case: the recorded root is `i`'s pre-`s` vote block
    have hroot_eq : lm.root = a.data.beacon_block_root :=
      E.latest_message_root cfg ext hhb hec hgen hi hvt hlm heq
    exact recorded_supports_c cfg ext hwf hsub
      (by rw [hroot_eq]; exact hbbr_vn) hb_vn
      (by rw [hroot_eq]; exact hwa_vn)
      (by rw [hroot_eq]; exact hgvn)
      hwf_pl hwa_wm hwb_wm hbc_wm
  · -- displacement case: a later `[s, k)`-vote installed `lm`; the IH covers it
    obtain ⟨a', u, tt, ifb, hsched, hvin, hbbr', hep'⟩ :=
      E.schedLMProv cfg ext hgen w m i lm hlm
    obtain ⟨m1, av, hvote_sl, hdata'⟩ := hhb.no_forgery u tt a' ifb hsched i hi hvin
    have hcomm_sl : i ∈ E.committee a'.data.slot :=
      hhb.votes_assigned i hi a'.data.slot (by rw [hvote_sl]; exact Option.some_ne_none _)
    obtain ⟨a2, -, -, -, hep2, hbound2, hcomm2, -, -⟩ :=
      E.latestMessageProvenance cfg ext hwf hec hgen w m hw hmH i lm hlm
    have hslot_eq : a'.data.slot = a2.data.slot :=
      hec.committee_assignment_unique i a'.data.slot a2.data.slot hcomm_sl hcomm2
        (by rw [hep', hep2])
    have hsl_lt_k : a'.data.slot < k := by
      rw [hslot_eq, ← hslot_m]; exact Nat.lt_of_succ_le hbound2
    have hsl_gt_t : t < a'.data.slot := by
      by_contra hle
      have hmono : compute_epoch_at_slot cfg a'.data.slot ≤ compute_epoch_at_slot cfg t :=
        compute_epoch_at_slot_mono cfg (not_lt.mp hle)
      rw [hep'] at hmono
      exact absurd hlt (not_lt.mpr hmono)
    have hsl_ge_s : s ≤ a'.data.slot := by
      by_contra hlt'
      have hnone := hmid a'.data.slot hsl_gt_t (not_le.mp hlt')
      rw [hvote_sl] at hnone
      exact absurd hnone (Option.some_ne_none _)
    have hge_wm : is_ancestor (E.store cfg ext w m)
        (get_node_for_root av.data.beacon_block_root) (get_node_for_root b) = true :=
      hIH i hi a'.data.slot hsl_ge_s hsl_lt_k m1 av hvote_sl
    have hbbr_eq : av.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr'
    rw [hbbr_eq] at hge_wm
    exact supports_of_ge_b hwf_pl hwa_wm hwb_wm hge_wm hbc_wm

/-! ## `EngineTransport` result 1: `HS₀` supports the fork child at `(w, m)`

Instantiating `recorded_supports_c_of_IH` per member of the confirmation-time
supporter set `HS₀` (its per-member vote facts come from the `ConfirmedSupport`
package), then folding in honest + committee membership
(`mem_AttSupporters_of_honest_committee`), gives that every `HS₀` member sits in
`AttSupporters cfg store_wm (get_node_for_root c) bs` at the later honest store.

The ubiquity input `hubiq` (a recorded message with epoch `≥ epochOf t`) is
`Delivery.vote_ubiquity`'s output shape, and the walk/known-root domain
conditions (`hdom_vn`, `hwalk_wm`, `hwb_wm`, `hwf_pl`) are the usual
`WalkKnown`-family premises; the engine IH `hIH` is the `EngineInduction` shape. -/

/-- **`HS₀` supporters at `(w, m)`.** Every member of the frozen honest supporter
set `HS₀` records, at the later honest store `(w, m in slot k)`, a latest message
supporting the fork child `c` on `b`'s chain, and hence sits in `AttSupporters`.
The recorded-support half is `recorded_supports_c_of_IH` (epoch-cased, closing
`EngineTransport`'s blocker 1); active/unslashed/non-equivocation are internal to
`mem_AttSupporters_of_honest_committee`. -/
theorem HS0_in_AttSupporters {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {b : Root} {s : Slot} {v₀ : ValidatorIndex} {n₀ : ℕ}
    {HS₀ : Finset ValidatorIndex} {Wold D discount boost : ℕ}
    (hpkg : ConfirmedSupport cfg ext E b s v₀ n₀ HS₀ Wold D discount boost)
    {w : ValidatorIndex} {m : ℕ} {k : Slot} {c : Root} {bs : BeaconState Root}
    (hsH : E.SlotWithinHorizon cfg s)
    (hslot_m : E.slot_at cfg m = k) (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (hIH : ∀ j ∈ E.honest, ∀ t' : Slot, s ≤ t' → t' < k →
      ∀ jj (a' : Attestation Root), E.vote j t' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hubiq : ∀ i ∈ HS₀, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) →
      ∃ lm, (E.store cfg ext w m).latest_messages i = some lm ∧
        compute_epoch_at_slot cfg t ≤ lm.epoch)
    (hsub : (E.store cfg ext v₀ n₀).block_roots ⊆ (E.store cfg ext w m).block_roots)
    (hb_vn : b ∈ (E.store cfg ext v₀ n₀).block_roots)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b)
    (hdom_vn : ∀ i ∈ HS₀, ∀ (t : Slot) (kk : ℕ) (a : Attestation Root),
      E.vote i t = some (kk, a) →
      a.data.beacon_block_root ∈ (E.store cfg ext v₀ n₀).block_roots ∧
      WalkKnown (E.store cfg ext v₀ n₀)
        ((E.store cfg ext v₀ n₀).blocks b).slot a.data.beacon_block_root)
    (hwalk_wm : ∀ i ∈ HS₀, ∀ lm, (E.store cfg ext w m).latest_messages i = some lm →
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    ∀ i ∈ HS₀, i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bs := by
  intro i hi
  obtain ⟨t, kk, a, hts, hvt, hmid, hgvn⟩ := hpkg.votes i hi
  have htH : E.SlotWithinHorizon cfg t :=
    ⟨(le_of_lt hts).trans hsH.1,
      lt_of_le_of_lt (Nat.div_le_div_right (le_of_lt hts)) hsH.2⟩
  have hih := hpkg.honest i hi
  obtain ⟨lm, hlm, hepge⟩ := hubiq i hi t kk a hvt
  obtain ⟨hbbr_vn, hwa_vn⟩ := hdom_vn i hi t kk a hvt
  have hcomm : i ∈ E.committee t :=
    hhb.votes_assigned i hih t (by rw [hvt]; exact Option.some_ne_none _)
  have hsupp : is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true :=
    recorded_supports_c_of_IH cfg ext (hw := hw) (hmH := hmH) hwf hhb hec hgen hih hts hvt hmid hgvn hlm hepge
      hslot_m hIH hsub hbbr_vn hb_vn hwa_vn hwf_pl (hwalk_wm i hi lm hlm) hwb_wm hbc_wm
  exact mem_AttSupporters_of_honest_committee cfg ext (hw := hw) (hmH := hmH) hhb hec hsv hgen hval hbsH
    hih htH hcomm hlm hsupp

/-! ## `EngineTransport` result 2: the new-window honest voters support the fork child

A *new-window voter* is an honest committee member of a slot `t'` with `s ≤ t'`.
Its recorded message at `(w, m)` cannot come from a pre-`s` seat: were the setting
slot `sl < s`, then `sl < s ≤ t'` forces `epochOf sl ≤ epochOf t'`, while ubiquity
forces `epochOf sl = lm.epoch ≥ epochOf t'`; the two pin `epochOf sl = epochOf t'`,
so `committee_assignment_unique` (both `i`-assigned) gives `sl = t'`, contradicting
`sl < s ≤ t'`. Hence `sl ≥ s`, and with `sl < k` from the provenance gate the
setting slot lands in `[s, k)` where the engine IH `hIH` puts `i`'s vote block
`⪰ b` at `(w, m)` — no equality/displacement split needed. -/

/-- **A new-window voter's recorded message supports `c` at `(w, m)`.** For honest
`i` assigned to a slot `t'` with `s ≤ t'`, and a recorded latest message `lm` at
`(w, m in slot k)` with `epochOf t' ≤ lm.epoch` (ubiquity), the message supports
the fork child `c` on `b`'s chain, under the engine IH `hIH` and the walk domain
conditions. The setting slot is forced into `[s, k)` by the within-epoch seat
uniqueness. -/
theorem newvoter_recorded_supports_c_of_IH {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {w : ValidatorIndex} {m : ℕ} {b c : Root} {i : ValidatorIndex}
    {t' : Slot} {s k : Slot} {lm : LatestMessage Root}
    (hi : i ∈ E.honest) (hcomm_t' : i ∈ E.committee t') (hst' : s ≤ t')
    (hlm : (E.store cfg ext w m).latest_messages i = some lm)
    (hepge : compute_epoch_at_slot cfg t' ≤ lm.epoch)
    (hslot_m : E.slot_at cfg m = k)
    (hIH : ∀ j ∈ E.honest, ∀ t'' : Slot, s ≤ t'' → t'' < k →
      ∀ jj (a' : Attestation Root), E.vote j t'' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hwa_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root)
    (hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_supported_node (E.store cfg ext w m) lm) (get_node_for_root c) = true := by
  obtain ⟨a', u, tt, ifb, hsched, hvin, hbbr', hep'⟩ :=
    E.schedLMProv cfg ext hgen w m i lm hlm
  obtain ⟨m1, av, hvote_sl, hdata'⟩ := hhb.no_forgery u tt a' ifb hsched i hi hvin
  have hcomm_sl : i ∈ E.committee a'.data.slot :=
    hhb.votes_assigned i hi a'.data.slot (by rw [hvote_sl]; exact Option.some_ne_none _)
  obtain ⟨a2, -, -, -, hep2, hbound2, hcomm2, -, -⟩ :=
    E.latestMessageProvenance cfg ext hwf hec hgen w m hw hmH i lm hlm
  have hslot_eq : a'.data.slot = a2.data.slot :=
    hec.committee_assignment_unique i a'.data.slot a2.data.slot hcomm_sl hcomm2
      (by rw [hep', hep2])
  have hsl_lt_k : a'.data.slot < k := by
    rw [hslot_eq, ← hslot_m]; exact Nat.lt_of_succ_le hbound2
  have hsl_ge_s : s ≤ a'.data.slot := by
    by_contra hlt'
    have hslt : a'.data.slot < s := not_le.mp hlt'
    have hmono : compute_epoch_at_slot cfg a'.data.slot ≤ compute_epoch_at_slot cfg t' :=
      compute_epoch_at_slot_mono cfg (le_of_lt (lt_of_lt_of_le hslt hst'))
    rw [hep'] at hmono
    have heq_ep : compute_epoch_at_slot cfg a'.data.slot = compute_epoch_at_slot cfg t' := by
      rw [hep']; exact le_antisymm hmono hepge
    have hsl_t' : a'.data.slot = t' :=
      hec.committee_assignment_unique i a'.data.slot t' hcomm_sl hcomm_t' heq_ep
    exact absurd hsl_t' (Nat.ne_of_lt (lt_of_lt_of_le hslt hst'))
  have hge_wm := hIH i hi a'.data.slot hsl_ge_s hsl_lt_k m1 av hvote_sl
  have hbbr_eq : av.data.beacon_block_root = lm.root := by rw [← hdata']; exact hbbr'
  rw [hbbr_eq] at hge_wm
  exact supports_of_ge_b hwf_pl hwa_wm hwb_wm hge_wm hbc_wm

/-- **New-window voters at `(w, m)`.** Every member of a new-window voter set `NV`
(honest committee members of some slot `t' ≥ s`, with a recorded message of epoch
`≥ epochOf t'` by ubiquity) sits in `AttSupporters cfg store_wm (get_node_for_root c)
bs` at the later honest store. The recorded-support half is
`newvoter_recorded_supports_c_of_IH`; active/unslashed/non-equivocation are internal
to `mem_AttSupporters_of_honest_committee`. -/
theorem NewVoters_in_AttSupporters {E : Execution Root}
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hec : ExternalsCoherence cfg ext E) (hsv : StaticValidatorSet cfg E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk)
    {b : Root} {s : Slot} {w : ValidatorIndex} {m : ℕ} {k : Slot} {c : Root}
    {bs : BeaconState Root} (hslot_m : E.slot_at cfg m = k) (hval : bs.validators = E.registry)
    (hbsH : get_current_epoch cfg bs < E.verification_horizon)
    (hIH : ∀ j ∈ E.honest, ∀ t'' : Slot, s ≤ t'' → t'' < k →
      ∀ jj (a' : Attestation Root), E.vote j t'' = some (jj, a') →
      is_ancestor (E.store cfg ext w m)
        (get_node_for_root a'.data.beacon_block_root) (get_node_for_root b) = true)
    (hwf_pl : ∀ r ∈ (E.store cfg ext w m).block_roots,
      ((E.store cfg ext w m).blocks r).parent_root ∈ (E.store cfg ext w m).block_roots →
        ((E.store cfg ext w m).blocks ((E.store cfg ext w m).blocks r).parent_root).slot <
          ((E.store cfg ext w m).blocks r).slot)
    (hbc_wm : is_ancestor (E.store cfg ext w m)
      (ForkChoiceNode.mk b) (ForkChoiceNode.mk c) = true)
    (hwb_wm : WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot b)
    (NV : Finset ValidatorIndex)
    (hNV : ∀ i ∈ NV, i ∈ E.honest ∧ ∃ (t' : Slot) (lm : LatestMessage Root),
      E.SlotWithinHorizon cfg t' ∧ i ∈ E.committee t' ∧ s ≤ t' ∧
      (E.store cfg ext w m).latest_messages i = some lm ∧
      compute_epoch_at_slot cfg t' ≤ lm.epoch ∧
      WalkKnown (E.store cfg ext w m) ((E.store cfg ext w m).blocks c).slot lm.root)
    (hw : w ∈ E.honest) (hmH : E.WithinHorizon cfg m) :
    ∀ i ∈ NV, i ∈ AttSupporters cfg (E.store cfg ext w m) (get_node_for_root c) bs := by
  intro i hi
  obtain ⟨hih, t', lm, ht'H, hcomm_t', hst', hlm, hepge, hwa_wm⟩ := hNV i hi
  have hsupp := newvoter_recorded_supports_c_of_IH cfg ext (hw := hw) (hmH := hmH) hwf hhb hec hgen hih hcomm_t' hst'
    hlm hepge hslot_m hIH hwf_pl hwa_wm hwb_wm hbc_wm
  exact mem_AttSupporters_of_honest_committee cfg ext (hw := hw) (hmH := hmH) hhb hec hsv hgen hval hbsH
    hih ht'H hcomm_t' hlm hsupp

/-! ## `EngineTransport` result 3: sibling disjointness against a `c`-supporting set

`fork_majority_of_windows` consumes `Disjoint (AttSupporters c').toFinset ·` for
the frozen supporters `HS₀` and the new-window voters. Both sets support the
`b`-side child `c` (results 1/2), while the sibling set supports `c'`; since
`c`, `c'` are distinct children of a common parent, no single recorded message can
support both (`SupportTransport.no_index_supports_both_siblings`), so a common
index is impossible. This closes the `hSib_HS0` and `hSib_new` premises whenever
the second set's members support `c`. The remaining `hHS0_D`, `hHS0_new`, `hD_new`
disjointnesses are pure slot-range/stuck-set bookkeeping and stay as hypotheses in
`fork_majority_of_windows`'s shape (`EngineTransport` scope note). -/

omit [Inhabited Root] in
/-- **Sibling supporters are disjoint from any `c`-supporting set.** With `c`, `c'`
distinct children of a common parent `p`, the supporter list of the sibling `c'`
is disjoint from any `HS` all of whose members record a latest message supporting
`c`: a shared index would carry one recorded message supporting both siblings,
impossible by `no_index_supports_both_siblings`. Discharges `fork_majority_of_windows`'s
`hSib_HS0` (with `HS := HS₀`, `c`-support from `HS0_in_AttSupporters`) and `hSib_new`
(with `HS :=` the new voters, `c`-support from `NewVoters_in_AttSupporters`). -/
theorem sibling_disjoint_of_supports_c {store : Store Root}
    (hwf_pl : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {p c c' : Root} {bs' : BeaconState Root}
    (hc : c ∈ store.block_roots) (hc' : c' ∈ store.block_roots) (hp : p ∈ store.block_roots)
    (hpc : (store.blocks c).parent_root = p) (hpc' : (store.blocks c').parent_root = p)
    (hne : c ≠ c') (HS : Finset ValidatorIndex)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks c).slot lm.root ∧
      WalkKnown store (store.blocks c').slot lm.root)
    (hHS_supp : ∀ i ∈ HS, ∃ lm, store.latest_messages i = some lm ∧
      is_ancestor store (get_supported_node store lm) (get_node_for_root c) = true) :
    Disjoint (AttSupporters cfg store (get_node_for_root c') bs').toFinset HS := by
  rw [Finset.disjoint_left]
  intro i hsib hHS
  rw [List.mem_toFinset] at hsib
  obtain ⟨lm', hlm', -, hsc'⟩ := mem_AttSupporters cfg hsib
  obtain ⟨lm, hlm, hsc⟩ := hHS_supp i hHS
  have hlmeq : lm = lm' := by rw [hlm] at hlm'; exact Option.some.inj hlm'
  rw [hlmeq] at hsc
  obtain ⟨hwc, hwc'⟩ := hwalk i lm' hlm'
  exact no_index_supports_both_siblings hwf_pl hc hc' hp hpc hpc' hne hwc hwc' hsc hsc'

end FastConfirmation.Spec

end
