module
public import FastConfirmation.Spec.Proof.WeakCertificateSupporter
public import FastConfirmation.Spec.Proof.WeakCertificateDissemination
public import FastConfirmation.Spec.Proof.WFTrajectory

@[expose] public section

/-!
# Spec / Proof / WeakCertificateMonotone

Ancestor-monotonicity of broadcast certificates (rule-independent).
`Weak.get_broadcast_certificate_support` (`Spec/Model/WeakSynchrony.lean`) counts
the weight of validators whose latest message's root is an ancestor of
`block_root`. If `anc` is itself a chain-ancestor of `block_root`, every such
vote also witnesses `anc` — ancestry is transitive within a fixed store
(`AncestryRoots.is_ancestor_trans`) — so the support is monotone: it can only
grow when read at an ancestor of the target. The economic budget
(`Weak.compute_adversarial_weight`) does not depend on the target root at all,
so a certificate on `block_root` transfers unchanged to a certificate on `anc`.

Composed with the already-proved `Execution.certificate_dissemination`
(`WeakCertificateDissemination.lean`, Obligation 2), a certificate observed on
`block_root` disseminates not just `block_root` but every known chain-ancestor
of it to every honest validator, over the same span.

## What is delivered

* `Weak.broadcast_certificate_support_mono_ancestor` — the support-monotonicity
  inequality, via `Finset.sum_le_sum_of_subset_of_nonneg` over
  `Weak.mem_broadcast_certificate_support_set`'s membership characterization.
* `Weak.has_broadcast_certificate_ancestor` — a certificate on `block_root`
  transfers to a certificate on `anc` (same span, same budget, support only
  grows).
* `Weak.certificate_chain_dissemination` — composed with
  `Execution.certificate_dissemination` applied directly at `anc`: a
  certificate on `block_root`, plus `anc`'s ancestry and knownness at the
  observer, disseminates `anc` to every honest validator from `end_slot + 1`
  on.

## Side conditions

`is_ancestor_trans` needs the walk from each counted vote's root, and from
`block_root` itself, down to `anc`'s slot to stay inside the store's known
blocks (`WalkKnown`), plus the store's own parent-slot-decrease discipline
(`ParentSlotLt`, exactly `WellFormedStore.parent_slot_lt`'s shape). The first
two lemmas take these as explicit hypotheses (bookkeeping, discharged at call
sites the way `Proof/SupportTransport.lean`'s analogous `hwalk` premise is).
`Weak.certificate_chain_dissemination` derives `ParentSlotLt` from
`WellFormedExecution` (`Execution.store_parentSlotLt`, as in
`WeakAncestryTransport.lean`) but still takes the two `WalkKnown` witnesses as
hypotheses: producing them from first principles would require reopening
`certificate_honest_supporter`'s internals to name the counted voter's vote
root, exactly the harder route this module avoids.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-! ## Support monotonicity -/

/-- **Broadcast-certificate support is monotone along ancestry.** If `anc` is a
chain-ancestor of `block_root` (`hanc`), every vote counted toward
`block_root`'s support is also counted toward `anc`'s: its root is an ancestor
of `block_root` (membership unpacks this via
`Weak.mem_broadcast_certificate_support_set`), and `is_ancestor_trans`
composes that with `hanc` to land it as an ancestor of `anc` too — the
`WalkKnown` witnesses `hwb`/`hwalk` pin the walks `is_ancestor_trans` needs,
down to `anc`'s slot, from `block_root` and from each counted vote's root
respectively. The committee/eligibility filters and the summed balances are
untouched, so `Finset.sum_le_sum_of_subset_of_nonneg` over the resulting
subset inequality gives the claim. -/
theorem Weak.broadcast_certificate_support_mono_ancestor {store : Store Root}
    (hwf : ParentSlotLt store)
    {block_root anc : Root} (bs : BeaconState Root) (a b : Slot)
    (hwb : WalkKnown store (store.blocks anc).slot block_root)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      is_ancestor store (get_node_for_root lm.root) (get_node_for_root block_root) = true →
      WalkKnown store (store.blocks anc).slot lm.root)
    (hanc : is_ancestor store (get_node_for_root block_root) (get_node_for_root anc) = true) :
    Weak.get_broadcast_certificate_support cfg ext store bs block_root a b ≤
      Weak.get_broadcast_certificate_support cfg ext store bs anc a b := by
  simp only [Weak.get_broadcast_certificate_support]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Nat.zero_le _)
  intro i hi
  obtain ⟨hcommem, hslashed, hactive, lm, hlm, hnoteq, hspan, hisanc⟩ :=
    (Weak.mem_broadcast_certificate_support_set cfg ext store bs block_root a b i).mp hi
  exact (Weak.mem_broadcast_certificate_support_set cfg ext store bs anc a b i).mpr
    ⟨hcommem, hslashed, hactive, lm, hlm, hnoteq, hspan,
      is_ancestor_trans hwf
        (a := get_node_for_root lm.root) (b := get_node_for_root block_root)
        (c := get_node_for_root anc)
        (hwalk i lm hlm hisanc) hwb hisanc hanc⟩

/-! ## Certificate transfer -/

/-- **A broadcast certificate transfers to a chain-ancestor.** The budget
`Weak.compute_adversarial_weight` reads no root at all, so it is literally the
same for `block_root` and `anc`; the certified surplus over that budget only
grows (`broadcast_certificate_support_mono_ancestor`), so `anc`'s support
still exceeds it. -/
theorem Weak.has_broadcast_certificate_ancestor {store : Store Root}
    (hwf : ParentSlotLt store)
    {block_root anc : Root} {bs : BeaconState Root} {a b : Slot}
    (hwb : WalkKnown store (store.blocks anc).slot block_root)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      is_ancestor store (get_node_for_root lm.root) (get_node_for_root block_root) = true →
      WalkKnown store (store.blocks anc).slot lm.root)
    (hanc : is_ancestor store (get_node_for_root block_root) (get_node_for_root anc) = true)
    (hcert : Weak.has_broadcast_certificate cfg ext store bs block_root a b = true) :
    Weak.has_broadcast_certificate cfg ext store bs anc a b = true := by
  simp only [Weak.has_broadcast_certificate] at hcert ⊢
  by_cases h0 : get_current_slot cfg store = 0
  · rw [if_pos h0] at hcert
    exact absurd hcert Bool.false_ne_true
  rw [if_neg h0] at hcert ⊢
  simp only [decide_eq_true_eq] at hcert ⊢
  exact hcert.trans_le
    (Weak.broadcast_certificate_support_mono_ancestor cfg ext hwf bs a b hwb hwalk hanc)

/-! ## Dissemination at an ancestor -/

/-- **A certificate on `block_root` disseminates every known chain-ancestor of
it.** Transfer the certificate to `anc` via `has_broadcast_certificate_ancestor`
(same span, same budget), then apply the already-proved
`Execution.certificate_dissemination` (`WeakCertificateDissemination.lean`)
directly at `anc` — no reopening of its internals is needed. `ParentSlotLt` at
the observer's store comes from `WellFormedExecution` exactly as in
`WeakAncestryTransport.lean`; the `WalkKnown` witnesses are still taken as
hypotheses (see the module docstring for why). -/
theorem Weak.certificate_chain_dissemination (E : Execution Root)
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : PaperSafetySynchrony cfg ext E) (hec : ExternalsCoherence cfg ext E)
    (hbb : ByzantineBound cfg E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root)
    (v : ValidatorIndex) (n : ℕ) (balance_source : BeaconState Root)
    (block_root anc : Root) (start_slot end_slot : Slot)
    (hnH : E.WithinHorizon cfg n)
    (hstartH : E.SlotWithinHorizon cfg start_slot)
    (hendH : E.SlotWithinHorizon cfg end_slot)
    (hstart0 : E.slot_at cfg 0 ≤ start_slot)
    (hval : balance_source.validators = E.registry)
    (htab : get_total_active_balance cfg balance_source = E.total_active cfg)
    (hcomm : ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext v n) s = E.committee s)
    (hb_obs : block_root ∈ (E.store cfg ext v n).block_roots)
    (hanc_obs : anc ∈ (E.store cfg ext v n).block_roots)
    (hcert : Weak.has_broadcast_certificate cfg ext (E.store cfg ext v n) balance_source
      block_root start_slot end_slot = true)
    (hwb : WalkKnown (E.store cfg ext v n)
      ((E.store cfg ext v n).blocks anc).slot block_root)
    (hwalk : ∀ i lm, (E.store cfg ext v n).latest_messages i = some lm →
      is_ancestor (E.store cfg ext v n) (get_node_for_root lm.root)
        (get_node_for_root block_root) = true →
      WalkKnown (E.store cfg ext v n) ((E.store cfg ext v n).blocks anc).slot lm.root)
    (hanc : is_ancestor (E.store cfg ext v n) (get_node_for_root block_root)
      (get_node_for_root anc) = true)
    (w : ValidatorIndex) (hw : w ∈ E.honest) (m : ℕ) (hHm : E.WithinHorizon cfg m)
    (htiming_m : end_slot + 1 ≤ E.slot_at cfg m) :
    anc ∈ (E.store cfg ext w m).block_roots := by
  have hpsl : ParentSlotLt (E.store cfg ext v n) :=
    E.store_parentSlotLt cfg ext hwf hec hgen hwf.anchor_parent_unscheduled v n
  have hcert_anc :=
    Weak.has_broadcast_certificate_ancestor cfg ext hpsl hwb hwalk hanc hcert
  exact E.certificate_dissemination cfg ext hwf hhb hsyn hec hbb hji hgen
    v n balance_source anc start_slot end_slot hnH hstartH hendH hstart0 hval htab hcomm
    hanc_obs hcert_anc w hw m hHm htiming_m

end FastConfirmation.Spec

end
