module
public import FastConfirmationProofs.Weak.Certificates.WeakCertificateSupporter
public import FastConfirmationProofs.Weak.Selection.WeakAncestryTransport
public import FastConfirmationProofs.ForkChoice.Head.HeadStack

@[expose] public section

/-!
# Spec / Proof / WeakCertificateDissemination

Discharges `Weak.CertificateDisseminationObligation` (`Spec/Model/WeakSynchrony.lean`,
Obligation 2): a broadcast certificate for `block_root` observed at any store
within the horizon implies every honest validator holds `block_root` from
slot `end_slot + 1` onward.

The route composes the two proved ingredients:

* `Execution.certificate_honest_supporter` (`WeakCertificateSupporter.lean`,
  Obligation 1) turns the certificate into an honest supporter `u`: a slot `s`
  in the span at which `u` is assigned and cast a genuine vote whose data root
  `d` is an ancestor of `block_root` in the observer's store, with `d` itself
  known to the observer.
* `u`'s vote is the validator-spec attestation computed from `u`'s own store
  at the vote's second (`HonestBehavior.votes_head`), so `d` is literally the
  head root of that store (`honest_attestation_data_eq` /
  `honest_attestation_data_beacon_block_root`), hence known to it
  (`Execution.head_root_known`).
* `Execution.is_ancestor_transport_closed` (`WeakAncestryTransport.lean`)
  replays the observer's `is_ancestor` walk from `d` to `block_root` into `u`'s
  store with no containment between the two stores, landing `block_root` in
  `u`'s store at the vote's second.
* `u` is honest and holds `block_root` at that second, so
  `NextSlotSynchronyPremises.block_relay` disseminates it to every honest validator
  from the following slot on — in particular from `end_slot + 1`, since the
  vote's slot lies at or below `end_slot`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- **Obligation 2.** See the module docstring for the composition; each
numbered step below matches the docstring's bullets. -/
theorem Execution.certificate_dissemination (E : Execution Root)
    (hwf : WellFormedExecution E) (hhb : HonestBehavior cfg ext E)
    (hsyn : NextSlotSynchronyPremises cfg ext E) (hec : BeaconExternalsPremises cfg ext E)
    (hbb : ByzantineWeightPremises cfg E) (hji : JustificationInterface cfg ext E)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot ∧ ablk.message.parent_root ≠ ablk.root) :
    Weak.CertificateDisseminationObligation cfg ext E := by
  intro v n balance_source block_root start_slot end_slot hnH hstartH hendH hstart0
    hval htab hcomm hb_obs hcert w hw m hHm htiming_m
  obtain ⟨ast, ablk, hgeq, hslot, hparent⟩ := hgen
  have hgen_weak : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk := ⟨ast, ablk, hgeq⟩
  -- Step 1: obligation 1 gives an honest supporter `u` for `block_root`.
  have hsupp := E.certificate_honest_supporter cfg ext hwf hhb hec hbb hgen_weak
    v n balance_source block_root start_slot end_slot hnH hstartH hendH hval htab hcomm hcert
  obtain ⟨u, hu, s, hs_lo, hs_hi, hcs, nu, a, hvote, hslot_a, hd_v, hanc⟩ := hsupp
  -- Step 2: the supporter's slot `s` is within the horizon and at/after slot 0.
  have hsSWH : E.SlotWithinHorizon cfg s := E.slotWithinHorizon_mono cfg hs_hi hendH
  have hs0 : E.slot_at cfg 0 ≤ s := hstart0.trans hs_lo
  -- Step 3: `u`'s vote for `s` is the validator-spec attestation from `u`'s own
  -- store at some second `nu'`; identify `(nu, a)` with that pair.
  obtain ⟨nu', index, hHnu', hslotnu', hvote'⟩ := hhb.votes_head u hu s hcs hsSWH hs0
  have heq' : (nu, a) = (nu', honest_attestation cfg ext (E.store cfg ext u nu') s index u) :=
    Option.some.inj (hvote.symm.trans hvote')
  have hnu_eq : nu = nu' := congrArg Prod.fst heq'
  have ha_eq : a = honest_attestation cfg ext (E.store cfg ext u nu') s index u :=
    congrArg Prod.snd heq'
  have hHnu : E.WithinHorizon cfg nu := by rw [hnu_eq]; exact hHnu'
  have hslot_nu : E.slot_at cfg nu = s := by rw [hnu_eq]; exact hslotnu'
  -- Step 4: `a`'s vote root is `u`'s own head root at `nu`, hence known to `u`'s
  -- store there.
  have ha_data : a.data.beacon_block_root =
      (get_head cfg (E.store cfg ext u nu')).root := by
    rw [ha_eq, honest_attestation_data_eq, honest_attestation_data_beacon_block_root]
  rw [← hnu_eq] at ha_data
  have hd_known : (get_head cfg (E.store cfg ext u nu)).root ∈
      (E.store cfg ext u nu).block_roots := E.head_root_known cfg ext hji hu nu hHnu
  have hd_u : a.data.beacon_block_root ∈ (E.store cfg ext u nu).block_roots := by
    rw [ha_data]; exact hd_known
  -- Step 5: transport the observer's `is_ancestor` fact into `u`'s store.
  have hanchor : ablk.message.slot ≤ ((E.store cfg ext v n).blocks block_root).slot :=
    E.store_anchor_min_slot cfg ext hwf hec hgeq hslot hparent v n block_root hb_obs
  have htrans : block_root ∈ (E.store cfg ext u nu).block_roots :=
    E.is_ancestor_transport_closed cfg ext hwf hec hgeq hslot hparent
      (v := v) (w := u) (n := n) (k := nu) (d := a.data.beacon_block_root) (b := block_root)
      hanchor hd_v hd_u hb_obs hanc
  -- Step 6: `u` is honest and holds `block_root` at `nu`, so it disseminates.
  have hmono : E.slot_at cfg m ≤ E.slot_at cfg (m + 1) := E.slot_at_mono cfg (Nat.le_succ m)
  have htiming : E.slot_at cfg nu + 1 ≤ E.slot_at cfg (m + 1) := by
    rw [hslot_nu]
    exact le_trans (Nat.add_le_add_right hs_hi 1) (le_trans htiming_m hmono)
  exact hsyn.block_relay u hu nu block_root hHnu htrans w hw m hHm htiming

end FastConfirmation.Spec

end
