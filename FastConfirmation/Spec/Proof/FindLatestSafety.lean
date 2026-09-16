import FastConfirmation.Spec.Proof.AnchorClose

/-!
# Safety of the exact `find_latest_confirmed_descendant` call

This module closes only the executable call made at an honest `fcrStep` store.
It deliberately does not reason about `get_latest_confirmed`'s reset selection:
the caller supplies one known, already-safe base `lcr`.  If the search leaves
that base unchanged, safety is immediate.  Otherwise the strengthened
selected-result inversion supplies the concrete candidate, its known parent,
and its confirmation certificate; the executable walk theorem supplies
`result ⪰ lcr`.  Same-slot provenance transports that entire relation to every
in-horizon endpoint, where the actual `[lcr, result]` `DescendStep` supply folds
from the base `SafeFrom` witness.

No genesis-start hypothesis, covering/FFG supply, reset-anchor case split, or
justified-checkpoint ancestry is used.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- **Safety of an honest actual `find_latest_confirmed_descendant` call.**
The chain supply is conditional on a strict advance, so the executable
unchanged case imposes no per-edge obligation. -/
theorem safeFrom_find_latest_confirmed_descendant
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ) (lcr : Root)
    (hlcr : lcr ∈ (E.fcrStep cfg ext v k).store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (k + 1))
    (hchain :
      find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr ≠ lcr →
        E.DescendStepChainSupply cfg ext
          (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr)
          lcr (k + 1)) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr)
      (k + 1) := by
  by_cases hsame :
      find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr = lcr
  · rw [hsame]
    exact hbase
  refine E.safeFrom_of_headStep cfg ext ?_
  intro w hw m hm hHm hIH
  have hHk1 : E.WithinHorizon cfg (k + 1) := E.withinHorizon_mono cfg hm hHm
  rcases E.find_latest_confirmed_descendant_selected cfg ext hSA v hv (k + 1) hHk1
      (E.fcrStep cfg ext v k) (E.fcrStep_store cfg ext v k) lcr hlcr with
    heq | ⟨hconf, hbSelected, hpSelected⟩
  · exact absurd heq hsame
  have hbConfirm : find_latest_confirmed_descendant cfg ext
        (E.fcrStep cfg ext v k) lcr ∈
      (E.store cfg ext v (k + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hbSelected
  have hpConfirm : ((E.store cfg ext v (k + 1)).blocks
        (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr)).parent_root ∈
      (E.store cfg ext v (k + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hpSelected
  have hlcrConfirm : lcr ∈ (E.store cfg ext v (k + 1)).block_roots := by
    simpa only [E.fcrStep_store] using hlcr
  have hsupply := hchain hsame
  obtain ⟨hwfConfirm, hwalkConfirm, hjcConfirm⟩ :=
    E.store_domainK cfg ext hSA.2.1 hSA.2.2.2.2.2.1 hSA.1
      hSA.2.2.2.2.2.2.2.2 v hv (k + 1) hHk1
  have hheadConfirm : (get_head cfg (E.store cfg ext v (k + 1))).root ∈
      (E.store cfg ext v (k + 1)).block_roots := by
    rcases get_head_root_mem_or cfg (E.store cfg ext v (k + 1)) with h | h
    · exact h
    · rw [h]
      exact hjcConfirm
  have hbgeConfirm : is_ancestor (E.store cfg ext v (k + 1))
      (get_node_for_root
        (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr))
      (get_node_for_root lcr) = true := by
    have hge := (find_latest_confirmed_descendant_ge cfg ext
      (E.fcrStep cfg ext v k)
      (by simpa only [E.fcrStep_store] using hwfConfirm)
      (by simpa only [E.fcrStep_store] using hwalkConfirm)
      (by simpa only [E.fcrStep_store] using hheadConfirm)
      lcr hlcr).1
    simpa only [E.fcrStep_store] using hge
  obtain ⟨hlcrEndpoint, hbEndpoint, hbgeEndpoint⟩ :=
    E.confirmed_ancestry_at_all_honest_endpoints cfg ext hSA v hv k _ lcr hHk1
      hbConfirm hpConfirm hlcrConfirm hbgeConfirm hconf w hw m
        (E.slot_at_mono cfg hm) hHm
  have hheadLcr : is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m)) (get_node_for_root lcr) = true :=
    hbase w hw m hm hHm
  obtain ⟨hwfEndpoint, hwalkEndpoint, hjcEndpoint⟩ :=
    E.store_domainK cfg ext hSA.2.1 hSA.2.2.2.2.2.1 hSA.1
      hSA.2.2.2.2.2.2.2.2 w hw m hHm
  exact head_ge_of_safe_scoped_terminal cfg hwfEndpoint
    (filtered_subset_block_roots cfg (E.store cfg ext w m) hjcEndpoint)
    hwalkEndpoint hjcEndpoint hlcrEndpoint hbEndpoint hheadLcr hbgeEndpoint
    (fun a c ha hc hlink hbc hclcr =>
      hsupply w hw m hm hHm hIH a c ha hc hlink hbc hclcr)

/-- The same exact-call bridge with its per-edge chain opened to the transparent
confirm-margin supply. -/
theorem safeFrom_find_latest_confirmed_descendant_of_confirmMargin
    (hSA : SpecAssumptions cfg ext E)
    (v : ValidatorIndex) (hv : v ∈ E.honest) (k : ℕ) (lcr : Root)
    (hlcr : lcr ∈ (E.fcrStep cfg ext v k).store.block_roots)
    (hbase : E.SafeFrom cfg ext lcr (k + 1))
    (hmargin :
      find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr ≠ lcr →
        E.ForkEdgeConfirmMarginSupply cfg ext
          (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr)
          lcr (k + 1)) :
    E.SafeFrom cfg ext
      (find_latest_confirmed_descendant cfg ext (E.fcrStep cfg ext v k) lcr)
      (k + 1) :=
  E.safeFrom_find_latest_confirmed_descendant cfg ext hSA v hv k lcr hlcr hbase
    (fun hne => E.descendStepChainSupply_of_confirmMargin cfg ext hSA (hmargin hne))

end Execution

end FastConfirmation.Spec
