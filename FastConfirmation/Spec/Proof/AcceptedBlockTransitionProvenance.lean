module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.BlockAgreement
public import FastConfirmation.Spec.Proof.Preservation
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Proof.ModelFacts
@[expose] public section

/-!
# Last accepted-writer provenance at exact execution prefixes

For every non-genesis root known in an exact execution prefix, this file
retains the actual successful scheduled `AcceptedBlockTransition` that most
recently wrote that root.  Duplicate deliveries are no-ops under the pinned
handler, so they carry the prior writer forward; only fresh deliveries install
the current block's identity fields.

The prefix-indexed invariant additionally records execution chronology.  A
writer is earlier than the prefix when it is on the same node and either lies
in an earlier scheduled second or at a lower event index in the same second.
Every other successful or rejected event carries the old witness forward.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}

/-! ## Handler-local block-identity facts -/

/-- Peel the block-identity-preserving tail of a successful block handler.
The result is either the pinned known-root no-op or the displayed fresh
insertion. -/
private theorem on_block_inserted_sameBlocks_for_lastWriter
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store') :
    (∃ post : BeaconState Root,
      ext.state_transition (store.block_states sb.message.parent_root) sb =
          some post ∧
        SameBlocks
          { store with
            block_roots :=
              if sb.root ∈ store.block_roots then store.block_roots
              else store.block_roots ++ [sb.root]
            blocks := Function.update store.blocks sb.root sb.message
            block_states := Function.update store.block_states sb.root post }
          store') ∨
      (sb.root ∈ store.block_roots ∧ store' = store) := by
  by_cases hknown : sb.root ∈ store.block_roots
  · right
    simp [on_block, hknown] at hh
    exact ⟨hknown, hh.symm⟩
  · left
    simp only [on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    cases hst : ext.state_transition
        (store.block_states sb.message.parent_root) sb with
    | none => rw [hst] at hh; cases hh
    | some post =>
      rw [hst] at hh
      let added : Store Root :=
        { store with
          block_roots := store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root post
          payload_timeliness_vote := Function.update store.payload_timeliness_vote
            sb.root (some (List.replicate cfg.ptc_size none))
          payload_data_availability_vote := Function.update store.payload_data_availability_vote
            sb.root (some (List.replicate cfg.ptc_size none)) }
      change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
        | none => none
        | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
            (FastConfirmation.Spec.update_checkpoints
              (FastConfirmation.Spec.update_proposer_boost_root cfg
                (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
                (get_head cfg store).root sb.root)
              post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
          some store' at hh
      cases hn : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => rw [hn] at hh; cases hh
      | some notified =>
        rw [hn] at hh
        cases hh
        have hf := notify_ptc_messages_frame cfg ext hn
        let timed := record_block_timeliness cfg notified sb.root
        let boosted := update_proposer_boost_root cfg timed
          (get_head cfg store).root sb.root
        let realized := update_checkpoints boosted
          post.current_justified_checkpoint post.finalized_checkpoint
        have htail : SameBlocks added
            (compute_pulled_up_tip cfg ext realized sb.root) :=
          hf.sameBlocks.trans
            ((record_block_timeliness_sameBlocks cfg notified sb.root).trans
              ((update_proposer_boost_root_sameBlocks cfg timed
                (get_head cfg store).root sb.root).trans
                ((update_checkpoints_sameBlocks boosted
                  post.current_justified_checkpoint post.finalized_checkpoint).trans
                  (compute_pulled_up_tip_sameBlocks cfg ext realized sb.root))))
        refine ⟨post, by simpa only [hst], ?_⟩
        simpa only [if_neg hknown] using htail

/-- A successful block write leaves every other block message unchanged. -/
theorem on_block_other_root_blocks
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store')
    {r : Root} (hne : r ≠ sb.root) :
    store'.blocks r = store.blocks r := by
  rcases on_block_inserted_sameBlocks_for_lastWriter hh with
    (⟨post, _hst, hsame⟩ | ⟨_hknown, rfl⟩)
  · calc
      store'.blocks r =
        ({ store with
          block_roots :=
            if sb.root ∈ store.block_roots then store.block_roots
            else store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root post } :
          Store Root).blocks r := congrFun hsame.2.1.symm r
      _ = store.blocks r := by
        change Function.update store.blocks sb.root sb.message r = _
        rw [Function.update_of_ne hne]
  · rfl

/-- A successful block write leaves every other block state unchanged. -/
theorem on_block_other_root_block_states
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store')
    {r : Root} (hne : r ≠ sb.root) :
    store'.block_states r = store.block_states r := by
  rcases on_block_inserted_sameBlocks_for_lastWriter hh with
    (⟨post, _hst, hsame⟩ | ⟨_hknown, rfl⟩)
  · calc
      store'.block_states r =
        ({ store with
          block_roots :=
            if sb.root ∈ store.block_roots then store.block_roots
            else store.block_roots ++ [sb.root]
          blocks := Function.update store.blocks sb.root sb.message
          block_states := Function.update store.block_states sb.root post } :
          Store Root).block_states r := congrFun hsame.2.2.symm r
      _ = store.block_states r := by
        change Function.update store.block_states sb.root post r = _
        rw [Function.update_of_ne hne]
  · rfl

/-- A non-written root known after a successful block was already known
before that handler call. -/
theorem on_block_other_root_known
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hh : on_block cfg ext store sb = some store')
    {r : Root} (hne : r ≠ sb.root)
    (hr : r ∈ store'.block_roots) :
    r ∈ store.block_roots := by
  rcases on_block_inserted_sameBlocks_for_lastWriter hh with
    (⟨_post, _hst, hsame⟩ | ⟨_hknown, rfl⟩)
  · rw [← hsame.1] at hr
    change r ∈ (if sb.root ∈ store.block_roots then store.block_roots
      else store.block_roots ++ [sb.root]) at hr
    by_cases hroot : sb.root ∈ store.block_roots
    · simpa only [if_pos hroot] using hr
    · simp only [if_neg hroot, List.mem_append, List.mem_singleton] at hr
      exact hr.resolve_right hne
  · exact hr

namespace Execution

namespace AcceptedBlockTransition

variable {E : Execution Root}

/-- A fresh accepted writer installs its exact signed message. -/
theorem inserted_message_fresh (t : E.AcceptedBlockTransition cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots) :
    t.postStore.blocks t.signedBlock.root = t.signedBlock.message := by
  rcases on_block_inserted_sameBlocks_for_lastWriter t.accepted with
    (⟨post, _hst, hsame⟩ | ⟨hknown, _⟩)
  · calc
      t.postStore.blocks t.signedBlock.root =
          ({ t.atPrefix.store cfg ext with
            block_roots :=
              if t.signedBlock.root ∈
                  (t.atPrefix.store cfg ext).block_roots then
                (t.atPrefix.store cfg ext).block_roots
              else
                (t.atPrefix.store cfg ext).block_roots ++
                  [t.signedBlock.root]
            blocks := Function.update (t.atPrefix.store cfg ext).blocks
              t.signedBlock.root t.signedBlock.message
            block_states := Function.update
              (t.atPrefix.store cfg ext).block_states
              t.signedBlock.root post } : Store Root).blocks
                t.signedBlock.root :=
        congrFun hsame.2.1.symm t.signedBlock.root
      _ = t.signedBlock.message := by
        change Function.update (t.atPrefix.store cfg ext).blocks
          t.signedBlock.root t.signedBlock.message t.signedBlock.root = _
        exact Function.update_self _ _ _
  · exact (hfresh hknown).elim

end AcceptedBlockTransition

/-! ## Prefix chronology -/

namespace ScheduledEventPrefix

variable {E : Execution Root}

/-- Lexicographic chronology for exact prefixes on one execution node. -/
def EarlierThan (p q : ScheduledEventPrefix E) : Prop :=
  p.node = q.node ∧
    (p.previousSecond < q.previousSecond ∨
      (p.previousSecond = q.previousSecond ∧
        p.processedCount < q.processedCount))

namespace EarlierThan

/-- Moving the target prefix one concrete event to the right preserves strict
chronology. -/
theorem successor_right {p q : ScheduledEventPrefix E}
    (h : p.EarlierThan q)
    (hnext : q.processedCount <
      (E.schedule q.node (q.previousSecond + 1)).length) :
    p.EarlierThan (q.successor hnext) := by
  rcases h with ⟨hnode, hsecond | ⟨hsecond, hcount⟩⟩
  · exact ⟨hnode, Or.inl hsecond⟩
  · exact ⟨hnode, Or.inr ⟨hsecond,
      hcount.trans (Nat.lt_succ_self q.processedCount)⟩⟩

/-- A prefix is strictly earlier than its own one-event successor. -/
theorem self_successor (p : ScheduledEventPrefix E)
    (hnext : p.processedCount <
      (E.schedule p.node (p.previousSecond + 1)).length) :
    p.EarlierThan (p.successor hnext) :=
  ⟨rfl, Or.inr ⟨rfl, Nat.lt_succ_self p.processedCount⟩⟩

end EarlierThan

end ScheduledEventPrefix

/-! ## Last-writer carriers and invariants -/

/-- The actual accepted transition most recently responsible for one current
non-genesis block identity.  Both totalized block maps are retained. -/
structure AcceptedBlockLastWriterCarrier
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (store : Store Root) (r : Root) where
  transition : E.AcceptedBlockTransition cfg ext
  root_eq : transition.signedBlock.root = r
  fresh : transition.signedBlock.root ∉
    (transition.atPrefix.store cfg ext).block_roots
  message_eq : transition.signedBlock.message = store.blocks r
  block_state_eq :
    transition.postStore.block_states r = store.block_states r

namespace AcceptedBlockLastWriterCarrier

/-- Block-identity equality transports a last-writer witness without changing
its actual transition. -/
def of_sameBlocks
    {E : Execution Root} {store store' : Store Root} {r : Root}
    (w : AcceptedBlockLastWriterCarrier cfg ext E store r)
    (hsame : SameBlocks store store') :
    AcceptedBlockLastWriterCarrier cfg ext E store' r where
  transition := w.transition
  root_eq := w.root_eq
  fresh := w.fresh
  message_eq := w.message_eq.trans (congrFun hsame.2.1 r)
  block_state_eq := w.block_state_eq.trans (congrFun hsame.2.2 r)

end AcceptedBlockLastWriterCarrier

/-- Store-level last-writer provenance.  Trusted genesis roots are the only
explicit base case and therefore intentionally excluded. -/
def AcceptedBlockLastWriterProvenance
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (store : Store Root) : Prop :=
  ∀ r ∈ store.block_roots, r ∉ E.genesis_store.block_roots →
    Nonempty (AcceptedBlockLastWriterCarrier cfg ext E store r)

/-- Prefix-indexed witness, strengthened with chronology to its target
prefix. -/
structure AcceptedBlockLastWriterAtPrefixCarrier
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (p : ScheduledEventPrefix E) (r : Root) where
  writer : AcceptedBlockLastWriterCarrier cfg ext E (p.store cfg ext) r
  earlier : writer.transition.atPrefix.EarlierThan p

/-- Exact-prefix last-writer provenance with target-prefix chronology. -/
def AcceptedBlockLastWriterPrefixProvenance
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (p : ScheduledEventPrefix E) : Prop :=
  ∀ r ∈ (p.store cfg ext).block_roots,
    r ∉ E.genesis_store.block_roots →
      Nonempty (AcceptedBlockLastWriterAtPrefixCarrier cfg ext E p r)

namespace AcceptedBlockLastWriterPrefixProvenance

variable {E : Execution Root}

/-- A block-identity-preserving successor carries every prior writer forward
and advances only the target chronology. -/
theorem successor_of_sameBlocks
    {p : E.ScheduledEventPrefix}
    (h : AcceptedBlockLastWriterPrefixProvenance cfg ext E p)
    (hnext : p.processedCount <
      (E.schedule p.node (p.previousSecond + 1)).length)
    (hsame : SameBlocks (p.store cfg ext)
      ((p.successor hnext).store cfg ext)) :
    AcceptedBlockLastWriterPrefixProvenance cfg ext E
      (p.successor hnext) := by
  intro r hr hnonGenesis
  have hrpre : r ∈ (p.store cfg ext).block_roots := by
    rw [hsame.1]
    exact hr
  obtain ⟨old⟩ := h r hrpre hnonGenesis
  exact ⟨
    { writer := old.writer.of_sameBlocks hsame
      earlier := old.earlier.successor_right hnext }⟩

/-- A successful block transition replaces the witness at its root with the
current transition, including on duplicate-root overwrites.  Every other root
carries its prior writer forward. -/
theorem acceptedBlockTransition
    (t : E.AcceptedBlockTransition cfg ext)
    (h : AcceptedBlockLastWriterPrefixProvenance cfg ext E t.atPrefix) :
    AcceptedBlockLastWriterPrefixProvenance cfg ext E
      t.successorPrefix := by
  unfold AcceptedBlockLastWriterPrefixProvenance
  rw [t.successorPrefix_store]
  intro r hr hnonGenesis
  by_cases hroot : r = t.signedBlock.root
  · subst r
    by_cases hfresh : t.signedBlock.root ∉
        (t.atPrefix.store cfg ext).block_roots
    · have hmessage :=
        Execution.AcceptedBlockTransition.inserted_message_fresh t hfresh
      exact ⟨
        { writer :=
            { transition := t
              root_eq := rfl
              fresh := hfresh
              message_eq := hmessage.symm.trans
                (congrArg (fun s => s.blocks t.signedBlock.root)
                  t.successorPrefix_store.symm)
              block_state_eq := congrArg
                (fun s => s.block_states t.signedBlock.root)
                  t.successorPrefix_store.symm }
          earlier := ScheduledEventPrefix.EarlierThan.self_successor
            t.atPrefix t.processedCount_lt }⟩
    · have hknown := Classical.byContradiction hfresh
      obtain ⟨old⟩ := h t.signedBlock.root hknown hnonGenesis
      have hpost : t.postStore = t.atPrefix.store cfg ext := by
        exact (Option.some.inj (by
          simpa only [on_block, if_pos hknown] using t.accepted)).symm
      have hsame : SameBlocks (t.atPrefix.store cfg ext)
          (t.successorPrefix.store cfg ext) := by
        rw [t.successorPrefix_store, hpost]
        exact SameBlocks.refl _
      exact ⟨
        { writer := old.writer.of_sameBlocks hsame
          earlier := old.earlier.successor_right t.processedCount_lt }⟩
  · have hrpre : r ∈ (t.atPrefix.store cfg ext).block_roots :=
      on_block_other_root_known t.accepted hroot hr
    obtain ⟨old⟩ := h r hrpre hnonGenesis
    exact ⟨
      { writer :=
          { transition := old.writer.transition
            root_eq := old.writer.root_eq
            fresh := old.writer.fresh
            message_eq := old.writer.message_eq.trans
              ((on_block_other_root_blocks t.accepted hroot).symm.trans
                (congrArg (fun s => s.blocks r)
                  t.successorPrefix_store.symm))
            block_state_eq := old.writer.block_state_eq.trans
              ((on_block_other_root_block_states t.accepted hroot).symm.trans
                (congrArg (fun s => s.block_states r)
                  t.successorPrefix_store.symm)) }
        earlier := old.earlier.successor_right t.processedCount_lt }⟩

end AcceptedBlockLastWriterPrefixProvenance

/-! ## Boundary and exact-prefix induction -/

/-- Boundary strengthening used to enter the next scheduled second. -/
private structure AcceptedBlockLastWriterBeforeBoundaryCarrier
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (w : ValidatorIndex) (n : ℕ) (r : Root) where
  writer : AcceptedBlockLastWriterCarrier cfg ext E
    (E.store cfg ext w n) r
  node_eq : writer.transition.atPrefix.node = w
  previousSecond_lt : writer.transition.atPrefix.previousSecond < n

private def AcceptedBlockLastWriterBoundaryProvenance
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (w : ValidatorIndex) (n : ℕ) : Prop :=
  ∀ r ∈ (E.store cfg ext w n).block_roots,
    r ∉ E.genesis_store.block_roots →
      Nonempty
        (AcceptedBlockLastWriterBeforeBoundaryCarrier cfg ext E w n r)

/-- Exact `take k` induction from one strengthened execution boundary. -/
private theorem acceptedBlockLastWriterPrefix_take
    (E : Execution Root) (w : ValidatorIndex) (n : ℕ)
    (hboundary : AcceptedBlockLastWriterBoundaryProvenance cfg ext E w n) :
    ∀ k : ℕ, ∀ hk : k ≤ (E.schedule w (n + 1)).length,
      AcceptedBlockLastWriterPrefixProvenance cfg ext E
        { node := w
          previousSecond := n
          processedCount := k
          count_le := hk } := by
  intro k hk
  induction k with
  | zero =>
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := 0
          count_le := hk }
      change AcceptedBlockLastWriterPrefixProvenance cfg ext E p
      intro r hr hnonGenesis
      have htick : SameBlocks (E.store cfg ext w n) (p.store cfg ext) := by
        simpa only [p, ScheduledEventPrefix.store, List.take_zero,
          List.foldl_nil] using
          on_tick_sameBlocks cfg (E.store cfg ext w n) (E.time_at (n + 1))
      have hrBoundary : r ∈ (E.store cfg ext w n).block_roots := by
        rw [htick.1]
        exact hr
      obtain ⟨old⟩ := hboundary r hrBoundary hnonGenesis
      exact ⟨
        { writer := old.writer.of_sameBlocks htick
          earlier := ⟨old.node_eq, Or.inl old.previousSecond_lt⟩ }⟩
  | succ k ih =>
      have hklt : k < (E.schedule w (n + 1)).length := by omega
      have hkle : k ≤ (E.schedule w (n + 1)).length :=
        Nat.le_of_lt hklt
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := k
          count_le := hkle }
      have hp : AcceptedBlockLastWriterPrefixProvenance cfg ext E p :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsuccessor :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedBlockLastWriterPrefixProvenance cfg ext E
        (p.successor hklt)
      cases heq : apply_event cfg ext (p.store cfg ext) nextEvent with
      | none =>
          apply hp.successor_of_sameBlocks hklt
          rw [hsuccessor, heq, Option.getD_none]
          exact SameBlocks.refl _
      | some store' =>
          have hsuccessorStore :
              (p.successor hklt).store cfg ext = store' := by
            rw [hsuccessor, heq, Option.getD_some]
          cases hevent : nextEvent with
          | block sb =>
              let t : E.AcceptedBlockTransition cfg ext :=
                { atPrefix := p
                  signedBlock := sb
                  event_at := by
                    have hget :
                        (E.schedule w (n + 1))[k]? = some nextEvent := by
                      simp [nextEvent, List.getElem?_eq_getElem hklt]
                    rw [hget, hevent]
                  postStore := store'
                  accepted := by
                    simpa [apply_event, hevent] using heq }
              have htPrefix : t.successorPrefix = p.successor hklt := by
                rfl
              rw [← htPrefix]
              exact hp.acceptedBlockTransition t
          | attestation a fromBlock =>
              apply hp.successor_of_sameBlocks hklt
              rw [hsuccessorStore]
              exact on_attestation_sameBlocks cfg ext
                (by simpa [apply_event, hevent] using heq)
          | attester_slashing sl =>
              apply hp.successor_of_sameBlocks hklt
              rw [hsuccessorStore]
              exact on_attester_slashing_sameBlocks ext
                (by simpa [apply_event, hevent] using heq)
          | execution_payload_envelope envelope observation =>
              apply hp.successor_of_sameBlocks hklt
              rw [hsuccessorStore]
              exact on_execution_payload_envelope_sameBlocks ext
                (by simpa [apply_event, hevent] using heq)
          | payload_attestation_message message fromBlock =>
              apply hp.successor_of_sameBlocks hklt
              rw [hsuccessorStore]
              exact on_payload_attestation_message_sameBlocks cfg ext
                (by simpa [apply_event, hevent] using heq)

/-- Every ordinary execution boundary has strengthened last-writer
provenance. -/
private theorem acceptedBlockLastWriterBoundaryProvenance
    (E : Execution Root) (w : ValidatorIndex) (n : ℕ) :
    AcceptedBlockLastWriterBoundaryProvenance cfg ext E w n := by
  induction n with
  | zero =>
      intro r hr hnonGenesis
      exact (hnonGenesis hr).elim
  | succ n ih =>
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := (E.schedule w (n + 1)).length
          count_le := le_rfl }
      have hp : AcceptedBlockLastWriterPrefixProvenance cfg ext E p :=
        acceptedBlockLastWriterPrefix_take E w n ih
          (E.schedule w (n + 1)).length le_rfl
      have hpStore : p.store cfg ext = E.store cfg ext w (n + 1) := by
        simp [p, ScheduledEventPrefix.store, Execution.store]
      intro r hr hnonGenesis
      have hrp : r ∈ (p.store cfg ext).block_roots := by
        rw [hpStore]
        exact hr
      obtain ⟨old⟩ := hp r hrp hnonGenesis
      have hsame : SameBlocks (p.store cfg ext)
          (E.store cfg ext w (n + 1)) := by
        rw [hpStore]
        exact SameBlocks.refl _
      refine ⟨
        { writer := old.writer.of_sameBlocks hsame
          node_eq := old.earlier.1
          previousSecond_lt := ?_ }⟩
      change old.writer.transition.atPrefix.previousSecond < n + 1
      rcases old.earlier.2 with hsecond | ⟨hsecond, _hcount⟩
      · exact hsecond.trans (Nat.lt_succ_self n)
      · rw [hsecond]
        exact Nat.lt_succ_self n

/-! ## Public exact-prefix and causal-store producers -/

/-- Every exact scheduled prefix has target-chronological last-writer
provenance. -/
theorem ScheduledEventPrefix.acceptedBlockLastWriterPrefixProvenance
    {E : Execution Root} (p : E.ScheduledEventPrefix) :
    AcceptedBlockLastWriterPrefixProvenance cfg ext E p :=
  acceptedBlockLastWriterPrefix_take E p.node p.previousSecond
    (acceptedBlockLastWriterBoundaryProvenance E p.node p.previousSecond)
    p.processedCount p.count_le

/-- Erasing chronology yields the store-level invariant at every exact
scheduled prefix. -/
theorem ScheduledEventPrefix.acceptedBlockLastWriterProvenance
    {E : Execution Root} (p : E.ScheduledEventPrefix) :
    AcceptedBlockLastWriterProvenance cfg ext E (p.store cfg ext) := by
  intro r hr hnonGenesis
  obtain ⟨carrier⟩ :=
    p.acceptedBlockLastWriterPrefixProvenance r hr hnonGenesis
  exact ⟨carrier.writer⟩

/-- Last accepted-writer provenance at every store in the exact causal
domain. -/
theorem CausalStore.acceptedBlockLastWriterProvenance
    {E : Execution Root} {store : Store Root}
    (hstore : E.CausalStore cfg ext store) :
    AcceptedBlockLastWriterProvenance cfg ext E store := by
  cases hstore with
  | genesis =>
      intro r hr hnonGenesis
      exact (hnonGenesis hr).elim
  | scheduledPrefix p =>
      exact p.acceptedBlockLastWriterProvenance


end Execution

end FastConfirmation.Spec

end
