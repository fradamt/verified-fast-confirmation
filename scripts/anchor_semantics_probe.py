"""Check raw anchor and epoch-1 limits with the pinned specification.

Run with the checkout's existing .venv/bin/python and pass its path.
BLS checks use the test helper switch. The Gloas filter experiment supplies
pre-anchor headers and timeliness entries for the proposer-boost lookup.
The inclusion control puts epoch-F votes in a canonical epoch-F+1 block.
It checks the raw source at F+2 and ancestry of the previously confirmed child.
This script does not assert a complete safety premise bundle.
"""
from pathlib import Path
import sys

repo = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(repo / "tests/core/pyspec"))
from eth_consensus_specs.utils import bls
from eth_consensus_specs.test.helpers.genesis import create_genesis_state
from eth_consensus_specs.test.helpers.attestations import (
    next_slots_with_attestations, get_valid_attestation_at_slot,
)
from eth_consensus_specs.test.helpers.block import build_empty_block, build_empty_block_for_next_slot
from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block

bls.bls_active = False


def state_for(spec):
    assert Path(spec.__file__).resolve().is_relative_to(repo), spec.__file__
    return create_genesis_state(spec, [32 * 10**9] * 64, 32 * 10**9)


def boundary_probe():
    from eth_consensus_specs.phase0 import minimal as spec
    state = state_for(spec)
    _, _, state = next_slots_with_attestations(
        spec, state, 2 * spec.SLOTS_PER_EPOCH - 1, True, False
    )
    assert spec.get_current_epoch(state) == 1
    eager = state.copy()
    spec.process_justification_and_finalization(eager)
    one_boundary = state.copy()
    spec.process_slots(one_boundary, 2 * spec.SLOTS_PER_EPOCH)
    assert one_boundary.current_justified_checkpoint == eager.current_justified_checkpoint
    advanced = state.copy()
    spec.process_slots(advanced, 3 * spec.SLOTS_PER_EPOCH)
    print("epoch-one boundary", "start_slot", int(state.slot), "eager_epoch",
          int(eager.current_justified_checkpoint.epoch), "advanced_epoch",
          int(advanced.current_justified_checkpoint.epoch), flush=True)
    assert eager.current_justified_checkpoint == state.current_justified_checkpoint
    assert advanced.current_justified_checkpoint.epoch == 1
    assert advanced.current_justified_checkpoint != eager.current_justified_checkpoint
    transitioned = state.copy()
    block = build_empty_block(spec, transitioned, slot=3 * spec.SLOTS_PER_EPOCH)
    state_transition_and_sign_block(spec, transitioned, block)
    assert transitioned.current_justified_checkpoint == advanced.current_justified_checkpoint
    print("epoch-one boundary transition", "target_slot", int(transitioned.slot),
          "justified_epoch", int(transitioned.current_justified_checkpoint.epoch), flush=True)
    guarded_cases = 0
    for start in (state, one_boundary, advanced):
        start_epoch = int(spec.get_current_epoch(start))
        pulled = start.copy()
        spec.process_justification_and_finalization(pulled)
        for jump in (1, 2, 3):
            if start_epoch < 2 and jump > 1:
                continue
            target = (start_epoch + jump) * spec.SLOTS_PER_EPOCH
            slotted = start.copy()
            spec.process_slots(slotted, target)
            assert slotted.current_justified_checkpoint == pulled.current_justified_checkpoint
            transitioned = start.copy()
            block = build_empty_block(spec, transitioned, slot=target)
            state_transition_and_sign_block(spec, transitioned, block)
            assert transitioned.current_justified_checkpoint == pulled.current_justified_checkpoint
            guarded_cases += 2
    print("guarded boundary slot/transition cases", guarded_cases, flush=True)


def checkpoint_sync_probe(include_epoch_f_votes=False):
    from eth_consensus_specs.gloas import minimal as spec
    state = state_for(spec)
    _, blocks, state = next_slots_with_attestations(
        spec, state, 3 * spec.SLOTS_PER_EPOCH, True, False
    )
    anchor = blocks[-1].message
    anchor_root = spec.hash_tree_root(anchor)
    assert state.slot == 3 * spec.SLOTS_PER_EPOCH
    assert state.current_justified_checkpoint.epoch == 2
    store = spec.get_forkchoice_store(state, anchor)
    # The pinned proposer-boost helper walks before the anchor. Supply the
    # already generated ancestor headers for that lookup only. Without these
    # headers the first on_block raises KeyError before it can finish.
    for prior in blocks[:-1]:
        prior_root = spec.hash_tree_root(prior.message)
        store.blocks[prior_root] = prior.message.copy()
        store.block_timeliness[prior_root] = [True, True]
    fcr = spec.get_fast_confirmation_store(store)
    print("sync anchor", int(state.slot), "raw_j",
          int(state.current_justified_checkpoint.epoch), "store_j",
          int(store.justified_checkpoint.epoch), flush=True)
    child = build_empty_block_for_next_slot(spec, state)
    signed_child = state_transition_and_sign_block(spec, state, child)
    child_root = spec.hash_tree_root(signed_child.message)
    spec.on_tick(store, int(state.genesis_time + state.slot * spec.config.SLOT_DURATION_MS // 1000))
    spec.on_block(store, signed_child)
    spec.on_fast_confirmation(fcr)
    confirmed_slot = None
    epoch_f_votes = []
    carrier_root = None
    inclusion_slot = 4 * spec.SLOTS_PER_EPOCH
    for slot in range(int(state.slot), 5 * spec.SLOTS_PER_EPOCH):
        voter = store.block_states[spec.get_head(store).root].copy()
        if voter.slot < slot:
            spec.process_slots(voter, slot)
        attestation = get_valid_attestation_at_slot(voter, spec, slot)
        spec.on_tick(store, int(state.genesis_time + (slot + 1) * spec.config.SLOT_DURATION_MS // 1000))
        spec.on_attestation(store, attestation)
        if slot < inclusion_slot:
            epoch_f_votes.append(attestation)
        if include_epoch_f_votes and slot + 1 == inclusion_slot:
            carrier_state = store.block_states[child_root].copy()
            carrier = build_empty_block(spec, carrier_state, slot=inclusion_slot)
            for epoch_f_vote in epoch_f_votes:
                carrier.body.attestations.append(epoch_f_vote)
            signed_carrier = state_transition_and_sign_block(spec, carrier_state, carrier)
            spec.on_block(store, signed_carrier)
            carrier_root = spec.hash_tree_root(signed_carrier.message)
            assert store.unrealized_justifications[carrier_root].epoch == 3
            print("included", len(epoch_f_votes), "epoch-F votes at", inclusion_slot,
                  "carrier raw GU", int(store.unrealized_justifications[carrier_root].epoch), flush=True)
        spec.on_fast_confirmation(fcr)
        head = spec.get_head(store).root
        if fcr.confirmed_root == child_root and confirmed_slot is None:
            confirmed_slot = slot + 1
        def root_name(root):
            if root == child_root:
                return "child"
            if root == anchor_root:
                return "anchor"
            assert root == carrier_root
            return "carrier"
        print("sync slot", slot + 1, "head", root_name(head),
              "confirmed", root_name(fcr.confirmed_root),
              "child_source", int(spec.get_voting_source(store, child_root).epoch),
              "head_source", int(spec.get_voting_source(store, head).epoch), flush=True)
    assert confirmed_slot is not None
    assert spec.get_current_slot(store) == 5 * spec.SLOTS_PER_EPOCH
    if include_epoch_f_votes:
        assert spec.get_voting_source(store, carrier_root).epoch == 3
        assert spec.is_ancestor(store, spec.get_head(store), spec.get_node_for_root(child_root))
        print("inclusion control keeps the confirmed child at", int(spec.get_current_slot(store)), flush=True)
        return
    assert spec.get_head(store).root == anchor_root
    assert not spec.is_ancestor(store, spec.get_node_for_root(anchor_root), spec.get_node_for_root(child_root))
    print("sync failure", "confirmed_at", confirmed_slot, "lost_at", int(spec.get_current_slot(store)), flush=True)
    # Demonstrate the semantic difference without changing the raw run.
    import copy
    normalized = copy.deepcopy(store)
    for root, checkpoint in normalized.unrealized_justifications.items():
        if checkpoint.epoch <= normalized.justified_checkpoint.epoch:
            normalized.unrealized_justifications[root] = normalized.justified_checkpoint.copy()
    assert spec.get_head(normalized).root == child_root
    print("normalized source changes the slot-40 head to child", flush=True)


boundary_probe()
checkpoint_sync_probe()
checkpoint_sync_probe(include_epoch_f_votes=True)
