"""Show that FULL payloads do not make Gloas fork choice equal phase0.

Read function text from the pinned Git objects. Execute it without changes.
Committee lookup and local availability are external projections. Committee
contents do not affect this fixture because the equivocating-index set is
empty. Local data is always available; neither head function calls that check.
This checks a store-level equality; it is not a full pyspec trace export
or a proof that a complete source execution reaches the fixture. It also
runs the exact FCR variable-update function, not the full FCR handler.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace
from typing import Any


PIN = "6b9bd532cca16555e2f3282d757622ebff29743e"
NS = SimpleNamespace

BEACON_HELPERS = (
    "is_active_validator",
    "compute_epoch_at_slot",
    "compute_start_slot_at_epoch",
    "get_current_epoch",
    "get_active_validator_indices",
    "get_total_balance",
    "get_total_active_balance",
)
COMMON_HELPERS = (
    "get_slots_since_genesis",
    "get_current_slot",
    "get_current_store_epoch",
    "compute_slots_since_epoch_start",
    "get_ancestor",
    "is_ancestor",
    "get_checkpoint_block",
    "get_supported_node",
    "get_attestation_score",
    "calculate_committee_fraction",
    "compute_proposer_score",
    "get_proposer_score",
    "get_weight",
    "get_voting_source",
    "filter_block_tree",
    "get_filtered_block_tree",
    "get_node_children",
    "get_head",
)
GLOAS_HELPERS = (
    "get_parent_payload_status",
    "is_parent_node_full",
    "is_payload_verified",
    "payload_timeliness",
    "payload_data_availability",
    "is_previous_slot_payload_decision",
    "should_extend_payload",
    "get_payload_status_tiebreaker",
    "should_apply_proposer_boost",
    "is_head_weak",
)
FCR_HELPERS = (
    "get_fast_confirmation_store",
    "is_start_slot_at_epoch",
    "update_fast_confirmation_variables",
)


@dataclass(frozen=True)
class Phase0Node:
    root: int


@dataclass(frozen=True)
class GloasNode:
    root: int
    payload_status: int


@dataclass(frozen=True)
class Checkpoint:
    epoch: int
    root: int


def source_functions(repo: Path, path: str, *, local_override: bool = False) -> dict[str, str]:
    """Read the pinned object, or the documented Gloas discount override."""
    if local_override:
        assert path == "specs/gloas/fast-confirmation.md"
        source = (repo / path).read_text()
    else:
        source = subprocess.run(
            ["git", "--no-replace-objects", "-C", str(repo), "show", f"{PIN}:{path}"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
    functions = {}
    for match in re.finditer(r"```python\n(.*?)```", source, re.S):
        block = match.group(1)
        for node in ast.parse(block).body:
            if isinstance(node, ast.FunctionDef):
                text = ast.get_source_segment(block, node)
                assert text is not None
                assert node.name not in functions, (path, node.name)
                functions[node.name] = text
    return functions


def fixture() -> Any:
    """Make a common store projection for the two source algorithms."""
    checkpoint = Checkpoint(epoch=0, root=1)
    validators = [
        NS(
            effective_balance=32_000_000_000,
            slashed=False,
            activation_epoch=0,
            exit_epoch=2**64 - 1,
        )
        for _ in range(100)
    ]

    def state(slot: int) -> Any:
        return NS(
            slot=slot,
            validators=validators,
            current_justified_checkpoint=checkpoint,
            finalized_checkpoint=checkpoint,
        )

    def block(
        slot: int, parent: int, proposer: int, block_hash: int, parent_hash: int
    ) -> Any:
        return NS(
            slot=slot,
            parent_root=parent,
            proposer_index=proposer,
            body=NS(
                signed_execution_payload_bid=NS(
                    message=NS(block_hash=block_hash, parent_block_hash=parent_hash)
                )
            ),
        )

    blocks = {
        1: block(0, 0, 0, 101, 0),
        2: block(1, 1, 7, 102, 101),
        3: block(1, 1, 7, 103, 101),
        4: block(2, 2, 8, 104, 102),
    }
    return NS(
        time=24,
        genesis_time=0,
        justified_checkpoint=checkpoint,
        finalized_checkpoint=checkpoint,
        unrealized_justified_checkpoint=checkpoint,
        unrealized_finalized_checkpoint=checkpoint,
        blocks=blocks,
        block_states={root: state(value.slot) for root, value in blocks.items()},
        checkpoint_states={checkpoint: state(0)},
        unrealized_justifications={root: checkpoint for root in blocks},
        proposer_boost_root=4,
        equivocating_indices=set(),
        # A same-slot vote supports PENDING in Gloas. The epoch field is the
        # phase0 projection of that same message, not a Gloas Store field.
        latest_messages={0: NS(epoch=0, slot=1, root=3, payload_present=False)},
        block_timeliness={root: [True, True] for root in blocks},
        # Membership is all that the selected helpers read from envelopes.
        payloads={root: NS(beacon_block_root=root) for root in blocks},
        payload_timeliness_vote={root: [True] * 512 for root in blocks},
        payload_data_availability_vote={root: [True] * 512 for root in blocks},
    )


def environment(node_type: type) -> dict[str, Any]:
    """Supply scalar aliases, configuration, and committee externals."""
    return {
        "ForkChoiceNode": node_type,
        "FastConfirmationStore": NS,
        "Root": int,
        "Slot": int,
        "Epoch": int,
        "ValidatorIndex": int,
        "CommitteeIndex": int,
        "Gwei": int,
        "Uint64": int,
        "Uint8": int,
        "GENESIS_SLOT": 0,
        "GENESIS_EPOCH": 0,
        "SLOT_DURATION_MS": 12000,
        "SLOTS_PER_EPOCH": 32,
        "EFFECTIVE_BALANCE_INCREMENT": 1_000_000_000,
        "PROPOSER_SCORE_BOOST": 40,
        "REORG_HEAD_WEIGHT_THRESHOLD": 20,
        "PAYLOAD_STATUS_EMPTY": 0,
        "PAYLOAD_STATUS_FULL": 1,
        "PAYLOAD_STATUS_PENDING": 2,
        "PTC_TIMELINESS_INDEX": 1,
        "PAYLOAD_TIMELY_THRESHOLD": 256,
        "DATA_AVAILABILITY_TIMELY_THRESHOLD": 256,
        # A local observation, not a PTC vote. The head does not read this
        # external, so setting it to true cannot remove the head difference.
        "is_data_available": lambda root: True,
        "get_committee_count_per_slot": lambda state, epoch: 1,
        "get_beacon_committee": lambda state, slot, index: list(
            range(len(state.validators))
        ),
    }


def load_helpers(repo: Path, fork: str) -> dict[str, Any]:
    beacon = source_functions(repo, "specs/phase0/beacon-chain.md")
    functions = source_functions(repo, "specs/phase0/fork-choice.md")
    fcr = source_functions(repo, "specs/phase0/fast-confirmation.md")
    names = COMMON_HELPERS
    if fork == "gloas":
        functions.update(source_functions(repo, "specs/gloas/fork-choice.md"))
        names += GLOAS_HELPERS
    env = environment(GloasNode if fork == "gloas" else Phase0Node)
    for source, selected in (
        (beacon, BEACON_HELPERS), (functions, names), (fcr, FCR_HELPERS)
    ):
        for name in selected:
            # Postpone type annotations only. Keep the source body unchanged.
            exec("from __future__ import annotations\n" + source[name], env)
    return env


def check(repo: Path) -> None:
    store = fixture()
    phase0 = load_helpers(repo, "phase0")
    gloas = load_helpers(repo, "gloas")
    roots = set(store.blocks)

    assert store.equivocating_indices == set()
    assert gloas["get_current_slot"](store) == 2
    assert all(
        gloas["get_parent_payload_status"](store, block) == 1
        for root, block in store.blocks.items()
        if root != store.justified_checkpoint.root
    )
    assert all(gloas["is_payload_verified"](store, root) for root in roots)
    assert all(gloas["is_data_available"](root) for root in roots)
    assert all(gloas["payload_timeliness"](store, root, True) for root in roots)
    assert all(gloas["payload_data_availability"](store, root, True) for root in roots)
    assert all(not gloas["payload_timeliness"](store, root, False) for root in roots)
    assert all(
        not gloas["payload_data_availability"](store, root, False) for root in roots
    )
    assert gloas["is_head_weak"](store, 2)
    assert not gloas["should_apply_proposer_boost"](store)

    heads = {}
    fcr_heads = {}
    for fork, env, node in (
        ("phase0", phase0, Phase0Node),
        ("gloas", gloas, lambda root: GloasNode(root, 2)),
    ):
        filtered = env["get_filtered_block_tree"](store)
        assert set(filtered) == roots
        head = env["get_head"](store)
        heads[fork] = head
        weights = tuple(env["get_weight"](store, node(root)) for root in (2, 3))
        expected = (40_000_000_000, 32_000_000_000) if fork == "phase0" else (
            0, 32_000_000_000
        )
        assert weights == expected, (fork, weights)
        fcr_store = env["get_fast_confirmation_store"](store)
        env["update_fast_confirmation_variables"](fcr_store)
        fcr_heads[fork] = fcr_store.current_slot_head
        assert fcr_store.previous_slot_head == 1
        assert fcr_store.current_slot_head == head.root
        print(
            f"{fork}: filtered_roots={list(filtered)} "
            f"weight_root2={weights[0]} weight_root3={weights[1]} head={head} "
            f"FCR_current_slot_head={fcr_store.current_slot_head}"
        )

    assert heads["phase0"].root == 4
    assert heads["gloas"] == GloasNode(root=3, payload_status=1)
    assert heads["phase0"].root != heads["gloas"].root
    assert fcr_heads == {"phase0": 4, "gloas": 3}

    # Control: remove just the early-equivocation condition. Payload maps,
    # payload votes, local availability, block hashes, and LMD votes stay fixed.
    control = fixture()
    control.block_timeliness[3][1] = False
    assert gloas["should_apply_proposer_boost"](control)
    assert phase0["get_head"](control).root == 4
    assert gloas["get_head"](control).root == 4
    print("control: root3 PTC deadline false; both head roots=4")
    print(f"pin={PIN}")
    print("FULL parent links: true; verified payloads: true; available data: true")
    print("OBSTACLE: FULL/available Gloas head root differs from phase0 head root")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus-repo", type=Path, required=True)
    args = parser.parse_args()
    check(args.consensus_repo)


if __name__ == "__main__":
    main()
