"""Export direct Gloas helper observations from unchanged pinned source.

The four-block store and committee reads are projections. These fixtures are
not pyspec traces or accepted executions. No source file is changed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from types import SimpleNamespace

from gloas_full_instance_obstacle import (
    GloasNode,
    PIN,
    fixture,
    load_helpers,
    source_functions,
)


def cases() -> list[dict]:
    base = dict(verified=True, timely_yes=0, timely_no=0, available_yes=0,
                available_no=0, boost_root=4, boost_parent_full=True,
                sibling_attestation_timely=False, sibling_ptc_timely=False)
    variants = [
        ("verified_unknown_no_boost", dict(boost_root=0, sibling_attestation_timely=True,
                                          sibling_ptc_timely=True)),
        ("unverified_positive_votes", dict(verified=False, timely_yes=512, available_yes=512,
                                           boost_parent_full=False)),
        ("tied_empty_boost", dict(timely_yes=256, timely_no=256,
                                 available_yes=256, available_no=256, boost_parent_full=False)),
        ("positive_majorities_empty_boost", dict(timely_yes=257, timely_no=255,
                                                available_yes=257, available_no=255,
                                                boost_parent_full=False)),
        ("negative_majorities_empty_boost", dict(timely_yes=255, timely_no=257,
                                                available_yes=255, available_no=257,
                                                boost_parent_full=False)),
        ("timely_only_empty_boost", dict(timely_yes=257, timely_no=255,
                                        available_yes=256, available_no=256,
                                        boost_parent_full=False)),
        ("available_only_empty_boost", dict(timely_yes=256, timely_no=256,
                                           available_yes=257, available_no=255,
                                           boost_parent_full=False)),
        ("early_equivocation_ptc_only", dict(sibling_attestation_timely=False,
                                            sibling_ptc_timely=True)),
        ("late_equivocation", {}),
    ]
    return [{"name": name, "input": base | changes} for name, changes in variants]


def votes(yes: int, no: int) -> list[bool | None]:
    assert yes + no <= 512
    return [True] * yes + [False] * no + [None] * (512 - yes - no)


def make_store(inputs: dict):
    store = fixture()
    store.latest_messages = {}
    store.proposer_boost_root = inputs["boost_root"]
    store.blocks[4].body.signed_execution_payload_bid.message.parent_block_hash = (
        102 if inputs["boost_parent_full"] else 101
    )
    store.block_timeliness[3] = [inputs["sibling_attestation_timely"], inputs["sibling_ptc_timely"]]
    store.payloads = {
        root: SimpleNamespace(beacon_block_root=root,
                              parent_beacon_block_root=block.parent_root, identity=root + 1000)
        for root, block in store.blocks.items() if root != 2 or inputs["verified"]
    }
    store.payload_timeliness_vote[2] = votes(inputs["timely_yes"], inputs["timely_no"])
    store.payload_data_availability_vote[2] = votes(inputs["available_yes"], inputs["available_no"])
    return store


def observe(spec: dict, store) -> dict:
    result = {
        "payload_verified": spec["is_payload_verified"](store, 2),
        "timely_yes": spec["payload_timeliness"](store, 2, True),
        "timely_no": spec["payload_timeliness"](store, 2, False),
        "available_yes": spec["payload_data_availability"](store, 2, True),
        "available_no": spec["payload_data_availability"](store, 2, False),
        "extend": spec["should_extend_payload"](store, 2),
        "head_weak": spec["is_head_weak"](store, 2),
        "apply_boost": spec["should_apply_proposer_boost"](store),
        "sibling_head_late": spec["is_head_late"](store, 3),
    }
    for label, status in [("empty", 0), ("full", 1), ("pending", 2)]:
        node = GloasNode(2, status)
        result[f"previous_{label}"] = spec["is_previous_slot_payload_decision"](store, node)
        result[f"tiebreak_{label}"] = spec["get_payload_status_tiebreaker"](store, node)
        result[f"weight_{label}"] = spec["get_weight"](store, node)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus-repo", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    spec = load_helpers(args.consensus_repo, "gloas")
    source = source_functions(args.consensus_repo, "specs/gloas/fork-choice.md")
    spec["ATTESTATION_TIMELINESS_INDEX"] = 0
    exec("from __future__ import annotations\n" + source["is_head_late"], spec)
    records = cases()
    for record in records:
        # The attestation deadline precedes the PTC deadline.
        assert not record["input"]["sibling_attestation_timely"] or record["input"]["sibling_ptc_timely"]
        record["expected"] = observe(spec, make_store(record["input"]))
        assert record["expected"]["weight_empty"] == record["expected"]["weight_full"] == 0
    early, late = records[-2]["expected"], records[-1]["expected"]
    assert (early["apply_boost"], early["weight_pending"], early["sibling_head_late"]) == (False, 0, True)
    assert (late["apply_boost"], late["weight_pending"], late["sibling_head_late"]) == (True, 40_000_000_000, True)
    assert not records[2]["expected"]["extend"] and records[3]["expected"]["extend"]
    output = {"format": "gloas-helper-observations-v1", "pin": PIN,
              "scope": "projected source functions; not an accepted execution", "fixtures": records}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    count = sum(len(record["expected"]) for record in records)
    print(f"SOURCE_HELPERS fixtures={len(records)} observations={count} pin={PIN}")


if __name__ == "__main__":
    main()
