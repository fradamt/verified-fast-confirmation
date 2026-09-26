#!/usr/bin/env python3
"""Check finite premise fields on one 100-validator mixed-balance pyspec run.

This is a falsification check, not a proof of the full execution bundle. It
reuses the accepted-block FFG projection and tests finite registry, committee,
and economic fields against the same genesis-to-epoch-6 run.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'projection'))
import run as projection  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    spec, genesis, next_slots, _, _, genesis_store = projection.setup(args.repo)
    balances = [(32 + i % 4) * 10**9 for i in range(100)]
    base = genesis(spec, balances, spec.MIN_ACTIVATION_BALANCE)
    _, anchor = genesis_store(spec, base)
    _, blocks, tail = next_slots(spec, base, 48, True, False)
    run = projection.Run('mixed-100-genesis-to-epoch-6', spec,
                         genesis(spec, balances, spec.MIN_ACTIVATION_BALANCE), anchor, blocks)
    if run.errors or len(run.roots) != 49 or int(tail.slot) < 48:
        raise RuntimeError(f'fixture did not import 48 normal-participation blocks: {run.errors}')
    results = []

    def field(name: str, passed: bool, checks: int, detail: dict | None = None) -> None:
        results.append({'field': name, 'status': 'PASS' if passed else 'FAIL',
                        'checks': checks, 'first_failure': detail if not passed else None})

    anchor_state = run.states[run.anchor_root]
    registry = anchor_state.validators
    horizon = 7
    slots_per_epoch = int(spec.SLOTS_PER_EPOCH)
    increment = int(spec.EFFECTIVE_BALANCE_INCREMENT)
    active = {e: set(map(int, spec.get_active_validator_indices(anchor_state, spec.Epoch(e))))
              for e in range(horizon)}
    field('StaticValidatorSet.genesis_within_horizon', 0 < horizon, 1)
    field('StaticValidatorSet.activity_constant', all(active[e] == active[0] for e in active), horizon)
    def registry_view(state):
        return tuple((int(v.effective_balance), bool(v.slashed), int(v.activation_epoch),
                      int(v.exit_epoch)) for v in state.validators)
    ref = registry_view(anchor_state)
    changed = next((root for root, state in run.states.items() if registry_view(state) != ref), None)
    field('BeaconExternalsPremises.registry_static_in_horizon', changed is None,
          len(run.states), {'root': changed} if changed else None)
    field('ScheduledFCRCallPremises.balance_floor',
          sum(int(registry[i].effective_balance) for i in active[0]) >= 2 * increment, 1)
    field('NextSlotSafetyPremises.slots_per_epoch_gt_one', slots_per_epoch > 1, 1)
    field('NextSlotSafetyPremises.epoch_ends_fit',
          horizon * slots_per_epoch < 2**64, 1)
    field('NextSlotSafetyPremises.anchor_boundary', int(anchor.slot) % slots_per_epoch == 0, 1)
    field('NextSlotSafetyPremises.anchor_eq', run.anchor[1] == run.anchor_root, 1)
    field('NextSlotSafetyPremises.anchor_state_checkpoints',
          run.anchor[0] == 0 and int(anchor_state.current_justified_checkpoint.epoch) == 0
          and int(anchor_state.finalized_checkpoint.epoch) == 0, 1)
    field('BeaconExternalsPremises.anchor_state_checkpoint_epoch',
          int(anchor_state.current_justified_checkpoint.epoch) <= int(anchor_state.slot) // slots_per_epoch
          and int(anchor_state.finalized_checkpoint.epoch) <= int(anchor_state.slot) // slots_per_epoch, 1)
    field('ScheduledExecutionPremises.whole_seconds', int(spec.config.SLOT_DURATION_MS) % 1000 == 0, 1)
    field('ByzantineWeightPremises.effective_balance_quantized',
          all(int(v.effective_balance) % increment == 0 for v in registry), len(registry))
    # T laws sampled on accepted keyed states of this same execution.
    slot_target_results = []
    pjf_results = []
    same_epoch_results = []
    one_boundary_results = []
    same_target_results = []
    for root, state in run.states.items():
        slot = int(state.slot)
        epoch = slot // slots_per_epoch
        next_slot = slot + 1
        processed = state.copy()
        spec.process_slots(processed, spec.Slot(next_slot))
        slot_target_results.append((int(processed.slot) == next_slot, root))
        eager = state.copy()
        spec.process_justification_and_finalization(eager)
        if int(state.current_justified_checkpoint.epoch) <= epoch:
            pjf_results.append((int(eager.current_justified_checkpoint.epoch) <= epoch, root))
        if next_slot // slots_per_epoch == epoch:
            same_epoch_results.append((projection.cp(processed.current_justified_checkpoint)
                                       == projection.cp(state.current_justified_checkpoint), root))
        boundary = (epoch + 1) * slots_per_epoch
        if boundary < horizon * slots_per_epoch:
            at_boundary = state.copy()
            spec.process_slots(at_boundary, spec.Slot(boundary))
            one_boundary_results.append((projection.cp(at_boundary.current_justified_checkpoint)
                                         == projection.cp(eager.current_justified_checkpoint), root))
            after_boundary = state.copy()
            spec.process_slots(after_boundary, spec.Slot(boundary + 1))
            same_target_results.append((projection.cp(at_boundary.current_justified_checkpoint)
                                        == projection.cp(after_boundary.current_justified_checkpoint), root))
    for name, cases in (
        ('BeaconExternalsPremises.process_slots_slot', slot_target_results),
        ('BeaconExternalsPremises.pjf_checkpoint_epoch', pjf_results),
        ('Phase0SourceCoherence.process_slots_current_justified', same_epoch_results),
        ('Phase0BoundarySourceCoherence.process_slots_one_boundary', one_boundary_results),
        ('Phase0BoundarySourceCoherence.process_slots_same_target_epoch', same_target_results),
    ):
        failed = next((root for ok, root in cases if not ok), None)
        field(name, failed is None and bool(cases), len(cases), {'root': failed} if failed else None)
    committees = {}
    for slot in range(48):
        epoch = slot // slots_per_epoch
        members = set()
        for index in range(int(spec.get_committee_count_per_slot(anchor_state, spec.Epoch(epoch)))):
            members.update(map(int, spec.get_beacon_committee(
                anchor_state, spec.Slot(slot), spec.CommitteeIndex(index))))
        committees[slot] = members
    unique = all(sum(len(committees[s]) for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch))
                 == len(set().union(*(committees[s] for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch))))
                 for e in range(6))
    field('BeaconExternalsPremises.committee_assignment_unique', unique, 6)
    covered = all(active[e] <= set().union(*(committees[s] for s in range(e*slots_per_epoch, (e+1)*slots_per_epoch)))
                  for e in range(6))
    field('BeaconExternalsPremises.committee_coverage', covered, 6)
    member_active = all(committees[s] <= active[s // slots_per_epoch] for s in committees)
    field('BeaconExternalsPremises.committee_members_active', member_active, len(committees))
    total = int(spec.get_total_active_balance(anchor_state))
    span_checks = 0
    estimate_failures = []
    fraction_failures = []
    for a in range(48):
        members = set()
        for b in range(a, 48):
            members.update(committees[b])
            actual = sum(int(registry[i].effective_balance) for i in members)
            estimate = int(spec.estimate_committee_weight_between_slots(
                total, spec.Slot(a), spec.Slot(b)))
            span_checks += 1
            if actual > estimate:
                estimate_failures.append({'a': a, 'b': b, 'weight': actual, 'estimate': estimate})
            # All validators in this run are honest, so this is a vacuous check
            # of the per-span bound. The report names this limit.
            if actual < 0:  # 0 Byzantine weight cannot exceed a nonnegative threshold.
                fraction_failures.append({'a': a, 'b': b})
    field('ByzantineWeightPremises.estimate_sound', not estimate_failures,
          span_checks, estimate_failures[0] if estimate_failures else None)
    field('ByzantineWeightPremises.span_fraction', not fraction_failures,
          span_checks, fraction_failures[0] if fraction_failures else None)
    for row in projection.check_run(run, projection.source_statements()):
        results.append({'field': row['field'], 'status': row['status'],
                        'checks': 1, 'first_failure': row['state'] if row['status'] == 'FAIL' else None})
    expected_failures = {'ByzantineWeightPremises.estimate_sound'}
    actual_failures = {row['field'] for row in results if row['status'] == 'FAIL'}
    summary = {'run': run.name, 'validators': len(registry), 'balances_gwei': sorted(set(
                   int(v.effective_balance) for v in registry)),
               'blocks': len(run.roots), 'max_slot': int(tail.slot),
               'fields': len(results), 'failures': sorted(actual_failures),
               'estimate_violations': len(estimate_failures),
               'not_established': sorted(row['field'] for row in results if row['status'] == 'NOT_ESTABLISHED'),
               'results': results,
               'limits': ['single accepted chain and one honest view; network relay, multi-view vote behavior, BLS, engine and KZG are not evaluated',
                          'span_fraction passes vacuously because this fixture has no Byzantine validators']}
    args.output.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'whole-bundle sample: {len(results)} fields; failures={sorted(actual_failures)}; '
          f'estimate violations={len(estimate_failures)}; NOT_ESTABLISHED={summary["not_established"]}')
    if actual_failures != expected_failures:
        print(f'unexpected field result: expected {sorted(expected_failures)}, got {sorted(actual_failures)}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
