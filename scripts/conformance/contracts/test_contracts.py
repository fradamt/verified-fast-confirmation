#!/usr/bin/env python3
"""Deterministic state-function contract probes for the pinned pyspec.

The default-state indexed check uses the Lean totalization convention:
Python rejection or exception maps to false. BLS is disabled through the
spec test-helper switch, so these probes do not test signatures.
Known false laws remain executable findings and do not stop other probes.
"""
from __future__ import annotations

import argparse
import json
import random
import re
import tomllib
import sys
import time
from pathlib import Path

PIN = "13f391516352f61b3ac5dcaae5be1884d104f86a"
SEED = 20260926


def setup(repo: Path):
    import subprocess
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if head != PIN:
        raise RuntimeError(f"pyspec pin mismatch: {head}")
    sys.path.insert(0, str(repo / "tests/core/pyspec"))
    from eth_consensus_specs.utils import bls
    from eth_consensus_specs.gloas import minimal as gloas
    from eth_consensus_specs.phase0 import minimal as phase0
    from eth_consensus_specs.test.helpers.genesis import create_genesis_state
    from eth_consensus_specs.test.helpers.attestations import next_slots_with_attestations
    from eth_consensus_specs.test.helpers.block import build_empty_block
    from eth_consensus_specs.test.helpers.attestations import get_valid_attestation
    from eth_consensus_specs.test.helpers.attester_slashings import get_valid_attester_slashing
    from eth_consensus_specs.test.helpers.proposer_slashings import get_valid_proposer_slashing
    from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block
    bls.bls_active = False
    for spec in (gloas, phase0):
        if not Path(spec.__file__).resolve().is_relative_to(repo.resolve()):
            raise RuntimeError(f"wrong pyspec source: {spec.__file__}")
    return (gloas, phase0, create_genesis_state, next_slots_with_attestations, build_empty_block,
            state_transition_and_sign_block, get_valid_attestation, get_valid_attester_slashing, get_valid_proposer_slashing)


def projection(st):
    return {
        "slot": int(st.slot),
        "epoch": int(st.slot) // 8,
        "justified": (int(st.current_justified_checkpoint.epoch), bytes(st.current_justified_checkpoint.root).hex()),
        "finalized": (int(st.finalized_checkpoint.epoch), bytes(st.finalized_checkpoint.root).hex()),
        "validators": [(int(v.effective_balance), bool(v.slashed), int(v.activation_epoch), int(v.exit_epoch)) for v in st.validators],
    }


def cp(c):
    return (int(c.epoch), bytes(c.root).hex())


def totalized_indexed_valid(spec, state, attestation):
    """The Lean Boolean maps every Python rejection, including an exception, to false."""
    try:
        return bool(spec.is_valid_indexed_attestation(state, attestation))
    except Exception:
        return False


def lean_statement(name: str) -> str | None:
    """Return the exact current Lean field text for a generated property."""
    here = Path(__file__).resolve().parent
    if name.startswith("m2."):
        preview = tomllib.loads((here / "m2_statements.toml").read_text())["statement"]
        field = name.removeprefix("m2.")
        if field != "process_slots_checkpoint_epoch_guarded":
            source = (here.parents[2] / "FastConfirmationStatements/Premises/FFG.lean").read_text()
            if re.search(r"(?m)^  " + re.escape(field) + r"\s*:", source):
                return lean_statement("Phase0BoundarySourceCoherence." + field)
        return preview.get(name, {}).get("lean")
    root = here.parents[2]
    inventory = tomllib.loads((here / "inventory.toml").read_text())
    row = next((x for x in inventory["field"] if x["path"] == name), None)
    if row is None:
        return None
    source = (root / "FastConfirmationStatements/Premises" / row["file"]).read_text()
    structure, field = name.split(".", 1)
    body = re.search(r"(?m)^structure " + re.escape(structure) + r"\b[\s\S]*?\bwhere\n([\s\S]*?)(?=\n(?:end|namespace|structure|/-!|section|def |abbrev |variable )|\Z)", source)
    if body is None:
        raise RuntimeError(f"Lean structure absent: {structure}")
    match = re.search(r"(?m)^  " + re.escape(field) + r"\s*:", body.group(1))
    if match is None:
        raise RuntimeError(f"Lean field absent: {name}")
    tail = body.group(1)[match.start():]
    stop = re.search(r"(?m)^  (?:[A-Za-z_][\w]*\s*:|/--)", tail[len(match.group(0)):])
    if stop:
        tail = tail[:len(match.group(0))+stop.start()]
    return tail.strip()


def run(repo: Path):
    (spec, phase0, genesis, with_attestations, build_block, sign_transition,
     get_attestation, attester_slashing, proposer_slashing) = setup(repo)
    random.seed(SEED)
    start = time.monotonic()
    results = []
    states = []
    for variant in ("empty", "voted", "low"):
        s = genesis(spec, [32 * 10**9] * 64, 32 * 10**9)
        states.append((variant + ":genesis", s.copy()))
        if variant == "empty":
            for slot in (7, 8, 15, 16, 23, 24, 31):
                if int(s.slot) < slot:
                    spec.process_slots(s, slot)
                states.append((f"{variant}:{slot}", s.copy()))
        else:
            part = None if variant == "voted" else lambda slot, index, indices: set(sorted(indices)[:max(1, len(indices)//4)])
            for target in (7, 8, 15, 16, 23, 24, 31):
                _, blocks, s = with_attestations(spec, s, target-int(s.slot), True, False, part)
                states.append((f"{variant}:{target}", s.copy()))
            if variant == "voted":
                _, blocks, s = with_attestations(spec, s, 16, True, False, part)
                states.append((f"{variant}:{int(s.slot)}", s.copy()))
    p0 = genesis(phase0, [32 * 10**9] * 64, 32 * 10**9)
    _, _, p0 = with_attestations(phase0, p0, 2 * phase0.SLOTS_PER_EPOCH - 1, True, False)
    states.append(("phase0:voted:15", p0.copy()))

    def check(name, statement, examples, predicate, known=False):
        errors = []
        count = 0
        for label, data in examples:
            count += 1
            try:
                ok, fields = predicate(data)
                if not ok:
                    errors.append({"case": label, **fields})
            except Exception as exc:
                errors.append({"case": label, "exception": f"{type(exc).__name__}: {exc}"})
        statement = lean_statement(name) or statement
        predicate.__doc__ = statement
        status = "FAIL" if errors else "PASS"
        results.append({"law": name, "status": status, "known": known, "cases": count, "counterexamples": errors[:4], "statement": statement})
        print(f"{status} {name} ({count} cases)", flush=True)

    st_samples = [(label, st) for label, st in states]
    slot_cases = []
    for label, st in st_samples:
        sp = phase0 if label.startswith("phase0") else spec
        for jump in (1, 2, 3, 4, 8, 9, 16, 24):
            target = int(st.slot) + jump
            if target > 64:
                continue
            slot_cases.append((f"{label}->{target}", (sp, st, target)))

    slot_cache = {}
    eager_cache = {}
    def slotted(data):
        sp, st, target = data
        key = (id(st), int(target))
        if key not in slot_cache:
            out = st.copy()
            sp.process_slots(out, target)
            slot_cache[key] = out
        return slot_cache[key]

    def eager(data):
        sp, st, target = data
        key = id(st)
        if key not in eager_cache:
            out = st.copy()
            sp.process_justification_and_finalization(out)
            eager_cache[key] = out
        return eager_cache[key]

    check("Phase0SourceCoherence.process_slots_current_justified",
          "(ext.process_slots st target).current_justified_checkpoint = st.current_justified_checkpoint when both slots have the same epoch",
          [(l,d) for l,d in slot_cases if int(d[1].slot)//8 == d[2]//8],
          lambda d: (cp(slotted(d).current_justified_checkpoint)==cp(d[1].current_justified_checkpoint), {"pre":projection(d[1]),"post":projection(slotted(d))}))
    check("Phase0BoundarySourceCoherence.process_slots_current_justified",
          "(ext.process_slots st target).current_justified_checkpoint = (ext.process_justification_and_finalization st).current_justified_checkpoint when target crosses an epoch boundary",
          [(l,d) for l,d in slot_cases if int(d[1].slot)//8 < d[2]//8],
          lambda d: (cp(slotted(d).current_justified_checkpoint)==cp(eager(d).current_justified_checkpoint), {"pre":projection(d[1]),"target":d[2],"post":projection(slotted(d)),"eager":projection(eager(d))}), known=True)
    check("m2.process_slots_one_boundary",
          "(ext.process_slots st target).current_justified_checkpoint = (ext.process_justification_and_finalization st).current_justified_checkpoint when target epoch = start epoch + 1",
          [(l,d) for l,d in slot_cases if int(d[1].slot)//8 + 1 == d[2]//8],
          lambda d: (cp(slotted(d).current_justified_checkpoint)==cp(eager(d).current_justified_checkpoint), {"pre":projection(d[1]),"target":d[2],"post":projection(slotted(d)),"eager":projection(eager(d))}))
    # The m2 Lean field has no active-balance guard. Build a valid Phase0
    # state shape with one active increment and a stable projected registry.
    degenerate = genesis(phase0, [32 * 10**9] * 64, 32 * 10**9)
    for index, validator in enumerate(degenerate.validators[1:], 1):
        validator.activation_epoch = phase0.FAR_FUTURE_EPOCH
        validator.activation_eligibility_epoch = phase0.FAR_FUTURE_EPOCH
        validator.effective_balance = phase0.Gwei(0)
        degenerate.balances[index] = phase0.Gwei(0)
    degenerate.validators[0].effective_balance = phase0.EFFECTIVE_BALANCE_INCREMENT
    degenerate.balances[0] = phase0.EFFECTIVE_BALANCE_INCREMENT
    degenerate.validators[0].exit_epoch = phase0.Epoch(5)
    assert int(phase0.get_total_active_balance(degenerate)) == int(phase0.EFFECTIVE_BALANCE_INCREMENT)
    degenerate_cases = [(f"phase0:one-increment:0->{target}",(phase0,degenerate,target)) for target in (24,32)]
    assert all(projection(slotted(d))["validators"] == projection(degenerate)["validators"] for _,d in degenerate_cases)
    normal_boundary = [(l,d) for l,d in slot_cases if int(d[1].slot)//8 < d[2]//8]
    def checkpoint_epoch_law(d):
        out = slotted(d)
        return (cp(out.current_justified_checkpoint)==cp(d[1].current_justified_checkpoint)
                or int(out.current_justified_checkpoint.epoch)<=int(d[1].slot)//8,
                {"pre":projection(d[1]),"target":d[2],"post":projection(out),
                 "total_active_balance":int(d[0].get_total_active_balance(d[1]))})
    check("m2.process_slots_checkpoint_epoch",
          "The exact Lean law has no active-balance guard: post checkpoint unchanged or its epoch <= start epoch",
          normal_boundary + degenerate_cases, checkpoint_epoch_law, known=True)
    check("m2.process_slots_checkpoint_epoch_guarded",
          "The same law when total active balance exceeds one increment",
          [(l,d) for l,d in normal_boundary if int(d[0].get_total_active_balance(d[1])) > int(d[0].EFFECTIVE_BALANCE_INCREMENT)],
          checkpoint_epoch_law)
    same_target=[]
    for l,d in slot_cases:
        sp,st,target=d
        if int(st.slot)//8 < target//8 and target%8==0 and target+1<=64:
            same_target.append((l,(sp,st,target,target+1)))
    check("m2.process_slots_same_target_epoch",
          "(ext.process_slots st target).current_justified_checkpoint = (ext.process_slots st target').current_justified_checkpoint when target epochs agree",
          same_target,
          lambda d:(cp(slotted(d[:3]).current_justified_checkpoint)==cp(slotted((d[0],d[1],d[3])).current_justified_checkpoint), {"pre":projection(d[1]),"targets":[d[2],d[3]],"first":projection(slotted(d[:3])),"second":projection(slotted((d[0],d[1],d[3])))}))

    check("BeaconExternalsPremises.process_slots_slot",
          "st.slot < s -> (ext.process_slots st s).slot = s",
          slot_cases, lambda d:(int(slotted(d).slot)==d[2],{"pre":projection(d[1]),"target":d[2],"post":projection(slotted(d))}))
    # These accepted epoch transitions change validator records. They are
    # outside RegistryStateInHorizon when the execution uses a static anchor.
    registry_changes=[]
    for mode in ("activation", "exit", "hysteresis"):
        pre=genesis(spec, [32 * 10**9] * 64, 32 * 10**9)
        spec.process_slots(pre, 7)
        validator=pre.validators[0]
        if mode == "activation":
            validator.activation_epoch=spec.FAR_FUTURE_EPOCH
            validator.activation_eligibility_epoch=spec.Epoch(0)
        elif mode == "exit":
            validator.effective_balance=spec.Gwei(16 * 10**9)
            pre.balances[0]=spec.Gwei(16 * 10**9)
        else:
            pre.balances[0]=spec.Gwei(30 * 10**9)
        registry_changes.append((f"gloas:{mode}:7->8",(spec,pre,8)))
    check("RegistryScope.excludes_epoch_registry_changes",
          "Epoch processing can set activation and exit epochs or update effective balance; such runs do not meet the static execution scope",
          registry_changes,
          lambda d:(projection(slotted(d))["validators"]!=projection(d[1])["validators"],
                    {"pre":projection(d[1]),"target":d[2],"post":projection(slotted(d))}))
    check("BeaconExternalsPremises.pjf_checkpoint_epoch",
          "(ext.process_justification_and_finalization st).current_justified_checkpoint.epoch <= compute_epoch_at_slot cfg st.slot",
          st_samples, lambda st:(int((lambda x:(spec if st.__class__ is states[0][1].__class__ else phase0).process_justification_and_finalization(x) or x)(st.copy()).current_justified_checkpoint.epoch)<=int(st.slot)//8,{"pre":projection(st)}))

    transition_cases=[]
    for label,st in st_samples:
        sp=phase0 if label.startswith("phase0") else spec
        if int(st.slot)>47: continue
        for jump in (1, 8, 16):
            target=int(st.slot)+jump
            if target>56: continue
            try:
                pre=st.copy()
                block=build_block(sp,pre,slot=target)
                post=pre.copy()
                signed=sign_transition(sp,post,block)
                actual=pre.copy()
                sp.state_transition(actual,signed)
                assert actual == post
                transition_cases.append((f"{label}->{target}",(sp,pre,signed,actual)))
            except Exception as exc:
                results.append({"law":"fixture.block","status":"FAIL","known":False,"cases":1,"counterexamples":[{"case":label,"exception":repr(exc)}]})
    # A real Gloas block with both slashing types changes validator records.
    try:
        pre=states[0][1].copy()
        at=pre.copy()
        spec.process_slots(at,1)
        block=build_block(spec,pre,slot=1)
        att=attester_slashing(spec,at,slot=0)
        excluded=set(int(i) for i in att.attestation_1.attesting_indices)
        proposer=next(i for i in range(len(pre.validators)) if i not in excluded)
        block.body.attester_slashings.append(att)
        block.body.proposer_slashings.append(proposer_slashing(spec,at,slashed_index=proposer,slot=0))
        post=pre.copy()
        signed=sign_transition(spec,post,block)
        actual=pre.copy()
        spec.state_transition(actual,signed)
        assert actual == post
        transition_cases.append(("gloas:both-slashings:0->1",(spec,pre,signed,actual)))
        states.append(("gloas:slashed:1",post.copy()))
    except Exception as exc:
        results.append({"law":"fixture.slashing_block","status":"FAIL","known":False,"cases":1,
                        "counterexamples":[{"exception":repr(exc)}]})
    check("BeaconExternalsPremises.state_transition_slot",
          "ext.state_transition st b = some st' -> st'.slot = b.message.slot",
          transition_cases,lambda d:(int(d[3].slot)==int(d[2].message.slot),{"pre":projection(d[1]),"post":projection(d[3])}))
    check("RegistryScope.excludes_slashing_inclusion",
          "A successful block with proposer and attester slashings changes the registry, so an execution containing it is outside the static scope",
          [(l,d) for l,d in transition_cases if l=="gloas:both-slashings:0->1"],
          lambda d:(projection(d[3])["validators"]!=projection(d[1])["validators"],
                    {"pre":projection(d[1]),"post":projection(d[3])}))
    check("BeaconExternalsPremises.state_transition_pre_slot_lt",
          "ext.state_transition st b = some st' -> st.slot < b.message.slot",
          transition_cases,lambda d:(int(d[1].slot)<int(d[2].message.slot),{"pre":projection(d[1]),"post":projection(d[3])}))
    check("BeaconExternalsPremises.state_transition_checkpoint_epoch",
          "ext.state_transition st b = some st' -> st'.current_justified_checkpoint.epoch <= block epoch and st'.finalized_checkpoint.epoch <= block epoch",
          transition_cases,lambda d:(int(d[3].current_justified_checkpoint.epoch)<=int(d[2].message.slot)//8 and int(d[3].finalized_checkpoint.epoch)<=int(d[2].message.slot)//8,{"pre":projection(d[1]),"post":projection(d[3])}))
    check("Phase0SourceCoherence.state_transition_current_justified",
          "ext.state_transition pre sb = some post -> same epoch -> post.current_justified_checkpoint = pre.current_justified_checkpoint",
          [(l,d) for l,d in transition_cases if int(d[1].slot)//8==int(d[2].message.slot)//8],
          lambda d:(cp(d[3].current_justified_checkpoint)==cp(d[1].current_justified_checkpoint),{"pre":projection(d[1]),"post":projection(d[3])}))
    check("Phase0BoundarySourceCoherence.state_transition_current_justified",
          "ext.state_transition pre sb = some post -> earlier epoch -> post.current_justified_checkpoint = (ext.process_justification_and_finalization pre).current_justified_checkpoint",
          [(l,d) for l,d in transition_cases if int(d[1].slot)//8<int(d[2].message.slot)//8],
          lambda d:(cp(d[3].current_justified_checkpoint)==cp(eager((d[0],d[1],int(d[2].message.slot))).current_justified_checkpoint),{"pre":projection(d[1]),"post":projection(d[3]),"eager":projection(eager((d[0],d[1],int(d[2].message.slot))))}),known=True)
    check("m2.state_transition_process_slots",
          "ext.state_transition pre sb = some post -> earlier epoch -> post.current_justified_checkpoint = (ext.process_slots pre sb.message.slot).current_justified_checkpoint",
          [(l,d) for l,d in transition_cases if int(d[1].slot)//8<int(d[2].message.slot)//8],
          lambda d:(cp(d[3].current_justified_checkpoint)==cp(slotted((d[0],d[1],int(d[2].message.slot))).current_justified_checkpoint),{"pre":projection(d[1]),"post":projection(d[3]),"slots":projection(slotted((d[0],d[1],int(d[2].message.slot))))}))
    check("NextSlotSafetyPremises.finalization_delay",
          "finalized = anchor or finalized.epoch + 2 <= block epoch for accepted blocks",
          transition_cases,lambda d:(int(d[3].finalized_checkpoint.epoch)==0 or int(d[3].finalized_checkpoint.epoch)+2<=int(d[2].message.slot)//8,{"pre":projection(d[1]),"post":projection(d[3])}))
    # Registry and committee properties use the exact spec assignment on a
    # generated state. A slot committee is the union of all committee indices.
    committee_cases = [(label, st, sp, epoch) for label, st in st_samples
                       for sp in [phase0 if label.startswith("phase0") else spec]
                       for epoch in range(4) if epoch <= int(st.slot)//8 + 1]
    def assignment(data):
        label, st, sp, epoch = data
        per_slot = {}
        for slot in range(epoch*8, (epoch+1)*8):
            per_slot[slot] = set()
            for index in range(int(sp.get_committee_count_per_slot(st, sp.Epoch(epoch)))):
                per_slot[slot].update(int(i) for i in sp.get_beacon_committee(st, sp.Slot(slot), sp.CommitteeIndex(index)))
        return per_slot
    check("BeaconExternalsPremises.committee_assignment_unique",
          "i in E.committee s and i in E.committee s' and epoch(s)=epoch(s') -> s=s'",
          [(f"{d[0]}:epoch{d[3]}",d) for d in committee_cases],
          lambda d:(len([i for members in assignment(d).values() for i in members])==len(set().union(*assignment(d).values())),
                    {"slot":int(d[1].slot),"epoch":d[3],"committees":{str(k):sorted(v) for k,v in assignment(d).items()}}))
    check("BeaconExternalsPremises.committee_coverage",
          "active registry validator i in epoch e -> exists in-horizon committee slot s of epoch e with i in E.committee s",
          [(f"{d[0]}:epoch{d[3]}",d) for d in committee_cases],
          lambda d:(set(int(i) for i in d[2].get_active_validator_indices(d[1],d[2].Epoch(d[3]))) <= set().union(*assignment(d).values()),
                    {"slot":int(d[1].slot),"epoch":d[3],"assigned":sorted(set().union(*assignment(d).values()))}))
    check("BeaconExternalsPremises.committee_members_active",
          "i in E.committee s -> is_active_validator registry[i] (epoch(s)) = true",
          [(f"{d[0]}:epoch{d[3]}",d) for d in committee_cases],
          lambda d:(set().union(*assignment(d).values()) <= set(int(i) for i in d[2].get_active_validator_indices(d[1],d[2].Epoch(d[3]))),
                    {"slot":int(d[1].slot),"epoch":d[3],"assigned":sorted(set().union(*assignment(d).values()))}))
    check("ByzantineWeightPremises.effective_balance_quantized",
          "cfg.effective_balance_increment divides E.weight_of i",
          st_samples,lambda st:(all(int(v.effective_balance)%int(spec.EFFECTIVE_BALANCE_INCREMENT)==0 for v in st.validators),{"slot":int(st.slot),"balances":[int(v.effective_balance) for v in st.validators]}))
    default=spec.BeaconState()
    indexed=spec.IndexedAttestation(attesting_indices=spec.AttestingIndices(data=[0]))
    check("BeaconExternalsPremises.valid_attestation_default",
          "ext.is_valid_indexed_attestation (default : BeaconState Root) a = false for every a",
          [("gloas-default-canonical-index",(default,indexed))],
          lambda d:(totalized_indexed_valid(spec,d[0],d[1]) is False,
                    {"indices":[int(i) for i in d[1].attesting_indices]}))
    # The Python indexed check does not query the slot committee. With BLS
    # switched off, an off-committee canonical index passes its Boolean check.
    off_state=states[0][1]
    committee=set()
    for committee_index in range(int(spec.get_committee_count_per_slot(off_state,spec.Epoch(0)))):
        committee.update(int(i) for i in spec.get_beacon_committee(off_state,spec.Slot(0),spec.CommitteeIndex(committee_index)))
    outsider=next(i for i in range(len(off_state.validators)) if i not in committee)
    attestation=get_attestation(spec,off_state,slot=0)
    off_attestation=spec.IndexedAttestation(
        attesting_indices=spec.AttestingIndices(data=[outsider]),data=attestation.data)
    check("IndexedAttestation.off_committee_valid",
          "The indexed Boolean can accept an off-committee signer; slashing evidence uses this path without on_attestation",
          [("gloas:genesis:offcommittee-index",(off_state,off_attestation,committee,outsider))],
          lambda d:(spec.is_valid_indexed_attestation(d[0],d[1]) and d[3] not in d[2],
                    {"slot":int(d[1].data.slot),"indices":[int(i) for i in d[1].attesting_indices],
                     "committee":sorted(d[2]),"valid":spec.is_valid_indexed_attestation(d[0],d[1])}))
    def offcommittee_slashing(d):
        state, outside, members = d
        signed_state=state.copy()
        spec.process_slots(signed_state, 1)
        evidence=attester_slashing(spec, signed_state, slot=0)
        for indexed_attestation in (evidence.attestation_1, evidence.attestation_2):
            indexed_attestation.attesting_indices=spec.AttestingIndices(data=[outside])
        anchor_state=state.copy()
        anchor_block=spec.BeaconBlock(slot=anchor_state.slot)
        anchor_state.latest_block_header.body_root=spec.hash_tree_root(anchor_block.body)
        anchor_block.state_root=spec.hash_tree_root(anchor_state)
        store=spec.get_forkchoice_store(anchor_state, anchor_block)
        spec.on_attester_slashing(store, evidence)
        return outside in store.equivocating_indices and outside not in members, {
            "outsider":outside,"committee":sorted(members),
            "equivocating":sorted(int(i) for i in store.equivocating_indices)}
    check("IndexedAttestation.off_committee_slashing",
          "Python on_attester_slashing accepts off-committee indexed evidence and only adds the signer to equivocating_indices",
          [("gloas:genesis:offcommittee-slashing",(off_state,outsider,committee))],
          offcommittee_slashing)
    # The indexed-attestation Boolean is checked before and after an actual
    # empty-slot transition. BLS is disabled by the test helper switch.
    canonical=spec.IndexedAttestation(attesting_indices=spec.AttestingIndices(data=[0]))
    empty_indices=spec.IndexedAttestation()
    validity_cases=[]
    for label,st in [("genesis",states[0][1]),("voted:31",next(st for name,st in st_samples if name=="voted:31"))]:
        for indexed in (canonical,empty_indices):
            for jump in (1,8,16):
                validity_cases.append((f"{label}:{len(indexed.attesting_indices)}-indices:+{jump}",(st,indexed,int(st.slot)+jump)))
    def validity_preserved(d):
        before=spec.is_valid_indexed_attestation(d[0],d[1])
        after=slotted((spec,d[0],d[2]))
        result=spec.is_valid_indexed_attestation(after,d[1])
        return before == result,{"pre":projection(d[0]),"post":projection(after),"indices":[int(i) for i in d[1].attesting_indices],"before":before,"after":result}
    check("BeaconExternalsPremises.process_slots_attestation_valid",
          "ext.is_valid_indexed_attestation (ext.process_slots state slot) a = ext.is_valid_indexed_attestation state a",
          validity_cases,validity_preserved)
    # The genesis state is an accepted anchor with a stub checkpoint root.
    # The store uses the hash of the anchor block as its checkpoint root.
    anchor_cases=[]
    later=genesis(spec,[32*10**9]*64,32*10**9)
    _,later_blocks,later=with_attestations(spec,later,3*spec.SLOTS_PER_EPOCH,True,False)
    for label,st,original_block in [("genesis",states[0][1].copy(),None),
                                    ("checkpoint-sync-like",later,later_blocks[-1].message)]:
        if original_block is None:
            block=spec.BeaconBlock(slot=st.slot)
            st.latest_block_header.body_root=spec.hash_tree_root(block.body)
            block.state_root=spec.hash_tree_root(st)
        else:
            block=original_block
        store=spec.get_forkchoice_store(st,block)
        root=spec.hash_tree_root(block)
        anchor_cases.append((label,(st,block,store,root)))
    check("NextSlotSafetyPremises.anchor_boundary",
          "(E.genesis_store.blocks anchor.root).slot <= compute_start_slot_at_epoch cfg anchor.epoch",
          anchor_cases,lambda d:(int(d[1].slot)<=int(d[2].justified_checkpoint.epoch)*8,
                                 {"anchor_slot":int(d[1].slot),"anchor_epoch":int(d[2].justified_checkpoint.epoch)}))
    check("NextSlotSafetyPremises.anchor_eq",
          "ffg_interpretation.anchor = E.genesis_store.justified_checkpoint",
          anchor_cases,lambda d:(cp(d[2].justified_checkpoint)==(int(d[0].slot)//8,bytes(d[3]).hex()),
                                 {"state":projection(d[0]),"store_checkpoint":cp(d[2].justified_checkpoint)}))
    check("FFGStateReadAgreement.genesis_unrealized_justification",
          "E.genesis_store.unrealized_justifications r = S.unrealized_justified r, together with genesis_gu fixing S.unrealized_justified to eager PJF",
          anchor_cases,lambda d:(cp(d[2].unrealized_justifications[d[3]])==cp(eager((spec,d[0],int(d[0].slot))).current_justified_checkpoint),
                                 {"state":projection(d[0]),"store_unrealized":cp(d[2].unrealized_justifications[d[3]]),
                                  "eager":projection(eager((spec,d[0],int(d[0].slot))))}),known=True)
    # Accept a valid child through the Gloas handler, then read the actual
    # per-root unrealized checkpoint written by compute_pulled_up_tip.
    accepted=[]
    st,anchor,store,root=anchor_cases[0][1]
    child=build_block(spec,st,slot=1)
    post=st.copy()
    signed=sign_transition(spec,post,child)
    spec.on_tick(store,int(st.genesis_time+spec.config.SLOT_DURATION_MS//1000))
    spec.on_block(store,signed)
    child_root=spec.hash_tree_root(signed.message)
    accepted.append(("genesis-child",(store,child_root,post)))
    check("FFGStateReadAgreement.transition_gu",
          "(ext.process_justification_and_finalization (t.postStore.block_states t.signedBlock.root)).current_justified_checkpoint = S.unrealized_justified t.signedBlock.root",
          accepted,lambda d:(cp(d[0].unrealized_justifications[d[1]])==cp(eager((spec,d[0].block_states[d[1]],int(d[2].slot))).current_justified_checkpoint),
                             {"post":projection(d[0].block_states[d[1]]),"store_unrealized":cp(d[0].unrealized_justifications[d[1]])}))
    check("FFGStateReadAgreement.transition_gj",
          "(t.postStore.block_states t.signedBlock.root).current_justified_checkpoint = S.realized_justified t.signedBlock.root",
          accepted,lambda d:(cp(d[0].block_states[d[1]].current_justified_checkpoint)==cp(d[2].current_justified_checkpoint),
                             {"store":projection(d[0].block_states[d[1]]),"transition":projection(d[2])}))
    check("FFGStateReadAgreement.transition_gf",
          "(t.postStore.block_states t.signedBlock.root).finalized_checkpoint = S.realized_finalized t.signedBlock.root",
          accepted,lambda d:(cp(d[0].block_states[d[1]].finalized_checkpoint)==cp(d[2].finalized_checkpoint),
                             {"store":projection(d[0].block_states[d[1]]),"transition":projection(d[2])}))
    def anchor_or_before(d):
        store,root,post=d
        j=store.block_states[root].current_justified_checkpoint
        anchor=store.justified_checkpoint
        epoch=int(store.blocks[root].slot)//8
        return cp(j)==cp(anchor) or int(j.epoch)<epoch,{
            "block_slot":int(store.blocks[root].slot),"block_epoch":epoch,
            "justified":cp(j),"anchor":cp(anchor)}
    check("AcceptedBlockFFGState.realized_justified_anchor_or_before",
          "realized_justified r = anchor or (realized_justified r).epoch < compute_epoch_at_slot cfg b.slot",
          accepted,anchor_or_before,known=True)
    check("AcceptedBlockFFGState.realized_finalized_epoch_le_realized_justified",
          "(realized_finalized r).epoch <= (realized_justified r).epoch",
          accepted,lambda d:(int(d[0].block_states[d[1]].finalized_checkpoint.epoch)<=int(d[0].block_states[d[1]].current_justified_checkpoint.epoch),
                             {"post":projection(d[0].block_states[d[1]])}))
    def unrealized_epochs(d):
        out=eager((spec,d[0].block_states[d[1]],int(d[2].slot)))
        return int(out.finalized_checkpoint.epoch)<=int(out.current_justified_checkpoint.epoch),{"eager":projection(out)}
    check("AcceptedBlockFFGState.unrealized_finalized_epoch_le_unrealized_justified",
          "(unrealized_finalized r).epoch <= (unrealized_justified r).epoch",
          accepted,unrealized_epochs)
    checkpoint_cases=[]
    for label,(state,anchor,store,root) in anchor_cases:
        for block_root in list(store.blocks):
            e0=int(store.justified_checkpoint.epoch)
            for source_epoch in range(e0,e0+3):
                for target_epoch in range(source_epoch,e0+3):
                    checkpoint_cases.append((f"{label}:{bytes(block_root).hex()[:8]}:{source_epoch}:{target_epoch}",
                                             (store,block_root,source_epoch,target_epoch)))
    def C(store,root,epoch):
        return spec.get_checkpoint_for_block(store,root,spec.Epoch(epoch))
    check("AcceptedBlockFFGState.checkpoint_epoch",
          "(checkpoint_at_epoch r e).epoch = e",
          checkpoint_cases,lambda d:(int(C(d[0],d[1],d[2]).epoch)==d[2],
                                     {"source_epoch":d[2],"checkpoint":cp(C(d[0],d[1],d[2]))}))
    check("EpochCheckpointProjectionLaws.checkpoint_root_accepted",
          "Accepted r -> anchor.epoch <= e -> Accepted (C r e).root",
          checkpoint_cases,lambda d:(C(d[0],d[1],d[2]).root in d[0].blocks,
                                     {"source_epoch":d[2],"checkpoint":cp(C(d[0],d[1],d[2]))}))
    check("EpochCheckpointProjectionLaws.checkpoint_comp",
          "C (C r targetEpoch).root sourceEpoch = C r sourceEpoch when anchor.epoch <= sourceEpoch <= targetEpoch",
          checkpoint_cases,lambda d:(cp(C(d[0],C(d[0],d[1],d[3]).root,d[2]))==cp(C(d[0],d[1],d[2])),
                                     {"source_epoch":d[2],"target_epoch":d[3],"checkpoint":cp(C(d[0],d[1],d[2]))}))

    elapsed=time.monotonic()-start
    fixture_summary = {label: {"slot":int(st.slot),
                               "justified_epoch":int(st.current_justified_checkpoint.epoch),
                               "finalized_epoch":int(st.finalized_checkpoint.epoch)}
                       for label,st in st_samples}
    return {"pin":PIN,"seed":SEED,"bls_active":False,"runtime_seconds":round(elapsed,3),
            "fixtures":fixture_summary,"results":results}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--repo",type=Path,required=True)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    data=run(args.repo)
    if args.output:
        args.output.write_text(json.dumps(data,indent=2)+"\n")
    failures=[x for x in data["results"] if x["status"]=="FAIL" and not x.get("known")]
    print(f"contracts: {len(data['results'])} laws; {len(failures)} new failures; {data['runtime_seconds']} s",flush=True)
    return bool(failures)


if __name__=="__main__":
    raise SystemExit(main())
