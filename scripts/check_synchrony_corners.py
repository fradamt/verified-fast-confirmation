#!/usr/bin/env python3
"""Check the reviewed cutoff contracts and reject legacy relay corners."""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
SYNC = ROOT / "FastConfirmationStatements/Premises/Synchrony.lean"


def lean_code(text):
    """Remove nested Lean comments and strings before checking source shapes."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def contracts(text):
    code = lean_code(text)
    matches = list(re.finditer(r"(?m)^(?:def|structure)\s+(\w+)", code))
    return {m[1]: re.sub(r"\s+", "", code[m.start():matches[i + 1].start()
            if i + 1 < len(matches) else len(code)]) for i, m in enumerate(matches)}


def check(text):
    code = lean_code(text)
    flat = re.sub(r"\s+", "", code)
    problems = []
    def require(ok, message):
        if not ok:
            problems.append(message)
    require(not re.search(r"\bblock_relay\s*:", code), "legacy block_relay field")
    require("slot_atcfgn+1≤E.slot_atcfg(m+1)" not in flat,
            "receiver predecessor corner")
    require(not re.search(r"E\.store\s+cfg\s+ext\s+w\s+\(?n\b", code),
            "same-second cross-node store")
    ds = contracts(text)
    for name in ("DeadlineBlockRelay", "DeadlineEnvelopeDelivery",
                 "DeadlineDataAvailabilityRelay", "DeadlineAttesterSlashingRelay",
                 "DeadlineBoundaryBlockPrefix"):
        d = ds.get(name, "")
        require(bool(d), f"missing {name}")
        require("n≤E.slot_startcfg(E.slot_atcfgn)+get_attestation_due_mscfg/1000→" in d,
                f"{name}: missing source cutoff")
        if name == "DeadlineBoundaryBlockPrefix":
            require("letboundary:=E.slot_startcfg(E.slot_atcfgn+1)" in d
                    and "n<boundary→" in d, f"{name}: missing distinct boundary")
        else:
            require("E.slot_startcfg(E.slot_atcfgn+1)≤m→n<m→" in d,
                    f"{name}: missing later receiver gate")
    for name in ("DeadlineBlockRelay", "DeadlineEnvelopeDelivery"):
        require("PermanentBlockExclusioncfgextEvnrw(E.slot_startcfg(E.slot_atcfgn+1)-1)"
                in ds.get(name, ""), f"{name}: exemption must precede tick")
    require("PermanentBlockExclusioncfgextEvnrw(boundary-1)" in
            ds.get("DeadlineBoundaryBlockPrefix", ""), "block prefix: tick-time exemption")
    require("PermanentBlockExclusion" not in ds.get("DeadlineAttesterSlashingRelay", ""),
            "evidence exclusion is not permitted")
    envelope = ds.get("DeadlineEnvelopeDelivery", "")
    require("pre=before++Event.execution_payload_envelopesignedreceiverObservation::middle"
            in envelope, "envelope must precede boundary vote")
    for name in ("Synchrony", "NextSlotSynchronyPremises"):
        d = ds.get(name, "")
        require("deadline_block_relay:DeadlineBlockRelaycfgextE" in d,
                f"{name}: wrong block relay type")
        require("attester_slashing_relay:DeadlineAttesterSlashingRelaycfgextE" in d,
                f"{name}: wrong evidence relay type")
        require("boundary_block_prefix:DeadlineBoundaryBlockPrefixcfgextE" in d,
                f"{name}: wrong block-prefix type")
        require("n≤E.slot_startcfgs+get_attestation_due_mscfg/1000→" in d,
                f"{name}: missing vote cutoff")
        require("0<delay_ms∧" in d, f"{name}: missing positive delay")
        require("get_attestation_due_mscfg+delay_ms<cfg.slot_duration_ms" in d,
                f"{name}: missing strict delay bound")
    next_slot = ds.get("NextSlotSynchronyPremises", "")
    require("envelope_delivery:DeadlineEnvelopeDeliverycfgextE" in next_slot,
            "NextSlotSynchronyPremises: wrong envelope relay type")
    require("data_availability_relay:DeadlineDataAvailabilityRelaycfgextE" in next_slot,
            "NextSlotSynchronyPremises: wrong data relay type")
    lookahead = ds.get("HorizonVoteDeliveryLookahead", "")
    require("n≤E.slot_startcfgs+get_attestation_due_mscfg/1000→" in lookahead,
            "lookahead: missing vote cutoff")
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    text = SYNC.read_text()
    failures = check(text)
    for library in ("FastConfirmationInternal", "FastConfirmationProofs",
                    "FastConfirmationWitnesses"):
        for path in (ROOT / library).rglob("*.lean"):
            if re.search(r"\.block_relay\b", lean_code(path.read_text())):
                failures.append(f"legacy projection: {path.relative_to(ROOT)}")
    if failures:
        raise SystemExit("\n".join(failures))
    if args.self_test:
        mutants = [
            text.replace("n < m →", "n ≤ m →", 1),
            text.replace("n ≤ E.slot_start cfg (E.slot_at cfg n) +", "n ≤ n +", 1),
            text.replace("(E.store cfg ext w m).block_roots", "(E.store cfg ext w n).block_roots", 1),
            text.replace("(E.slot_start cfg (E.slot_at cfg n + 1) - 1)",
                         "(E.slot_start cfg (E.slot_at cfg n + 1))", 1),
            text + "\nstructure Bad where\n  block_relay : True\n",
            text.replace("pre = before ++", "pre = middle ++", 1),
        ]
        for i, mutant in enumerate(mutants, 1):
            if mutant == text or not check(mutant):
                raise SystemExit(f"self-test {i} failed to reject a corner")
        print(f"synchrony corner self-test passed ({len(mutants)} rejected mutations)")
    print("synchrony corner check passed (five cutoff contracts, no legacy projections)")


if __name__ == "__main__":
    main()
