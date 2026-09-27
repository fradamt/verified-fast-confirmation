#!/usr/bin/env python3
"""Keep the trust audit and statement fingerprint on the same witness set."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def names(path: str) -> list[str]:
    text = (ROOT / path).read_text()
    block = text.split('private def publicWitnesses', 1)[1].split(']', 1)[0]
    return re.findall(r'``([A-Za-z0-9_.]+)', block)

audit = names('scripts/Audit.lean')
shape = names('scripts/ReviewSurfaceShape.lean')
if not audit or audit != shape or len(audit) != len(set(audit)):
    raise SystemExit('public witness lists differ or contain duplicates')
print(f'public witness lists agree: {len(audit)} names')
