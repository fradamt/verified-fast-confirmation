#!/usr/bin/env python3
"""Check code-styled Lean names and local paths in current review documents."""
from __future__ import annotations
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = [ROOT / 'README.md', ROOT / 'AGENTS.md', *sorted((ROOT / 'docs').glob('*.md'))]
LEAN = [p for lib in ('FastConfirmationModel', 'FastConfirmationStatements',
                      'FastConfirmationInternal', 'FastConfirmationProofs',
                      'FastConfirmationWitnesses', 'FastConfirmationPaper')
        for p in (ROOT / lib).rglob('*.lean')]
DECL = re.compile(r'^\s*(?:(?:private|protected|noncomputable|partial|unsafe|public|scoped|local)\s+)*'
                  r'(?:def|theorem|lemma|structure|class|inductive|abbrev|instance|opaque|'
                  r'axiom|constant)\s+([\w.₀-₉]+)', re.M)
CODE = re.compile(r'(?<!`)`([^`\n]+)`(?!`)')
IDENT = re.compile(r'[A-Za-z_][\w.₀-₉]*\Z')
known = set()
for file in LEAN:
    known.update(DECL.findall(file.read_text()))
    known.update(re.findall(r'^  ([A-Za-z_][\w₀-₉]*)\s*:', file.read_text(), re.M))
# Names in source sometimes appear with a namespace prefix. Check their final
# declared component, and require the cited qualification to appear in source.
source = '\n'.join(p.read_text() for p in LEAN)
exceptions = {'module', 'public', 'Model', 'Statements', 'Internal', 'Proofs',
              'Witnesses', 'Paper', 'Core', 'LMDGhost', 'HFC', 'Gloas', 'VALID',
              'PENDING', 'FULL', 'EMPTY', 'Nat', 'Root', 'Bool', 'List', 'Fin',
              'Lean', 'Python', 'README', 'SUMMARY', 'end', 'propext',
              'Classical.choice', 'Quot.sound'}
missing = []
checked = 0
for doc in DOCS:
    lines = doc.read_text().splitlines()
    fence = False
    for n, line in enumerate(lines, 1):
        if line.startswith('```'):
            fence = not fence
            continue
        if fence:
            continue
        for name in CODE.findall(line):
            if name == 'fradamt/consensus-specs' or name.startswith('scripts/validate.sh '):
                continue
            if name.startswith('.') and name.count('/') == 0:
                continue
            if '/' in name or name.endswith(('.lean', '.md', '.py', '.sh')):
                if name.startswith(('--', 'http')) or '/path/' in name:
                    continue
                path = (doc.parent / name).resolve()
                if not path.exists() and not (ROOT / name).exists() and not any(p.name == name.rstrip('/') for p in ROOT.rglob('*')):
                    missing.append((doc, n, name))
                else:
                    checked += 1
                continue
            if not IDENT.fullmatch(name) or name in exceptions:
                continue
            if name.startswith('fcr-') or name[0].isdigit() or name.startswith('--'):
                continue
            checked += 1
            final = name.rsplit('.', 1)[-1]
            if final not in known and name not in known and not (ROOT / (name + '.lean')).exists():
                missing.append((doc, n, name))
            elif '.' in name and name not in source and final not in known:
                missing.append((doc, n, name))
if missing:
    for doc, line, name in missing:
        print(f'{doc.relative_to(ROOT)}:{line}: unresolved `{name}`')
    raise SystemExit(1)
print(f'DOC_NAMES_OK {checked}')
