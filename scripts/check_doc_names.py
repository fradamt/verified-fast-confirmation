#!/usr/bin/env python3
"""Check review document names and Lean source comment file references."""
from __future__ import annotations
import re
import subprocess
from pathlib import Path
from check_imports import without_comments

ROOT = Path(__file__).resolve().parent.parent
DOCS = [ROOT / 'README.md', ROOT / 'AGENTS.md', *sorted((ROOT / 'docs').glob('*.md'))]
LEAN = [p for lib in ('FastConfirmationModel', 'FastConfirmationStatements',
                      'FastConfirmationInternal', 'FastConfirmationProofs',
                      'FastConfirmationWitnesses')
        for p in (ROOT / lib).rglob('*.lean')]
DECL = re.compile(r'^\s*(?:(?:private|protected|noncomputable|partial|unsafe|public|scoped|local)\s+)*'
                  r'(?:def|theorem|lemma|structure|class|inductive|abbrev|instance|opaque|'
                  r'axiom|constant)\s+([\w.₀-₉]+)', re.M)
# Paths resolve against tracked files only, so an untracked or ignored local
# file cannot hide a reference that a clean checkout lacks.
TRACKED = set(subprocess.run(['git', 'ls-files', '-z'], cwd=ROOT, check=True,
                             capture_output=True, text=True).stdout.split('\0')) - {''}
TRACKED_DIRS = {parent.as_posix() for name in TRACKED for parent in Path(name).parents} - {'.'}
TRACKED_NAMES = {Path(name).name for name in TRACKED | TRACKED_DIRS}


def tracked(path: Path) -> bool:
    try:
        rel = path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return False
    return rel in TRACKED or rel in TRACKED_DIRS


CODE = re.compile(r'(?<!`)`([^`\n]+)`(?!`)')
IDENT = re.compile(r'[A-Za-z_][\w.₀-₉]*\Z')
for doc in DOCS:
    fence_open = False
    for line_number, line in enumerate(doc.read_text().splitlines(), 1):
        if "```" in line and not line.startswith("```"):
            raise SystemExit(f"{doc.relative_to(ROOT)}:{line_number}: fence must have its own line")
        if line.startswith("```"):
            fence_open = not fence_open
    if fence_open:
        raise SystemExit(f"{doc.relative_to(ROOT)}: unclosed fence")

known = set()
qualified = set()
for file in LEAN:
    scope: list[tuple[str, str]] = []
    structure = None
    for line in without_comments(file.read_text()).splitlines():
        opening = re.match(r'^\s*(namespace|section)\s+([\w.₀-₉]+)', line)
        if opening:
            scope.append((opening.group(1), opening.group(2)))
            continue
        if re.match(r'^\s*end(?:\s+[\w.₀-₉]+)?\s*$', line):
            if scope:
                scope.pop()
            structure = None
            continue
        namespace = '.'.join(name for kind, name in scope if kind == 'namespace')
        match = DECL.match(line)
        if match:
            name = match.group(1)
            full = f'{namespace}.{name}' if namespace else name
            qualified.add(full)
            known.add(name.rsplit('.', 1)[-1])
            structure = full if re.search(r'\b(?:structure|class)\s+' + re.escape(name), line) else None
            continue
        field = re.match(r'^\s{2,}([A-Za-z_][\w₀-₉]*)\s*:', line)
        if field and structure:
            known.add(field.group(1))
            qualified.add(f'{structure}.{field.group(1)}')
exceptions = {'module', 'public', 'Model', 'Statements', 'Internal', 'Proofs',
              'Witnesses', 'Gloas', 'VALID',
              'PENDING', 'FULL', 'EMPTY', 'Nat', 'Root', 'Bool', 'List', 'Fin',
              'Lean', 'Python', 'README', 'SUMMARY', 'end', 'propext',
              'Classical.choice', 'Quot.sound'}
# These are expressions or Python spec fields, not Lean declaration names.
exceptions.update({'E.committee', 'BeaconBlockBody.attestations', 'store.payloads'})
missing = []
checked = 0
for doc in DOCS:
    lines = doc.read_text().splitlines()
    fence = False
    for n, line in enumerate(lines, 1):
        if line.startswith('```'):
            fence = not fence
            continue
        if fence and not ('│' in line or (line.lstrip().startswith('|') and '`' in line)):
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
                if not tracked(path) and not tracked(ROOT / name) and name.rstrip('/') not in TRACKED_NAMES:
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
            if final not in known and name not in known and not tracked(ROOT / (name + '.lean')):
                missing.append((doc, n, name))
            elif '.' in name and not any(full == name or full.endswith('.' + name)
                                             for full in qualified):
                missing.append((doc, n, name))
if missing:
    for doc, line, name in missing:
        print(f'{doc.relative_to(ROOT)}:{line}: unresolved `{name}`')
    raise SystemExit(1)

# A path in a Lean comment can be relative to the file, relative to the
# repository, or a shortened suffix. A bare file name must exist somewhere.
COMMENT_FILE = re.compile(r'(?<![\w./-])([A-Za-z_][\w./-]*\.lean)')
all_lean = [*LEAN, *sorted((ROOT / 'scripts').rglob('*.lean'))]
relative_lean = [p.relative_to(ROOT).as_posix() for p in all_lean]

def comments(text: str):
    pos = 0
    while pos < len(text):
        if text.startswith('--', pos):
            end = text.find('\n', pos)
            if end < 0:
                end = len(text)
            yield pos, text[pos:end]
            pos = end
        elif text.startswith('/-', pos):
            start = pos
            depth = 1
            pos += 2
            while pos < len(text) and depth:
                if text.startswith('/-', pos):
                    depth += 1
                    pos += 2
                elif text.startswith('-/', pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            yield start, text[start:pos]
        else:
            pos += 1

missing_comments = []
for file in all_lean:
    source_text = file.read_text()
    for start, comment in comments(source_text):
        for match in COMMENT_FILE.finditer(comment):
            name = match.group(1)
            if not any(path == name or path.endswith('/' + name)
                       for path in relative_lean):
                line = source_text.count('\n', 0, start + match.start()) + 1
                missing_comments.append((file, line, name))
if missing_comments:
    for file, line, name in missing_comments:
        print(f'{file.relative_to(ROOT)}:{line}: unresolved Lean file {name}')
    raise SystemExit(1)
print(f'DOC_NAMES_OK {checked}')
