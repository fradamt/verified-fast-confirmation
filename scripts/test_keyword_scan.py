#!/usr/bin/env python3
"""Test the keyword gate, including controls with its rejection removed."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ('"--"', 'example'),
    ('"--"', 'theorem'),
    ('"--"', 'lemma'),
    ('"/-"', 'example'),
    (r'"escaped \" --"', 'example'),
    ('s!"{("--")} /-"', 'example'),
    ('s! "{("--")} /-"', 'example'),
    ('s! /- gap -/ "{("--")} /-"', 'example'),
    ('s!"{s!"{("/-")}"} --"', 'example'),
    ('s!"{( /- outer /- inner -/ -/ "--")}"', 'example'),
    ('r#"-- " /-"#', 'example'),
    ('"«example» theorem lemma"', 'example'),
    ("'\"'", 'example'),
    (r"'\''", 'example'),
    ("s!\"{('\"')}\"", 'example'),
    ('(let «--» := "/-"; «--»)', 'example'),
]


def check(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(['python3', 'scripts/check_imports.py'], cwd=root,
                          text=True, capture_output=True, timeout=120)


def rejected(result: subprocess.CompletedProcess[str], diagnostic: str) -> None:
    if result.returncode != 1 or diagnostic not in (result.stdout + result.stderr).splitlines():
        raise AssertionError(f'missing target diagnostic {diagnostic}: {result.stdout}{result.stderr}')


def accepted(result: subprocess.CompletedProcess[str]) -> None:
    if result.returncode:
        raise AssertionError(f'positive control failed: {result.stdout}{result.stderr}')


def main() -> None:
    with tempfile.TemporaryDirectory(prefix='fcr-keyword-') as name:
        root = Path(name)
        listed = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT, text=True)
        for file in filter(None, listed.split('\0')):
            target = root / file
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / file, target)
        (root / '.lake').mkdir()
        (root / '.lake/packages').symlink_to(ROOT / '.lake/packages')
        checker = root / 'scripts/check_imports.py'
        original_checker = checker.read_text()
        guard = 'if count > allowed.get(key, 0):'
        assert original_checker.count(guard) == 1
        mutant = original_checker.replace(guard, 'if False:  # removed keyword guard')
        target = root / 'FastConfirmationModel/Spec/Config.lean'
        original = target.read_text()
        # Keywords in literals, quoted identifiers, comments, and char literals
        # are data. Comments can nest. Apostrophes in names are not chars.
        positive = r'''
public def rcStringMarker : String := "--"
public def rcBlockMarker : String := "/-"
public def «example» : String := "theorem lemma example"
public def rcEscape : String := "\" -- /-"
public def rcInterp : String := s!"{("--")} {s!"{("/-")}"}"
public def rcChar : Char := '\''
public def rcBrace : Char := '{'
public def rcPrime' : String := "--"
/- example /- theorem -/ lemma -/
-- example
'''
        target.write_text(original + positive)
        accepted(check(root))
        for literal, keyword in CASES:
            declaration = ('example : True := True.intro' if keyword == 'example' else
                           f'public {keyword} rcProof : True := True.intro')
            annotation = " : String" if literal == '"--"' else ""
            target.write_text(original + f'\npublic def rcStringMarker{annotation} := {literal} {declaration}\n')
            diagnostic = f'FastConfirmationModel.Spec.Config: `{keyword}` keyword in Model or Statements'
            rejected(check(root), diagnostic)
            checker.write_text(mutant)
            try:
                result = check(root)
                accepted(result)
                try:
                    rejected(result, diagnostic)
                except AssertionError:
                    pass
                else:
                    raise AssertionError('negative test survived guard removal')
            finally:
                checker.write_text(original_checker)
    print(f'keyword tests passed: {len(CASES)} negatives; {len(CASES)} guard-removal controls; positive literals')


if __name__ == '__main__':
    main()
