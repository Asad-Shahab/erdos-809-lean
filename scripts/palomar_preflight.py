#!/usr/bin/env python3
"""Conservative source and packaging checks, not a replacement for Comparator."""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess

from port_modules import skip_layout

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def code_only(text: str) -> str:
    result = []
    pos = 0
    while pos < len(text):
        if text.startswith('--', pos) or text.startswith('/-', pos):
            end = skip_layout(text, pos)
            result.append(' ' + '\n' * text[pos:end].count('\n'))
            pos = end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == '\\':
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
            result.append(' ')
        else:
            result.append(text[pos])
            pos += 1
    return ''.join(result)


def main() -> None:
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    errors = []
    lean_count = 0
    maximum = (0, '')
    for name in filter(None, names):
        path = ROOT / name
        if any(part in {'.git', '.lake'} for part in path.relative_to(ROOT).parts):
            continue
        if path.suffix in {'.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace'}:
            errors.append(f'{name}: compiled artifact in submitted source')
        if path.suffix != '.lean':
            continue
        if path.is_symlink():
            errors.append(f'{name}: Lean symlink is not permitted')
            continue
        text = path.read_text(encoding='utf-8')
        lines = len(text.splitlines())
        lean_count += 1
        maximum = max(maximum, (lines, name))
        if lines > 10000:
            errors.append(f'{name}: {lines} lines exceeds 10000')
        code = code_only(text)
        if path.name != 'lakefile.lean' and not re.match(r'\s*module\b', code):
            errors.append(f'{name}: missing module header')
        if name != 'Challenge.lean':
            forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|sorryAx|Lean\.ofReduceBool)\b', code)
            if forbidden:
                errors.append(f'{name}: prohibited proof tokens {sorted(set(forbidden))}')
    challenge = (ROOT / 'Challenge.lean').read_text(encoding='utf-8')
    solution = (ROOT / 'Solution.lean').read_text(encoding='utf-8')
    if len(challenge.splitlines()) > 1000 or len(challenge.encode()) > 100 * 1024:
        errors.append('Challenge exceeds the hard source limits')
    imports = re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', code_only(challenge), re.M)
    if not imports or any(not name.strip().startswith('Mathlib.') for name in imports):
        errors.append('Challenge must import only the selected Mathlib modules')
    if len(re.findall(r'\bsorry\b', code_only(challenge))) != 1:
        errors.append('Challenge should have exactly one deliberate theorem hole')
    def statement(text: str) -> str:
        return text.split('theorem main_result', 1)[1].split(':= by', 1)[0]
    if statement(challenge) != statement(solution):
        errors.append('Challenge and Solution statement text differs')
    config = json.loads((ROOT / 'comparator.json').read_text())
    required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    if not required <= config.keys() or config.keys() - required - {'definition_names', 'enable_nanoda'}:
        errors.append('Comparator configuration keys are invalid')
    if config.get('challenge_module') != 'Challenge' or config.get('solution_module') != 'Solution':
        errors.append('Comparator module names do not match the root layout')
    if config.get('theorem_names') != ['Erdos809Palomar.main_result'] or config.get('definition_names', []):
        errors.append('Comparator must check the fully expanded main theorem, with no supplied definitions')
    if set(config.get('permitted_axioms', [])) != ALLOWED_AXIOMS:
        errors.append('Comparator axiom allowlist differs from the standard three')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        if package.get('type') != 'git' or not re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')):
            errors.append(f"dependency is not pinned to a Git SHA: {package.get('name')}")
        if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', package.get('url', '')):
            errors.append(f"dependency URL is invalid: {package.get('name')}")
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    if toolchain != 'leanprover/lean4:v4.35.0-rc2':
        errors.append('Unexpected toolchain; reassess the Palomar minimum and Mathlib pin')
    mathlib_toolchain = ROOT / '.lake/packages/mathlib/lean-toolchain'
    if mathlib_toolchain.exists() and mathlib_toolchain.read_text().strip() != toolchain:
        errors.append('Mathlib and project toolchains differ')
    print(f'Scanned {lean_count} tracked Lean files; maximum {maximum[0]} lines: {maximum[1]}')
    print(f'Challenge: {len(challenge.splitlines())} lines, {len(challenge.encode())} bytes')
    print('Metadata schema, Lean compilation, and kernel comparison are separate checks.')
    if errors:
        print('\n'.join(f'ERROR: {error}' for error in errors))
        raise SystemExit(1)
    print('SOURCE AND PACKAGING PREFLIGHT PASSED')


if __name__ == '__main__':
    main()
