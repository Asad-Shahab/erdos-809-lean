#!/usr/bin/env python3
"""Port visibility without changing declaration statements or proof bodies.

This is a one-time migration helper, not a proof checker. It refuses oversized
files and unsupported headers rather than hiding source or silently rewriting it.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess


def skip_layout(text: str, pos: int) -> int:
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end + 1
        elif text.startswith('/-', pos):
            depth = 1
            pos += 2
            while depth and pos < len(text):
                if text.startswith('/-', pos):
                    depth += 1
                    pos += 2
                elif text.startswith('-/', pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            if depth:
                raise ValueError('unterminated block comment')
        else:
            break
    return pos


def migrate(text: str) -> str:
    start = skip_layout(text, 0)
    if re.match(r'module\b', text[start:]):
        return text
    if re.match(r'prelude\b', text[start:]):
        raise ValueError('unexpected prelude header')
    pieces = []
    end = 0
    pos = start
    while re.match(r'import\b', text[pos:]):
        line_end = text.find('\n', pos)
        line_end = len(text) if line_end < 0 else line_end + 1
        line = text[pos:line_end]
        if not re.fullmatch(r"import\s+[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*\s*(?:--[^\n]*)?\n?", line):
            raise ValueError(f'unsupported import header: {line.rstrip()}')
        pieces.append(text[end:pos] + 'public ' + line)
        end = line_end
        pos = skip_layout(text, end)
    header = ''.join(pieces)
    if header and not header.endswith('\n'):
        header += '\n'
    return 'module\n' + header + '\n@[expose] public section\n' + text[end:]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='apply the checked migration')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=root).decode().split('\0')
    changes = []
    stats = []
    for name in paths:
        path = root / name
        if not name.endswith('.lean') or path.name == 'lakefile.lean':
            continue
        if path.is_symlink():
            raise SystemExit(f'refusing Lean symlink: {name}')
        original = path.read_text(encoding='utf-8')
        result = migrate(original)
        count = len(result.splitlines())
        stats.append((count, name))
        if result != original:
            changes.append((path, result))
    print(f'Lean files: {len(stats)}; files needing module conversion: {len(changes)}')
    print('Largest resulting files:')
    for count, name in sorted(stats, reverse=True)[:20]:
        print(f'{count:7d}  {name}')
    oversized = [(n, name) for n, name in stats if n > 10000]
    if oversized:
        for count, name in oversized:
            print(f'BLOCKER: {name}: {count} lines, limit 10000')
        raise SystemExit('Split oversized source modules before applying the migration.')
    if args.write:
        for path, result in changes:
            path.write_text(result, encoding='utf-8')
        print(f'Applied module visibility migration to {len(changes)} files.')
    else:
        print('Dry run only. Use --write to apply; rebuild and run Comparator afterwards.')


if __name__ == '__main__':
    main()
