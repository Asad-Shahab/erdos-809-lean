#!/usr/bin/env python3
"""Port the generated local-graph coverage proofs to Lean 4.35.

`witnesses` is the left-associated append `unit000 ++ unit001 ++ ... ++ unit031`,
while the generated `checked` proof peels off one unit at a time and therefore
needs the right-associated form.  Older Lean closed that gap by definitional
unfolding; Lean 4.35 does not.  This migration:

* unfolds `witnesses` and `start` and right-associates the goal once, and
* writes each tail argument of `checkIndexedRange_append_of_checked`
  explicitly right-associated, so every nested layer matches syntactically.

Only the proof of `checked` is touched.  Witness lists, offsets, lengths,
counts and every other declaration are left byte-for-byte unchanged.  The
script is idempotent and accepts both the original generated form and the
earlier `List.append_assoc`/`simpa` migration.
"""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
directory = root / "Erdos809" / "Certificate" / "LocalGraphs"

CHECKED = (
    "theorem checked : checkIndexedRange Data.representatives Data.permutations "
    "start witnesses = true := by\n"
)
NEW_HEAD = CHECKED + "  simp only [witnesses, start, List.append_assoc]\n  exact ("
OLD_HEADS = [
    CHECKED + "  exact (",
    CHECKED + "  simpa only [witnesses, List.append_assoc] using (",
]

TAIL = re.compile(
    r"^(    unit\d{3} )\((unit\d{3}(?: \+\+ \(?unit\d{3})*)\)*( \d+ unit\d{3}_checked)$",
    re.MULTILINE,
)


def right_assoc(units: list[str]) -> str:
    if len(units) <= 2:
        return " ++ ".join(units)
    return f"{units[0]} ++ ({right_assoc(units[1:])})"


def port_tail(match: re.Match[str]) -> str:
    units = re.findall(r"unit\d{3}", match.group(2))
    return f"{match.group(1)}({right_assoc(units)}){match.group(3)}"


changed = 0
for path in sorted(directory.glob("Block*.lean")):
    text = path.read_text(encoding="utf-8")
    original = text

    for head in OLD_HEADS:
        text = text.replace(head, NEW_HEAD)
    if NEW_HEAD not in text:
        raise SystemExit(f"{path.name}: unrecognised `checked` proof header")

    text = re.sub(
        r"simpa only \[(unit\d{3}_length), Nat\.reduceAdd, List\.append_assoc\]",
        r"simpa only [\1, Nat.reduceAdd]",
        text,
    )

    start = text.index(NEW_HEAD)
    end = text.index("\ndef orbitCount", start)
    proof, tails = TAIL.subn(port_tail, text[start:end])
    if tails != 31:
        raise SystemExit(f"{path.name}: expected 31 tail arguments, found {tails}")
    text = text[:start] + proof + text[end:]

    if text != original:
        path.write_text(text, encoding="utf-8")
        changed += 1

print(f"updated {changed} generated local-graph files")
