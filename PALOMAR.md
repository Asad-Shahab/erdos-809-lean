# Palomar local verification

This branch carries the Lean/Mathlib `4.35.0-rc2` compatibility port and the
independent Challenge/Solution interface for `Asad-Shahab/erdos-809-lean`.
Development remained in local branches; Linux verification used a separate
AWS VM reached over SSH. No push, GitHub write, workflow, or submission was
performed. The preserved main snapshot is
`cfa2b4427b523d1dfaa40d538c99776380840374`.

Paper: [arXiv:2609.38286](https://arxiv.org/abs/2609.38286).

## Statement and attribution

`Challenge.lean` states the attained minimum for every fixed odd cycle of
length at least seven using Mathlib definitions. It counts used colors,
allows non-induced copies, and quantifies over all sufficiently large
orders and every eligible host and coloring. Its one statement hole is
intentional. `Solution.lean` has the identical theorem type and applies
`Erdos809.erdos_809 k hk`, with no additional mathematical hypothesis.

The seven-cycle proof is Shahab's. The longer-cycle mathematics is due to
Bucić, Chen, and Ma. The metadata records Jacob Parish's
`PALOMAR-2026-09-30-000004` as an independent related formalization and
makes no priority claim.

## Verified state

The full `LEAN_NUM_THREADS=2 lake build Erdos809 Solution` passed on macOS.
The separate Linux arm64 build passed too. The four public declarations and
all bridge lemmas elaborate. Their axiom closures contain only `propext`,
`Classical.choice`, and `Quot.sound` (the threshold arithmetic lemma uses
only `propext`). Source preflight and the independent standard-library
certificate replay passed. The unchanged Comparator script passed on an ARM64
Ubuntu 24.04 VM with 61 GiB RAM: con-ron accepted 72,095 declarations in verified
mode, nanoda accepted, and Lean’s default kernel accepted. The final summary
was `Your solution is okay!`, with exit 0.
[Linux verification evidence](verification/LINUX_COMPARATOR_VERIFICATION.md)
records the checked source commit, exact output, and reproduction commands.

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Module visibility and the
compatibility repairs are committed. All preexisting theorem signatures,
certificate data, and project imports are preserved. The generated-block
migration is retained and reruns with zero changes.

[Formal Conjectures verification evidence](verification/FORMAL_CONJECTURES_VERIFICATION.md)
records the three original declarations checked at the exact `7ec4aaa` pin
on Lean 4.28.0 and the separately checked 4.35 semantic bridge. The bridge
proves finite-palette compression, the exact-edge minimum, and the FC
asymptotic types; each result uses its own historical declaration.

## Reproduction

```bash
export LEAN_NUM_THREADS=2
lake exe cache get
lake build Erdos809.Verification.FormalConjecturesBridge
lake build Erdos809 Solution
lake env lean --stdin <<'LEAN'
import Solution
#check Erdos809Palomar.main_result
#print axioms Erdos809Palomar.main_result
#print axioms Erdos809.FormalConjecturesBridge.full
#print axioms Erdos809.FormalConjecturesBridge.bcm
#print axioms Erdos809.FormalConjecturesBridge.c7
#print axioms Erdos809.FormalConjecturesBridge.full_true_iff
LEAN
python3 scripts/palomar_preflight.py
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
git checkout -- certificate/results/selected_union_independent_replay.json
bash scripts/verify-comparator.sh
```

Comparator needs Linux Bubblewrap. Use a separate Linux checkout with
sufficient memory following [LOCAL_PORT.md](LOCAL_PORT.md). The submitted
`comparator.json`
and `scripts/verify-comparator.sh` are unchanged since takeover; the axiom
allowlist has exactly the standard three entries. The independent certificate
replay's timing field is restored after every run.

## Submission fields, after successful validation

Use [Palomar's submission form](https://submit.palomar-registry.org/).

- Repository: `Asad-Shahab/erdos-809-lean`.
- Commit: the full 40-character SHA of the final pushed and verified snapshot.
- Project, Comparator, and metadata paths: leave blank for the root defaults.
- Authorization: responsible author or maintainer of the substantive proof.
- Existing Palomar ID: leave blank. This is a new independent entry.

Keep the private status-page link supplied by the form. No submission or
registration was performed by the local verification. The author retains the
choice whether to submit and whether to register after review.

## Policy references

- https://palomar-registry.org/how-to-submit
- https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json
- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
- https://github.com/PalomarRegistry/PalomarTemplate
- https://github.com/mathlib-initiative/formalization.yaml
