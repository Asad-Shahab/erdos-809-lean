# Local Lean 4.35 verification

The compatibility port, generated-block migration, and FC bridge are
committed. The branch contains no GitHub Actions workflow, and its local
verification performed no push or submission. Main remains at
`cfa2b4427b523d1dfaa40d538c99776380840374`; the older submission branch is
preserved. The pinned toolchain is `leanprover/lean4:v4.35.0-rc2`.

The macOS and Linux full builds, theorem/axiom audits, source preflight,
independent rational certificate replay, and Comparator passed. Comparator ran
on a separate ARM64 Ubuntu VM with 61 GiB RAM. Con-ron, nanoda, and Lean’s
default kernel all accepted the solution, ending with `Your solution is okay!`
and exit 0. See the
[Linux verification evidence](verification/LINUX_COMPARATOR_VERIFICATION.md).
Historical-pin and bridge evidence is in
[verification/FORMAL_CONJECTURES_VERIFICATION.md](verification/FORMAL_CONJECTURES_VERIFICATION.md).

## Reproduce on macOS

With elan installed, the committed toolchain is selected automatically:

```bash
export LEAN_NUM_THREADS=2
lake exe cache get
lake build Erdos809.Verification.FormalConjecturesBridge
lake build Erdos809 Solution
python3 scripts/palomar_preflight.py
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
git checkout -- certificate/results/selected_union_independent_replay.json
```

The complete theorem and axiom audit commands are in the verification report.
They report the original public theorem types and only the standard three
axioms, with no dependency on the deliberate Challenge hole.

## Linux Comparator

macOS cannot run the Linux Bubblewrap sandbox. The successful check used a
separate ARM64 Ubuntu 24.04 VM with 32 CPUs, 61 GiB usable RAM, and a 96 GiB
root disk. The Mac checkout's `.lake` was not transferred. Source arrived as a
local Git bundle; no branch was pushed. The fresh Linux build passed 3569 jobs,
and Comparator's sandbox build passed 3568 jobs.

Reproduction, including local-bundle transfer and Ubuntu sandbox permissions,
is in [verification/LINUX_COMPARATOR_VERIFICATION.md](verification/LINUX_COMPARATOR_VERIFICATION.md).
The checker ran with all 32 CPUs available, `LEAN_NUM_THREADS=16`, and no memory
limit. Con-ron's bundled default caps its workers at 16. Temporary 16 GiB swap
was added as a buffer; no swap use was observed. Keep enough disk for the cache,
exported proof, and any swap. Run the unchanged Comparator script at the exact
commit being reviewed and retain its output.

Earlier Docker attempts used `ubuntu:24.04`, `--platform linux/arm64`,
`--privileged`, and separate Linux volumes. They exhausted the approximately
8 GiB Docker VM's memory. Lower-concurrency diagnostics were interrupted
without a verdict; those attempts are not accepted checks. The full successful
VM run resolves that earlier gap. Creating `/run/user/0` fixed the minimal
container's missing sandbox-home parent. On Ubuntu, sudo was needed for
Bubblewrap under the default AppArmor policy. The disposable VM checkout was
owned by root to match the sandbox runner; the user's home allowed directory
traversal. Comparator clears its sandbox environment, so environment-only Git
ownership exceptions do not solve a mismatched checkout owner.

Restore the certificate timing JSON after every independent Python replay.

## Migration record

`scripts/port_435_generated_blocks.py` is idempotent and now reports zero
updated files. It normalizes associativity in the `checked` proofs of all
256 generated LocalGraphs blocks. Witness data is unchanged. Other repairs
adapt bundled graph symmetry, changed counting/Walk APIs, Real star-order
instances, PSD proof conversion, explicit embedding/relabel equalities, and
nested finite-quantifier decision instances. These retain the original
statements and kernel-checked certificate computations.
