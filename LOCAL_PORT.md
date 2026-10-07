# Local Lean 4.35 verification

The compatibility port, generated-block migration, and FC bridge are
committed. The branch contains no GitHub Actions workflow, and its local
verification performed no push or submission. Main remains at
`cfa2b4427b523d1dfaa40d538c99776380840374`; the older submission branch is
preserved. The pinned toolchain is `leanprover/lean4:v4.35.0-rc2`.

The macOS and Linux full builds, theorem/axiom audits, source preflight,
and independent rational certificate replay passed. Comparator remains the sole
incomplete check: Linux killed con-ron for memory exhaustion in the
approximately 8 GB Docker VM. Nanoda accepted the solution; the complete
Comparator run has not passed.
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

## Linux Comparator on Apple Silicon

Use `ubuntu:24.04` with `--platform linux/arm64`, `--privileged` for Bubblewrap,
and Docker volumes `cmp809-work` and `cmp809-elan`. Mount the macOS checkout
read-only at `/src`; clone it into `/work/repo`. Never share the macOS `.lake`
with Linux. Before running Comparator, install curl, git, ca-certificates,
bubblewrap, python3, xz-utils, and zstd; install elan with no default toolchain;
and create `/run/user/0` so Bubblewrap can create its temporary home.

Inside the Linux checkout:

```bash
git fetch /src palomar/final-809
git checkout --detach FETCH_HEAD
printf '== commit '; git rev-parse HEAD
cat lean-toolchain
lake exe cache get
export LEAN_NUM_THREADS=2
lake build Erdos809 Solution
python3 scripts/palomar_preflight.py
bash scripts/verify-comparator.sh
```

Use the actual final branch name if a numerical suffix was needed. Run the
unchanged Comparator script at that exact commit and retain its output.
The first minimal-Ubuntu run failed because `/run/user` was absent; creating
it before the sandbox resolved that environmental issue. The large exported
proof needs substantial memory during independent kernel checking. A first
con-ron run was killed by Linux OOM in the approximately 8 GB Docker VM;
a one-worker verified diagnostic avoided OOM but was interrupted after
approximately 96 minutes without a verdict. A four-worker verified retry
consumed approximately 7 GB of swap and was interrupted to protect the host disk
reserve. Neither diagnostic accepted or rejected a named theorem. Added swap and
copied diagnostic exports were removed afterwards. These resource failures do
not establish a complete independent-kernel check.
Keep at least 5 GB free on the host. Restore the certificate timing JSON if
running the independent Python replay in the Linux checkout.

## Migration record

`scripts/port_435_generated_blocks.py` is idempotent and now reports zero
updated files. It normalizes associativity in the `checked` proofs of all
256 generated LocalGraphs blocks. Witness data is unchanged. Other repairs
adapt bundled graph symmetry, changed counting/Walk APIs, Real star-order
instances, PSD proof conversion, explicit embedding/relabel equalities, and
nested finite-quantifier decision instances. These retain the original
statements and kernel-checked certificate computations.
