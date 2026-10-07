# Linux Comparator verification

The unchanged `bash scripts/verify-comparator.sh` passed at source commit
`de13121330f31b7fdb33725d53e656d9487fe7c9` on 2026-10-07. The source tree was
`bdda827e79d10054eeae4a97f5c693936d52c732`. This records a completed check of
that source snapshot; any later commit must be checked at its own exact SHA.

The VM ran Ubuntu 24.04.4 LTS, ARM64, with 32 CPUs, 61 GiB usable RAM, and a
96 GiB root disk. Lean was `leanprover/lean4:v4.35.0-rc2`, compiler revision
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib was pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Source was transferred using a local
Git bundle. Mac build artifacts were not copied, and no GitHub write occurred.

## Source and cache provenance

The initial VM source was a fresh Git clone of a self-contained local bundle,
not a copy of the Mac working directory. `setup.log` records the clone from
`/home/ubuntu/erdos809-source.bundle` and checkout of the exact de131 snapshot.
The bundle SHA256 was
`c2844f6f3f9bc87423d2b5a1e097cd2a4e95a55ed7b86d26a5e9baac426d009e`.
Git bundles carry committed Git objects and refs; `.lake` is untracked and was
not included. Cache logs show dependency materialization from the pinned Git
revisions and downloads of the Linux Mathlib cache. Project proof artifacts
were built on the VM. The original setup did not print a pre-cache `.lake`
absence assertion; that limitation of the recorded evidence is explicit.

A later exact-commit replay in this VM checkout reused its Linux `.lake` after
fetching a documentation-only commit from another local bundle. That replay is
cache-assisted and is not described as starting with an empty cache. To make
fresh-clone provenance explicit for the final source, the final runner must
clone the final bundle into a new directory, assert `.lake` is absent before
`lake exe cache get`, log its HEAD and tree, and perform a full build and all
three Comparator kernels from that directory. A Mathlib cache download is
permitted; no Mac or earlier project `.lake/build` directory is copied. Final
exact-commit logs and their verdict belong in the final local report.

## Statement and dependency integrity

The prepared statement snapshot is commit
`e5e9d583e3fa9b026fcce0fbd6599ea3e0369b62`, which introduced `Challenge.lean`.
Against that snapshot, this command produces no output:

```bash
git diff e5e9d583e3fa9b026fcce0fbd6599ea3e0369b62 palomar/final-809 -- Challenge.lean
```

Both Challenge blobs are `8b90ec6a18b78a6d34558f182f207d51906627bc`.
Main predates Challenge, so a diff against main shows the whole newly added
52-line file; it does not show a modified registered statement. No external
registration transaction is asserted here. Mathlib in `lake-manifest.json` is
pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`v4.35.0-rc2`).
The final branch must retain at most two commits above immutable main and
`git merge-base --is-ancestor main palomar/final-809` must exit zero; these
commands are reproduced in the final local report.

## Recorded results

- Fresh `LEAN_NUM_THREADS=12 lake build Erdos809 Solution`: 3569 jobs, exit 0.
- Four public declarations and all 12 bridge axiom closures: audit exit 0,
  only `propext`, `Classical.choice`, and `Quot.sound`; `threshold_eq` uses
  only `propext`. Types and exact axiom output are in the FC verification report.
- Source preflight: 407 tracked Lean files, maximum 798 lines, exit 0.
- Isolated Python replay: `EXACTLY VERIFIED BY INDEPENDENT STANDARD-LIBRARY CHECKER`,
  exit 0; runtime-only certificate JSON restored.
- Comparator sandbox build: 3568 jobs, exit 0. All three kernels accepted.

The complete successful Comparator run started at 19:18:31 UTC and finished
at 22:56:04 UTC. Exact selected output:

```text
== commit de13121330f31b7fdb33725d53e656d9487fe7c9
Build completed successfully (3568 jobs).
Running con-ron kernel on solution
con-ron: 1 inductive blocks modelled in-process: Lean.Syntax (30 generated records, checked by the fold as declarations and not counted as records of the file)
con-ron: accepted 72095 declarations (--verified)
con-ron kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
COMPARATOR EXIT 0
```

## Reproduction from local source

Create a bundle of the exact local branch on the Mac, then copy it over SSH:

```bash
git bundle create /tmp/erdos809-source.bundle palomar/final-809
scp -i "$HOME/.ssh/testssh.pem" /tmp/erdos809-source.bundle ubuntu@VM:/home/ubuntu/
```

On a disposable Ubuntu ARM64 VM, install dependencies and elan, then clone
from that bundle. These commands assume the default `ubuntu` user:

```bash
sudo apt-get update -qq
sudo apt-get install -y curl git ca-certificates bubblewrap python3 xz-utils zstd
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p /home/ubuntu/erdos809-aws
git clone /home/ubuntu/erdos809-source.bundle /home/ubuntu/erdos809-aws/repo
cd /home/ubuntu/erdos809-aws/repo
git checkout --detach refs/remotes/origin/palomar/final-809
printf '== commit '; git rev-parse HEAD
lean --version
MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get
LEAN_NUM_THREADS=12 lake build Erdos809 Solution
python3 scripts/palomar_preflight.py
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
git checkout -- certificate/results/selected_union_independent_replay.json
sudo mkdir -p /run/user/0
chmod o+x /home/ubuntu
sudo chown -R root:root /home/ubuntu/erdos809-aws/repo
sudo env HOME=/home/ubuntu PATH="$PATH" LEAN_NUM_THREADS=16 \
  taskset -c 0-31 bash scripts/verify-comparator.sh
printf 'COMPARATOR EXIT %s\n' "$?"
```

Use the exact branch name and verify its 40-character SHA. The documented
Mathlib cache fallback reads the same pinned artifacts from Azure; the public
endpoint's bulk transfer was unusually slow during this run. Checkout ownership
must match the account running the sandbox: Bubblewrap clears environment and
uses a temporary home, so environment/global Git exceptions were insufficient.
Ubuntu's default AppArmor policy rejected an unprivileged user namespace;
sudo ran the original sandbox successfully. No policy or sandbox was disabled.

All 32 CPUs and VM memory were available. Con-ron's default uses at most 16
workers in verified mode; nanoda used four workers and Lean's default checker
one. A temporary 16 GiB swap file was added as a buffer against transient
con-ron memory growth; no swap use was observed. Remove that file after all
checks finish. The earlier 8 GiB Docker OOM attempts and interrupted diagnostics
did not yield complete verdicts; this completed run resolves that gap.

## Evidence hashes

Full logs were saved locally under `/tmp/erdos809-aws/accepted-evidence/`.
Their SHA256 values identify the actual captured outputs:

| Log | SHA256 |
| --- | --- |
| `environment.log` | `74b732f6b53bcc8e14c1ebd4c91230ec30987307291edf370462ced9eaa3f03c` |
| `build.log` | `2851bfb858c21e4202a56c1985667eb50669fd7057b992f196f1de7a6d0a0845` |
| `axioms.log` | `130a738ac2c6fbba5cc81bdf32d744a166042d6b0f3efc4d24dbe3ae853c0068` |
| `preflight.log` | `c439c7965e5eb37cee4c89e4a7dbb558d0e0b4ce3390bd20632f3a74e7d2904e` |
| `certificate.log` | `2c20b09eb946abb3ac5d4bc8b026d595d37243e5df4088f5762e4926d7aa3225` |
| `comparator.log` | `92c0c0d2a6c4d97fba880c50329a3ddc5ad652e2a72f1c04a49db6459efb47b6` |

No theorem, certificate datum, import graph, toolchain, Comparator configuration,
or three-axiom allowlist was changed to obtain this result. The deliberate
Challenge hole is absent from the proved solution's axiom closure. No push,
PR, workflow, submission, or unrelated Formal Conjectures edit was performed.
