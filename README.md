# Erdős #809 in Lean

The formalization is verified on Lean and Mathlib `4.35.0-rc2`.
The full proof, Formal Conjectures bridge, source preflight, independent
rational certificate replay, and Comparator passed. The unchanged Comparator
script ran on a separate ARM64 Ubuntu VM: con-ron, nanoda, and Lean’s default
kernel accepted the solution. Exact output and reproduction details are in
[Linux verification evidence](verification/LINUX_COMPARATOR_VERIFICATION.md).
See [PALOMAR.md](PALOMAR.md), [LOCAL_PORT.md](LOCAL_PORT.md), and the
[Formal Conjectures verification evidence](verification/FORMAL_CONJECTURES_VERIFICATION.md).
This branch contains no GitHub Actions workflow. The preserved `main`
snapshot remains unchanged; these checks performed no push or submission.

Paper: [The Burr-Erdős-Graham-Sós conjecture for the
seven-cycle](https://arxiv.org/abs/2609.38286), by Asad Shahab.

For every fixed integer `k ≥ 3`, the minimum number of colors used over all
simple `n`-vertex graphs with at least `⌊n²/4⌋ + 1` edges and all edge colorings
in which every simple, not necessarily induced, `C₂ₖ₊₁` is rainbow satisfies

```text
f(n, ⌊n²/4⌋ + 1, C₂ₖ₊₁) = (1/8 + o(1)) n².
```

The formal statement asserts an attained minimum: for every `ε > 0`, there is
`N` such that for every integer `n ≥ N` the minimum lies between
`(1/8 - ε)n²` and `(1/8 + ε)n²`. Colors are counted by the image of the coloring.

```lean
Erdos809.erdos_809 (k : ℕ) (hk : 3 ≤ k) :
  Erdos809.CycleAsymptoticExtremalValue (2 * k + 1)
```

The original public sources were exported from the author's development
repository at `d7fcc0cd633946076a0ccc965fc088fa2cca676f`. The preserved public
snapshot `cfa2b4427b523d1dfaa40d538c99776380840374` used Lean 4.28.0 and
Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. This branch ports
that same mathematics to Palomar's newer toolchain and module requirements.

- Target Lean: `leanprover/lean4:v4.35.0-rc2`.
- Target Mathlib: `v4.35.0-rc2`, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- Every Git dependency is pinned in `lake-manifest.json`.
- The expanded statement of record is `Erdos809Palomar.main_result` in
  [Challenge.lean](Challenge.lean), paired with [Solution.lean](Solution.lean).

The seven-cycle argument is Shahab's independent proof. The mathematical
argument for longer odd cycles is credited to Bucić, Chen, and Ma; the
contribution here in those cases is its formalization. The metadata records
Jacob Parish's `PALOMAR-2026-09-30-000004` as an independent related
formalization and makes no priority claim.

With [elan](https://github.com/leanprover/elan) installed, use the local
verification commands in [PALOMAR.md](PALOMAR.md). Module migration is already
committed. The build commands are:

```sh
export LEAN_NUM_THREADS=2
lake exe cache get
lake build Challenge
lake build Erdos809 Solution
```

Check the submission theorem and its axioms:

```sh
lake env lean --stdin <<'EOF'
import Solution
#check Erdos809Palomar.main_result
#print axioms Erdos809Palomar.main_result
EOF
bash scripts/verify-comparator.sh
```

The current public and FC bridge theorem audits report only `propext`,
`Classical.choice`, and `Quot.sound`. The historical pin was separately checked
on Lean 4.28.0. The intentional hole in `Challenge.lean` does not occur in the
proved Solution's dependency closure. Comparator requires Linux Bubblewrap;
use a separate Linux checkout with sufficient memory as described in
[LOCAL_PORT.md](LOCAL_PORT.md).

## Certificate verifier

The separate standard-library verifier regenerates all admissible colored
five-vertex graphs and their flag contributions. It checks exact rational
positive definiteness of the 15 reduced Gram matrices, all 1436 coefficient
identities, and nonnegative multipliers and slacks. The maximum density
multiplier is `383936867/1000000000 < 1`. This is a separate check alongside
the Lean kernel check of the same certificate data; the Lean build does not
depend on it.

Run from the repository root with Python 3.10 or later:

```sh
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
```

Never use `-O`: the assertions are the proof checks. Input and verifier hashes
are recorded in [SHA256SUMS](certificate/SHA256SUMS). The command writes
[the reference result](certificate/results/selected_union_independent_replay.json),
including its measured `seconds` field. Restore that runtime-only change after
each replay with `git checkout --
certificate/results/selected_union_independent_replay.json`.

Expected status: `EXACTLY VERIFIED BY INDEPENDENT STANDARD-LIBRARY CHECKER`.

| Output field | Expected value |
| --- | --- |
| `unlabeled_colored_graphs` | 1436 |
| `labeled_allowed_graphs` | 117916 |
| `gram_matrices` | 15 |
| `reduced_dimensions` | `[20,55,28,44,40,14,18,23,30,35,34,29,30,30,26]` |
| `positive_LDL_pivots` | 456 |
| `positive_coefficient_slacks` | 1397 |
| `zero_coefficient_slacks` | 39 |
| `minimum_positive_coefficient_slack` | `2835633/500000000` |
| `maximum_density_multiplier` | `383936867/1000000000` |

## License

Apache License 2.0; see [LICENSE](LICENSE).
