# Erdős #809 in Lean

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

The Lean sources are the import closure of that theorem, exported unchanged
from the author's development repository at commit
`d7fcc0cd633946076a0ccc965fc088fa2cca676f`.

- Lean: `4.28.0` (`leanprover/lean4:v4.28.0`).
- mathlib: `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- All dependency revisions are pinned in `lake-manifest.json`.

With [elan](https://github.com/leanprover/elan) installed, build from the
repository root. The thread setting bounds compilation parallelism.

```sh
export LEAN_NUM_THREADS=2
lake exe cache get
lake build
```

Check the theorem and its axioms:

```sh
lake env lean --stdin <<'EOF'
import Erdos809
#check Erdos809.erdos_809
#print axioms Erdos809.erdos_809
EOF
```

The axiom query reports:

```text
'Erdos809.erdos_809' depends on axioms: [propext, Classical.choice, Quot.sound]
```

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
including its measured `seconds` field.

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
