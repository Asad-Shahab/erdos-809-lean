# Erdős Problem 809 in Lean

A Lean 4 formalization of the Burr-Erdős-Graham-Sós conjecture for odd cycles.

**Paper:** [The Burr-Erdős-Graham-Sós conjecture for the seven-cycle](https://arxiv.org/abs/2609.38286)  
**Palomar:** [PALOMAR-2026-10-09-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000006&version=1)

For every fixed integer $k \ge 3$,

$$ f\left(n,\left\lfloor \frac{n^2}{4}\right\rfloor+1,C_{2k+1}\right)=\left(\frac18+o(1)\right)n^2.$$

Here $f(n,e,H)$ is the minimum number of colors used in an edge-coloring of an
$n$-vertex graph with at least $e$ edges such that every copy of $H$ is rainbow.

The $C_7$ case is proved by Asad Shahab. For $k \ge 4$, the mathematical argument
is due to Bucić, Chen, and Ma and is formalized here. Together these give the full
$k \ge 3$ statement.

## Formal theorem

The main theorem is:

```lean
Erdos809.erdos_809 (k : ℕ) (hk : 3 ≤ k) :
  Erdos809.CycleAsymptoticExtremalValue (2 * k + 1)
```

The formal statement is an attained version of the asymptotic result. For every
$\varepsilon > 0$, there exists $N$ such that for every integer $n \ge N$, the
minimum number of colors lies between

$$
\left(\frac18-\varepsilon\right)n^2
$$

and

$$
\left(\frac18+\varepsilon\right)n^2.
$$

Colors are counted by the image of the coloring. Graph copies are simple and
need not be induced.

## Verification

The formalization is built with:

- Lean `4.35.0-rc2`
- Mathlib `4.35.0-rc2`
- Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`

The Palomar statement of record is:

```lean
Erdos809Palomar.main_result
```

in [`Challenge.lean`](Challenge.lean), with its proof in
[`Solution.lean`](Solution.lean).

The submission was mechanically verified and registered as:

**[PALOMAR-2026-10-09-000006 v1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000006&version=1)**

Palomar's Comparator accepted the solution with:

- Lean's default kernel
- NanoDa
- con-ron

The proved submission theorem has only the standard axiom closure:

```text
propext
Classical.choice
Quot.sound
```

Detailed verification records are available in:

- [`PALOMAR.md`](PALOMAR.md)
- [`verification/LINUX_COMPARATOR_VERIFICATION.md`](verification/LINUX_COMPARATOR_VERIFICATION.md)
- [`verification/FORMAL_CONJECTURES_VERIFICATION.md`](verification/FORMAL_CONJECTURES_VERIFICATION.md)

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build Erdos809 Solution
```

To inspect the registered theorem and its axiom closure:

```sh
lake env lean --stdin <<'EOF'
import Solution
#check Erdos809Palomar.main_result
#print axioms Erdos809Palomar.main_result
EOF
```

The Palomar Comparator can be reproduced on Linux with Bubblewrap:

```sh
bash scripts/verify-comparator.sh
```

## Exact certificate for the seven-cycle case

The $C_7$ proof uses an exact rational certificate on colored five-vertex
graphs.

A separate standard-library Python verifier independently reconstructs and
checks the certificate. In particular, it verifies:

- all `1436` coefficient identities;
- `15` reduced Gram matrices;
- `456` positive LDL pivots;
- all multiplier and slack inequalities;
- the exact rational density bound.

Run it with:

```sh
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
```

Expected result:

```text
EXACTLY VERIFIED BY INDEPENDENT STANDARD-LIBRARY CHECKER
```

Selected certificate statistics:

| Quantity | Value |
| --- | ---: |
| Unlabeled colored graphs | 1,436 |
| Labeled allowed graphs | 117,916 |
| Gram matrices | 15 |
| Positive LDL pivots | 456 |
| Positive coefficient slacks | 1,397 |
| Zero coefficient slacks | 39 |
| Minimum positive coefficient slack | `2835633/500000000` |
| Maximum density multiplier | `383936867/1000000000 < 1` |

Input and verifier hashes are recorded in
[`certificate/SHA256SUMS`](certificate/SHA256SUMS).

## Formal Conjectures bridge

The repository contains a checked bridge to the formulation used in the
Google DeepMind Formal Conjectures project.

[`Erdos809/Verification/FormalConjecturesBridge.lean`](Erdos809/Verification/FormalConjecturesBridge.lean)
formally establishes the correspondence between:

- the two rainbow-copy predicates;
- arbitrary used palettes and finite palettes `Fin r`;
- the at-least-$e$ and exact-$e$ extremal formulations;
- the epsilon formulation and `Asymptotics.IsEquivalent`.

It derives the full $k \ge 3$ result, the Bucić-Chen-Ma $k \ge 4$ result, and
the $C_7$ result from their corresponding original declarations.

See
[`verification/FORMAL_CONJECTURES_VERIFICATION.md`](verification/FORMAL_CONJECTURES_VERIFICATION.md)
for the complete audit and reproduction details.

## Attribution and provenance

The seven-cycle argument is Asad Shahab's independent proof.

For odd cycles of length at least nine, the mathematical argument is due to
Matija Bucić, Kaizhe Chen, and Jie Ma. This repository formalizes that argument
for $k \ge 4$.

The original public Lean development used Lean 4.28.0. It was subsequently
ported to Lean 4.35.0-rc2 for Palomar while preserving the mathematical theorem
statements and certificate data.

An independent formalization by Jacob Parish is registered separately as
`PALOMAR-2026-09-30-000004`. This repository does not import or adapt that
formalization and makes no priority claim over it.

## Citation

If you use the mathematical result, please cite the paper:

```bibtex
@misc{shahab2026burrerdosgrahamsos,
  author = {Asad Shahab},
  title = {The Burr--Erdős--Graham--Sós conjecture for the seven-cycle},
  year = {2026},
  eprint = {2609.38286},
  archivePrefix = {arXiv},
  primaryClass = {math.CO},
  url = {https://arxiv.org/abs/2609.38286}
}
```

If you use or reference the Lean formalization, please cite the registered
Palomar artifact:

```bibtex
@misc{palomar-2026-10-09-000006-v1,
  author = {{Asad Shahab}},
  title = {{Erdős Problem 809: an independent proof of the seven-cycle threshold}},
  year = {2026},
  howpublished = {Palomar, PALOMAR-2026-10-09-000006 v1},
  url = {https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000006&version=1},
}
```

## License

Apache License 2.0. See [`LICENSE`](LICENSE).
