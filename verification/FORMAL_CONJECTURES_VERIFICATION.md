# Formal Conjectures reviewer verification

The three formal_proof references in FC PR 6634 point to 7ec4aaa6e9d685e8f9948005d8be69923cce2ab8. That snapshot is checked on its own Lean 4.28.0 toolchain. The new semantic bridge is checked on Lean/Mathlib 4.35.0-rc2; it does not import the FC checkout, which uses Lean 4.33.1. The three source declaration signatures agree at the pin and in the port, modulo whitespace/pretty-printing.

FC source read locally: commit 338c1efab080e61bcd4de7e202c3a3d784e6bdab, FormalConjectures/ErdosProblems/809.lean. Source SHA256 e36f9efdda43c891f942fb2c1bc2b67c7b42d631f8512d2260fc02a249e57e8e. The IsRainbow source is FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean, SHA256 c8fd859de2574369d2c43518ade29b1b730af7944fbd6a03b6e13a3d2459420c. Both definition texts were compared verbatim; all three substantive FC proposition texts were checked by examples in the bridge (the full-result answer wrapper is replaced by True).

## Current PR head checked read-only

On 2026-10-07 at 23:40 UTC, PR #6634 was fetched from
`google-deepmind/formal-conjectures` into a throwaway clone, using only a Git
read. Its head was `338c1efab080e61bcd4de7e202c3a3d784e6bdab`, tree
`912e21ea3af0d60ad231849675c51b0d708a3766`; `git ls-remote` confirmed that
same current PR head. This matches the local FC source snapshot above.
The PR uses Lean 4.33.1 and pins Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`.

The declarations below were extracted and compared by unified diff. Each diff
was empty. Definitions include their argument types and bodies. For theorem
statements, only the declaration name was changed to `example`; the full
result's `answer(True)` was replaced by `True`, as in the checked bridge.

| PR source | Current bridge or dependency | Comparison |
| --- | --- | --- |
| `809.lean:46–48`, `strongChromaticNum` | `PaletteBridge.lean`, mirrored definition | Exact text, empty diff |
| `Coloring/Vertex.lean:148–150`, `IsRainbow` | `PaletteBridge.lean`, mirrored definition | Exact text, empty diff |
| Pinned Mathlib `Coloring/EdgeLabeling.lean`, `EdgeLabeling` | Current Mathlib 4.35 `EdgeLabeling` | Exact declaration text, empty diff: `G.edgeSet → K` |
| Same Mathlib file, `EdgeLabeling.pullback` | Current Mathlib 4.35 `pullback` | Exact declaration text, empty diff: `C ∘ f.mapEdgeSet` |
| `809.lean:59–61`, link at 57–58 | Checked full-result `example`, proved by `full_true_iff` | Empty diff after the stated wrapper/name changes |
| `809.lean:80–82`, link at 78–79 | Checked BCM `example`, proved by `bcm k hk` | Empty diff after the declaration-name change |
| `809.lean:90–92`, link at 88–89 | Checked C7 `example`, proved by `c7` | Empty diff after the declaration-name change |

The pinned FC Mathlib file was also retrieved directly at its 40-character
revision. Its SHA256 is
`33b287eb682ff17ffc8e51f7bcc835e46c30d96befd051e60c23d22c0fc201c6`.
`EdgeLabeling` is imported from Mathlib by FC and the bridge; it is not a copied
project definition. The comparison includes `pullback`, which connects the
mirrored `IsRainbow` to the original copy-edge injectivity predicate.
FC's `Answer.lean` was read: `answer(True)` elaborates the supplied `True` with
metadata, or through a safe auxiliary abbreviation whose value is `True`.
The bridge imports none of FC's answer machinery and proves `True ↔ …`.

Reproduce the source fetch without editing an existing FC checkout:

```bash
scratch=$(mktemp -d /tmp/erdos809-fc-pr-6634.XXXXXX)
git init "$scratch"
git -C "$scratch" remote add origin https://github.com/google-deepmind/formal-conjectures.git
git -C "$scratch" fetch --depth=1 --filter=blob:none origin pull/6634/head:fc-pr-6634
git -C "$scratch" checkout --detach fc-pr-6634
git -C "$scratch" rev-parse HEAD 'HEAD^{tree}'
git -C "$scratch" ls-remote origin refs/pull/6634/head
# Compare the exact declarations at the paths and lines in the table above.
# Remove the scratch clone after saving the evidence.
```

This is a comparison against the PR head at the stated time, not a claim about
future PR edits. No PR, comment, formal_proof link, or GitHub object was modified.
A reviewer-reply draft is kept outside the repository; its proposed link targets
use `<NEW_SHA>` until the user pushes the verified final commit. The historical
pin's declarations and axioms were checked at 7ec4aaa; the new bridge is checked
only on the current Lean 4.35 tree, not retrofitted or compiled at that old pin.

## Historical pin checked locally

Toolchain: leanprover/lean4:v4.28.0 (Lean commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b).
The exact detached worktree was clean at 7ec4aaa6e9d685e8f9948005d8be69923cce2ab8.
`lake exe cache get` passed; `LEAN_NUM_THREADS=1 lake build` completed successfully (3566 jobs), exit 0.
The source scan returned no proof holes or prohibited declarations. Exact declaration/axiom output:

```text
Erdos809.erdos_809 (k : ℕ) (hk : 3 ≤ k) : Erdos809.CycleAsymptoticExtremalValue (2 * k + 1)
Erdos809.erdos_809_long_odd_cycles (k : ℕ) (hk : 4 ≤ k) : Erdos809.CycleAsymptoticExtremalValue (2 * k + 1)
Erdos809.erdos_809_C7 (ε : ℝ) :
  0 < ε →
    ∃ N,
      ∀ n ≥ N,
        ∃ k,
          Erdos809.ExtremalValue n (Erdos809.exactThreshold n) k ∧ (1 / 8 - ε) * ↑n ^ 2 ≤ ↑k ∧ ↑k ≤ (1 / 8 + ε) * ↑n ^ 2
'Erdos809.erdos_809' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.erdos_809_long_odd_cycles' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.erdos_809_C7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Cache provenance: the initial two-worker rebuild was interrupted to protect disk from host swap growth; a one-worker retry was also interrupted after finding a matching local Lean 4.28 cache. The local /Users/asad/erdos-809 cache has identical Lake configuration and dependency pins, and 401 of the pin's 402 source files are byte-identical. Its .lake/build artifacts were copied into the pin worktree. Lake then validated traces against the pin's sources and rebuilt the differing root module; the completed build and subsequent audits ran in the exact pinned worktree. This is a cache-assisted verification, not a fresh-cache replay. No pin source was edited.

## Semantic bridge

The root imports Erdos809/Verification/FormalConjecturesBridge.lean. Supporting modules are PaletteBridge.lean and AsymptoticBridge.lean in the same directory. The namespace is Erdos809.FormalConjecturesBridge.

- rainbow_iff is Iff.rfl: Copy.mapEdgeSet has the same underlying function as the Hom edge map used by EdgeLabeling.pullback. Copies are injective homomorphisms, with no induced-copy requirement.
- palette_compression maps each color to its subtype in range c, then through range c ≃ Fin r. It proves the resulting labeling is rainbow on every copy and surjective. finite_palette proves the converse rainbow condition and usedColors c ≤ r, allowing unused labels.
- exact_palette_minimum uses cycleExtremalValue_realized_exactly, the generic lemma underlying erdos_809_realized_exactly. That lemma deletes edges using exists_subgraph_edgeCount_eq, preserves validity under restriction, and uses minimality to show no used colors can be lost. An exact-e realization and palette compression supply q as a member of the FC sInf set. Every member r is at least q. Thus strongChromaticNum_eq follows from IsLeast.csInf_eq, without using a default value for an empty set.
- EdgeCount G = G.edgeSet.ncard definitionally. threshold_eq proves n^2/4+1 = n*n/4+1 over naturals.
- ratio_tendsto_one enlarges each epsilon cutoff to at least one, making n²/8 positive. For a<1 use epsilon=(1-a)/16, and for a>1 use epsilon=(a-1)/16. The two strict order bounds prove ratio convergence by tendsto_order. asymptotic_bridge applies isEquivalent_of_tendsto_one.
- full applies the generic bridge to Erdos809.erdos_809. bcm applies it to Erdos809.erdos_809_long_odd_cycles. c7 applies it to Erdos809.erdos_809_C7 using cycleExtremalValue_seven_iff, an Iff.rfl bridge to the C7 semantics. Each formal_proof claim therefore has its own source declaration.
- full_true_iff proves True ↔ the full result. FC's answer(True) annotation wraps True (or an auxiliary abbreviation of it); the proposition wrapper is trivial. No FC answer implementation is imported.

## Full bridge types

Inside namespace Erdos809.FormalConjecturesBridge, with SimpleGraph, Filter, Asymptotics open:

```lean
theorem full : ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8

theorem bcm : ∀ k, 4 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8

theorem c7 :
    (fun n ↦ (strongChromaticNum (cycleGraph 7) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8

theorem full_true_iff : True ↔ ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8

```

## Bridge axiom output

```text
'Erdos809.FormalConjecturesBridge.rainbow_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.palette_compression' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.finite_palette' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.exact_palette_minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.strongChromaticNum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.threshold_eq' depends on axioms: [propext]
'Erdos809.FormalConjecturesBridge.ratio_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.asymptotic_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.full' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.bcm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.c7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos809.FormalConjecturesBridge.full_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reproduction

Historical pin, without editing its source:

```bash
git worktree add --detach ../erdos-809-pin-7ec4aaa 7ec4aaa6e9d685e8f9948005d8be69923cce2ab8
cd ../erdos-809-pin-7ec4aaa
cat lean-toolchain
lake exe cache get
LEAN_NUM_THREADS=2 lake build
lake env lean --stdin <<'LEAN'
import Erdos809
#check Erdos809.erdos_809
#check Erdos809.erdos_809_long_odd_cycles
#check Erdos809.erdos_809_C7
#print axioms Erdos809.erdos_809
#print axioms Erdos809.erdos_809_long_odd_cycles
#print axioms Erdos809.erdos_809_C7
LEAN
rg -n '\bsorry\b|\badmit\b|native_decide|ofReduceBool|^\s*axiom\b' --glob '*.lean' --glob '!.lake/**' .
# rg exits 1 when there are no matches, as expected at this pin.
cd ../erdos-809-lean
git worktree remove ../erdos-809-pin-7ec4aaa
```

Current tree, with the committed Lean 4.35.0-rc2 toolchain:

```bash
LEAN_NUM_THREADS=2 lake build Erdos809.Verification.FormalConjecturesBridge
LEAN_NUM_THREADS=2 lake build Erdos809 Solution
lake env lean --stdin <<'LEAN'
import Solution
import Erdos809.Verification.FormalConjecturesBridge
#check Erdos809.erdos_809
#check Erdos809.erdos_809_long_odd_cycles
#check Erdos809.erdos_809_C7
#check Erdos809Palomar.main_result
#print axioms Erdos809.erdos_809
#print axioms Erdos809.erdos_809_long_odd_cycles
#print axioms Erdos809.erdos_809_C7
#print axioms Erdos809Palomar.main_result
#check Erdos809.FormalConjecturesBridge.full
#check Erdos809.FormalConjecturesBridge.bcm
#check Erdos809.FormalConjecturesBridge.c7
#check Erdos809.FormalConjecturesBridge.full_true_iff
#print axioms Erdos809.FormalConjecturesBridge.full
#print axioms Erdos809.FormalConjecturesBridge.bcm
#print axioms Erdos809.FormalConjecturesBridge.c7
#print axioms Erdos809.FormalConjecturesBridge.full_true_iff
LEAN
python3 scripts/palomar_preflight.py
python3 -I -S -B certificate/code/verify_selected_union_certificate.py
git checkout -- certificate/results/selected_union_independent_replay.json
```

On Linux with Bubblewrap (including the privileged arm64 Docker container), run the unmodified `bash scripts/verify-comparator.sh`. Do not share the Mac `.lake` directory with Linux: clone the read-only source mount into a Docker volume and build there. The script runs the bundled Lean kernel plus nanoda and con-ron, with the unchanged three-axiom allowlist. macOS itself cannot run this Linux-only Bubblewrap sandbox.

## Integrity and scope

No theorem was weakened. No sorry, admit, custom axiom, native_decide, Lean.ofReduceBool, or custom trusted declaration was introduced. The intentional Challenge statement hole remains unchanged and is absent from the Solution and bridge axiom closures. The source scan finds only that hole in the current tree and no holes at the historical pin.

Certificate witness lists, representatives, permutations, offsets, counts, matrices, numerators, and rational values are unchanged. All 9,371 preexisting certificate definition/abbreviation bodies in 334 files match main after comments and whitespace normalization; the raw certificate directory and its four recorded hashes match main. All 28,671 preexisting theorem/lemma signatures match main, none are missing, and no project module imports were removed. Challenge.lean, Solution.lean, comparator.json, and scripts/verify-comparator.sh are byte-for-byte unchanged since the takeover at b32de74.

The bridge is checked on the new 4.35 tree; the three pinned declarations are checked at 7ec4aaa itself on 4.28.0. Their substantive theorem types agree. This is compiler/kernel and independent certificate-checker evidence, with no claim of external human refereeing or Palomar acceptance.

## Comparator verification

The unchanged `scripts/verify-comparator.sh` passed on a separate ARM64
Ubuntu 24.04 VM at source commit
`de13121330f31b7fdb33725d53e656d9487fe7c9`, using the committed Lean 4.35.0-rc2
toolchain. Con-ron accepted 72,095 declarations in verified mode, nanoda
accepted, and Lean’s default kernel accepted. Comparator finished with
`Your solution is okay!` and `COMPARATOR EXIT 0`.

[LINUX_COMPARATOR_VERIFICATION.md](LINUX_COMPARATOR_VERIFICATION.md) records
exact output, log hashes, and reproduction commands. The previous 8 GiB
Docker OOM and interrupted diagnostics were incomplete attempts; the successful
VM run resolves that verification gap. Comparator configuration, its
three-axiom allowlist, the proof, and certificate data were unchanged.
