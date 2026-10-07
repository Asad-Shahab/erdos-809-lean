module
public import Erdos809.Certificate.LocalGraphs

@[expose] public section

/-!
# Kernel reflection for exhaustive local graph coverage

A coverage entry is either an explicit forbidden ordered triangle (codes
0..124), or a representative/permutation pair. The checker verifies witnesses;
it performs no canonical-label search and trusts no generator result.
-/

namespace Erdos809.Certificate.LocalGraph

def codeGraph (n : ℕ) : LocalGraph :=
  codeEquiv.symm ⟨n % (4 ^ 10), Nat.mod_lt _ (by decide)⟩

@[simp] theorem codeGraph_encode (g : LocalGraph) : codeGraph (codeEquiv g).val = g := by
  unfold codeGraph
  have h : (⟨(codeEquiv g).val % (4 ^ 10), Nat.mod_lt _ (by decide)⟩ : Fin (4 ^ 10)) =
      codeEquiv g := Fin.ext (Nat.mod_eq_of_lt (codeEquiv g).isLt)
  rw [h, Equiv.symm_apply_apply]

/-- Small binary lookup trees keep witness checks logarithmic in the size of
the representative table, using ordinary kernel-reducible definitions. -/
inductive NatTable where
  | leaf : ℕ → NatTable
  | branch : NatTable → NatTable → NatTable

def NatTable.get : NatTable → ℕ → ℕ
  | .leaf n, _ => n
  | .branch a b, i => if i % 2 = 0 then a.get (i / 2) else b.get (i / 2)

variable (representatives : Fin 1436 → LocalGraph)
  (permutations : Fin 120 → Equiv.Perm (Fin 5))

def checkEntry (n w : ℕ) : Bool :=
  if w < 125 then
    let i : Fin 5 := ⟨w % 5, Nat.mod_lt _ (by decide)⟩
    let j : Fin 5 := ⟨w / 5 % 5, Nat.mod_lt _ (by decide)⟩
    let k : Fin 5 := ⟨w / 25 % 5, Nat.mod_lt _ (by decide)⟩
    decide (color (codeGraph n) i j = 1 ∧
      color (codeGraph n) i k ≠ 0 ∧ color (codeGraph n) j k ≠ 0)
  else
    let r : Fin 1436 := ⟨(w - 125) / 120 % 1436, Nat.mod_lt _ (by decide)⟩
    let p : Fin 120 := ⟨(w - 125) % 120, Nat.mod_lt _ (by decide)⟩
    decide ((codeEquiv (relabel (representatives r) (permutations p))).val = n)

theorem checkEntry_sound {n w : ℕ}
    (hcheck : checkEntry representatives permutations n w = true)
    (ha : Admissible (codeGraph n)) :
    ∃ r p, relabel (representatives r) (permutations p) = codeGraph n := by
  unfold checkEntry at hcheck
  split_ifs at hcheck with hw
  · have hbad := of_decide_eq_true hcheck
    exact False.elim ((ha _ _ _ hbad.1).elim hbad.2.1 hbad.2.2)
  · have heq := of_decide_eq_true hcheck
    refine ⟨⟨(w - 125) / 120 % 1436, Nat.mod_lt _ (by decide)⟩,
      ⟨(w - 125) % 120, Nat.mod_lt _ (by decide)⟩, ?_⟩
    rw [← heq, codeGraph_encode]

def checkRange : ℕ → List ℕ → Bool
  | _, [] => true
  | n, w :: ws => checkEntry representatives permutations n w &&
      checkRange (n + 1) ws

theorem checkRange_sound (ws : List ℕ) (start : ℕ)
    (hcheck : checkRange representatives permutations start ws = true)
    (k : ℕ) (hk : k < ws.length) (ha : Admissible (codeGraph (start + k))) :
    ∃ r p, relabel (representatives r) (permutations p) = codeGraph (start + k) := by
  induction ws generalizing start k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [checkRange, Bool.and_eq_true] at hcheck
    cases k with
    | zero => simpa using checkEntry_sound representatives permutations hcheck.1 ha
    | succ k =>
      have hk' : k < ws.length := Nat.lt_of_succ_lt_succ hk
      have ha' : Admissible (codeGraph (start + 1 + k)) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ha
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
        ih (start + 1) hcheck.2 k hk' ha'

/-- Store the current code explicitly and verify consecutive order. Passing
the stored numeral forward prevents a long unreduced successor chain from
forming during a large kernel check. -/
def checkIndexedRange : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | start, (n, w) :: ws => decide (start = n) &&
      checkEntry representatives permutations n w && checkIndexedRange (n + 1) ws

theorem checkIndexedRange_sound (ws : List (ℕ × ℕ)) (start : ℕ)
    (hcheck : checkIndexedRange representatives permutations start ws = true)
    (k : ℕ) (hk : k < ws.length) (ha : Admissible (codeGraph (start + k))) :
    ∃ r p, relabel (representatives r) (permutations p) = codeGraph (start + k) := by
  induction ws generalizing start k with
  | nil => simp at hk
  | cons nw ws ih =>
    rcases nw with ⟨n, w⟩
    simp only [checkIndexedRange, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨rfl, hentry⟩, htail⟩ := hcheck
    cases k with
    | zero => simpa using checkEntry_sound representatives permutations hentry ha
    | succ k =>
      have hk' : k < ws.length := Nat.lt_of_succ_lt_succ hk
      have ha' : Admissible (codeGraph (start + 1 + k)) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ha
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
        ih (start + 1) htail k hk' ha'

theorem checkIndexedRange_append_of_checked (as bs : List (ℕ × ℕ)) (start : ℕ)
    (ha : checkIndexedRange representatives permutations start as = true)
    (hb : checkIndexedRange representatives permutations (start + as.length) bs = true) :
    checkIndexedRange representatives permutations start (as ++ bs) = true := by
  induction as generalizing start with
  | nil => simpa using hb
  | cons nw ws ih =>
    rcases nw with ⟨n, w⟩
    simp only [checkIndexedRange, Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨⟨rfl, hentry⟩, htail⟩ := ha
    simp only [List.cons_append, checkIndexedRange, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨True.intro, hentry⟩, ih (start + 1) htail ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ws.length] using hb

/-- Combine separately checked blocks into complete graph coverage. The
arithmetic partition is proved once, independently of all generated data. -/
theorem coverage_of_indexedBlocks {B S : ℕ} (hS : 0 < S) (hsize : B * S = 4 ^ 10)
    (blocks : Fin B → List (ℕ × ℕ))
    (hlength : ∀ i, (blocks i).length = S)
    (hchecked : ∀ i, checkIndexedRange representatives permutations (i.val * S) (blocks i) = true)
    (g : LocalGraph) (ha : Admissible g) :
    ∃ r p, relabel (representatives r) (permutations p) = g := by
  let n := codeEquiv g
  let i : Fin B := ⟨n.val / S, (Nat.div_lt_iff_lt_mul hS).mpr (hsize.symm ▸ n.isLt)⟩
  let k := n.val % S
  have hk : k < (blocks i).length := by
    rw [hlength]
    exact Nat.mod_lt _ hS
  have hnum : i.val * S + k = n.val := by
    dsimp [i, k]
    exact Nat.div_add_mod' _ _
  have hadm : Admissible (codeGraph (i.val * S + k)) := by
    rw [hnum]
    change Admissible (codeGraph (codeEquiv g).val)
    rwa [codeGraph_encode]
  have h := checkIndexedRange_sound representatives permutations (blocks i)
    (i.val * S) (hchecked i) k hk hadm
  rw [hnum, codeGraph_encode] at h
  exact h

/-- Explicit cached position map; bijectivity is checked once for each listed
permutation, rather than searched for while checking individual graphs. -/
def permutationCodeMap (p : ℕ) (i : Fin 5) : Fin 5 :=
  ⟨p / 5 ^ i.val % 5, Nat.mod_lt _ (by decide)⟩

def relabelCodes (r p : ℕ) : LocalGraph :=
  fun e => color (codeGraph r) (permutationCodeMap p e.val.1) (permutationCodeMap p e.val.2)

/-- A tag plus cached representative and permutation codes. The cache is
checked against both frozen tables before it is used. -/
abbrev CachedWitness := ℕ × ℕ × ℕ

def checkCachedEntry (rt pt : NatTable) (n : ℕ) (w : CachedWitness) : Bool :=
  if w.1 < 125 then checkEntry representatives permutations n w.1 else
    decide (rt.get ((w.1 - 125) / 120 % 1436) = w.2.1) &&
    decide (pt.get ((w.1 - 125) % 120) = w.2.2) &&
    decide ((codeEquiv (relabelCodes w.2.1 w.2.2)).val = n)

theorem checkCachedEntry_sound (rt pt : NatTable)
    (hrep : ∀ r, representatives r = codeGraph (rt.get r.val))
    (hperm : ∀ p i, permutations p i = permutationCodeMap (pt.get p.val) i)
    {n : ℕ} {w : CachedWitness}
    (hcheck : checkCachedEntry representatives permutations rt pt n w = true)
    (ha : Admissible (codeGraph n)) :
    ∃ r p, relabel (representatives r) (permutations p) = codeGraph n := by
  unfold checkCachedEntry at hcheck
  split_ifs at hcheck with hw
  · exact checkEntry_sound representatives permutations hcheck ha
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    let r : Fin 1436 := ⟨(w.1 - 125) / 120 % 1436, Nat.mod_lt _ (by decide)⟩
    let p : Fin 120 := ⟨(w.1 - 125) % 120, Nat.mod_lt _ (by decide)⟩
    have hcodes : relabel (representatives r) (permutations p) =
        relabelCodes w.2.1 w.2.2 := by
      funext e
      simp only [relabel, relabelCodes, hrep, hperm]
      rw [hcheck.1.1, hcheck.1.2]
    refine ⟨r, p, ?_⟩
    rw [hcodes, ← hcheck.2, codeGraph_encode]

def checkCachedRange (rt pt : NatTable) : ℕ → List CachedWitness → Bool
  | _, [] => true
  | n, w :: ws => checkCachedEntry representatives permutations rt pt n w &&
      checkCachedRange rt pt (n + 1) ws

theorem checkCachedRange_sound (rt pt : NatTable)
    (hrep : ∀ r, representatives r = codeGraph (rt.get r.val))
    (hperm : ∀ p i, permutations p i = permutationCodeMap (pt.get p.val) i)
    (ws : List CachedWitness) (start : ℕ)
    (hcheck : checkCachedRange representatives permutations rt pt start ws = true)
    (k : ℕ) (hk : k < ws.length) (ha : Admissible (codeGraph (start + k))) :
    ∃ r p, relabel (representatives r) (permutations p) = codeGraph (start + k) := by
  induction ws generalizing start k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [checkCachedRange, Bool.and_eq_true] at hcheck
    cases k with
    | zero => simpa using checkCachedEntry_sound representatives permutations rt pt hrep hperm hcheck.1 ha
    | succ k =>
      have hk' : k < ws.length := Nat.lt_of_succ_lt_succ hk
      have ha' : Admissible (codeGraph (start + 1 + k)) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ha
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using
        ih (start + 1) hcheck.2 k hk' ha'

end Erdos809.Certificate.LocalGraph
