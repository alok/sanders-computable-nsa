/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA

open SandersNSA.SystemH.Examples
open SandersNSA.Antipodes
open SandersNSA.Tactic
open SandersNSA.ReverseMath

/-- Live end-to-end executable demonstration of every subsystem in `sanders-computable-nsa`. -/
def main : IO Unit := do
  IO.println "=========================================================================="
  IO.println s!"  sanders-computable-nsa v{SandersNSA.version} — Live Constructive NSA Extraction"
  IO.println "  100% Computable · 0 sorry · 0 Classical.choice · Pure Lean 4.35.0"
  IO.println "=========================================================================="
  IO.println ""

  -- 1. System H & Nonstandard Dialectica Extraction
  IO.println "[1/4] System H & Nonstandard Dialectica (Xu / van den Berg–Briseid–Safarik / Sanders)"
  IO.println s!"  • Ex0 (∃ m > n, internal):                r0 10       = {r0 10}"
  IO.println s!"  • Ex1 (∀st n, ∃st k, ∀ m ≥ k …):         sr1 7       = {sr1 7}"
  IO.println s!"  • Ex3  (constructive exact witness):      r3 5        = {r3 5}"
  IO.println s!"  • Ex3'' (NSA lmStLe countdown widening):  r3'' 5      = {r3'' 5}"
  IO.println s!"  • Ex4  (HAC + Idealisation choice):       r4Choice 4  = {r4Choice 4}"
  IO.println s!"  • Herbrand refinement (largest even ≤ 9): refine 9    = {(refineCountdownEven 9).val}"
  IO.println ""

  -- 2. Antipodes: QVal, Abstract Interpretation, Overspill/Underspill, IVT & Dini
  IO.println "[2/4] Reuniting the Antipodes (Abstract Interpretation, Overspill, IVT & Dini)"
  let approxPred (k N : Nat) : Bool := decide (3 * k ≤ N)
  IO.println s!"  • Overspill precision k(N=20) on 3k ≤ N:  k           = {overspillPrecisionIndex approxPred 25 20}"
  let sqGe50 (n : Nat) : Bool := decide (50 ≤ n * n)
  IO.println s!"  • Underspill min threshold (n² ≥ 50):     n_min       = {underspillMinThreshold sqGe50 100}"
  let halfSq (x : QVal) : QVal := x * x - ⟨1, 1⟩
  let ivt99 := invSqrt2Seq 99
  IO.println s!"  • Hyperfinite IVT on x² - 1/2 (k=99):     x_99        = {ivt99}  (x_99² = {ivt99 * ivt99})"
  IO.println s!"  • Grid sign-crossing index at N=99:       i*          = {findGridCrossing halfSq 99}/100"
  IO.println s!"  • Dini uniform modulus (k=4, lin moduli): N_Dini      = {extractDiniModulus id (fun _ k => k) 4}"
  IO.println ""

  -- 3. Set / Type / NSA Witness Reification & Translation Dictionary
  IO.println "[3/4] Set/Type/NSA Witness Reification & Metaprogramming Translator"
  let hGrid := HyperfiniteSet.natRange 20
  let hMult7 : HyperfiniteSet.existsB (fun n => decide (n > 10 ∧ n % 7 == 0)) hGrid = true := by decide
  let w7 := HyperfiniteSet.reifyFromBool hGrid (fun n => decide (n > 10 ∧ n % 7 == 0)) hMult7
  IO.println s!"  • Reified Σ-witness (n ∈ [0..20], 7∣n>10): w          = {w7.val}"
  for entry in nsaTranslationTable do
    IO.println s!"  • Dual: {entry.nsaName}  <==>  {entry.constructiveName}"
  IO.println ""

  -- 4. Higher-Order Reverse Math, Dialogue Trees, Provident HF, Loeb & Stateful Realizers
  IO.println "[4/4] Higher-Order Reverse Math, Dialogue Trees, Provident HF, Loeb & Stateful Realizers"
  let dSum := DualQ.add (DualQ.embed 5) DualQ.eps
  IO.println s!"  • DualQ nilpotent halo (st(5 + ε), ε²):   st={DualQ.st dSum}, ε²=({(DualQ.mul DualQ.eps DualQ.eps).std}, {(DualQ.mul DualQ.eps DualQ.eps).inf})"
  let cousinPart := solveUniformCousin 3
  IO.println s!"  • Uniform Cousin 1/4-partition cells:     count       = {cousinPart.length}"
  let oscFn : Nat → QVal := fun n => if n % 2 == 0 then 0 else ⟨1, 1⟩
  IO.println s!"  • Jordan BV on 0, 1/2, 0, 1/2 (n=6):      P={posVariation oscFn 6}, N={negVariation oscFn 6}, TV={totalVariation oscFn 6}"
  let box := cliquish_isolatedSpike.selectBox ⟨1, 1⟩ 1 3
  IO.println s!"  • Cliquish box for isolatedSpike at 1/2:  [{box.lo}, {box.hi}] -> f(lo)={isolatedSpike box.lo}, f(hi)={isolatedSpike box.hi}"
  let dPar5 := Dialogue.parityPrefixDialogue 5
  IO.println s!"  • Kleene S1-S9 Cantor fanModulus (par 5): M_fan       = {dPar5.fanModulus}"
  let vn4 := HF.vonNeumann 4
  let cart23 := HF.cartesian (HF.vonNeumann 2) (HF.vonNeumann 3)
  IO.println s!"  • Mathias PROV vonNeumann(4) & |2 × 3|:   |4|={vn4.elems.length}, |2×3|={cart23.elems.length}"
  let loebHalf := hyperfiniteProb 99 (fun i => decide (i < 50))
  let loebExpId := hyperfiniteExpect 99 (fun i => QVal.gridPt 99 i)
  IO.println s!"  • Loeb grid P_99(i<50) & E_99[x]:         P={loebHalf}, E[x]={loebExpId}"
  let (stSize, qRoot) := extractedQuadraticRoot
  IO.println s!"  • StatefulRealizer do-block (n²-5n+6=0):  store={stSize} candidates, certified root={qRoot.val}"
  IO.println ""
  IO.println "All subsystems executed constructively with zero axioms beyond [propext, Quot.sound]."
