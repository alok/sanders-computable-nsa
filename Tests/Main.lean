import SandersNSA

open SandersNSA.SystemH.Examples
open SandersNSA.Antipodes
open SandersNSA.Tactic
open SandersNSA.ReverseMath

def main : IO Unit := do
  assert! (SandersNSA.version == "0.1.0")

  -- Milestone 1: System H & Nonstandard Dialectica extraction regression checks
  assert! (r0 10 == [11])
  assert! (sr1 0 == [[0]])
  assert! (sr1 7 == [[7, 6, 5, 4, 3, 2, 1, 0]])
  assert! (sr1 12 == [[12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]])
  assert! (r3 5 == [0])
  assert! (r3' 5 == [0])
  assert! (r3'' 0 == [0])
  assert! (r3'' 2 == [2, 1, 0])
  assert! (r4Choice 3 == [3, 2, 1, 0])
  assert! ((refineCountdownEven 2).val == 2)
  assert! ((refineCountdownEven 5).val == 4)
  IO.println "Milestone 1 (SystemH) tests passed!"

  -- Milestone 2: Antipodes (QVal, AbstractInterpretation, OverspillOmega, IVTAndDini)
  let half : QVal := ⟨2, 3⟩
  assert! (toString half == "1/2")
  assert! (QVal.eqvB (half + half) 1)
  -- Overspill schedule on approx(k, N) := (2 * k ≤ N)
  let approxPred (k N : Nat) : Bool := decide (2 * k ≤ N)
  assert! (overspillPrecisionIndex approxPred 20 11 == 5)
  -- Underspill minimal threshold on P(n) := (n * n ≥ 50)
  let sqGe50 (n : Nat) : Bool := decide (50 ≤ n * n)
  assert! (underspillMinThreshold sqGe50 100 == 8)
  -- Hyperfinite grid sign-crossing on x^2 - 1/2 ≈ 0.7071 at N = 99 (grid step 1/100)
  let quadRoot2 (x : QVal) : QVal := x * x - ⟨1, 1⟩
  let crossIdx := findGridCrossing quadRoot2 99
  assert! (crossIdx == 70) -- 70/100 = 0.70 ≤ √0.5 ≤ 0.71 = 71/100!
  -- Dini uniform modulus extraction on g_n(x) = x / (n + 1)
  let diniMod := extractDiniModulus (fun k => k) (fun _ k => k) 4
  assert! (diniMod == 9)
  -- Abstract interpretation candidate range
  assert! ((boundApprox 4).candidates.length == 5)
  IO.println "Milestone 2 (Antipodes) tests passed!"

  -- Milestone 3: SetTypeBridge & NSA ↔ Constructive Translation Tactics
  let hNat := HyperfiniteSet.natRange 10
  assert! (hNat.card == 11)
  let hEvens := hNat.sep (fun n => decide (n % 2 == 0))
  assert! (hEvens.card == 6)
  let hGt7 : HyperfiniteSet.existsB (fun n => decide (n > 7 ∧ n % 2 == 0)) hNat = true := by decide
  let wEven := HyperfiniteSet.reifyFromBool hNat (fun n => decide (n > 7 ∧ n % 2 == 0)) hGt7
  assert! (wEven.val == 8)
  -- Bidirectional tactic translation dictionary lookup & extracted modulus check
  assert! ((lookupDualConcept ``SContinuousOn).map Prod.fst == some ``UniformContOn)
  assert! ((lookupDualConcept ``RiemannIntegrableWithModulus).map Prod.fst == some ``SRiemannIntegrable)
  assert! (id_sContinuousOn.haloScale 9 == 9)
  IO.println "Milestone 3 (Tactic & SetTypeBridge) tests passed!"

  -- Milestone 4: Higher-Order Reverse Math, Provident Set Theory, Loeb Measure & Stateful Realizers
  -- 1. Independence (`DualQ` nilpotent standard part & `invSqrt2Seq` at k = 99)
  let epsDual : DualQ := DualQ.eps
  let epsSq := DualQ.mul epsDual epsDual
  assert! (QVal.eqvB epsSq.std 0 && QVal.eqvB epsSq.inf 0)
  assert! (QVal.eqvB (DualQ.st (DualQ.add (DualQ.embed 3) epsDual)) 3)
  let approxInvSqrt2 := invSqrt2Seq 99
  assert! (QVal.leB (QVal.dist (approxInvSqrt2 * approxInvSqrt2) ⟨1, 1⟩) (QVal.unitFrac 99))
  -- 2. Cousin & Pincherle
  assert! ((solveUniformCousin 7).length == 8)
  -- 3. Borel Countability & Jordan BV Decomposition
  let oscSeq : Nat → QVal := fun n => if n % 2 == 0 then 0 else 1
  assert! (QVal.eqvB (totalVariation oscSeq 6) 6)
  assert! (QVal.eqvB (oscSeq 0 + posVariation oscSeq 5 - negVariation oscSeq 5) (oscSeq 5))
  assert! (countLargeJumps oscSeq 1 6 == 6)
  -- 4. Continuity Zoo (`cliquish_isolatedSpike`)
  let boxSpike := cliquish_isolatedSpike.selectBox ⟨1, 1⟩ 2 4
  assert! (isolatedSpike boxSpike.lo == 0)
  assert! (isolatedSpike boxSpike.hi == 0)
  -- 5. Kleene S1-S9 Dialogue Trees & Uniform Fan Modulus
  let dParity4 := Dialogue.parityPrefixDialogue 4
  assert! (dParity4.fanModulus == 4)
  assert! (dParity4.eval (fun i => decide (i % 2 == 0)) == false)
  assert! (Dialogue.adaptiveLookupDialogue.eval (fun i => i + 3) == 7)
  -- 6. Mathias's Provident Set Theory (`PROV`) without Powerset
  let ord3 := HF.vonNeumann 3
  assert! (ord3.elems.length == 3)
  assert! (HF.memB (HF.vonNeumann 2) ord3 == true)
  let cart22 := HF.cartesian (HF.vonNeumann 2) (HF.vonNeumann 2)
  assert! (HF.memB (HF.kpair (HF.vonNeumann 0) (HF.vonNeumann 1)) cart22 == true)
  -- 7. Hyperfinite Counting & Loeb Measure / Riemann Expectation Bridge
  let pEven := hyperfiniteProb 9 (fun i => decide (i % 2 == 0))
  assert! (QVal.eqvB pEven ⟨1, 1⟩)
  assert! (hyperfiniteExpect 9 (fun i => QVal.gridPt 9 i) == uniformGridSum id 9)
  -- 8. Imperative / Stateful Realizer `do`-notation extraction
  let (storeLen, rootSub) := extractedQuadraticRoot
  assert! (storeLen == 7)
  assert! (isQuadraticRoot rootSub.val == true)
  IO.println "Milestone 4 (ReverseMath, KleeneDialogue, Provident, Loeb & StatefulRealizers) tests passed!"
