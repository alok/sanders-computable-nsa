import SandersNSA

open SandersNSA.SystemH.Examples
open SandersNSA.Antipodes

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
