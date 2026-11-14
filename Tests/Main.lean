import SandersNSA

open SandersNSA.SystemH.Examples

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
