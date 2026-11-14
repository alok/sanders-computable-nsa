import SandersNSA

def main : IO Unit := do
  assert! (SandersNSA.version == "0.1.0")
  IO.println "All tests passed (scaffold)."
