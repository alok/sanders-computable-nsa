import Lake
open Lake DSL

package «sanders-computable-nsa» where
  version := v!"0.1.0"
  description := "Computable Nonstandard Analysis & Higher-Order Reverse Mathematics in Lean 4: System H Dialectica Extraction, Constructive-NSA Tactic Translation, Abstract Interpretation, Omega-Invariance, Overspill/Underspill, Cousin/Pincherle, Borel Height & BV, Continuity Zoo, Kleene Dialogue, Provident Sets, Loeb Measure, and Stateful Realizers"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib SandersNSA

lean_exe «sanders-nsa» where
  root := `Main

@[test_driver]
lean_exe «sanders-nsa-tests» where
  root := `Tests.Main
