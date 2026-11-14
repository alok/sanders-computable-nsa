/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import SandersNSA.SystemH.Syntax
import SandersNSA.SystemH.Dialectica
import SandersNSA.SystemH.Examples
import SandersNSA.Antipodes.ConstructiveAnalysis
import SandersNSA.Antipodes.AbstractInterpretation
import SandersNSA.Antipodes.OverspillOmega
import SandersNSA.Antipodes.IVTAndDini
import SandersNSA.Tactic.SetTypeBridge
import SandersNSA.Tactic.Translate
import SandersNSA.ReverseMath.Independence
import SandersNSA.ReverseMath.CousinPincherle
import SandersNSA.ReverseMath.BorelBV
import SandersNSA.ReverseMath.ContinuityZoo
import SandersNSA.ReverseMath.KleeneDialogue
import SandersNSA.ReverseMath.Provident
import SandersNSA.ReverseMath.LoebMeasure
import SandersNSA.ReverseMath.StatefulRealizers

/-!
# Kernel Axiom & Computability Audit (`AxiomAudit`)

Compile-time kernel audit verifying across all flagship extractors, realisers, tactics, and
theorems in `SandersNSA` that:
1. **Zero `sorryAx`** appears anywhere in the transitive kernel dependency cone.
2. **Zero `Classical.choice`** appears anywhere — not even inside `Prop` proofs!
3. **Zero custom `axiom`s** appear (only Lean's standard propositional extensionality `propext`
   and quotient soundness `Quot.sound` are permitted, and computational definitions typically
   depend on `[]` — zero axioms altogether).
4. **Every computational realiser** is kernel-executable (`! Lean.isNoncomputable env decl`).
-/

namespace SandersNSA
namespace AxiomAudit

open Lean Elab Command

/-- Permitted foundational kernel axioms (strictly excluding `sorryAx` and `Classical.choice`). -/
def permittedAxioms : List Name :=
  [``propext, ``Quot.sound]

/-- Compile-time command that inspects `Lean.collectAxioms` and `Lean.isNoncomputable` in the
    Lean 4 kernel environment for a list of declarations, failing compilation on any violation. -/
elab "#audit_pure_constructive " ids:ident+ : command => do
  let env ← getEnv
  for idStx in ids do
    let declName ← liftCoreM <| realizeGlobalConstNoOverload idStx
    if Lean.isNoncomputable env declName then
      throwErrorAt idStx m!"[AxiomAudit] {declName} is marked noncomputable!"
    let axs ← liftCoreM <| Lean.collectAxioms declName
    for ax in axs do
      if ax == ``sorryAx then
        throwErrorAt idStx m!"[AxiomAudit] {declName} transitively depends on sorryAx!"
      if ax == ``Classical.choice then
        throwErrorAt idStx m!"[AxiomAudit] {declName} transitively depends on Classical.choice!"
      unless permittedAxioms.contains ax do
        throwErrorAt idStx m!"[AxiomAudit] {declName} depends on unexpected axiom {ax}!"

-- 1. Milestone 1: System H & Nonstandard Dialectica Extraction
#audit_pure_constructive
  SandersNSA.SystemH.Tm.eval
  SandersNSA.SystemH.extract
  SandersNSA.SystemH.simpExtract
  SandersNSA.SystemH.extractExactWitness
  SandersNSA.SystemH.eval_substPar
  SandersNSA.SystemH.Examples.r0
  SandersNSA.SystemH.Examples.sr1
  SandersNSA.SystemH.Examples.r3
  SandersNSA.SystemH.Examples.r3''
  SandersNSA.SystemH.Examples.r4Choice
  SandersNSA.SystemH.Examples.refineCountdownEven

-- 2. Milestone 2: Antipodes (QVal, AbstractInterpretation, OverspillOmega, IVTAndDini)
#audit_pure_constructive
  SandersNSA.Antipodes.QVal.unitFrac_half_sum
  SandersNSA.Antipodes.WitnessApprox.galois_singleton_subsumes
  SandersNSA.Antipodes.WitnessApprox.bindApprox_sound
  SandersNSA.Antipodes.WitnessApprox.concretizeApprox
  SandersNSA.Antipodes.boundApprox_sound_of_bounded
  SandersNSA.Antipodes.overspillPrecisionIndex
  SandersNSA.Antipodes.overspillPrecisionIndex_valid
  SandersNSA.Antipodes.overspillPrecisionIndex_diverges
  SandersNSA.Antipodes.underspillMinThreshold_spec
  SandersNSA.Antipodes.omegaInvariant_to_cauchy
  SandersNSA.Antipodes.cauchy_to_omegaInvariant
  SandersNSA.Antipodes.omegaInvariantFn_to_uniformCont
  SandersNSA.Antipodes.findGridCrossing_spec
  SandersNSA.Antipodes.approxIVT_spec
  SandersNSA.Antipodes.exactIVT_cauchy
  SandersNSA.Antipodes.llpo_hovering_jump
  SandersNSA.Antipodes.dini_uniform_conv
  SandersNSA.Antipodes.dini_monotone_from_subcover

-- 3. Milestone 3: Set/Type/NSA Witness Bridge & Bidirectional Translation Tactics
#audit_pure_constructive
  SandersNSA.Tactic.HyperfiniteSet.reifyWitness
  SandersNSA.Tactic.HyperfiniteSet.reifyFromBool
  SandersNSA.Tactic.HyperfiniteSet.reifyHyperfiniteChoice
  SandersNSA.Tactic.HyperfiniteSet.reifyChoiceGraph
  SandersNSA.Tactic.sContinuousOn_to_uniformCont
  SandersNSA.Tactic.uniformCont_to_sContinuousOn
  SandersNSA.Tactic.sCauchy_to_cauchy
  SandersNSA.Tactic.sDerivOn_to_diff
  SandersNSA.Tactic.sRiemann_to_riemann
  SandersNSA.Tactic.roundtrip_uniformCont
  SandersNSA.Tactic.scauchy_hyp_demo

-- 4. Milestone 4: Reverse Mathematics, Kleene Dialogue, Provident HF, Loeb & Stateful Realizers
#audit_pure_constructive
  SandersNSA.ReverseMath.no_qval_sq_eqv_half
  SandersNSA.ReverseMath.DualQ.dualQ_transfer_fails
  SandersNSA.ReverseMath.hyperSeq_horn_transfer
  SandersNSA.ReverseMath.invSqrt2Seq_has_no_qval_standard_part
  SandersNSA.ReverseMath.solveUniformCousin_deltaFine
  SandersNSA.ReverseMath.solveUniformCousin_covers
  SandersNSA.ReverseMath.pincherleGlobalBound_spec
  SandersNSA.ReverseMath.nonuniform_gauge_unbounded
  SandersNSA.ReverseMath.subset_flattenSublevels
  SandersNSA.ReverseMath.heightCountableOfList
  SandersNSA.ReverseMath.jordan_decomposition
  SandersNSA.ReverseMath.totalVariation_eqv_sum
  SandersNSA.ReverseMath.borel_jump_height_bound
  SandersNSA.ReverseMath.lipschitz_to_uniformCont
  SandersNSA.ReverseMath.globalUniformCont_to_quasiCont
  SandersNSA.ReverseMath.quasiCont_to_cliquish
  SandersNSA.ReverseMath.not_uniformCont_heavisideHalf
  SandersNSA.ReverseMath.not_quasiCont_isolatedSpike
  SandersNSA.ReverseMath.cliquish_isolatedSpike
  SandersNSA.ReverseMath.Dialogue.eval_bind
  SandersNSA.ReverseMath.Dialogue.eval_eq_of_agree_below_pointwiseModulus
  SandersNSA.ReverseMath.Dialogue.eval_eq_of_agree_below_fanModulus
  SandersNSA.ReverseMath.Dialogue.adaptive_not_uniform
  SandersNSA.ReverseMath.HF.extEqB_iff_forall_memB
  SandersNSA.ReverseMath.HF.memB_cartesian_iff
  SandersNSA.ReverseMath.HF.vonNeumann_length
  SandersNSA.ReverseMath.hyperfiniteProb_disjoint_or
  SandersNSA.ReverseMath.hyperfiniteProb_complement
  SandersNSA.ReverseMath.hyperfiniteExpect_grid_eq_riemannSum
  SandersNSA.ReverseMath.loebGridExpect_converges_to_integral
  SandersNSA.ReverseMath.extractedQuadraticRoot

end AxiomAudit
end SandersNSA
