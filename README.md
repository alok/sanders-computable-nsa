# `sanders-computable-nsa`

**Computable Nonstandard Analysis, Proof Mining & Higher-Order Reverse Mathematics in Lean 4 (`v4.35.0`)**

A **100% computable**, `sorry`-free, `Classical.choice`-free, zero-external-dependency Lean 4 library formalizing the computational content of Nonstandard Analysis (NSA) and Higher-Order Reverse Mathematics developed by **Sam Sanders** and **Chuangjie Xu**.

- **Kernel Axiom Footprint**: Verified at compile time by [`SandersNSA/AxiomAudit.lean`](SandersNSA/AxiomAudit.lean) (`#audit_pure_constructive`): **0 `sorryAx`**, **0 `Classical.choice`**, **0 `noncomputable`**, **0 custom axioms** across all 18 modules.
- **Specification & Reconstruction Manual**: See [`SPEC.md`](SPEC.md) for the formal specification and [`docs/DEVELOPER_GUIDE.md`](docs/DEVELOPER_GUIDE.md) for an exhaustive pedagogical guide teaching how to code every component manually from scratch.

---

## Module Index (18 Modules)

| Subsystem | Module | Key Definitions & Verified Theorems |
|---|---|---|
| **`SystemH`** | [`SandersNSA/SystemH/Syntax.lean`](SandersNSA/SystemH/Syntax.lean) | `SnocList`, Gödel's System $\mathcal{T}$ `Tm` (parallel `Ren`/`Sub`, closed combinators), `Tm.eval`, System $\mathcal{H}$ `Fml` & 46-rule `Prf` |
| **`SystemH`** | [`SandersNSA/SystemH/Dialectica.lean`](SandersNSA/SystemH/Dialectica.lean) | Single-pass `dTypes`, `let`-shared `dialecticaPair`, lazy unit-erasure `simpExtract`, `eval_substPar`, `eval_beta`, `extractExactWitness` |
| **`SystemH`** | [`SandersNSA/SystemH/Examples.lean`](SandersNSA/SystemH/Examples.lean) | `ex0`, `ex1` (`sr1`), `ex3` vs. `ex3'` vs. `ex3''` (`lmStLe` countdown widening), `ex4Hac`, `refineCountdownEven` |
| **`Antipodes`** | [`SandersNSA/Antipodes/ConstructiveAnalysis.lean`](SandersNSA/Antipodes/ConstructiveAnalysis.lean) | Subtraction-free exact rationals `QVal`, `unitFrac_half_sum`, `Type`-valued Bishop structures (`UniformContOn`, `CauchySeqWithModulus`, `DiffOnWithModulus`, `RiemannIntegrableWithModulus`) |
| **`Antipodes`** | [`SandersNSA/Antipodes/AbstractInterpretation.lean`](SandersNSA/Antipodes/AbstractInterpretation.lean) | `WitnessApprox` Galois connection (`galois_singleton_subsumes`), `bindApprox_sound`, `concretizeApprox`, `boundApprox_sound_of_bounded`, `QValInterval` |
| **`Antipodes`** | [`SandersNSA/Antipodes/OverspillOmega.lean`](SandersNSA/Antipodes/OverspillOmega.lean) | `overspillPrecisionIndex` (`overspillPrecisionIndex_valid`, `overspillPrecisionIndex_diverges`), `underspillMinThreshold_spec`, `omegaInvariant_to_cauchy`, `omegaInvariantFn_to_uniformCont` |
| **`Antipodes`** | [`SandersNSA/Antipodes/IVTAndDini.lean`](SandersNSA/Antipodes/IVTAndDini.lean) | `findGridCrossing_spec`, `approxIVT_spec`, `exactIVT_cauchy`, `llpo_hovering_jump` (`LLPO` obstruction), `extractDiniModulus` (`dini_uniform_conv`) |
| **`Tactic`** | [`SandersNSA/Tactic/SetTypeBridge.lean`](SandersNSA/Tactic/SetTypeBridge.lean) | `HyperfiniteSet α`, `reifyWitness`, `reifyFromBool`, `reifyHyperfiniteChoice`, `reifyChoiceGraph` (`Prop` → `Type` without `Classical.choice`) |
| **`Tactic`** | [`SandersNSA/Tactic/Translate.lean`](SandersNSA/Tactic/Translate.lean) | `SContinuousOn`, `SCauchy`, `SLimit`, `SDerivOn`, `SRiemannIntegrable`, `nsa_to_constructive`, `constructive_to_nsa`, `nsa_to_constructive_at`, `#nsa_translate` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/Independence.lean`](SandersNSA/ReverseMath/Independence.lean) | `no_qval_sq_eqv_half`, `DualQ.dualQ_transfer_fails` (`st ⊬ Transfer`), `hyperSeq_horn_transfer`, `invSqrt2Seq_has_no_qval_standard_part` (`Transfer ⊬ st` over `QVal`) |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/CousinPincherle.lean`](SandersNSA/ReverseMath/CousinPincherle.lean) | `solveUniformCousin_deltaFine`, `solveUniformCousin_covers`, `solveDyadicCousin`, `pincherleGlobalBound_spec`, `nonuniform_gauge_unbounded` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/BorelBV.lean`](SandersNSA/ReverseMath/BorelBV.lean) | Borel `HeightCountable` (`arXiv:2208.03027`), `jordan_decomposition`, `totalVariation_eqv_sum`, `borel_jump_height_bound` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/ContinuityZoo.lean`](SandersNSA/ReverseMath/ContinuityZoo.lean) | `LipschitzOn` → `GlobalUniformCont` → `QuasiContOn` → `CliquishOn` (`arXiv:2303.00493`), `BaireOneOn`, `not_uniformCont_heavisideHalf`, `not_quasiCont_isolatedSpike`, `cliquish_isolatedSpike` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/KleeneDialogue.lean`](SandersNSA/ReverseMath/KleeneDialogue.lean) | Kleene S1–S9 `Dialogue` (`arXiv:2102.04787`), `eval_bind` (`S4`), `eval_eq_of_agree_below_pointwiseModulus`, `eval_eq_of_agree_below_fanModulus`, `adaptive_not_uniform` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/Provident.lean`](SandersNSA/ReverseMath/Provident.lean) | Mathias's Provident Set Theory `PROV` (`HF`, `extEqFuel_invariant`, `extEqB_iff_forall_memB`, powerset-free `memB_cartesian_iff`, `vonNeumann_length`) |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/LoebMeasure.lean`](SandersNSA/ReverseMath/LoebMeasure.lean) | `hyperfiniteProb_disjoint_or`, `hyperfiniteProb_complement`, `LoebApproximable`, `hyperfiniteExpect_grid_eq_riemannSum`, `loebGridExpect_converges_to_integral` |
| **`ReverseMath`** | [`SandersNSA/ReverseMath/StatefulRealizers.lean`](SandersNSA/ReverseMath/StatefulRealizers.lean) | Dinis–Miquey (`arXiv:2210.05346`) `StatefulRealizer` (`LawfulMonad`), `WitnessM` `do`-DSL, `seq_sound_of_monotone`, `runAndConcretize`, `extractedQuadraticRoot` |
| **`Audit`** | [`SandersNSA/AxiomAudit.lean`](SandersNSA/AxiomAudit.lean) | Compile-time `#audit_pure_constructive` inspecting `Lean.collectAxioms` & `Lean.isNoncomputable` across 60+ declarations |

---

## Quickstart & Live CLI Output

```bash
lake --wfail build                        # Compile all 18 modules (0 sorry, 0 warnings)
lake test                                 # Run executable regression suite (~1s)
lake exe sanders-nsa                      # Run live CLI extraction showcase
lake env lean SandersNSA/AxiomAudit.lean  # Run standalone kernel axiom & computability audit
```

Sample output of `lake exe sanders-nsa`:

```text
==========================================================================
  sanders-computable-nsa v0.1.0 — Live Constructive NSA Extraction
  100% Computable · 0 sorry · 0 Classical.choice · Pure Lean 4.35.0
==========================================================================

[1/4] System H & Nonstandard Dialectica (Xu / van den Berg–Briseid–Safarik / Sanders)
  • Ex0 (∃ m > n, internal):                r0 10       = [11]
  • Ex1 (∀st n, ∃st k, ∀ m ≥ k …):         sr1 7       = [[7, 6, 5, 4, 3, 2, 1, 0]]
  • Ex3  (constructive exact witness):      r3 5        = [0]
  • Ex3'' (NSA lmStLe countdown widening):  r3'' 5      = [5, 4, 3, 2, 1, 0]
  • Ex4  (HAC + Idealisation choice):       r4Choice 4  = [4, 3, 2, 1, 0]
  • Herbrand refinement (largest even ≤ 9): refine 9    = 8

[2/4] Reuniting the Antipodes (Abstract Interpretation, Overspill, IVT & Dini)
  • Overspill precision k(N=20) on 3k ≤ N:  k           = 6
  • Underspill min threshold (n² ≥ 50):     n_min       = 8
  • Hyperfinite IVT on x² - 1/2 (k=99):     x_99        = 142/201  (x_99² = 20164/40401)
  • Grid sign-crossing index at N=99:       i*          = 70/100
  • Dini uniform modulus (k=4, lin moduli): N_Dini      = 9

[3/4] Set/Type/NSA Witness Reification & Metaprogramming Translator
  • Reified Σ-witness (n ∈ [0..20], 7∣n>10): w          = 14
  • Dual: SandersNSA.Tactic.SContinuousOn  <==>  SandersNSA.Antipodes.UniformContOn
  • Dual: SandersNSA.Tactic.SCauchy  <==>  SandersNSA.Antipodes.CauchySeqWithModulus
  • Dual: SandersNSA.Tactic.SLimit  <==>  SandersNSA.Antipodes.LimitWithModulus
  • Dual: SandersNSA.Tactic.SDerivOn  <==>  SandersNSA.Antipodes.DiffOnWithModulus
  • Dual: SandersNSA.Tactic.SRiemannIntegrable  <==>  SandersNSA.Antipodes.RiemannIntegrableWithModulus

[4/4] Higher-Order Reverse Math, Dialogue Trees, Provident HF, Loeb & Stateful Realizers
  • DualQ nilpotent halo (st(5 + ε), ε²):   st=5, ε²=(0, 0)
  • Uniform Cousin 1/4-partition cells:     count       = 4
  • Jordan BV on 0, 1/2, 0, 1/2 (n=6):      P=3/2, N=3/2, TV=3
  • Cliquish box for isolatedSpike at 1/2:  [5/8, 3/4] -> f(lo)=0, f(hi)=0
  • Kleene S1-S9 Cantor fanModulus (par 5): M_fan       = 5
  • Mathias PROV vonNeumann(4) & |2 × 3|:   |4|=4, |2×3|=6
  • Loeb grid P_99(i<50) & E_99[x]:         P=1/2, E[x]=99/200
  • StatefulRealizer do-block (n²-5n+6=0):  store=7 candidates, certified root=3

All subsystems executed constructively with zero axioms beyond [propext, Quot.sound].
```

## License

Apache-2.0
