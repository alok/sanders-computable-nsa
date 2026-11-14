# Specification: `sanders-computable-nsa` — Computable Nonstandard Analysis, Proof Mining & Higher-Order Reverse Mathematics in Lean 4

## 1. Purpose & Provenance

`sanders-computable-nsa` is a cohesive, **100% computable**, `sorry`-free Lean 4 (`v4.35.0`, pure stdlib) library implementing the full computational research program across Alok Singh's correspondence and technical discussions (2024–2026) with **Sam Sanders** (RUB Bochum) and **Chuangjie Xu** (LMU Munich / Fraunhofer):

1. **System $\mathcal{H}$ & Nonstandard Dialectica Term Extraction** — Faithful Lean 4 port and extension of Chuangjie Xu & Sam Sanders's Agda artifact [`nonstandard_dialectica`](https://cj-xu.github.io/agda/nonstandard_dialectica/Index.html) implementing van den Berg, Briseid & Safarik (*APAL* 2012) and Sanders (*CL&C* 2016, *"The computational content of Nonstandard Analysis"*). Resolves two upstream Agda limitations:
   - Eliminates `{-# OPTIONS --no-termination-check #-}` via total structural renaming and substitution in Lean 4.
   - Factors realiser/counterexample types (`dPos`, `dNeg`) through term-erased `FmlShape`, eliminating transport clutter and enabling a machine-checked **Herbrand/Dialectica Witness-Refinement Soundness Theorem** alongside unit-erasure simplification (`Simp`) and executable proof comparisons (`Examples`).
2. **Nonstandardization as Abstract Interpretation (Galois Connection)** — Formalizes Chuangjie Xu's observation (Jan 14, 2026) that nonstandardizing a proof over-approximates its computation by producing a finite candidate witness set or range (`[0..n]` in `Ex₃''` vs. `[0]` in `Ex₃`), paired with decidable concretization collapsing over-approximations back into exact Bishop witnesses.
3. **"Reuniting the Antipodes": Constructive ↔ Nonstandard Analysis, Overspill/Underspill & $\Omega$-Invariance** — Implements Sam Sanders's flagship constructive-NSA correspondence (*"To be or not to be constructive, that is not the question"*, *"Reuniting the antipodes"*, *"The Unreasonable Effectiveness of Nonstandard Analysis"*):
   - Computable exact rational/dyadic arithmetic (`QVal`) and Bishop modulus-bearing structures (`UniformContOn`, `CauchySeqWithModulus`, `DiffOnWithModulus`, `RiemannIntegrableWithModulus`, `UniformConvWithModulus`).
   - Effective local-constructivity hyper-sequences (`HyperSeq`), **Overspill** & **Underspill** threshold extractors ("practical significance of overflow and underflow"), and **$\Omega$-Invariance** (hyperfinite algorithms invariant across reindexings of unlimited $\omega$ computably induce Bishop moduli).
   - **Hyperfinite IVT** (computable grid crossing + approximate IVT + exact root extraction under local non-constancy modulus + formal `LLPO` sign-flip barrier) and **Computable Dini's Theorem** (extracting an explicit uniform convergence modulus from monotone pointwise convergence on compact dyadic grids).
4. **Lean 4 Metaprogramming Translator & Set/Type/NSA Bridge** — Addresses the metaprogramming & type-theory design goals from Apr 2025 and Dec 2025–Jan 2026:
   - `SetTypeBridge`: Computable `HyperfiniteSet` & `ReifyWitness` machinery avoiding `Prop`-erased `Set α` / `noncomputable` contamination when meshing sets, dependent types, and NSA.
   - `Translate`: Verified `@[nsa_constructive_iff]` two-way equivalences, `nsa_to_constructive` / `constructive_to_nsa` Lean 4 tactics, and `#nsa_translate` interactive command unrolling nonstandard definitions (`SContinuousOn`, `SCauchy`, `SDerivOn`, `SRiemannSum`) into explicit constructive modulus types.
5. **Higher-Order Reverse Mathematics & Foundational Models** — Covers all topics from the Jan 31, 2024 Sanders interview, Aug 2025 Loeb measure discussion, and Apr 2026 Stateful Realizers note:
   - **Mutual Independence of `StandardPart` (`st`) and `Transfer`** (including $\Pi_1$-fragments) via explicit computable algebraic countermodels (`ModelTransferNoSt`, `ModelStNoTransfer`).
   - **Cousin's Lemma & Pincherle's Theorem**: Computable dyadic gauge-partition solver (`solveUniformCousin`), constructive Pincherle global-bound extractor (`extractUniformBoundFromModulus`), and witness of the `HBU` uncountable gauge obstruction when positivity moduli are absent.
   - **Borel's Height Functions & Jordan Bounded Variation** (`arXiv:2208.03027`): Explicit `HeightCountable` vs. injection-countability, computable `totalVariation`, **Jordan Decomposition** ($f = f(0) + P - N$), and explicit Borel height bound on $\varepsilon$-jumps ($\le \lfloor V/\varepsilon \rfloor$).
   - **Weak & Generalized Continuity Decomposition** (Waaldijk / Normann–Sanders, `arXiv:2303.00493`): Computable hierarchy (`UniformContinuous`, `Regulated`, `Cliquish`, `QuasiContinuous`, `Darboux`, `BaireOne`) with proved implications and separating counterexamples.
   - **Brouwer–Kleene Dialogue Trees (`KleeneDialogue`)**: Computable higher-order evaluation `(α → β) → β`, finite query-trace modulus extraction (`dialogue_determined_by_queries`), and uniform fan modulus explaining why Kleene S1–S9 succeeds constructively without Cohen forcing.
   - **Mathias's Provident Set Theory (`PROV`)**: Computable hereditarily finite sets (`HF`) closed under rudimentary/provident operations (pairing, union, $\Delta_0$-separation, difference, Cartesian product, transitive closure, von Neumann finite ranks) without full powerset blowup.
   - **Computable Hyperfinite Counting & Loeb Measure**: Hyperfinite grid probability $P_N(A) = |A|/N$, expectation, finite additivity, constructive Carathéodory inner/outer approximation modulus, and quantitative convergence to Riemann/Loeb integrals.
   - **Stateful Realizers Monad** (Dinis & Miquey, `arXiv:2210.05346`): `LawfulMonad` `StatefulRealizer σ α` supporting Lean 4 `do`-notation for stateful witness-cache refinement with proved realization soundness.

## 2. Module Architecture

| Namespace / Module | Core Deliverable |
| --- | --- |
| `SandersNSA.SystemH.Syntax` | Gödel System $\mathcal{T}$ + System $\mathcal{H}$ AST, total `wk`/`subst` (no termination bypass), evaluator, 46 proof rules & axioms (`I`, `NCR`, `HAC`, `HGMPˢᵗ`, `HIP-∀ˢᵗ`, `IRˢᵗ`), Nelson $\Delta_{\text{ns}}$ analyzer |
| `SandersNSA.SystemH.Dialectica` | `FmlShape`, `dPos`/`dNeg`, full `realiser` ($\mathfrak{r}$) & `counterexample` ($\mathfrak{c}$) extractors, `Simp` unit-erasure (`simpTy`/`simpVal`/`backVal`), Herbrand witness-refinement soundness |
| `SandersNSA.SystemH.Examples` | All upstream Agda examples (`Ex₀`, `Ex₁`/`Lm_st_le`, `Ex₂`, `Ex₂'`, `Ex₃`, `Ex₃'`, `Ex₃''`) + Idealisation/`HAC`/`HGMPˢᵗ` witness extractions verified by kernel reduction |
| `SandersNSA.Antipodes.ConstructiveAnalysis` | Computable exact rationals (`QVal`), dyadic scales, Bishop modulus-bearing continuity, Cauchy, derivative, Riemann integral, and uniform convergence types |
| `SandersNSA.Antipodes.AbstractInterpretation` | Galois connection / soundness between nonstandard finite-set/interval over-approximations and exact constructive witnesses |
| `SandersNSA.Antipodes.OverspillOmega` | Effective `HyperSeq`, Overspill/Underspill threshold extractors, and Sanders's $\Omega$-Invariance $\implies$ computable modulus theorem |
| `SandersNSA.Antipodes.IVTAndDini` | Computable hyperfinite grid crossing, approximate IVT, local-non-constancy root finder, `LLPO` sign-flip barrier, and computable Dini uniform-convergence modulus |
| `SandersNSA.Tactic.SetTypeBridge` | `HyperfiniteSet` & `ReifyWitness` solving `Set`/`Subtype`/`Sigma` meshing without `noncomputable` |
| `SandersNSA.Tactic.Translate` | Verified NSA ↔ Constructive iff lemmas, `nsa_to_constructive` & `constructive_to_nsa` Lean 4 tactics, and `#nsa_translate` command |
| `SandersNSA.ReverseMath.Independence` | Computable algebraic models proving mutual independence of `StandardPart` (`st`) and `Transfer` (and fragments) |
| `SandersNSA.ReverseMath.CousinPincherle` | Computable dyadic Cousin gauge-partition solver, constructive Pincherle global bound extractor, and non-uniform gauge counterexample |
| `SandersNSA.ReverseMath.BorelBV` | Borel `HeightCountable`, computable Jordan Bounded Variation (`totalVariation`, $f = f(0) + P - N$), and Borel height bound on $\varepsilon$-jumps |
| `SandersNSA.ReverseMath.ContinuityZoo` | Computable continuity hierarchy (`UniformCont`, `Regulated`, `Cliquish`, `QuasiContinuous`, `Darboux`, `BaireOne`) + separating counterexamples |
| `SandersNSA.ReverseMath.KleeneDialogue` | Brouwer–Kleene dialogue trees, query-list modulus continuity theorem, and uniform fan modulus |
| `SandersNSA.ReverseMath.Provident` | Mathias's Provident Set Theory (`PROV`) over computable hereditarily finite sets (`HF`) without powerset |
| `SandersNSA.ReverseMath.LoebMeasure` | Hyperfinite counting probability, expectation, Loeb approximability modulus, and quantitative Riemann/Loeb convergence |
| `SandersNSA.ReverseMath.StatefulRealizers` | Dinis–Miquey `StatefulRealizer` monad (`LawfulMonad`) with `do`-notation and witness-store refinement soundness |
| `SandersNSA.AxiomAudit` | `#print axioms` & metaprogramming audit verifying `0 sorryAx`, `0` custom axioms, `0 Classical.choice` |

## 3. Acceptance Criteria

- `lake --wfail build` exits `0` with `0` warnings and `0 sorry`.
- `lake test` passes all unit, extraction, equivalence, tactic, and countermodel assertions.
- `lake exe sanders-nsa` prints a self-contained computational showcase across all 17 modules.
- `lake env lean SandersNSA/AxiomAudit.lean` verifies zero `sorryAx`, zero custom axioms, and zero `Classical.choice` across flagship theorems.
- `docs/DEVELOPER_GUIDE.md` provides an exhaustive, pedagogical guide to coding every component from scratch.
