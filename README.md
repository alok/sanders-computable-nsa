# `sanders-computable-nsa`

**Computable Nonstandard Analysis, Proof Mining & Higher-Order Reverse Mathematics in Lean 4 (`v4.35.0`)**

A **100% computable**, zero-`sorry`, zero-external-dependency Lean 4 formalization unifying the computational content of Nonstandard Analysis (NSA) and Higher-Order Reverse Mathematics developed by **Sam Sanders** and **Chuangjie Xu**.

> **Zero-install browser tour**: Every file under [`SandersNSA/`](SandersNSA/) is self-contained pure Lean 4 (`v4.35.0`), verified on every push by [GitHub Actions CI](.github/workflows/ci.yml), and accompanied by [`SPEC.md`](SPEC.md) and [`docs/DEVELOPER_GUIDE.md`](docs/DEVELOPER_GUIDE.md).

## Highlights

1. **System $\mathcal{H}$ & Nonstandard Dialectica Term Extraction (`SandersNSA.SystemH`)**
   - Full Lean 4 port and extension of Chuangjie Xu's Agda [`nonstandard_dialectica`](https://cj-xu.github.io/agda/nonstandard_dialectica/Index.html) (van den Berg–Briseid–Safarik *APAL* 2012; Sanders *CL&C* 2016).
   - **Total structural termination** (eliminates upstream Agda's `--no-termination-check`).
   - **Shape-factored realiser & counterexample types** (`FmlShape`) + unit-erasure simplification (`Simp`) + **machine-checked Herbrand witness-refinement soundness**.
   - Reproduces all upstream proof-extraction comparisons (`Ex₀`–`Ex₃''`) plus Idealisation (`I`), `HAC`, and `HGMPˢᵗ` extractions.
2. **Reuniting the Antipodes & Abstract Interpretation (`SandersNSA.Antipodes`)**
   - **Abstract Interpretation Galois Connection**: Formalizes how nonstandard proofs compute finite candidate witness sets/ranges (`[0..n]`) that soundly over-approximate constructive point witnesses (`[0]`), with decidable concretization.
   - **Overspill, Underspill & $\Omega$-Invariance**: Formalizes Sanders's *Reuniting the Antipodes* / *To be or not to be constructive* bridge — $\Omega$-invariant hyperfinite algorithms computably induce explicit Bishop moduli.
   - **Hyperfinite IVT & Computable Dini's Theorem**: Grid-crossing approximate IVT, exact root extraction under local non-constancy, formal `LLPO` sign-flip obstruction, and computable uniform-convergence modulus extraction for Dini's theorem.
3. **Lean 4 Metaprogramming Translator & Set/Type/NSA Bridge (`SandersNSA.Tactic`)**
   - `HyperfiniteSet` & `ReifyWitness` bridge dependent `Sigma` witnesses and set-like NSA predicates without `noncomputable` contamination.
   - `nsa_to_constructive`, `constructive_to_nsa`, and `#nsa_translate` automatically translate between nonstandard predicates (`SContinuousOn`, `SCauchy`, `SDerivOn`, `SRiemannSum`) and explicit constructive modulus types.
4. **Higher-Order Reverse Mathematics & Foundational Models (`SandersNSA.ReverseMath`)**
   - **Mutual Independence of `st` and `Transfer`** (including fragments) via computable algebraic countermodels.
   - **Cousin's Lemma & Pincherle's Theorem**: Computable dyadic gauge-partition solver + global bound extractor + non-uniform gauge obstruction.
   - **Borel's Height Functions & Jordan Bounded Variation** (`arXiv:2208.03027`): `HeightCountable`, `totalVariation`, Jordan decomposition $f = f(0) + P - N$, and explicit $\lfloor V/\varepsilon \rfloor$ jump-height bound.
   - **Continuity Zoo** (`arXiv:2303.00493`): Computable hierarchy (`UniformCont`, `Regulated`, `Cliquish`, `QuasiContinuous`, `Darboux`, `BaireOne`) + separating counterexamples.
   - **Brouwer–Kleene Dialogue Trees**: Higher-order `(α → β) → β` evaluation, finite query-trace continuity, and uniform fan modulus.
   - **Mathias's Provident Set Theory (`PROV`)**: Computable hereditarily finite sets (`HF`) closed under rudimentary/provident operations without powerset.
   - **Computable Loeb Measure**: Hyperfinite grid probability $P_N(A) = |A|/N$, expectation, Loeb approximability modulus, and Riemann/Loeb convergence.
   - **Stateful Realizers Monad** (`arXiv:2210.05346`): `LawfulMonad` `StatefulRealizer` with `do`-notation and witness-store refinement soundness.

## Quickstart

```bash
lake --wfail build                        # Compile all modules (0 sorry, 0 warnings)
lake test                                 # Run executable test suite
lake exe sanders-nsa                      # Print extracted terms, moduli, partitions & decompositions
lake env lean SandersNSA/AxiomAudit.lean  # Kernel axiom & computability audit
```

## License

Apache-2.0
