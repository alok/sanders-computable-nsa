# CLAUDE.md — `sanders-computable-nsa`

## Build & Verification Commands

```bash
lake --wfail build                        # Build library + executables (0 sorry, 0 warnings)
lake test                                 # Run executable unit, extraction, and countermodel test suite
lake exe sanders-nsa                      # Run live CLI showcase printing extracted witnesses & moduli
lake env lean SandersNSA/AxiomAudit.lean  # Verify 0 sorryAx, 0 custom axioms, 0 Classical.choice
```

## Engineering & Computability Rules

1. **Toolchain**: `leanprover/lean4:v4.35.0` (pure stdlib, zero external dependencies, builds in seconds).
2. **100% Computable**: **Zero `noncomputable` definitions** anywhere in the repository. Prefer `Fin`, `List`, inductive trees, and explicit witness-carrying `Sigma` / `structure` records over `Finset` or `Prop`-erased existentials.
3. **Zero `sorry`**, **zero custom `axiom`**, **zero `partial` / `unsafe` / `native_decide`**, and **zero `Classical.choice`** on constructive/computational theorems.
4. **`autoImplicit := false`** across the entire package.
5. **Continuous Public Updates**: Make atomic commits per module and push immediately to `https://github.com/alok/sanders-computable-nsa`. Track milestones in Linear (`Alok` team).
