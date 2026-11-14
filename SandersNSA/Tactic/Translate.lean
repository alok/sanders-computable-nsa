/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import SandersNSA.Tactic.SetTypeBridge
import SandersNSA.Antipodes.OverspillOmega

/-!
# Bidirectional NSA ↔ Constructive Calculus Translation & Lean 4 Tactics (`Translate`)

Implements the bidirectional translation engine envisioned in Alok Singh's April 6, 2026
blog post (*Nonstandard Definitions*) and Sam Sanders's *"Reuniting the antipodes"*:

> *"I keep wanting a Lean tactic that translates between the two, so you can think in
> whichever style fits the step and switch freely."*

## Contents
1. **Quantitative Nonstandard Calculus Predicates (`Type`-valued)**:
   - `SContinuousOn`: halo preservation `x ≈ y ⇒ *f(x) ≈ *f(y)` on `[a, b]`.
   - `SCauchy`: Sanders's Ω-invariance `s(M₁) ≈ s(M₂)` across unbounded reindexings.
   - `SLimit`: `s(Ω) ≈ *L` along unbounded indices.
   - `SDerivOn`: infinitesimal ratio `f(x + dx) - f(x) ≈ f'(x) · dx` up to `o(|dx|)`.
   - `SRiemannIntegrable`: hyperfinite grid sum `∑_{i=0}^{Ω} f(x_i) Δx ≈ *I`.
2. **Verified Constructive Two-Way Equivalences** (`*_to_*` + `*_nonempty_iff`), preserving
   explicit `Modulus` data in both directions with zero `Classical.choice`.
3. **Lean 4 Metaprogramming Tactics & Command**:
   - `nsa_to_constructive` / `constructive_to_nsa`: switch the current goal (`Type` or `Prop`)
     between nonstandard and Bishop modulus-bearing forms.
   - `nsa_to_constructive_at h` / `constructive_to_nsa_at h`: translate a local hypothesis `h`
     while preserving full definitional reduction of extracted moduli.
   - `#nsa_translate <term>`: command inspecting a calculus signature and displaying its dual.
-/

namespace SandersNSA
namespace Tactic

open Lean Meta Elab Tactic Command
open SandersNSA.Antipodes

/-- Nonstandard infinite-closeness notation `x ≈ₘ y` (`InfinitelyClose x y`). -/
infix:50 " ≈ₘ " => InfinitelyClose

/-! ## 1. Sequential Nonstandard Calculus Definitions -/

/-- **Nonstandard S-Continuity on `[a, b]`**:
    Whenever two bounded hyper-sequences `x, y` in `[a, b]` lie within the `haloScale k`
    infinitesimal scale from stage `N` onward, `*f(x)` and `*f(y)` lie within `1 / (k + 1)`. -/
structure SContinuousOn (f : QVal → QVal) (a b : QVal) : Type where
  haloScale : Modulus
  preserveHalo : ∀ (x y : HyperSeq QVal),
    (∀ n : Nat, QVal.le a (x n) ∧ QVal.le (x n) b) →
    (∀ n : Nat, QVal.le a (y n) ∧ QVal.le (y n) b) →
    ∀ (k N : Nat),
      (∀ n : Nat, N ≤ n → QVal.le (QVal.dist (x n) (y n)) (QVal.unitFrac (haloScale k))) →
      ∀ n : Nat, N ≤ n → QVal.le (QVal.dist (f (x n)) (f (y n))) (QVal.unitFrac k)

/-- **Halo Mapping Theorem (`x ≈ₘ y ⇒ *f(x) ≈ₘ *f(y)`)**:
    Every `SContinuousOn` function maps infinitely close sequences in `[a, b]` to infinitely
    close output sequences with composed modulus `ω_close ∘ haloScale`. -/
def SContinuousOn.mapClose {f : QVal → QVal} {a b : QVal}
    (hS : SContinuousOn f a b) {x y : HyperSeq QVal}
    (hx : ∀ n : Nat, QVal.le a (x n) ∧ QVal.le (x n) b)
    (hy : ∀ n : Nat, QVal.le a (y n) ∧ QVal.le (y n) b)
    (hClose : x ≈ₘ y) :
    liftSeq1 f x ≈ₘ liftSeq1 f y where
  modulus k := hClose.modulus (hS.haloScale k)
  spec k n hn :=
    hS.preserveHalo x y hx hy k (hClose.modulus (hS.haloScale k))
      (fun m hm => hClose.spec (hS.haloScale k) m hm) n hn

/-- **Nonstandard S-Cauchy Sequence**:
    `s(M₁) ≈ₘ s(M₂)` uniformly across all unbounded hypernatural reindexings `M₁, M₂`. -/
structure SCauchy (s : HyperSeq QVal) : Type where
  invariance : OmegaInvariantSeq s

/-- **Nonstandard S-Limit (`s(Ω) ≈ₘ *L`)**:
    The hyper-sequence `s` is infinitely close to the constant standard copy `*L`. -/
structure SLimit (s : HyperSeq QVal) (L : QVal) : Type where
  closeToLimit : s ≈ₘ starConst L

/-- **Nonstandard S-Derivative on `[a, b]`**:
    Along any bounded base sequence `x` and non-zero infinitesimal perturbation `dx` in `[a, b]`,
    `f(x + dx) - f(x)` agrees with `f'(x) · dx` within `|dx| / (k + 1)`. -/
structure SDerivOn (f f' : QVal → QVal) (a b : QVal) : Type where
  haloScale : Modulus
  approxLinear : ∀ (x dx : HyperSeq QVal) (k N : Nat),
    (∀ n : Nat, N ≤ n →
      QVal.le a (x n) ∧ QVal.le (x n) b ∧
      QVal.le a (x n + dx n) ∧ QVal.le (x n + dx n) b ∧
      QVal.lt 0 (dx n).abs ∧
      QVal.le (dx n).abs (QVal.unitFrac (haloScale k))) →
    ∀ n : Nat, N ≤ n →
      QVal.le (QVal.dist (f (x n + dx n) - f (x n)) (f' (x n) * dx n))
              (QVal.unitFrac k * (dx n).abs)

/-- **Nonstandard Hyperfinite Riemann Integrability on `[0, 1]`**:
    The hyperfinite uniform-grid sum `N ↦ ∑_{i=0}^{N} f(i/(N+1)) · (1/(N+1))` is infinitely
    close to `*integral`. -/
structure SRiemannIntegrable (f : QVal → QVal) : Type where
  integral : QVal
  hyperSumClose : (fun N => uniformGridSum f N) ≈ₘ starConst integral

/-! ## 2. Verified Constructive ↔ Nonstandard Bridge Theorems -/

/-- **NSA → Constructive (`SContinuousOn → UniformContOn`)**. -/
def sContinuousOn_to_uniformCont {f : QVal → QVal} {a b : QVal}
    (hS : SContinuousOn f a b) : UniformContOn f a b where
  modulus := hS.haloScale
  spec k x y hax hxb hay hyb hdist :=
    hS.preserveHalo (starConst x) (starConst y)
      (fun _ => ⟨hax, hxb⟩) (fun _ => ⟨hay, hyb⟩)
      k 0 (fun _ _ => hdist) 0 (Nat.le_refl 0)

/-- **Constructive → NSA (`UniformContOn → SContinuousOn`)**. -/
def uniformCont_to_sContinuousOn {f : QVal → QVal} {a b : QVal}
    (hC : UniformContOn f a b) : SContinuousOn f a b where
  haloScale := hC.modulus
  preserveHalo x y hx hy k _N hClose n hn :=
    hC.spec k (x n) (y n) (hx n).1 (hx n).2 (hy n).1 (hy n).2 (hClose n hn)

theorem sContinuousOn_nonempty_iff (f : QVal → QVal) (a b : QVal) :
    Nonempty (SContinuousOn f a b) ↔ Nonempty (UniformContOn f a b) :=
  ⟨fun ⟨h⟩ => ⟨sContinuousOn_to_uniformCont h⟩,
   fun ⟨h⟩ => ⟨uniformCont_to_sContinuousOn h⟩⟩

/-- **NSA → Constructive (`SCauchy → CauchySeqWithModulus`)** via Sanders's Ω-Invariance. -/
def sCauchy_to_cauchy {s : HyperSeq QVal} (hS : SCauchy s) : CauchySeqWithModulus s :=
  omegaInvariant_to_cauchy hS.invariance

/-- **Constructive → NSA (`CauchySeqWithModulus → SCauchy`)**. -/
def cauchy_to_sCauchy {s : HyperSeq QVal} (hC : CauchySeqWithModulus s) : SCauchy s :=
  ⟨cauchy_to_omegaInvariant hC⟩

theorem sCauchy_nonempty_iff (s : HyperSeq QVal) :
    Nonempty (SCauchy s) ↔ Nonempty (CauchySeqWithModulus s) :=
  ⟨fun ⟨h⟩ => ⟨sCauchy_to_cauchy h⟩, fun ⟨h⟩ => ⟨cauchy_to_sCauchy h⟩⟩

/-- **NSA → Constructive (`SLimit → LimitWithModulus`)**. -/
def sLimit_to_limit {s : HyperSeq QVal} {L : QVal} (hS : SLimit s L) : LimitWithModulus s L where
  modulus := hS.closeToLimit.modulus
  spec := hS.closeToLimit.spec

/-- **Constructive → NSA (`LimitWithModulus → SLimit`)**. -/
def limit_to_sLimit {s : HyperSeq QVal} {L : QVal} (hC : LimitWithModulus s L) : SLimit s L where
  closeToLimit := ⟨hC.modulus, hC.spec⟩

theorem sLimit_nonempty_iff (s : HyperSeq QVal) (L : QVal) :
    Nonempty (SLimit s L) ↔ Nonempty (LimitWithModulus s L) :=
  ⟨fun ⟨h⟩ => ⟨sLimit_to_limit h⟩, fun ⟨h⟩ => ⟨limit_to_sLimit h⟩⟩

/-- Every `SLimit` witness induces an `SCauchy` witness. -/
def SLimit.toSCauchy {s : HyperSeq QVal} {L : QVal} (h : SLimit s L) : SCauchy s :=
  cauchy_to_sCauchy (sLimit_to_limit h).toCauchy

/-- **NSA → Constructive (`SDerivOn → DiffOnWithModulus`)**. -/
def sDerivOn_to_diff {f f' : QVal → QVal} {a b : QVal}
    (hS : SDerivOn f f' a b) : DiffOnWithModulus f f' a b where
  modulus := hS.haloScale
  spec k x h hax hxb haxh hxbh hpos hsmall :=
    hS.approxLinear (starConst x) (starConst h) k 0
      (fun _ _ => ⟨hax, hxb, haxh, hxbh, hpos, hsmall⟩) 0 (Nat.le_refl 0)

/-- **Constructive → NSA (`DiffOnWithModulus → SDerivOn`)**. -/
def diff_to_sDerivOn {f f' : QVal → QVal} {a b : QVal}
    (hC : DiffOnWithModulus f f' a b) : SDerivOn f f' a b where
  haloScale := hC.modulus
  approxLinear x dx k _N hCond n hn :=
    let ⟨hax, hxb, haxd, hxbd, hpos, hsmall⟩ := hCond n hn
    hC.spec k (x n) (dx n) hax hxb haxd hxbd hpos hsmall

theorem sDerivOn_nonempty_iff (f f' : QVal → QVal) (a b : QVal) :
    Nonempty (SDerivOn f f' a b) ↔ Nonempty (DiffOnWithModulus f f' a b) :=
  ⟨fun ⟨h⟩ => ⟨sDerivOn_to_diff h⟩, fun ⟨h⟩ => ⟨diff_to_sDerivOn h⟩⟩

/-- **NSA → Constructive (`SRiemannIntegrable → RiemannIntegrableWithModulus`)**. -/
def sRiemann_to_riemann {f : QVal → QVal}
    (hS : SRiemannIntegrable f) : RiemannIntegrableWithModulus f where
  integral := hS.integral
  modulus := hS.hyperSumClose.modulus
  spec := hS.hyperSumClose.spec

/-- **Constructive → NSA (`RiemannIntegrableWithModulus → SRiemannIntegrable`)**. -/
def riemann_to_sRiemann {f : QVal → QVal}
    (hC : RiemannIntegrableWithModulus f) : SRiemannIntegrable f where
  integral := hC.integral
  hyperSumClose := ⟨hC.modulus, hC.spec⟩

theorem sRiemann_nonempty_iff (f : QVal → QVal) :
    Nonempty (SRiemannIntegrable f) ↔ Nonempty (RiemannIntegrableWithModulus f) :=
  ⟨fun ⟨h⟩ => ⟨sRiemann_to_riemann h⟩, fun ⟨h⟩ => ⟨riemann_to_sRiemann h⟩⟩

/-! ## 3. Lean 4 Metaprogramming Translation Table, Tactics & Command -/

/-- Entry in the verified NSA ↔ Constructive translation dictionary. -/
structure DualEntry where
  nsaName : Name
  constructiveName : Name
  nsaToConstructiveFn : Name
  constructiveToNsaFn : Name
  nonemptyIff : Name
  summary : String
  deriving Repr

/-- Canonical bidirectional dictionary linking nonstandard sequential definitions to Bishop
    modulus-bearing definitions. -/
def nsaTranslationTable : List DualEntry :=
  [ { nsaName := ``SContinuousOn
      constructiveName := ``UniformContOn
      nsaToConstructiveFn := ``sContinuousOn_to_uniformCont
      constructiveToNsaFn := ``uniformCont_to_sContinuousOn
      nonemptyIff := ``sContinuousOn_nonempty_iff
      summary := "x ≈ y ⇒ *f(x) ≈ *f(y)  ⟷  Bishop UniformContOn with modulus ω(k)" },
    { nsaName := ``SCauchy
      constructiveName := ``CauchySeqWithModulus
      nsaToConstructiveFn := ``sCauchy_to_cauchy
      constructiveToNsaFn := ``cauchy_to_sCauchy
      nonemptyIff := ``sCauchy_nonempty_iff
      summary := "Ω-invariance s(M₁) ≈ s(M₂)  ⟷  Bishop CauchySeqWithModulus" },
    { nsaName := ``SLimit
      constructiveName := ``LimitWithModulus
      nsaToConstructiveFn := ``sLimit_to_limit
      constructiveToNsaFn := ``limit_to_sLimit
      nonemptyIff := ``sLimit_nonempty_iff
      summary := "s(Ω) ≈ *L  ⟷  Bishop LimitWithModulus" },
    { nsaName := ``SDerivOn
      constructiveName := ``DiffOnWithModulus
      nsaToConstructiveFn := ``sDerivOn_to_diff
      constructiveToNsaFn := ``diff_to_sDerivOn
      nonemptyIff := ``sDerivOn_nonempty_iff
      summary := "f(x+dx)-f(x) ≈ f'(x)·dx  ⟷  Bishop DiffOnWithModulus" },
    { nsaName := ``SRiemannIntegrable
      constructiveName := ``RiemannIntegrableWithModulus
      nsaToConstructiveFn := ``sRiemann_to_riemann
      constructiveToNsaFn := ``riemann_to_sRiemann
      nonemptyIff := ``sRiemann_nonempty_iff
      summary := "∑_{i=0}^{Ω} f(x_i)Δx ≈ *I  ⟷  Bishop RiemannIntegrableWithModulus" } ]

/-- Pure lookup helper used both by tactics and runtime tests. -/
def lookupDualConcept (c : Name) : Option (Name × String) :=
  match nsaTranslationTable.find? (fun e => e.nsaName == c) with
  | some e => some (e.constructiveName, e.summary)
  | none =>
      match nsaTranslationTable.find? (fun e => e.constructiveName == c) with
      | some e => some (e.nsaName, e.summary)
      | none => none

/-- Extract either a direct head constant `C ...` or a `Nonempty (C ...)` wrapper. -/
def classifyGoalExpr (e : Expr) : Option (Bool × Name) :=
  let fn := e.getAppFn
  match fn.constName? with
  | some ``Nonempty =>
      match e.getAppArgs with
      | #[inner] =>
          match inner.getAppFn.constName? with
          | some c => some (true, c)
          | none => none
      | _ => none
  | some c => some (false, c)
  | none => none

/-- **`nsa_to_constructive` tactic**:
    Switches a nonstandard calculus goal (`SContinuousOn`, `SCauchy`, `SLimit`, `SDerivOn`,
    `SRiemannIntegrable`, or `Nonempty (...)`) into its constructive Bishop modulus-bearing goal. -/
elab "nsa_to_constructive" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match classifyGoalExpr target with
  | some (false, c) =>
      match nsaTranslationTable.find? (fun e => e.nsaName == c) with
      | some entry =>
          let fnIdent := mkIdent entry.constructiveToNsaFn
          evalTactic (← `(tactic| apply $fnIdent))
      | none =>
          throwError "nsa_to_constructive: goal head `{c}` is not a registered NSA predicate"
  | some (true, c) =>
      match nsaTranslationTable.find? (fun e => e.nsaName == c) with
      | some entry =>
          let iffIdent := mkIdent entry.nonemptyIff
          evalTactic (← `(tactic| rw [$iffIdent:ident]))
      | none =>
          throwError "nsa_to_constructive: Nonempty inner head `{c}` is not a registered NSA predicate"
  | none =>
      throwError "nsa_to_constructive: could not recognize goal head"

/-- **`constructive_to_nsa` tactic**:
    Switches a constructive Bishop calculus goal (`UniformContOn`, `CauchySeqWithModulus`,
    `LimitWithModulus`, `DiffOnWithModulus`, `RiemannIntegrableWithModulus`, or `Nonempty (...)`)
    into its sequential nonstandard counterpart. -/
elab "constructive_to_nsa" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match classifyGoalExpr target with
  | some (false, c) =>
      match nsaTranslationTable.find? (fun e => e.constructiveName == c) with
      | some entry =>
          let fnIdent := mkIdent entry.nsaToConstructiveFn
          evalTactic (← `(tactic| apply $fnIdent))
      | none =>
          throwError "constructive_to_nsa: goal head `{c}` is not a registered constructive predicate"
  | some (true, c) =>
      match nsaTranslationTable.find? (fun e => e.constructiveName == c) with
      | some entry =>
          let iffIdent := mkIdent entry.nonemptyIff
          evalTactic (← `(tactic| rw [← $iffIdent:ident]))
      | none =>
          throwError "constructive_to_nsa: Nonempty inner head `{c}` is not a registered constructive predicate"
  | none =>
      throwError "constructive_to_nsa: could not recognize goal head"

/-- **`nsa_to_constructive_at h` tactic**:
    Translates a nonstandard local hypothesis `h` into its Bishop modulus-bearing counterpart
    while preserving full definitional reduction of extracted moduli. -/
elab "nsa_to_constructive_at " h:ident : tactic => withMainContext do
  let ldecl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars ldecl.type
  match ty.getAppFn.constName? with
  | some c =>
      match nsaTranslationTable.find? (fun e => e.nsaName == c) with
      | some entry =>
          let fnIdent := mkIdent entry.nsaToConstructiveFn
          evalTactic (← `(tactic| let $h := $fnIdent $h))
      | none =>
          throwError "nsa_to_constructive_at: `{h.getId}` has head `{c}`, not a registered NSA predicate"
  | none =>
      throwError "nsa_to_constructive_at: could not inspect head of `{h.getId}`"

/-- **`constructive_to_nsa_at h` tactic**:
    Translates a constructive Bishop hypothesis `h` into its sequential nonstandard counterpart. -/
elab "constructive_to_nsa_at " h:ident : tactic => withMainContext do
  let ldecl ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars ldecl.type
  match ty.getAppFn.constName? with
  | some c =>
      match nsaTranslationTable.find? (fun e => e.constructiveName == c) with
      | some entry =>
          let fnIdent := mkIdent entry.constructiveToNsaFn
          evalTactic (← `(tactic| let $h := $fnIdent $h))
      | none =>
          throwError "constructive_to_nsa_at: `{h.getId}` has head `{c}`, not a registered constructive predicate"
  | none =>
      throwError "constructive_to_nsa_at: could not inspect head of `{h.getId}`"

/-- **`#nsa_translate <term>` command**:
    Elaborates `<term>`, locates its head in `nsaTranslationTable` (in either direction),
    constructs the dual expression with the same arguments, and logs the translation summary. -/
elab "#nsa_translate " t:term : command => runTermElabM fun _ => do
  let e ← Term.elabTermAndSynthesize t none
  let e ← instantiateMVars e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some c =>
      match lookupDualConcept c with
      | some (dualConst, summary) =>
          let dualExpr ← mkAppOptM dualConst (args.map some)
          let origPP ← ppExpr e
          let dualPP ← ppExpr dualExpr
          logInfo m!"[NSA ↔ Constructive]\n  Input : {origPP}\n  Dual  : {dualPP}\n  Bridge: {summary}"
      | none =>
          throwError "#nsa_translate: `{c}` is not in `nsaTranslationTable`"
  | none =>
      throwError "#nsa_translate: expected an application of an NSA or constructive predicate"

/-! ## 4. Live Tactic Demonstrations -/

/-- Proving nonstandard `SContinuousOn` of the identity map by switching the goal to
    constructive `UniformContOn` via `nsa_to_constructive`. -/
def id_sContinuousOn : SContinuousOn (fun x => x) 0 1 := by
  nsa_to_constructive
  exact { modulus := fun k => k, spec := fun _ _ _ _ _ _ _ h => h }

/-- Proving constructive `UniformContOn` from a nonstandard `SContinuousOn` hypothesis
    using `constructive_to_nsa` on the goal! -/
def roundtrip_uniformCont {f : QVal → QVal} (h : SContinuousOn f 0 1) : UniformContOn f 0 1 := by
  constructive_to_nsa
  exact h

/-- Translating a local `SCauchy` hypothesis into `CauchySeqWithModulus` in-place via
    `nsa_to_constructive_at`. -/
def scauchy_hyp_demo {s : HyperSeq QVal} (h : SCauchy s) : CauchySeqWithModulus s := by
  nsa_to_constructive_at h
  exact h

/-- Propositional `Nonempty` rewriting via `nsa_to_constructive`. -/
theorem nonempty_slimit_demo (s : HyperSeq QVal) (L : QVal)
    (h : Nonempty (LimitWithModulus s L)) : Nonempty (SLimit s L) := by
  nsa_to_constructive
  exact h

end Tactic
end SandersNSA
