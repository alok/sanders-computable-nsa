/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.SystemH.Syntax

/-!
# Nonstandard Dialectica Interpretation (`D_st`), Unit-Erasure Simplifier & Soundness

Computable Lean 4 port and extension of `Dialectica.agda` and `Simp.agda` from
Chuangjie Xu & Sam Sanders's `nonstandard_dialectica` (following van den Berg, Briseid
& Safarik, *APAL* 2012, and Sanders, *CL&C* 2016).

## Architectural Advances over Upstream Agda
1. **Parallel-Substitution Invariance**: `dPos_substPar` and `dNeg_substPar` are proved by direct
   mutual structural induction on `Fml`, making all single-variable and successor-shift transport
   identities (`dPos_substF`, `dPos_shiftSuccF`, etc.) immediate corollaries.
2. **Transport-Free Unit Erasure (`simpTy` / `simpVal` / `backVal`)**: Upstream `Simp.agda` threads
   propositional `transport` proofs through `careⁱʳ`, slowing kernel normalization. Here `simpListTy`,
   `simpProdTy`, and `simpArrTy` compute by direct pattern-matching so `simpVal` and `backVal` are
   completely transport-free (`rfl` reduction!).
3. **Machine-Checked Semantic & Herbrand Soundness**: Proves the substitution/evaluation soundness
   lemmas (`eval_wk`, `eval_substPar`, `eval_subst`) for System T and proves computable constructive
   witness refinement (`extractExactWitness`) turning Herbrand-valid finite candidate lists into
   exact constructive dependent witnesses without `Classical.choice`.
-/

namespace SandersNSA
namespace SystemH

/-! ## 1. Types of Realisers (`d⁺`) and Counterexamples (`d⁻`) -/

/-- Simultaneous positive realiser type `d⁺(Φ)` and negative counterexample type `d⁻(Φ)`
    computed in a single structural pass on `Fml` (avoiding `Fml.brecOn`). -/
def dTypes {Γ : Cxt} : Fml Γ → Ty × Ty
  | .st (σ := σ) _ => (σ, .unit)
  | .eq _ _ => (.unit, .unit)
  | .le _ _ => (.unit, .unit)
  | .mem _ _ => (.unit, .unit)
  | .and A B =>
      let dA := dTypes A
      let dB := dTypes B
      (.prod dA.1 dB.1, .prod dA.2 dB.2)
  | .or A B =>
      let dA := dTypes A
      let dB := dTypes B
      (.prod dA.1 dB.1, .prod dA.2 dB.2)
  | .imp A B =>
      let dA := dTypes A
      let dB := dTypes B
      (.prod (.arr (.list dA.1) (.list dB.1)) (.arr (.list dA.1) (.arr dB.2 (.list dA.2))),
       .prod (.list dA.1) dB.2)
  | .allH A => dTypes A
  | .exH A =>
      let dA := dTypes A
      (dA.1, .list dA.2)
  | .allSt (σ := σ) A =>
      let dA := dTypes A
      (.arr σ (.list dA.1), .prod σ dA.2)
  | .exSt (σ := σ) A =>
      let dA := dTypes A
      (.prod σ dA.1, .list dA.2)
  | .even _ => (.unit, .unit)

/-- Type `d⁺(Φ)` of potential positive witnesses / realisers of a System H formula. -/
@[reducible] def dPos {Γ : Cxt} (A : Fml Γ) : Ty := (dTypes A).1

/-- Type `d⁻(Φ)` of counterexample challenges of a System H formula. -/
@[reducible] def dNeg {Γ : Cxt} (A : Fml Γ) : Ty := (dTypes A).2

/-- Candidate-list type `(d⁺ A)*`. -/
abbrev dPosStar {Γ : Cxt} (A : Fml Γ) : Ty := .list (dPos A)

/-- Counterexample-list type `(d⁻ A)*`. -/
abbrev dNegStar {Γ : Cxt} (A : Fml Γ) : Ty := .list (dNeg A)

/-- Map `d⁺*` across an assumption context `Ξ`. -/
def ddPosStar {Γ : Cxt} : Asmpt Γ → Cxt
  | .nil => .nil
  | .snoc Ξ A => .snoc (ddPosStar Ξ) (dPosStar A)

/-- Map `d⁻*` across an assumption context `Ξ`. -/
def ddNegStar {Γ : Cxt} : Asmpt Γ → Cxt
  | .nil => .nil
  | .snoc Ξ A => .snoc (ddNegStar Ξ) (dNegStar A)

/-- Left-nested product `Π ρ` of a snoc-list of types. -/
def prodCxt : Cxt → Ty
  | .nil => .unit
  | .snoc ρ σ => .prod (prodCxt ρ) σ

/-- Tuple of System T terms `Tms Γ ρ := Tm Γ (Π ρ)`. -/
abbrev Tms (Γ : Cxt) (ρ : Cxt) : Type := Tm Γ (prodCxt ρ)

/-! ## 2. Invariance of `d⁺` and `d⁻` under Renaming & Parallel Substitution -/

theorem dTypes_wkF {Γ Δ : Cxt} (ξ : Ren Γ Δ) : (A : Fml Γ) → dTypes (A.wkF ξ) = dTypes A
  | .st _ | .eq _ _ | .le _ _ | .mem _ _ | .even _ => rfl
  | .and A B => by simp [Fml.wkF, dTypes, dTypes_wkF ξ A, dTypes_wkF ξ B]
  | .or A B => by simp [Fml.wkF, dTypes, dTypes_wkF ξ A, dTypes_wkF ξ B]
  | .imp A B => by simp [Fml.wkF, dTypes, dTypes_wkF ξ A, dTypes_wkF ξ B]
  | .allH A => dTypes_wkF (Ren.lift ξ) A
  | .exH A => by simp [Fml.wkF, dTypes, dTypes_wkF (Ren.lift ξ) A]
  | .allSt A => by simp [Fml.wkF, dTypes, dTypes_wkF (Ren.lift ξ) A]
  | .exSt A => by simp [Fml.wkF, dTypes, dTypes_wkF (Ren.lift ξ) A]

theorem dPos_wkF {Γ Δ : Cxt} (ξ : Ren Γ Δ) (A : Fml Γ) : dPos (A.wkF ξ) = dPos A :=
  congrArg Prod.fst (dTypes_wkF ξ A)

theorem dNeg_wkF {Γ Δ : Cxt} (ξ : Ren Γ Δ) (A : Fml Γ) : dNeg (A.wkF ξ) = dNeg A :=
  congrArg Prod.snd (dTypes_wkF ξ A)

theorem dTypes_substPar {Γ Δ : Cxt} (θ : Sub Γ Δ) : (A : Fml Γ) → dTypes (A.substPar θ) = dTypes A
  | .st _ | .eq _ _ | .le _ _ | .mem _ _ | .even _ => rfl
  | .and A B => by simp [Fml.substPar, dTypes, dTypes_substPar θ A, dTypes_substPar θ B]
  | .or A B => by simp [Fml.substPar, dTypes, dTypes_substPar θ A, dTypes_substPar θ B]
  | .imp A B => by simp [Fml.substPar, dTypes, dTypes_substPar θ A, dTypes_substPar θ B]
  | .allH A => dTypes_substPar (Sub.lift θ) A
  | .exH A => by simp [Fml.substPar, dTypes, dTypes_substPar (Sub.lift θ) A]
  | .allSt A => by simp [Fml.substPar, dTypes, dTypes_substPar (Sub.lift θ) A]
  | .exSt A => by simp [Fml.substPar, dTypes, dTypes_substPar (Sub.lift θ) A]

theorem dPos_substPar {Γ Δ : Cxt} (θ : Sub Γ Δ) (A : Fml Γ) : dPos (A.substPar θ) = dPos A :=
  congrArg Prod.fst (dTypes_substPar θ A)

theorem dNeg_substPar {Γ Δ : Cxt} (θ : Sub Γ Δ) (A : Fml Γ) : dNeg (A.substPar θ) = dNeg A :=
  congrArg Prod.snd (dTypes_substPar θ A)

theorem dPos_substF {Γ : Cxt} {σ : Ty} (A : Fml (.snoc Γ σ)) (u : Tm Γ σ) :
    dPos (A.substF u) = dPos A := dPos_substPar (Sub.single u) A

theorem dNeg_substF {Γ : Cxt} {σ : Ty} (A : Fml (.snoc Γ σ)) (u : Tm Γ σ) :
    dNeg (A.substF u) = dNeg A := dNeg_substPar (Sub.single u) A

theorem dPos_shiftSuccF {Γ : Cxt} (A : Fml (.snoc Γ .nat)) :
    dPos A.shiftSuccF = dPos A := dPos_substPar Sub.shiftSucc A

theorem dNeg_shiftSuccF {Γ : Cxt} (A : Fml (.snoc Γ .nat)) :
    dNeg A.shiftSuccF = dNeg A := dNeg_substPar Sub.shiftSucc A

theorem ddPosStar_wknAsmpt {Γ : Cxt} {σ : Ty} :
    (Ξ : Asmpt Γ) → ddPosStar (wknAsmpt (σ := σ) Ξ) = ddPosStar Ξ
  | .nil => rfl
  | .snoc Ξ A => by
      simp [wknAsmpt, ddPosStar, ddPosStar_wknAsmpt Ξ, dPosStar, Fml.wknF, dPos_wkF]

theorem ddNegStar_wknAsmpt {Γ : Cxt} {σ : Ty} :
    (Ξ : Asmpt Γ) → ddNegStar (wknAsmpt (σ := σ) Ξ) = ddNegStar Ξ
  | .nil => rfl
  | .snoc Ξ A => by
      simp [wknAsmpt, ddNegStar, ddNegStar_wknAsmpt Ξ, dNegStar, Fml.wknF, dNeg_wkF]

/-- Cast a System T term along a type equality via direct pattern matching. -/
def castTm {Γ : Cxt} {σ τ : Ty} (h : σ = τ) (t : Tm Γ σ) : Tm Γ τ :=
  match h with
  | rfl => t

/-- Cast a System T term along a context equality via direct pattern matching. -/
def castCtxTm {Γ₁ Γ₂ : Cxt} {σ : Ty} (h : Γ₁ = Γ₂) (t : Tm Γ₁ σ) : Tm Γ₂ σ :=
  match h with
  | rfl => t

/-- Cast a System T term along simultaneous context and type equalities. -/
def castCtxTyTm {Γ₁ Γ₂ : Cxt} {σ₁ σ₂ : Ty} (hΓ : Γ₁ = Γ₂) (hσ : σ₁ = σ₂) (t : Tm Γ₁ σ₁) :
    Tm Γ₂ σ₂ :=
  match hΓ, hσ with
  | rfl, rfl => t

/-! ## 3. Structural Context Helpers for `dd⁺*` and `dd⁻*` -/

/-- Swap two adjacent positive-realiser assumptions across suffix `Ζ`. -/
def swapPos {Γ : Cxt} {Ξ : Asmpt Γ} {A B : Fml Γ} :
    (Ζ : Asmpt Γ) → {σ : Ty} →
    Tm (Γ.append (ddPosStar ((SnocList.snoc (.snoc Ξ A) B).append Ζ))) σ →
    Tm (Γ.append (ddPosStar ((SnocList.snoc (.snoc Ξ B) A).append Ζ))) σ
  | .nil, _, t => t.wk Ren.exch
  | .snoc Ζ _, _, t => (swapPos Ζ (.lam t)).wkn ⬝ Tm.v0

/-- Closed combinator for concatenating counterexample tuples across `Ξ ₊₊ Ζ` (`Pair⁻`). -/
def pairNegComb {Γ Δ : Cxt} (Ξ : Asmpt Γ) :
    (Ζ : Asmpt Γ) →
    Tm Δ (.arr (prodCxt (ddNegStar Ξ))
               (.arr (prodCxt (ddNegStar Ζ)) (prodCxt (ddNegStar (Ξ.append Ζ)))))
  | .nil => .lam (.lam Tm.v1)
  | .snoc Ζ _ =>
      .lam (.lam (.pair (pairNegComb Ξ Ζ ⬝ Tm.v1 ⬝ (.pr1 Tm.v0)) (.pr2 Tm.v0)))

/-- Concatenate counterexample tuples across `Ξ ₊₊ Ζ` (`Pair⁻`, `O(|Ζ|)` AST size). -/
def pairNeg {Γ Δ : Cxt} (Ξ : Asmpt Γ) (Ζ : Asmpt Γ)
    (u : Tms Δ (ddNegStar Ξ)) (v : Tms Δ (ddNegStar Ζ)) : Tms Δ (ddNegStar (Ξ.append Ζ)) :=
  pairNegComb Ξ Ζ ⬝ u ⬝ v

/-- Project left counterexample tuple (`pr₁⁻`). -/
def pr1Neg {Γ Δ : Cxt} (Ξ : Asmpt Γ) :
    (Ζ : Asmpt Γ) → Tms Δ (ddNegStar (Ξ.append Ζ)) → Tms Δ (ddNegStar Ξ)
  | .nil, w => w
  | .snoc Ζ _, w => pr1Neg Ξ Ζ (.pr1 w)

/-- Closed combinator for projecting right counterexample tuple (`pr₂⁻`). -/
def pr2NegComb {Γ Δ : Cxt} (Ξ : Asmpt Γ) :
    (Ζ : Asmpt Γ) → Tm Δ (.arr (prodCxt (ddNegStar (Ξ.append Ζ))) (prodCxt (ddNegStar Ζ)))
  | .nil => .lam .unit
  | .snoc Ζ _ => .lam (.pair (pr2NegComb Ξ Ζ ⬝ (.pr1 Tm.v0)) (.pr2 Tm.v0))

/-- Project right counterexample tuple (`pr₂⁻`, `O(|Ζ|)` AST size). -/
def pr2Neg {Γ Δ : Cxt} (Ξ : Asmpt Γ) (Ζ : Asmpt Γ)
    (w : Tms Δ (ddNegStar (Ξ.append Ζ))) : Tms Δ (ddNegStar Ζ) :=
  pr2NegComb Ξ Ζ ⬝ w

/-- Closed combinator for componentwise concatenation of counterexample list tuples (`++ᵐˢ⁻`). -/
def appendNegComb {Γ Δ : Cxt} :
    (Ξ : Asmpt Γ) →
    Tm Δ (.arr (prodCxt (ddNegStar Ξ)) (.arr (prodCxt (ddNegStar Ξ)) (prodCxt (ddNegStar Ξ))))
  | .nil => .lam (.lam .unit)
  | .snoc Ξ _ =>
      .lam (.lam (.pair (appendNegComb Ξ ⬝ (.pr1 Tm.v1) ⬝ (.pr1 Tm.v0))
                        (Tm.appendTm (.pr2 Tm.v1) (.pr2 Tm.v0))))

/-- Componentwise concatenation of counterexample list tuples (`++ᵐˢ⁻`, `O(|Ξ|)` AST size
    with zero duplication of `xs` or `ys`). -/
def appendNeg {Γ Δ : Cxt} {Ξ : Asmpt Γ}
    (xs ys : Tms Δ (ddNegStar Ξ)) : Tms Δ (ddNegStar Ξ) :=
  appendNegComb Ξ ⬝ xs ⬝ ys

/-- Empty counterexample list tuple (`Nilᵐˢ⁻`). -/
def nilNeg {Γ Δ : Cxt} : {Ξ : Asmpt Γ} → Tms Δ (ddNegStar Ξ)
  | .nil => .unit
  | .snoc _ _ => .pair nilNeg .nil

/-- Collect counterexample tuples across a candidate list (`Appᵐˢ⁻`, zero weakening traversal). -/
def appNeg {Γ Δ : Cxt} {Ξ : Asmpt Γ} {σ : Ty}
    (f : Tm Δ (.arr σ (prodCxt (ddNegStar Ξ)))) (xs : Tm Δ (.list σ)) : Tms Δ (ddNegStar Ξ) :=
  (.lam (.lam (.recList ⬝ nilNeg ⬝ (.lam (.lam (appendNeg (Tm.v3 ⬝ Tm.v1) Tm.v0))) ⬝ Tm.v0))) ⬝ f ⬝ xs

/-! ## 4. Mutual Realiser (`𝔯`) and Counterexample (`𝔠`) Term Extraction -/

/-- Simultaneously extract `(𝔯(p), 𝔠(p))` in a single structural pass on `Prf` (`Prf.rec`).
    Crucially uses lazy `.1`/`.2` projections rather than strict tuple pattern matching so
    extracting `realiser p` never forces dead `counterexample` subtrees in WHNF. -/
def dialecticaPair : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A : Fml Γ} →
    Prf Ξ A →
    Tm (Γ.append (ddPosStar Ξ)) (dPosStar A) ×
    Tms (.snoc (Γ.append (ddPosStar Ξ)) (dNeg A)) (ddNegStar Ξ)
  | _, _, _, .id =>
      (Tm.v0, .pair .unit (Tm.singletonTm Tm.v0))
  | _, _, _, .wkn p =>
      let dp := dialecticaPair p
      (dp.1.wkn, .pair (dp.2.wk (Ren.lift Ren.wkn)) Tm.defaultTm)
  | _, _, _, .swap (Ξ := Ξ₀) Ζ p =>
      let dp := dialecticaPair p
      let cp' := (swapPos Ζ (.lam dp.2)).wkn ⬝ Tm.v0
      let cp1 := pr1Neg (.snoc (.snoc Ξ₀ _) _) Ζ cp'
      let u := Tm.pr1 (.pr1 cp1)
      let a := Tm.pr2 (.pr1 cp1)
      let b := Tm.pr2 cp1
      let v := pr2Neg (.snoc (.snoc Ξ₀ _) _) Ζ cp'
      (swapPos Ζ dp.1, pairNeg (.snoc (.snoc Ξ₀ _) _) Ζ (.pair (.pair u b) a) v)
  | _, _, _, .recZer | _, _, _, .recSuc | _, _, _, .lrecNil | _, _, _, .lrecCon
  | _, _, _, .betaEq | _, _, _, .etaEq | _, _, _, .betaProd1 | _, _, _, .betaProd2
  | _, _, _, .etaProd | _, _, _, .refl =>
      (Tm.defaultTm, .unit)
  | _, _, _, .sym p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, dp.2)
  | _, _, _, .trans p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      (Tm.defaultTm, appendNeg dp.2 dq.2)
  | _, _, _, .apF p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, dp.2)
  | _, _, _, .funExt p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, dp.2)
  | _, _, _, .leZero =>
      (Tm.defaultTm, Tm.defaultTm)
  | _, _, _, .leSucc p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, dp.2)
  | _, _, _, .memZero =>
      (Tm.defaultTm, .unit)
  | _, _, _, .memSucc p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, dp.2)
  | _, _, _, .botElim p =>
      let dp := dialecticaPair p
      (Tm.defaultTm, (dp.2.subst Tm.defaultTm).wkn)
  | _, _, _, .andIntro p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      let wcp := (Tm.lam dp.2).wkn ⬝ (.pr1 Tm.v0)
      let wcq := (Tm.lam dq.2).wkn ⬝ (.pr2 Tm.v0)
      (Tm.pairListTm dp.1 dq.1, appendNeg wcp wcq)
  | _, _, _, .andElim1 p =>
      let dp := dialecticaPair p
      (Tm.pr1ListTm dp.1, (Tm.lam dp.2).wkn ⬝ (.pair Tm.v0 Tm.defaultTm))
  | _, _, _, .andElim2 p =>
      let dp := dialecticaPair p
      (Tm.pr2ListTm dp.1, (Tm.lam dp.2).wkn ⬝ (.pair Tm.defaultTm Tm.v0))
  | _, _, _, .orInl p =>
      let dp := dialecticaPair p
      (Tm.pairListTm dp.1 Tm.defaultTm, (Tm.lam dp.2).wkn ⬝ (.pr1 Tm.v0))
  | _, _, _, .orInr p =>
      let dp := dialecticaPair p
      (Tm.pairListTm Tm.defaultTm dp.1, (Tm.lam dp.2).wkn ⬝ (.pr2 Tm.v0))
  | _, _, _, .orElim cL cR p =>
      let dcL := dialecticaPair cL
      let dcR := dialecticaPair cR
      let dp := dialecticaPair p
      let pos :=
        (.lam (Tm.appendTm
          (Tm.collect1Tm (Tm.pr1ListTm dcL.1).wkn (Tm.pr1ListTm Tm.v0))
          (Tm.collect1Tm (Tm.pr1ListTm dcR.1).wkn (Tm.pr2ListTm Tm.v0)))) ⬝ dp.1
      let neg :=
        (.lam (
          (.lam (.lam (
            let a := Tm.collect2Tm (Tm.pr2ListTm dcL.1).wkn4 Tm.v1 Tm.v3
            let b := Tm.collect2Tm (Tm.pr2ListTm dcR.1).wkn4 Tm.v0 Tm.v3
            let ab := Tm.pairListTm a b
            let u := (Tm.lam dcL.2).wkn4 ⬝ (.pair Tm.v1 Tm.v3)
            let v := (Tm.lam dcR.2).wkn4 ⬝ (.pair Tm.v0 Tm.v3)
            let w := appNeg (Tm.lam dp.2).wkn4 ab
            appendNeg (appendNeg u v) w)))
          ⬝ (Tm.pr1ListTm Tm.v0) ⬝ (Tm.pr2ListTm Tm.v0)))
        ⬝ dp.1.wkn
      (pos, neg)
  | _, _, _, .impIntro p =>
      let dp := dialecticaPair p
      let f := Tm.lam dp.1
      let g := Tm.lam (.lam ((Tm.lam (.pr2 dp.2)).wkn ⬝ Tm.v0))
      (Tm.singletonTm (.pair f g),
       (Tm.lam (.lam (.pr1 dp.2))).wkn ⬝ (.pr1 Tm.v0) ⬝ (.pr2 Tm.v0))
  | _, _, _, .impElim p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      let pos := Tm.collect1Tm (Tm.pr1ListTm dp.1) dq.1
      let neg :=
        (.lam (.lam (
          let u := (Tm.lam dp.2).wkn3 ⬝ (.pair Tm.v0 Tm.v2)
          let a := Tm.collect2Tm (Tm.pr2ListTm Tm.v1) Tm.v0 Tm.v2
          let v := appNeg (Tm.lam dq.2).wkn3 a
          appendNeg u v))) ⬝ dp.1.wkn ⬝ dq.1.wkn
      (pos, neg)
  | Γ, Ξ, _, .allIntro (σ := σ) (A := B) p =>
      let dp := dialecticaPair p
      let rp' : Tm ((SnocList.snoc Γ σ).append (ddPosStar Ξ)) (dPosStar B) :=
        castCtxTm (congrArg (SnocList.append (.snoc Γ σ)) (ddPosStar_wknAsmpt Ξ)) dp.1
      let pos := (rp'.wk (Ren.exchEnd (ddPosStar Ξ))).subst Tm.defaultTm
      let cpSub := (dp.2.wk (Ren.exchEnd (.snoc (ddPosStar (wknAsmpt Ξ)) (dNeg B)))).subst Tm.defaultTm
      let hCtx : SnocList.snoc (Γ.append (ddPosStar (wknAsmpt (σ := σ) Ξ))) (dNeg B) =
                 SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg B) :=
        congrArg (fun Z => SnocList.snoc (Γ.append Z) (dNeg B)) (ddPosStar_wknAsmpt Ξ)
      let hTy : prodCxt (ddNegStar (wknAsmpt (σ := σ) Ξ)) = prodCxt (ddNegStar Ξ) :=
        congrArg prodCxt (ddNegStar_wknAsmpt Ξ)
      (pos, castCtxTyTm hCtx hTy cpSub)
  | Γ, Ξ, _, .allElim (A := B) p u =>
      let dp := dialecticaPair p
      let pos := castTm (congrArg Ty.list (dPos_substF B u).symm) dp.1
      let hCtx : SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg B) =
                 SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg (B.substF u)) :=
        congrArg (SnocList.snoc (Γ.append (ddPosStar Ξ))) (dNeg_substF B u).symm
      (pos, castCtxTm hCtx dp.2)
  | Γ, Ξ, _, .exIntro (A := B) u p =>
      let dp := dialecticaPair p
      let pos := castTm (congrArg Ty.list (dPos_substF B u)) dp.1
      let hCtx : SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg (B.substF u)) =
                 SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg B) :=
        congrArg (SnocList.snoc (Γ.append (ddPosStar Ξ))) (dNeg_substF B u)
      let cp' := castCtxTm hCtx dp.2
      (pos, appNeg (Tm.lam cp').wkn Tm.v0)
  | Γ, Ξ, _, .exElim (A := A₀) (B := B₀) p =>
      let dp := dialecticaPair p
      have hBpos : Ty.arr (dPosStar A₀) (dPosStar B₀.wknF) =
          Ty.arr (dPosStar A₀) (dPosStar B₀) :=
        congrArg (fun x => Ty.arr (dPosStar A₀) (Ty.list x)) (dPos_wkF Ren.wkn B₀)
      have hBneg : dNeg B₀ = dNeg B₀.wknF := (dNeg_wkF Ren.wkn B₀).symm
      let stepBody :
          Tm (.snoc (.snoc (Γ.append (ddPosStar Ξ))
                (.prod (.arr (dPosStar A₀) (dPosStar B₀.wknF))
                       (.arr (dPosStar A₀) (.arr (dNeg B₀.wknF) (dNegStar A₀)))))
                (.list (.prod (.arr (dPosStar A₀) (dPosStar B₀))
                              (.arr (dPosStar A₀) (.arr (dNeg B₀) (.list (dNegStar A₀)))))))
             (.list (.prod (.arr (dPosStar A₀) (dPosStar B₀))
                           (.arr (dPosStar A₀) (.arr (dNeg B₀) (.list (dNegStar A₀)))))) :=
        .cons
          (.pair
            (castTm hBpos (.pr1 Tm.v1))
            (.lam (.lam (Tm.singletonTm
              ((.pr2 Tm.v3) ⬝ Tm.v1 ⬝ (castTm hBneg Tm.v0))))))
          Tm.v0
      let hCtx :
          SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod (dPosStar A₀) (dNeg B₀.wknF)) =
          SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod (dPosStar A₀) (dNeg B₀)) :=
        congrArg (fun x => SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod (dPosStar A₀) x))
          (dNeg_wkF Ren.wkn B₀)
      (.recList ⬝ .nil ⬝ (.lam (.lam stepBody)) ⬝ dp.1, castCtxTm hCtx dp.2)
  | _, _, _, .stEq p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      (dp.1, appendNeg dp.2 dq.2)
  | _, Ξ, _, .stCl t =>
      ((Tm.singletonTm t.wkNil).wknAppend (ddPosStar Ξ), Tm.defaultTm)
  | _, _, _, .stAp p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      (Tm.appListTm dp.1 dq.1, appendNeg dp.2 dq.2)
  | _, _, _, .allStI p =>
      let dp := dialecticaPair p
      let rp1 := Tm.pr1ListTm dp.1
      (Tm.singletonTm (.lam (Tm.collect1Tm rp1.wkn (Tm.singletonTm Tm.v0))),
       (Tm.lam dp.2).wkn ⬝ (.pair (Tm.singletonTm (.pr1 Tm.v0)) (.pr2 Tm.v0)))
  | _, _, _, .allStE p =>
      let dp := dialecticaPair p
      let F := .recList ⬝ .nil ⬝ (.lam (.lam (Tm.appendTm (Tm.collect1Tm dp.1.wkn2 Tm.v1) Tm.v0)))
      (Tm.singletonTm (.pair F Tm.defaultTm),
       .recList ⬝ nilNeg ⬝
         (.lam (.lam (appendNeg ((Tm.lam dp.2).wkn3 ⬝ (.pair Tm.v1 (.pr2 Tm.v2))) Tm.v0))) ⬝
         (.pr1 Tm.v0))
  | _, _, _, .exStI p =>
      let dp := dialecticaPair p
      (dp.1, (Tm.lam dp.2).wkn ⬝ (Tm.pairRightTm .unit Tm.v0))
  | _, _, _, .exStE p =>
      let dp := dialecticaPair p
      (dp.1, (Tm.lam dp.2).wkn ⬝ (Tm.pr2ListTm Tm.v0))
  | _, _, _, .ir _ _ _ =>
      (Tm.defaultTm, Tm.defaultTm)
  | Γ, Ξ, _, .irSt (A := B) p q =>
      let dp := dialecticaPair p
      let dq := dialecticaPair q
      let a : Tm _ (dPosStar B) :=
        castTm (congrArg Ty.list (dPos_substF B .zero)) dp.1
      let rq1 : Tm _ (.arr .nat (.arr (dPosStar B) (dPosStar B.shiftSuccF))) :=
        .lam (.lam (Tm.collect1Tm (Tm.pr1ListTm (Tm.collect1Tm dq.1.wkn2 Tm.v1)) Tm.v0))
      let f : Tm _ (.arr .nat (.arr (dPosStar B) (dPosStar B))) :=
        castTm (congrArg (fun x => Ty.arr .nat (Ty.arr (dPosStar B) (Ty.list x))) (dPos_shiftSuccF B)) rq1
      let g : Tm _ (.arr .nat (dPosStar B)) := .recNat ⬝ a ⬝ f
      let hCtx0 : SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg (B.substF .zero)) =
                  SnocList.snoc (Γ.append (ddPosStar Ξ)) (dNeg B) :=
        congrArg (SnocList.snoc (Γ.append (ddPosStar Ξ))) (dNeg_substF B .zero)
      let cp' := castCtxTm hCtx0 dp.2
      let hCtxS :
          SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod .nat (.prod (dPosStar B) (dNeg B.shiftSuccF))) =
          SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod .nat (.prod (dPosStar B) (dNeg B))) :=
        congrArg (fun x => SnocList.snoc (Γ.append (ddPosStar Ξ)) (.prod .nat (.prod (dPosStar B) x)))
          (dNeg_shiftSuccF B)
      let cq' := castCtxTm hCtxS dq.2
      let u := (Tm.lam cp').wkn ⬝ (.pr2 Tm.v0)
      let h := Tm.lam (.lam ((Tm.lam cq').wkn3 ⬝
        (.pair Tm.v1 (.pair (g.wkn3 ⬝ Tm.v1) (.pr2 Tm.v2)))))
      (Tm.singletonTm g, .recNat ⬝ u ⬝ h ⬝ (.pr1 Tm.v0))
  | _, _, _, .idealisation (φ := φ) _ =>
      have hNeg : dNeg φ = dNeg φ.wkn2F := (dNeg_wkF (Ren.lift (Ren.lift Ren.wkn)) φ).symm
      let U := Tm.lam .nil
      let Y := Tm.lam (.lam (Tm.singletonTm
        (.pair (Tm.pr1ListTm Tm.v0)
          (.recList ⬝ .nil ⬝
            (.lam (.lam (.cons (.pair (Tm.singletonTm .unit) (castTm hNeg Tm.v1)) Tm.v0))) ⬝
            (Tm.pr2ListTm Tm.v0)))))
      (Tm.singletonTm (.pair U Y), .unit)
  | _, _, _, .ncr (Φ := Φ) =>
      have hPos : dPos Φ = dPos Φ.wkn2F := (dPos_wkF (Ren.lift (Ren.lift Ren.wkn)) Φ).symm
      have hNeg : dNegStar Φ.wkn2F = dNegStar Φ :=
        congrArg Ty.list (dNeg_wkF (Ren.lift (Ren.lift Ren.wkn)) Φ)
      let U := Tm.lam (.recList ⬝ .nil ⬝
        (.lam (.lam (.cons (.pair (Tm.pr1ListTm Tm.v2)
          (.pair .unit (castTm hPos (.pr2 Tm.v1)))) Tm.v0))) ⬝ Tm.v0)
      let Y := Tm.lam (.recList ⬝ .nil ⬝
        (.lam (.lam (.cons (castTm hNeg (Tm.pr2ListTm Tm.v1)) Tm.v0))))
      (Tm.singletonTm (.pair U Y), .unit)
  | _, _, _, .hac (Φ := Φ) =>
      have hPos : dPos Φ = dPos Φ.wkn2F := (dPos_wkF (Ren.lift (Ren.lift Ren.wkn)) Φ).symm
      have hNeg : dNegStar Φ.wkn2F = dNegStar Φ :=
        congrArg Ty.list (dNeg_wkF (Ren.lift (Ren.lift Ren.wkn)) Φ)
      let U := Tm.lam (Tm.singletonTm
        (.pair
          (.lam (Tm.pr1ListTm (Tm.collect1Tm Tm.v1 Tm.v0)))
          (.lam (.recList ⬝ .nil ⬝
            (.lam (.lam (.cons (.pair .unit (castTm hPos (.pr2 Tm.v1))) Tm.v0))) ⬝
            (Tm.collect1Tm Tm.v1 Tm.v0)))))
      let Y := Tm.lam (.recList ⬝ .nil ⬝
        (.lam (.lam (.cons (.pair (.pr1 Tm.v1)
          (castTm hNeg (Tm.pr2ListTm (.pr2 Tm.v1)))) Tm.v0))))
      (Tm.singletonTm (.pair U Y), .unit)
  | _, _, _, .hgmpSt _ _ =>
      let U := Tm.lam (Tm.singletonTm
        (.pair (Tm.pr1ListTm (Tm.collect2Tm (Tm.pr2ListTm Tm.v0) Tm.defaultTm Tm.defaultTm))
               Tm.defaultTm))
      let Y := Tm.lam (.lam (Tm.singletonTm Tm.defaultTm))
      (Tm.singletonTm (.pair U Y), .unit)
  | _, _, _, .hipAllSt (σ := σ) (φ := φ) (Ψ := Ψ) _ =>
      have hPosΨ : dPos Ψ = dPos Ψ.wkn1F := (dPos_wkF (Ren.lift Ren.wkn) Ψ).symm
      have hNegφ : Ty.list (.prod σ (dNeg φ)) = Ty.list (.prod σ (dNeg φ.wkn1F)) :=
        congrArg (fun x => Ty.list (.prod σ x)) (dNeg_wkF (Ren.lift Ren.wkn) φ).symm
      have hNegΨ : dNegStar Ψ.wkn1F = dNegStar Ψ :=
        congrArg Ty.list (dNeg_wkF (Ren.lift Ren.wkn) Ψ)
      let U := Tm.lam (Tm.singletonTm
        (.pair
          (Tm.pr1ListTm (Tm.collect1Tm (Tm.pr1ListTm Tm.v0) Tm.defaultTm))
          (.pair
            (.lam (.recList ⬝ .nil ⬝
              (.lam (.lam (.cons (.pair .unit (castTm hPosΨ Tm.v1)) Tm.v0))) ⬝
              (Tm.pr2ListTm (Tm.collect1Tm (Tm.pr1ListTm Tm.v1) Tm.defaultTm))))
            (.lam (.lam (castTm hNegφ
              (Tm.collect2Tm (Tm.pr2ListTm Tm.v2) Tm.defaultTm Tm.defaultTm)))))))
      let Y := Tm.lam (.recList ⬝ .nil ⬝
        (.lam (.lam (.cons (.pair Tm.defaultTm
          (castTm hNegΨ (Tm.pr2ListTm (.pr2 Tm.v1)))) Tm.v0))))
      (Tm.singletonTm (.pair U Y), .unit)
  | _, _, _, .stSucc p =>
      let dp := dialecticaPair p
      (Tm.mapTm (.lam (.succ Tm.v0)) dp.1, dp.2)
  | _, _, _, .leZeroEq _ | _, _, _, .leSuccOr _ | _, _, _, .evenZ | _, _, _, .evenS _ =>
      (Tm.defaultTm, Tm.defaultTm)

/-- Extract a System T positive-realiser list term `𝔯(p) : Tm (Γ ₊₊ dd⁺* Ξ) (d⁺ A *)`
    from any formal proof `p : Prf Ξ A` in System H. -/
def realiser {Γ : Cxt} {Ξ : Asmpt Γ} {A : Fml Γ} (p : Prf Ξ A) :
    Tm (Γ.append (ddPosStar Ξ)) (dPosStar A) :=
  (dialecticaPair p).1

/-- Extract a System T counterexample transformer `𝔠(p) : Tms (Γ ₊₊ dd⁺* Ξ ₊ d⁻ A) (dd⁻* Ξ)`
    from any formal proof `p : Prf Ξ A` in System H. -/
def counterexample {Γ : Cxt} {Ξ : Asmpt Γ} {A : Fml Γ} (p : Prf Ξ A) :
    Tms (.snoc (Γ.append (ddPosStar Ξ)) (dNeg A)) (ddNegStar Ξ) :=
  (dialecticaPair p).2

/-! ## 5. Transport-Free Unit-Erasure Simplifier (`Simp`) -/

/-- Simplify `.list σ'` by collapsing `.list .unit` to `.unit`. -/
@[reducible] def simpListTy : Ty → Ty
  | .unit => .unit
  | .bool => .list .bool
  | .nat => .list .nat
  | .list α => .list (.list α)
  | .prod α β => .list (.prod α β)
  | .arr α β => .list (.arr α β)

/-- Simplify `.prod σ' τ'` by erasing `.unit` factors. -/
@[reducible] def simpProdTy : Ty → Ty → Ty
  | .unit, τ' => τ'
  | .bool, .unit => .bool
  | .nat, .unit => .nat
  | .list α, .unit => .list α
  | .prod α β, .unit => .prod α β
  | .arr α β, .unit => .arr α β
  | .bool, τ' => .prod .bool τ'
  | .nat, τ' => .prod .nat τ'
  | .list α, τ' => .prod (.list α) τ'
  | .prod α β, τ' => .prod (.prod α β) τ'
  | .arr α β, τ' => .prod (.arr α β) τ'

/-- Simplify `.arr σ' τ'` by collapsing `.unit → τ'` to `τ'` and `σ' → .unit` to `.unit`. -/
@[reducible] def simpArrTy : Ty → Ty → Ty
  | .unit, τ' => τ'
  | .bool, .unit => .unit
  | .nat, .unit => .unit
  | .list _, .unit => .unit
  | .prod _ _, .unit => .unit
  | .arr _ _, .unit => .unit
  | .bool, τ' => .arr .bool τ'
  | .nat, τ' => .arr .nat τ'
  | .list α, τ' => .arr (.list α) τ'
  | .prod α β, τ' => .arr (.prod α β) τ'
  | .arr α β, τ' => .arr (.arr α β) τ'

/-- Recursively erase noncomputational `.unit` components from a System T type (`simpᵀ`). -/
@[reducible] def simpTy : Ty → Ty
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .list σ => simpListTy (simpTy σ)
  | .prod σ τ => simpProdTy (simpTy σ) (simpTy τ)
  | .arr σ τ => simpArrTy (simpTy σ) (simpTy τ)

/-- Transport-free list value projection into `(simpListTy σ').denote` that skips list
    traversal altogether whenever `σ' = .unit`. -/
def simpListMap : (σ' : Ty) → {α : Type} → (α → σ'.denote) → List α → (simpListTy σ').denote
  | .unit, _, _, _ => ()
  | .bool, _, f, xs => xs.map f
  | .nat, _, f, xs => xs.map f
  | .list _, _, f, xs => xs.map f
  | .prod _ _, _, f, xs => xs.map f
  | .arr _ _, _, f, xs => xs.map f

/-- Transport-free list value embedding from `(simpListTy σ').denote`. -/
def backListVal : (σ' : Ty) → (simpListTy σ').denote → List σ'.denote
  | .unit, _ => []
  | .bool, xs => xs
  | .nat, xs => xs
  | .list _, xs => xs
  | .prod _ _, xs => xs
  | .arr _ _, xs => xs

/-- Transport-free lazy product value projection into `(simpProdTy σ' τ').denote`
    that never forces unit-erased components (e.g., dead counterexample closures). -/
def simpProdLazy : (σ' τ' : Ty) → (Unit → σ'.denote) → (Unit → τ'.denote) → (simpProdTy σ' τ').denote
  | .unit, _, _, fy => fy ()
  | .bool, .unit, fx, _ => fx ()
  | .nat, .unit, fx, _ => fx ()
  | .list _, .unit, fx, _ => fx ()
  | .prod _ _, .unit, fx, _ => fx ()
  | .arr _ _, .unit, fx, _ => fx ()
  | .bool, .bool, fx, fy => (fx (), fy ())
  | .bool, .nat, fx, fy => (fx (), fy ())
  | .bool, .list _, fx, fy => (fx (), fy ())
  | .bool, .prod _ _, fx, fy => (fx (), fy ())
  | .bool, .arr _ _, fx, fy => (fx (), fy ())
  | .nat, .bool, fx, fy => (fx (), fy ())
  | .nat, .nat, fx, fy => (fx (), fy ())
  | .nat, .list _, fx, fy => (fx (), fy ())
  | .nat, .prod _ _, fx, fy => (fx (), fy ())
  | .nat, .arr _ _, fx, fy => (fx (), fy ())
  | .list _, .bool, fx, fy => (fx (), fy ())
  | .list _, .nat, fx, fy => (fx (), fy ())
  | .list _, .list _, fx, fy => (fx (), fy ())
  | .list _, .prod _ _, fx, fy => (fx (), fy ())
  | .list _, .arr _ _, fx, fy => (fx (), fy ())
  | .prod _ _, .bool, fx, fy => (fx (), fy ())
  | .prod _ _, .nat, fx, fy => (fx (), fy ())
  | .prod _ _, .list _, fx, fy => (fx (), fy ())
  | .prod _ _, .prod _ _, fx, fy => (fx (), fy ())
  | .prod _ _, .arr _ _, fx, fy => (fx (), fy ())
  | .arr _ _, .bool, fx, fy => (fx (), fy ())
  | .arr _ _, .nat, fx, fy => (fx (), fy ())
  | .arr _ _, .list _, fx, fy => (fx (), fy ())
  | .arr _ _, .prod _ _, fx, fy => (fx (), fy ())
  | .arr _ _, .arr _ _, fx, fy => (fx (), fy ())

/-- Transport-free product value embedding from `(simpProdTy σ' τ').denote`. -/
def backProdVal : (σ' τ' : Ty) → (simpProdTy σ' τ').denote → σ'.denote × τ'.denote
  | .unit, _, w => ((), w)
  | .bool, .unit, w => (w, ())
  | .nat, .unit, w => (w, ())
  | .list _, .unit, w => (w, ())
  | .prod _ _, .unit, w => (w, ())
  | .arr _ _, .unit, w => (w, ())
  | .bool, .bool, w => w
  | .bool, .nat, w => w
  | .bool, .list _, w => w
  | .bool, .prod _ _, w => w
  | .bool, .arr _ _, w => w
  | .nat, .bool, w => w
  | .nat, .nat, w => w
  | .nat, .list _, w => w
  | .nat, .prod _ _, w => w
  | .nat, .arr _ _, w => w
  | .list _, .bool, w => w
  | .list _, .nat, w => w
  | .list _, .list _, w => w
  | .list _, .prod _ _, w => w
  | .list _, .arr _ _, w => w
  | .prod _ _, .bool, w => w
  | .prod _ _, .nat, w => w
  | .prod _ _, .list _, w => w
  | .prod _ _, .prod _ _, w => w
  | .prod _ _, .arr _ _, w => w
  | .arr _ _, .bool, w => w
  | .arr _ _, .nat, w => w
  | .arr _ _, .list _, w => w
  | .arr _ _, .prod _ _, w => w
  | .arr _ _, .arr _ _, w => w

/-- Transport-free function value projection into `(simpArrTy σ' τ').denote`.
    Crucially returns `()` without calling `g` whenever `τ' = .unit` (including `σ' = .unit`). -/
def simpArrVal : (σ' τ' : Ty) → (σ'.denote → τ'.denote) → (simpArrTy σ' τ').denote
  | .unit, .unit, _ => ()
  | .unit, .bool, g => g ()
  | .unit, .nat, g => g ()
  | .unit, .list _, g => g ()
  | .unit, .prod _ _, g => g ()
  | .unit, .arr _ _, g => g ()
  | .bool, .unit, _ => ()
  | .nat, .unit, _ => ()
  | .list _, .unit, _ => ()
  | .prod _ _, .unit, _ => ()
  | .arr _ _, .unit, _ => ()
  | .bool, .bool, g => g
  | .bool, .nat, g => g
  | .bool, .list _, g => g
  | .bool, .prod _ _, g => g
  | .bool, .arr _ _, g => g
  | .nat, .bool, g => g
  | .nat, .nat, g => g
  | .nat, .list _, g => g
  | .nat, .prod _ _, g => g
  | .nat, .arr _ _, g => g
  | .list _, .bool, g => g
  | .list _, .nat, g => g
  | .list _, .list _, g => g
  | .list _, .prod _ _, g => g
  | .list _, .arr _ _, g => g
  | .prod _ _, .bool, g => g
  | .prod _ _, .nat, g => g
  | .prod _ _, .list _, g => g
  | .prod _ _, .prod _ _, g => g
  | .prod _ _, .arr _ _, g => g
  | .arr _ _, .bool, g => g
  | .arr _ _, .nat, g => g
  | .arr _ _, .list _, g => g
  | .arr _ _, .prod _ _, g => g
  | .arr _ _, .arr _ _, g => g

/-- Transport-free function value embedding from `(simpArrTy σ' τ').denote`. -/
def backArrVal : (σ' τ' : Ty) → (simpArrTy σ' τ').denote → (σ'.denote → τ'.denote)
  | .unit, _, w => fun _ => w
  | .bool, .unit, _ => fun _ => ()
  | .nat, .unit, _ => fun _ => ()
  | .list _, .unit, _ => fun _ => ()
  | .prod _ _, .unit, _ => fun _ => ()
  | .arr _ _, .unit, _ => fun _ => ()
  | .bool, .bool, g => g
  | .bool, .nat, g => g
  | .bool, .list _, g => g
  | .bool, .prod _ _, g => g
  | .bool, .arr _ _, g => g
  | .nat, .bool, g => g
  | .nat, .nat, g => g
  | .nat, .list _, g => g
  | .nat, .prod _ _, g => g
  | .nat, .arr _ _, g => g
  | .list _, .bool, g => g
  | .list _, .nat, g => g
  | .list _, .list _, g => g
  | .list _, .prod _ _, g => g
  | .list _, .arr _ _, g => g
  | .prod _ _, .bool, g => g
  | .prod _ _, .nat, g => g
  | .prod _ _, .list _, g => g
  | .prod _ _, .prod _ _, g => g
  | .prod _ _, .arr _ _, g => g
  | .arr _ _, .bool, g => g
  | .arr _ _, .nat, g => g
  | .arr _ _, .list _, g => g
  | .arr _ _, .prod _ _, g => g
  | .arr _ _, .arr _ _, g => g

/-- Combined unit-erasure projection (`simpᴹ`) and embedding (`backᴹ`) by direct structural
    recursion on `Ty` (avoiding `Ty.brecOn` and skipping unit-erased counterexample closures). -/
def simpBackPair : (σ : Ty) → (σ.denote → (simpTy σ).denote) × ((simpTy σ).denote → σ.denote)
  | .unit => (fun _ => (), fun _ => ())
  | .bool => (fun b => b, fun b => b)
  | .nat => (fun n => n, fun n => n)
  | .list σ =>
      let sb := simpBackPair σ
      (fun xs => simpListMap (simpTy σ) sb.1 xs,
       fun w => (backListVal (simpTy σ) w).map sb.2)
  | .prod σ τ =>
      let sb1 := simpBackPair σ
      let sb2 := simpBackPair τ
      (fun p => simpProdLazy (simpTy σ) (simpTy τ) (fun _ => sb1.1 p.1) (fun _ => sb2.1 p.2),
       fun w =>
         let (x', y') := backProdVal (simpTy σ) (simpTy τ) w
         (sb1.2 x', sb2.2 y'))
  | .arr σ τ =>
      let sb1 := simpBackPair σ
      let sb2 := simpBackPair τ
      (fun f => simpArrVal (simpTy σ) (simpTy τ) (fun x' => sb2.1 (f (sb1.2 x'))),
       fun w =>
         let g := backArrVal (simpTy σ) (simpTy τ) w
         fun x => sb2.2 (g (sb1.1 x)))

/-- Erase unit clutter from a semantic System T value (`simpᴹ`). -/
def simpVal (σ : Ty) : σ.denote → (simpTy σ).denote := (simpBackPair σ).1

/-- Embed a simplified value back into the unsimplified semantic type (`backᴹ`). -/
def backVal (σ : Ty) : (simpTy σ).denote → σ.denote := (simpBackPair σ).2

/-- Top-level program extractor (`extract` in `Dialectica.agda`): evaluates `𝔯(p)` in `()`. -/
def extract {Φ : Fml .nil} (p : Prf .nil Φ) : (dPosStar Φ).denote :=
  (realiser p).eval ()

/-- Top-level simplified program extractor (`simpExtract` in `Dialectica.agda`). -/
def simpExtract {Φ : Fml .nil} (p : Prf .nil Φ) : (simpTy (dPosStar Φ)).denote :=
  simpVal (dPosStar Φ) (extract p)

/-! ## 6. Machine-Checked Semantic & Herbrand Soundness -/

/-- Interpret a renaming `ξ : Ren Γ Δ` as an environment projection `Δ.denote → Γ.denote`. -/
def evalRen : {Γ Δ : Cxt} → Ren Γ Δ → Cxt.denote Δ → Cxt.denote Γ
  | .nil, _, _, _ => ()
  | .snoc _ _, _, ξ, ρ =>
      (evalRen ⟨fun i => ξ.apply (.there i)⟩ ρ, lookupEnv (ξ.apply .here) ρ)

theorem lookupEnv_evalRen :
    {Γ Δ : Cxt} → (ξ : Ren Γ Δ) → (ρ : Cxt.denote Δ) →
    ∀ {σ : Ty} (i : SnocList.Mem σ Γ), lookupEnv i (evalRen ξ ρ) = lookupEnv (ξ.apply i) ρ
  | .snoc _ _, _, _, _, _, .here => rfl
  | .snoc _ _, _, ξ, ρ, _, .there i =>
      lookupEnv_evalRen ⟨fun j => ξ.apply (.there j)⟩ ρ i

theorem evalRen_comp_wkn :
    {Γ Δ : Cxt} → {τ : Ty} → (ξ : Ren Γ Δ) → (ρ : Cxt.denote Δ) → (x : τ.denote) →
    evalRen (⟨fun i => .there (ξ.apply i)⟩ : Ren Γ (.snoc Δ τ)) (ρ, x) = evalRen ξ ρ
  | .nil, _, _, _, _, _ => rfl
  | .snoc _ _, _, _, ξ, ρ, x => by
      simp [evalRen, lookupEnv]
      exact evalRen_comp_wkn ⟨fun i => ξ.apply (.there i)⟩ ρ x

theorem evalRen_lift {Γ Δ : Cxt} {τ : Ty} (ξ : Ren Γ Δ) (ρ : Cxt.denote Δ) (x : τ.denote) :
    evalRen (Ren.lift ξ) (ρ, x) = (evalRen ξ ρ, x) := by
  simp [evalRen, Ren.lift, lookupEnv]
  exact evalRen_comp_wkn ξ ρ x

/-- Soundness of System T term weakening with respect to Lean 4 evaluation. -/
theorem eval_wk {Γ Δ : Cxt} {σ : Ty} (t : Tm Γ σ) (ξ : Ren Γ Δ) (ρ : Cxt.denote Δ) :
    (t.wk ξ).eval ρ = t.eval (evalRen ξ ρ) := by
  induction t generalizing Δ with
  | var i => exact (lookupEnv_evalRen ξ ρ i).symm
  | unit | tt | ff | ite | zero | recNat | nil | recList => rfl
  | succ n ih => simp [Tm.wk, Tm.eval, ih]
  | cons h tl ihh iht => simp [Tm.wk, Tm.eval, ihh, iht]
  | pair a b iha ihb => simp [Tm.wk, Tm.eval, iha, ihb]
  | pr1 w ih => simp [Tm.wk, Tm.eval, ih]
  | pr2 w ih => simp [Tm.wk, Tm.eval, ih]
  | lam body ih =>
      funext x
      simp [Tm.wk, Tm.eval, ih, evalRen_lift]
  | app f a ihf iha => simp [Tm.wk, Tm.eval, ihf, iha]

theorem evalRen_id : {Γ : Cxt} → (ρ : Cxt.denote Γ) → evalRen Ren.id ρ = ρ
  | .nil, _ => rfl
  | .snoc Γ' _, (ρ, y) => by
      simp only [evalRen, Ren.id, lookupEnv]
      have h1 : evalRen ⟨fun i => .there i⟩ (ρ, y) = evalRen (Ren.id (Γ := Γ')) ρ :=
        evalRen_comp_wkn (Ren.id (Γ := Γ')) ρ y
      rw [h1, evalRen_id ρ]

theorem evalRen_wkn {Γ : Cxt} {τ : Ty} (ρ : Cxt.denote Γ) (x : τ.denote) :
    evalRen (Ren.wkn (Γ := Γ) (τ := τ)) (ρ, x) = ρ := by
  have h := evalRen_comp_wkn (Ren.id (Γ := Γ)) ρ x
  change evalRen (Ren.wkn (Γ := Γ) (τ := τ)) (ρ, x) = evalRen (Ren.id (Γ := Γ)) ρ at h
  rw [h, evalRen_id]

/-- Interpret a parallel substitution `θ : Sub Γ Δ` semantically (`Δ.denote → Γ.denote`). -/
def evalSub : {Γ Δ : Cxt} → Sub Γ Δ → Cxt.denote Δ → Cxt.denote Γ
  | .nil, _, _, _ => ()
  | .snoc _ _, _, θ, ρ =>
      (evalSub ⟨fun i => θ.apply (.there i)⟩ ρ, (θ.apply .here).eval ρ)

theorem lookupEnv_evalSub :
    {Γ Δ : Cxt} → (θ : Sub Γ Δ) → (ρ : Cxt.denote Δ) →
    ∀ {σ : Ty} (i : SnocList.Mem σ Γ), lookupEnv i (evalSub θ ρ) = (θ.apply i).eval ρ
  | .snoc _ _, _, _, _, _, .here => rfl
  | .snoc _ _, _, θ, ρ, _, .there i =>
      lookupEnv_evalSub ⟨fun j => θ.apply (.there j)⟩ ρ i

theorem evalSub_comp_wkn :
    {Γ Δ : Cxt} → {τ : Ty} → (θ : Sub Γ Δ) → (ρ : Cxt.denote Δ) → (x : τ.denote) →
    evalSub (⟨fun i => (θ.apply i).wkn⟩ : Sub Γ (.snoc Δ τ)) (ρ, x) = evalSub θ ρ
  | .nil, _, _, _, _, _ => rfl
  | .snoc _ _, _, _, θ, ρ, x => by
      simp [evalSub, Tm.wkn, eval_wk, evalRen_wkn]
      exact evalSub_comp_wkn ⟨fun i => θ.apply (.there i)⟩ ρ x

theorem evalSub_lift {Γ Δ : Cxt} {τ : Ty} (θ : Sub Γ Δ) (ρ : Cxt.denote Δ) (x : τ.denote) :
    evalSub (Sub.lift θ) (ρ, x) = (evalSub θ ρ, x) := by
  simp [evalSub, Sub.lift, Tm.eval, lookupEnv]
  exact evalSub_comp_wkn θ ρ x

/-- **Substitution Soundness Theorem for Gödel's System T**: parallel substitution commutes
    with denotational evaluation (`⟦ t[θ] ⟧ ρ = ⟦ t ⟧ (⟦ θ ⟧ ρ)`). -/
theorem eval_substPar {Γ Δ : Cxt} {σ : Ty} (t : Tm Γ σ) (θ : Sub Γ Δ) (ρ : Cxt.denote Δ) :
    (t.substPar θ).eval ρ = t.eval (evalSub θ ρ) := by
  induction t generalizing Δ with
  | var i => exact (lookupEnv_evalSub θ ρ i).symm
  | unit | tt | ff | ite | zero | recNat | nil | recList => rfl
  | succ n ih => simp [Tm.substPar, Tm.eval, ih]
  | cons h tl ihh iht => simp [Tm.substPar, Tm.eval, ihh, iht]
  | pair a b iha ihb => simp [Tm.substPar, Tm.eval, iha, ihb]
  | pr1 w ih => simp [Tm.substPar, Tm.eval, ih]
  | pr2 w ih => simp [Tm.substPar, Tm.eval, ih]
  | lam body ih =>
      funext x
      simp [Tm.substPar, Tm.eval, ih, evalSub_lift]
  | app f a ihf iha => simp [Tm.substPar, Tm.eval, ihf, iha]

theorem evalSub_id : {Γ : Cxt} → (ρ : Cxt.denote Γ) → evalSub ⟨fun i => .var i⟩ ρ = ρ
  | .nil, _ => rfl
  | .snoc Γ' τ', (ρ, y) => by
      have h1 : evalSub (⟨fun i => (Tm.var i).wkn⟩ : Sub Γ' (.snoc Γ' τ')) (ρ, y) =
          evalSub (⟨fun i => .var i⟩ : Sub Γ' Γ') ρ :=
        evalSub_comp_wkn (⟨fun i => .var i⟩ : Sub Γ' Γ') ρ y
      exact congrArg (fun z => (z, y)) (h1.trans (evalSub_id ρ))

theorem evalSub_single {Γ : Cxt} {τ : Ty} (u : Tm Γ τ) (ρ : Cxt.denote Γ) :
    evalSub (Sub.single u) ρ = (ρ, u.eval ρ) := by
  simp [evalSub, Sub.single, evalSub_id]

/-- **β-Reduction Soundness Theorem**: `(λ body) ⬝ u` evaluates identically to `body[u]`. -/
theorem eval_beta {Γ : Cxt} {σ τ : Ty} (body : Tm (.snoc Γ σ) τ) (u : Tm Γ σ) (ρ : Cxt.denote Γ) :
    ((Tm.lam body) ⬝ u).eval ρ = (body.subst u).eval ρ := by
  simp [Tm.eval, Tm.subst, eval_substPar, evalSub_single]

/-! ### Herbrand Candidate-List Validity & Constructive Witness Refinement -/

/-- A Dialectica-extracted candidate function `F : α → List β` is *Herbrand-valid* for a
    decidable internal relation `P : α → β → Bool` (`∀ˢᵗ x ∃ˢᵗ y P(x,y)`) if for every standard
    input `x`, at least one element of the finite candidate list `F x` satisfies `P x y`. -/
def HerbrandValid {α β : Type} (P : α → β → Bool) (F : α → List β) : Prop :=
  ∀ x : α, ∃ y ∈ F x, P x y = true

/-- Computably search a finite candidate list for a verified witness `{ y : β // q y = true }`. -/
def findVerifiedWitness {β : Type} (q : β → Bool) :
    (ys : List β) → (∃ y ∈ ys, q y = true) → { y : β // q y = true }
  | [], h => False.elim (by rcases h with ⟨_, hMem, _⟩; nomatch hMem)
  | y :: ys, h =>
      if hq : q y = true then
        ⟨y, hq⟩
      else
        findVerifiedWitness q ys (by
          rcases h with ⟨z, hMem, hz⟩
          cases hMem with
          | head => exact False.elim (hq hz)
          | tail _ hTail => exact ⟨z, hTail, hz⟩)

/-- **Constructive Refinement Soundness Theorem**: Any Herbrand-valid finite-list realiser
    `F : α → List β` (such as an unpruned System H Dialectica realiser `r₃''`) computably
    determines a single exact Bishop witness `(x : α) → { y : β // P x y = true }`, with
    **zero `Classical.choice`**. -/
def extractExactWitness {α β : Type} (P : α → β → Bool) (F : α → List β)
    (hValid : HerbrandValid P F) (x : α) : { y : β // P x y = true } :=
  findVerifiedWitness (P x) (F x) (hValid x)

/-- Over-approximating a candidate list preserves `HerbrandValid` (monotonicity of nonstandard
    witness ranges). -/
theorem herbrandValid_mono {α β : Type} {P : α → β → Bool} {F G : α → List β}
    (hSub : ∀ x y, y ∈ F x → y ∈ G x) (hF : HerbrandValid P F) : HerbrandValid P G := by
  intro x
  rcases hF x with ⟨y, hy, hPy⟩
  exact ⟨y, hSub x y hy, hPy⟩

end SystemH
end SandersNSA
