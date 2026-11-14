/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# System H & Gödel's System T — Intrinsically Typed Syntax & Semantics

Computable Lean 4 port and extension of module `H` from Chuangjie Xu & Sam Sanders's
`nonstandard_dialectica` (implementing van den Berg, Briseid & Safarik, *Annals of Pure
and Applied Logic* 163(12), 2012, pp. 1962–1994, and Sanders, *CL&C* 2016).

## Improvements over the Upstream Agda Formalization
1. **Total Structural Termination**: Upstream Agda required `{-# OPTIONS --no-termination-check #-}`
   because single-variable substitution recursed through `exch`. Here we formulate parallel
   renamings (`Ren`) and parallel substitutions (`Sub`), making `Tm.wk`, `Tm.substPar`,
   `Fml.wkF`, and `Fml.substPar` **primitively structurally recursive** with kernel `rfl` reduction.
2. **Decidable Internal Predicate**: `Fml.isInternal : Fml Γ → Bool` decides whether a formula
   belongs to the internal fragment (free of `st`, `∀ˢᵗ`, `∃ˢᵗ`), so internal side conditions discharge
   by `rfl` while preserving named smart constructors.
3. **Syntactic `Δ_ns` / `∀ˢᵗ∃ˢᵗ` Classification**: Includes computable syntactic recognizers for pure
   external prefixes (`∀ˢᵗ x ∃ˢᵗ y φ(x,y)` with internal matrix `φ`), connecting System H directly
   to Nelson's algorithm and Sanders's *CL&C'16* translation.
-/

namespace SandersNSA
namespace SystemH

universe u v

/-- Snoc-lists (`ε`, `Γ ₊ x`) matching type-theoretic context growth on the right. -/
inductive SnocList (α : Type u) : Type u where
  | nil : SnocList α
  | snoc : SnocList α → α → SnocList α
  deriving DecidableEq, Repr

namespace SnocList

/-- Right-associative snoc-list concatenation (`Γ ₊₊ Δ`). -/
def append {α : Type u} : SnocList α → SnocList α → SnocList α
  | xs, .nil => xs
  | xs, .snoc ys y => .snoc (append xs ys) y

/-- Map a function across a `SnocList`. -/
def map {α : Type u} {β : Type v} (f : α → β) : SnocList α → SnocList β
  | .nil => .nil
  | .snoc xs x => .snoc (map f xs) (f x)

/-- Length of a `SnocList`. -/
def length {α : Type u} : SnocList α → Nat
  | .nil => 0
  | .snoc xs _ => xs.length + 1

/-- Proof-relevant de Bruijn membership witness (`x ∈ Γ`). -/
inductive Mem {α : Type u} : α → SnocList α → Type u where
  | here : {xs : SnocList α} → {x : α} → Mem x (.snoc xs x)
  | there : {xs : SnocList α} → {x y : α} → Mem x xs → Mem x (.snoc xs y)
  deriving DecidableEq, Repr

end SnocList

/-- Finite types of Gödel's System T extended with finite lists (`σ *`). -/
inductive Ty : Type where
  | unit : Ty
  | bool : Ty
  | nat : Ty
  | list : Ty → Ty
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Typing contexts are snoc-lists of System T types. -/
abbrev Cxt : Type := SnocList Ty

/-- Type-preserving variable renaming between contexts (`Γ ⊆ Δ`). -/
structure Ren (Γ Δ : Cxt) : Type where
  apply : ∀ {σ : Ty}, SnocList.Mem σ Γ → SnocList.Mem σ Δ

namespace Ren

/-- Identity renaming. -/
def id {Γ : Cxt} : Ren Γ Γ := ⟨fun i => i⟩

/-- Composition of renamings. -/
def comp {Γ Δ Θ : Cxt} (ξ₂ : Ren Δ Θ) (ξ₁ : Ren Γ Δ) : Ren Γ Θ :=
  ⟨fun i => ξ₂.apply (ξ₁.apply i)⟩

/-- Lift a renaming under a bound variable of type `τ`. -/
def lift {Γ Δ : Cxt} {τ : Ty} (ξ : Ren Γ Δ) : Ren (.snoc Γ τ) (.snoc Δ τ) :=
  ⟨fun
    | .here => .here
    | .there i => .there (ξ.apply i)⟩

/-- Weakening by one variable (`Γ ⊆ Γ ₊ τ`). -/
def wkn {Γ : Cxt} {τ : Ty} : Ren Γ (.snoc Γ τ) :=
  ⟨fun i => .there i⟩

/-- Weakening from the empty context (`ε ⊆ Γ`). -/
def wkNil {Γ : Cxt} : Ren .nil Γ :=
  ⟨fun i => nomatch i⟩

/-- Weakening on the right by an arbitrary context (`Γ ⊆ Γ ₊₊ Δ`). -/
def wkAppendR {Γ : Cxt} : (Δ : Cxt) → Ren Γ (Γ.append Δ)
  | .nil => Ren.id
  | .snoc Δ _ => ⟨fun i => .there ((wkAppendR Δ).apply i)⟩

/-- Extend a renaming across a shared suffix `Δ` (`Γ ₊₊ Δ ⊆ Θ ₊₊ Δ`). -/
def ext {Γ Θ : Cxt} (ξ : Ren Γ Θ) : (Δ : Cxt) → Ren (Γ.append Δ) (Θ.append Δ)
  | .nil => ξ
  | .snoc Δ _ => lift (ext ξ Δ)

/-- Exchange the top two bound variables (`Γ ₊ α ₊ β ⊆ Γ ₊ β ₊ α`). -/
def exch {Γ : Cxt} {α β : Ty} : Ren (.snoc (.snoc Γ α) β) (.snoc (.snoc Γ β) α) :=
  ⟨fun
    | .here => .there .here
    | .there .here => .here
    | .there (.there i) => .there (.there i)⟩

/-- Move a variable across suffix `Δ` (`(Γ ₊ α) ₊₊ Δ ⊆ (Γ ₊₊ Δ) ₊ α`). -/
def exchEnd {Γ : Cxt} {α : Ty} : (Δ : Cxt) → Ren ((SnocList.snoc Γ α).append Δ) ((Γ.append Δ).snoc α)
  | .nil => Ren.id
  | .snoc Δ _ => ⟨fun i => exch.apply ((lift (exchEnd Δ)).apply i)⟩

end Ren

/-- Intrinsically well-typed terms of Gödel's System T with finite lists. -/
inductive Tm : Cxt → Ty → Type where
  | var : {Γ : Cxt} → {σ : Ty} → SnocList.Mem σ Γ → Tm Γ σ
  | unit : {Γ : Cxt} → Tm Γ .unit
  | tt : {Γ : Cxt} → Tm Γ .bool
  | ff : {Γ : Cxt} → Tm Γ .bool
  | ite : {Γ : Cxt} → {α : Ty} → Tm Γ (.arr α (.arr α (.arr .bool α)))
  | zero : {Γ : Cxt} → Tm Γ .nat
  | succ : {Γ : Cxt} → Tm Γ .nat → Tm Γ .nat
  | recNat : {Γ : Cxt} → {α : Ty} → Tm Γ (.arr α (.arr (.arr .nat (.arr α α)) (.arr .nat α)))
  | nil : {Γ : Cxt} → {α : Ty} → Tm Γ (.list α)
  | cons : {Γ : Cxt} → {α : Ty} → Tm Γ α → Tm Γ (.list α) → Tm Γ (.list α)
  | recList : {Γ : Cxt} → {α β : Ty} → Tm Γ (.arr α (.arr (.arr β (.arr α α)) (.arr (.list β) α)))
  | pair : {Γ : Cxt} → {α β : Ty} → Tm Γ α → Tm Γ β → Tm Γ (.prod α β)
  | pr1 : {Γ : Cxt} → {α β : Ty} → Tm Γ (.prod α β) → Tm Γ α
  | pr2 : {Γ : Cxt} → {α β : Ty} → Tm Γ (.prod α β) → Tm Γ β
  | lam : {Γ : Cxt} → {α β : Ty} → Tm (.snoc Γ α) β → Tm Γ (.arr α β)
  | app : {Γ : Cxt} → {α β : Ty} → Tm Γ (.arr α β) → Tm Γ α → Tm Γ β
  deriving Repr

infixl:70 " ⬝ " => Tm.app

namespace Tm

/-- Structurally recursive weakening/renaming of System T terms. -/
def wk {Γ Δ : Cxt} {σ : Ty} (ξ : Ren Γ Δ) : Tm Γ σ → Tm Δ σ
  | .var i => .var (ξ.apply i)
  | .unit => .unit
  | .tt => .tt
  | .ff => .ff
  | .ite => .ite
  | .zero => .zero
  | .succ n => .succ (wk ξ n)
  | .recNat => .recNat
  | .nil => .nil
  | .cons h t => .cons (wk ξ h) (wk ξ t)
  | .recList => .recList
  | .pair a b => .pair (wk ξ a) (wk ξ b)
  | .pr1 w => .pr1 (wk ξ w)
  | .pr2 w => .pr2 (wk ξ w)
  | .lam body => .lam (wk (Ren.lift ξ) body)
  | .app f a => .app (wk ξ f) (wk ξ a)

/-- Weaken by one new outermost variable. -/
def wkn {Γ : Cxt} {α χ : Ty} (t : Tm Γ α) : Tm (.snoc Γ χ) α := t.wk Ren.wkn

/-- Weaken by two variables in a single AST pass. -/
def wkn2 {Γ : Cxt} {α χ₁ χ₂ : Ty} (t : Tm Γ α) : Tm (.snoc (.snoc Γ χ₁) χ₂) α :=
  t.wk ⟨fun i => .there (.there i)⟩

/-- Weaken by three variables in a single AST pass. -/
def wkn3 {Γ : Cxt} {α χ₁ χ₂ χ₃ : Ty} (t : Tm Γ α) :
    Tm (.snoc (.snoc (.snoc Γ χ₁) χ₂) χ₃) α :=
  t.wk ⟨fun i => .there (.there (.there i))⟩

/-- Weaken by four variables in a single AST pass. -/
def wkn4 {Γ : Cxt} {α χ₁ χ₂ χ₃ χ₄ : Ty} (t : Tm Γ α) :
    Tm (.snoc (.snoc (.snoc (.snoc Γ χ₁) χ₂) χ₃) χ₄) α :=
  t.wk ⟨fun i => .there (.there (.there (.there i)))⟩

/-- Weaken a closed term into any context. -/
def wkNil {Γ : Cxt} {α : Ty} (t : Tm .nil α) : Tm Γ α := t.wk Ren.wkNil

/-- Weaken across an appended context `Δ`. -/
def wknAppend {Γ : Cxt} (Δ : Cxt) {α : Ty} (t : Tm Γ α) : Tm (Γ.append Δ) α :=
  t.wk (Ren.wkAppendR Δ)

/-- Exchange the top two variables in a term. -/
def exch {Γ : Cxt} {α β γ : Ty} (t : Tm (.snoc (.snoc Γ α) β) γ) :
    Tm (.snoc (.snoc Γ β) α) γ := t.wk Ren.exch

end Tm

/-- Parallel substitution from context `Γ` into `Δ`. -/
structure Sub (Γ Δ : Cxt) : Type where
  apply : ∀ {σ : Ty}, SnocList.Mem σ Γ → Tm Δ σ

namespace Sub

/-- Lift a parallel substitution under a binder of type `τ`. -/
def lift {Γ Δ : Cxt} {τ : Ty} (θ : Sub Γ Δ) : Sub (.snoc Γ τ) (.snoc Δ τ) :=
  ⟨fun {_} m =>
    match m with
    | .here => .var .here
    | .there i => (θ.apply i).wkn⟩

/-- Single-variable substitution replacing the top variable with `u`. -/
def single {Γ : Cxt} {τ : Ty} (u : Tm Γ τ) : Sub (.snoc Γ τ) Γ :=
  ⟨fun {_} m =>
    match m with
    | .here => u
    | .there i => .var i⟩

/-- Shift the top natural-number variable `x ↦ Succ x`. -/
def shiftSuccAux : {Γ : Cxt} → {σ : Ty} → SnocList.Mem σ (.snoc Γ .nat) → Tm (.snoc Γ .nat) σ
  | _, _, .here => .succ (.var .here)
  | _, _, .there i => .var (.there i)

def shiftSucc {Γ : Cxt} : Sub (.snoc Γ .nat) (.snoc Γ .nat) :=
  ⟨fun m => shiftSuccAux m⟩

end Sub

namespace Tm

/-- Structurally recursive parallel substitution on System T terms. -/
def substPar {Γ Δ : Cxt} {σ : Ty} (θ : Sub Γ Δ) : Tm Γ σ → Tm Δ σ
  | .var i => θ.apply i
  | .unit => .unit
  | .tt => .tt
  | .ff => .ff
  | .ite => .ite
  | .zero => .zero
  | .succ n => .succ (substPar θ n)
  | .recNat => .recNat
  | .nil => .nil
  | .cons h t => .cons (substPar θ h) (substPar θ t)
  | .recList => .recList
  | .pair a b => .pair (substPar θ a) (substPar θ b)
  | .pr1 w => .pr1 (substPar θ w)
  | .pr2 w => .pr2 (substPar θ w)
  | .lam body => .lam (substPar (Sub.lift θ) body)
  | .app f a => .app (substPar θ f) (substPar θ a)

/-- Substitute `u` for the top variable (`t[u]`). -/
def subst {Γ : Cxt} {α γ : Ty} (t : Tm (.snoc Γ α) γ) (u : Tm Γ α) : Tm Γ γ :=
  t.substPar (Sub.single u)

/-- Replace the top `Ⓝ` variable by its successor (`t[s]`). -/
def shiftSucc {Γ : Cxt} {σ : Ty} (t : Tm (.snoc Γ .nat) σ) : Tm (.snoc Γ .nat) σ :=
  t.substPar Sub.shiftSucc

/-- Substitute `u` for a middle variable across suffix `Δ`. -/
def substMid {Γ : Cxt} (Δ : Cxt) {α γ : Ty}
    (t : Tm ((SnocList.snoc Γ α).append Δ) γ) (u : Tm (Γ.append Δ) α) :
    Tm (Γ.append Δ) γ :=
  (t.wk (Ren.exchEnd Δ)).subst u

/-- De Bruijn variables `ν₀` through `ν₄`. -/
def v0 {Γ : Cxt} {σ : Ty} : Tm (.snoc Γ σ) σ := .var .here
def v1 {Γ : Cxt} {σ σ₁ : Ty} : Tm (.snoc (.snoc Γ σ) σ₁) σ := .var (.there .here)
def v2 {Γ : Cxt} {σ σ₁ σ₂ : Ty} : Tm (.snoc (.snoc (.snoc Γ σ) σ₁) σ₂) σ :=
  .var (.there (.there .here))
def v3 {Γ : Cxt} {σ σ₁ σ₂ σ₃ : Ty} : Tm (.snoc (.snoc (.snoc (.snoc Γ σ) σ₁) σ₂) σ₃) σ :=
  .var (.there (.there (.there .here)))
def v4 {Γ : Cxt} {σ σ₁ σ₂ σ₃ σ₄ : Ty} :
    Tm (.snoc (.snoc (.snoc (.snoc (.snoc Γ σ) σ₁) σ₂) σ₃) σ₄) σ :=
  .var (.there (.there (.there (.there .here))))

/-- Singleton list term `⟪ x ⟫`. -/
def singletonTm {Γ : Cxt} {σ : Ty} (x : Tm Γ σ) : Tm Γ (.list σ) := .cons x .nil

/-- Canonical inhabitant `𝒄` of every System T type. -/
def defaultTm {Γ : Cxt} : {σ : Ty} → Tm Γ σ
  | .unit => .unit
  | .bool => .tt
  | .nat => .zero
  | .list _ => singletonTm defaultTm
  | .prod _ _ => .pair defaultTm defaultTm
  | .arr _ _ => .lam defaultTm

/-- Closed combinator for list concatenation inside System T. -/
def appendComb {Γ : Cxt} {σ : Ty} : Tm Γ (.arr (.list σ) (.arr (.list σ) (.list σ))) :=
  .lam (.lam (.recList ⬝ v0 ⬝ (.lam (.lam (.cons v1 v0))) ⬝ v1))

/-- List concatenation `xs ++ ys` inside System T (`O(1)` AST size, zero weakening traversal). -/
def appendTm {Γ : Cxt} {σ : Ty} (xs ys : Tm Γ (.list σ)) : Tm Γ (.list σ) :=
  appendComb ⬝ xs ⬝ ys

/-- Closed combinator for `Mapᴸ` inside System T. -/
def mapComb {Γ : Cxt} {σ τ : Ty} : Tm Γ (.arr (.arr σ τ) (.arr (.list σ) (.list τ))) :=
  .lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (.cons (v3 ⬝ v1) v0))) ⬝ v0))

/-- `Mapᴸ f xs` inside System T (`O(1)` AST size, zero weakening traversal). -/
def mapTm {Γ : Cxt} {σ τ : Ty} (f : Tm Γ (.arr σ τ)) (xs : Tm Γ (.list σ)) : Tm Γ (.list τ) :=
  mapComb ⬝ f ⬝ xs

/-- Closed combinator for pointwise list application `Appᴸ`. -/
def appListComb {Γ : Cxt} {σ τ : Ty} :
    Tm Γ (.arr (.list (.arr σ τ)) (.arr (.list σ) (.list τ))) :=
  .lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (appendTm (mapTm v1 v2) v0))) ⬝ v1))

/-- Pointwise list application `Appᴸ fs xs` (`O(1)` AST size). -/
def appListTm {Γ : Cxt} {σ τ : Ty} (fs : Tm Γ (.list (.arr σ τ))) (xs : Tm Γ (.list σ)) :
    Tm Γ (.list τ) :=
  appListComb ⬝ fs ⬝ xs

/-- Closed combinator for `F ⟪ x ⟫ᴸ`. -/
def collect1Comb {Γ : Cxt} {σ τ : Ty} :
    Tm Γ (.arr (.list (.arr σ (.list τ))) (.arr σ (.list τ))) :=
  .lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (appendTm (v1 ⬝ v2) v0))) ⬝ v1))

/-- Collect outputs of a list of list-valued functions `F ⟪ x ⟫ᴸ` (`O(1)` AST size). -/
def collect1Tm {Γ : Cxt} {σ τ : Ty} (F : Tm Γ (.list (.arr σ (.list τ)))) (x : Tm Γ σ) :
    Tm Γ (.list τ) :=
  collect1Comb ⬝ F ⬝ x

/-- Closed combinator for `F ⟪ x ₓ y ⟫ᴸ`. -/
def collect2Comb {Γ : Cxt} {σ τ ρ : Ty} :
    Tm Γ (.arr (.list (.arr σ (.arr τ (.list ρ)))) (.arr σ (.arr τ (.list ρ)))) :=
  .lam (.lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (appendTm (v1 ⬝ v3 ⬝ v2) v0))) ⬝ v2)))

/-- Collect outputs of a list of binary list-valued functions `F ⟪ x ₓ y ⟫ᴸ` (`O(1)` AST size). -/
def collect2Tm {Γ : Cxt} {σ τ ρ : Ty}
    (F : Tm Γ (.list (.arr σ (.arr τ (.list ρ))))) (x : Tm Γ σ) (y : Tm Γ τ) :
    Tm Γ (.list ρ) :=
  collect2Comb ⬝ F ⬝ x ⬝ y

/-- First projection as a System T morphism. -/
def pr1FnTm {Γ : Cxt} {σ τ : Ty} : Tm Γ (.arr (.prod σ τ) σ) := .lam (.pr1 v0)

/-- Second projection as a System T morphism. -/
def pr2FnTm {Γ : Cxt} {σ τ : Ty} : Tm Γ (.arr (.prod σ τ) τ) := .lam (.pr2 v0)

/-- Map first projection over a list of pairs (`Pr1ᴸ`). -/
def pr1ListTm {Γ : Cxt} {σ τ : Ty} (xs : Tm Γ (.list (.prod σ τ))) : Tm Γ (.list σ) :=
  mapTm pr1FnTm xs

/-- Map second projection over a list of pairs (`Pr2ᴸ`). -/
def pr2ListTm {Γ : Cxt} {σ τ : Ty} (xs : Tm Γ (.list (.prod σ τ))) : Tm Γ (.list τ) :=
  mapTm pr2FnTm xs

/-- Closed combinator for `Pairʳ`. -/
def pairRightComb {Γ : Cxt} {σ τ : Ty} :
    Tm Γ (.arr σ (.arr (.list τ) (.list (.prod σ τ)))) :=
  .lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (.cons (.pair v3 v1) v0))) ⬝ v0))

/-- Pair a fixed left element `x` with every element of `ys` (`Pairʳ`, `O(1)` AST size). -/
def pairRightTm {Γ : Cxt} {σ τ : Ty} (x : Tm Γ σ) (ys : Tm Γ (.list τ)) :
    Tm Γ (.list (.prod σ τ)) :=
  pairRightComb ⬝ x ⬝ ys

/-- Closed combinator for Cartesian product `Pairᴸ`. -/
def pairListComb {Γ : Cxt} {σ τ : Ty} :
    Tm Γ (.arr (.list σ) (.arr (.list τ) (.list (.prod σ τ)))) :=
  .lam (.lam (.recList ⬝ .nil ⬝ (.lam (.lam (appendTm (pairRightTm v1 v2) v0))) ⬝ v1))

/-- Cartesian product of two candidate lists (`Pairᴸ`, `O(1)` AST size). -/
def pairListTm {Γ : Cxt} {σ τ : Ty} (xs : Tm Γ (.list σ)) (ys : Tm Γ (.list τ)) :
    Tm Γ (.list (.prod σ τ)) :=
  pairListComb ⬝ xs ⬝ ys

end Tm

/-! ## Denotational Semantics of System T in Computable Lean 4 -/

/-- Standard Lean 4 denotation `⟦ σ ⟧ʸ` of System T types. -/
@[reducible] def Ty.denote : Ty → Type
  | .unit => Unit
  | .bool => Bool
  | .nat => Nat
  | .list σ => List σ.denote
  | .prod σ τ => σ.denote × τ.denote
  | .arr σ τ => σ.denote → τ.denote

/-- Canonical semantic inhabitant `⟦𝒄⟧ σ`. -/
def Ty.defaultVal : (σ : Ty) → σ.denote
  | .unit => ()
  | .bool => true
  | .nat => Nat.zero
  | .list σ => [σ.defaultVal]
  | .prod σ τ => (σ.defaultVal, τ.defaultVal)
  | .arr _ τ => fun _ => τ.defaultVal

/-- Standard Lean 4 denotation `⟦ Γ ⟧ˣ` of System T contexts. -/
@[reducible] def Cxt.denote : Cxt → Type
  | .nil => Unit
  | .snoc Γ σ => Cxt.denote Γ × σ.denote

/-- Primitive recursion combinator on `Nat` matching `RecZer` and `RecSuc` definitionally. -/
def recNatVal {α : Type} (a : α) (f : Nat → α → α) : Nat → α
  | 0 => a
  | n + 1 => f n (recNatVal a f n)

/-- Primitive recursion combinator on `List` matching `LRecNil` and `LRecCon` definitionally. -/
def recListVal {α β : Type} (a : α) (f : β → α → α) : List β → α
  | [] => a
  | x :: xs => f x (recListVal a f xs)

/-- Look up a de Bruijn variable in an environment `ρ : Cxt.denote Γ`. -/
def lookupEnv : {Γ : Cxt} → {σ : Ty} → SnocList.Mem σ Γ → Cxt.denote Γ → σ.denote
  | .snoc _ _, _, .here, (_, a) => a
  | .snoc _ _, _, .there i, (ρ, _) => lookupEnv i ρ

/-- Total, computable evaluator `⟦ t ⟧ᵐ` embedding System T terms into Lean 4 functions. -/
def Tm.eval {Γ : Cxt} {σ : Ty} : Tm Γ σ → Cxt.denote Γ → σ.denote
  | .var i, ρ => lookupEnv i ρ
  | .unit, _ => ()
  | .tt, _ => true
  | .ff, _ => false
  | .ite, _ => fun t e b => if b then t else e
  | .zero, _ => 0
  | .succ n, ρ => n.eval ρ + 1
  | .recNat, _ => recNatVal
  | .nil, _ => []
  | .cons h t, ρ => h.eval ρ :: t.eval ρ
  | .recList, _ => recListVal
  | .pair a b, ρ => (a.eval ρ, b.eval ρ)
  | .pr1 w, ρ => (w.eval ρ).1
  | .pr2 w, ρ => (w.eval ρ).2
  | .lam body, ρ => fun x => body.eval (ρ, x)
  | .app f a, ρ => (f.eval ρ) (a.eval ρ)

/-! ## Formulas of Nonstandard Heyting Arithmetic (System H) -/

/-- Formulas `Fml Γ` of System H, with internal (`∀ᴴ`, `∃ᴴ`) and external (`st`, `∀ˢᵗ`, `∃ˢᵗ`) layers. -/
inductive Fml : Cxt → Type where
  | st : {Γ : Cxt} → {σ : Ty} → Tm Γ σ → Fml Γ
  | eq : {Γ : Cxt} → {σ : Ty} → Tm Γ σ → Tm Γ σ → Fml Γ
  | le : {Γ : Cxt} → Tm Γ .nat → Tm Γ .nat → Fml Γ
  | mem : {Γ : Cxt} → {σ : Ty} → Tm Γ σ → Tm Γ (.list σ) → Fml Γ
  | and : {Γ : Cxt} → Fml Γ → Fml Γ → Fml Γ
  | or : {Γ : Cxt} → Fml Γ → Fml Γ → Fml Γ
  | imp : {Γ : Cxt} → Fml Γ → Fml Γ → Fml Γ
  | allH : {Γ : Cxt} → {σ : Ty} → Fml (.snoc Γ σ) → Fml Γ
  | exH : {Γ : Cxt} → {σ : Ty} → Fml (.snoc Γ σ) → Fml Γ
  | allSt : {Γ : Cxt} → {σ : Ty} → Fml (.snoc Γ σ) → Fml Γ
  | exSt : {Γ : Cxt} → {σ : Ty} → Fml (.snoc Γ σ) → Fml Γ
  | even : {Γ : Cxt} → Tm Γ .nat → Fml Γ
  deriving Repr

/-- Falsity `⊥ᴴ` defined internally as `0 =ᴴ 1`. -/
def Fml.bot {Γ : Cxt} : Fml Γ := .eq .zero (.succ .zero)

namespace Fml

/-- Computable Boolean check for whether a formula belongs to the internal language (no `st`, `∀ˢᵗ`, `∃ˢᵗ`). -/
def isInternal {Γ : Cxt} : Fml Γ → Bool
  | .st _ => false
  | .eq _ _ => true
  | .le _ _ => true
  | .mem _ _ => true
  | .and A B => A.isInternal && B.isInternal
  | .or A B => A.isInternal && B.isInternal
  | .imp A B => A.isInternal && B.isInternal
  | .allH A => A.isInternal
  | .exH A => A.isInternal
  | .allSt _ => false
  | .exSt _ => false
  | .even _ => true

/-- Propositional internal-formula predicate (`A.isInternal = true`), decidable by kernel computation. -/
abbrev Internal {Γ : Cxt} (A : Fml Γ) : Prop := A.isInternal = true

/-- Computable recognizer for `∃ˢᵗ y₁ … φ` with internal matrix `φ`. -/
def isSigmaStPrefix {Γ : Cxt} : Fml Γ → Bool
  | .exSt A => A.isSigmaStPrefix
  | A => A.isInternal

/-- Recognizes `∀ˢᵗ … ∃ˢᵗ … φ` normal-form formulas (`Πˢᵗ₂` / `Δ_ns` computational normal form). -/
def isDeltaNS {Γ : Cxt} : Fml Γ → Bool
  | .allSt A => A.isDeltaNS
  | A => A.isSigmaStPrefix

/-- Structurally recursive formula renaming. -/
def wkF {Γ Δ : Cxt} (ξ : Ren Γ Δ) : Fml Γ → Fml Δ
  | .st a => .st (a.wk ξ)
  | .eq a b => .eq (a.wk ξ) (b.wk ξ)
  | .le a b => .le (a.wk ξ) (b.wk ξ)
  | .mem a w => .mem (a.wk ξ) (w.wk ξ)
  | .and A B => .and (A.wkF ξ) (B.wkF ξ)
  | .or A B => .or (A.wkF ξ) (B.wkF ξ)
  | .imp A B => .imp (A.wkF ξ) (B.wkF ξ)
  | .allH A => .allH (A.wkF (Ren.lift ξ))
  | .exH A => .exH (A.wkF (Ren.lift ξ))
  | .allSt A => .allSt (A.wkF (Ren.lift ξ))
  | .exSt A => .exSt (A.wkF (Ren.lift ξ))
  | .even n => .even (n.wk ξ)

/-- Weaken a formula by one variable (`wknᶠ`). -/
def wknF {Γ : Cxt} {σ : Ty} (A : Fml Γ) : Fml (.snoc Γ σ) := A.wkF Ren.wkn

/-- Insert a variable one position from the right (`wkn₁ᶠ : Fml (Γ ₊ σ) → Fml (Γ ₊ τ ₊ σ)`). -/
def wkn1F {Γ : Cxt} {σ τ : Ty} (A : Fml (.snoc Γ σ)) : Fml (.snoc (.snoc Γ τ) σ) :=
  A.wkF (Ren.lift Ren.wkn)

/-- Insert a variable two positions from the right (`wkn₂ᶠ : Fml (Γ ₊ σ ₊ τ) → Fml (Γ ₊ ρ ₊ σ ₊ τ)`). -/
def wkn2F {Γ : Cxt} {σ τ ρ : Ty} (A : Fml (.snoc (.snoc Γ σ) τ)) :
    Fml (.snoc (.snoc (.snoc Γ ρ) σ) τ) :=
  A.wkF (Ren.lift (Ren.lift Ren.wkn))

/-- Weaken a formula by two variables (`wkn²ᶠ`). -/
def wknSqF {Γ : Cxt} {σ τ : Ty} (A : Fml Γ) : Fml (.snoc (.snoc Γ σ) τ) := A.wknF.wknF

/-- Exchange the top two bound variables in a formula. -/
def exchF {Γ : Cxt} {σ τ : Ty} (A : Fml (.snoc (.snoc Γ σ) τ)) : Fml (.snoc (.snoc Γ τ) σ) :=
  A.wkF Ren.exch

/-- Structurally recursive parallel substitution on System H formulas. -/
def substPar {Γ Δ : Cxt} (θ : Sub Γ Δ) : Fml Γ → Fml Δ
  | .st a => .st (a.substPar θ)
  | .eq a b => .eq (a.substPar θ) (b.substPar θ)
  | .le a b => .le (a.substPar θ) (b.substPar θ)
  | .mem a w => .mem (a.substPar θ) (w.substPar θ)
  | .and A B => .and (A.substPar θ) (B.substPar θ)
  | .or A B => .or (A.substPar θ) (B.substPar θ)
  | .imp A B => .imp (A.substPar θ) (B.substPar θ)
  | .allH A => .allH (A.substPar (Sub.lift θ))
  | .exH A => .exH (A.substPar (Sub.lift θ))
  | .allSt A => .allSt (A.substPar (Sub.lift θ))
  | .exSt A => .exSt (A.substPar (Sub.lift θ))
  | .even n => .even (n.substPar θ)

/-- Single-variable formula substitution `A[u]ᶠ`. -/
def substF {Γ : Cxt} {σ : Ty} (A : Fml (.snoc Γ σ)) (u : Tm Γ σ) : Fml Γ :=
  A.substPar (Sub.single u)

/-- Shift top `Ⓝ` variable to `Succ ν₀` in a formula (`A[s]ᶠ`). -/
def shiftSuccF {Γ : Cxt} (A : Fml (.snoc Γ .nat)) : Fml (.snoc Γ .nat) :=
  A.substPar Sub.shiftSucc

end Fml

/-- Assumption contexts `Ξ` in System H. -/
abbrev Asmpt (Γ : Cxt) : Type := SnocList (Fml Γ)

/-- Weaken every assumption in `Ξ` by one term variable (`wknᵃ`). -/
def wknAsmpt {Γ : Cxt} {σ : Ty} : Asmpt Γ → Asmpt (.snoc Γ σ)
  | .nil => .nil
  | .snoc Ξ A => .snoc (wknAsmpt Ξ) A.wknF

/-! ## Proof Trees of System H (`Prf Ξ A`) -/

/-- Natural deduction / sequent proofs of System H, including Gödel's System T equations,
standardness rules, external induction `IRˢᵗ`, Idealisation `I`, Nonstandard Collection `NCR`,
Herbrandized Choice `HAC`, `HGMPˢᵗ`, and `HIP-∀ˢᵗ`. -/
inductive Prf : {Γ : Cxt} → Asmpt Γ → Fml Γ → Type where
  -- Structural rules
  | id : {Γ : Cxt} → {A : Fml Γ} → Prf (.snoc .nil A) A
  | wkn : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} →
      Prf Ξ B → Prf (.snoc Ξ A) B
  | swap : {Γ : Cxt} → {Ξ : Asmpt Γ} → (Ζ : Asmpt Γ) → {A B C : Fml Γ} →
      Prf ((SnocList.snoc (.snoc Ξ A) B).append Ζ) C →
      Prf ((SnocList.snoc (.snoc Ξ B) A).append Ζ) C
  -- Computational rules for `Ⓝ`
  | recZer : {Γ : Cxt} → {σ : Ty} → {a : Tm Γ σ} → {f : Tm Γ (.arr .nat (.arr σ σ))} →
      Prf .nil (.eq (.recNat ⬝ a ⬝ f ⬝ .zero) a)
  | recSuc : {Γ : Cxt} → {σ : Ty} → {a : Tm Γ σ} →
      {f : Tm Γ (.arr .nat (.arr σ σ))} → {n : Tm Γ .nat} →
      Prf .nil (.eq (.recNat ⬝ a ⬝ f ⬝ (.succ n)) (f ⬝ n ⬝ (.recNat ⬝ a ⬝ f ⬝ n)))
  -- Computational rules for `*` (`List`)
  | lrecNil : {Γ : Cxt} → {σ τ : Ty} → {a : Tm Γ σ} → {f : Tm Γ (.arr τ (.arr σ σ))} →
      Prf .nil (.eq (.recList ⬝ a ⬝ f ⬝ .nil) a)
  | lrecCon : {Γ : Cxt} → {σ τ : Ty} → {a : Tm Γ σ} → {f : Tm Γ (.arr τ (.arr σ σ))} →
      {x : Tm Γ τ} → {xs : Tm Γ (.list τ)} →
      Prf .nil (.eq (.recList ⬝ a ⬝ f ⬝ (.cons x xs)) (f ⬝ x ⬝ (.recList ⬝ a ⬝ f ⬝ xs)))
  -- Computational β/η rules for `⇾` and `⊠`
  | betaEq : {Γ : Cxt} → {σ τ : Ty} → {t : Tm (.snoc Γ σ) τ} → {u : Tm Γ σ} →
      Prf .nil (.eq ((.lam t) ⬝ u) (t.subst u))
  | etaEq : {Γ : Cxt} → {σ τ : Ty} → {f : Tm Γ (.arr σ τ)} →
      Prf .nil (.eq (.lam (f.wkn ⬝ Tm.v0)) f)
  | betaProd1 : {Γ : Cxt} → {σ τ : Ty} → {a : Tm Γ σ} → {b : Tm Γ τ} →
      Prf .nil (.eq (.pr1 (.pair a b)) a)
  | betaProd2 : {Γ : Cxt} → {σ τ : Ty} → {a : Tm Γ σ} → {b : Tm Γ τ} →
      Prf .nil (.eq (.pr2 (.pair a b)) b)
  | etaProd : {Γ : Cxt} → {σ τ : Ty} → {w : Tm Γ (.prod σ τ)} →
      Prf .nil (.eq (.pair (.pr1 w) (.pr2 w)) w)
  -- Equality congruence & extensionality
  | refl : {Γ : Cxt} → {σ : Ty} → {a : Tm Γ σ} → Prf .nil (.eq a a)
  | sym : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {a b : Tm Γ σ} →
      Prf Ξ (.eq a b) → Prf Ξ (.eq b a)
  | trans : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {a b c : Tm Γ σ} →
      Prf Ξ (.eq a b) → Prf Ξ (.eq b c) → Prf Ξ (.eq a c)
  | apF : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ τ : Ty} → {a b : Tm Γ σ} → {f : Tm Γ (.arr σ τ)} →
      Prf Ξ (.eq a b) → Prf Ξ (.eq (f ⬝ a) (f ⬝ b))
  | funExt : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ τ : Ty} → {f g : Tm Γ (.arr σ τ)} →
      Prf Ξ (.allH (.eq (f.wkn ⬝ Tm.v0) (g.wkn ⬝ Tm.v0))) → Prf Ξ (.eq f g)
  -- Order `≤ᴴ` and list membership `∈ᴴ`
  | leZero : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n : Tm Γ .nat} → Prf Ξ (.le .zero n)
  | leSucc : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n m : Tm Γ .nat} →
      Prf Ξ (.le n m) → Prf Ξ (.le (.succ n) (.succ m))
  | memZero : {Γ : Cxt} → {σ : Ty} → {a : Tm Γ σ} → {w : Tm Γ (.list σ)} →
      Prf .nil (.mem a (.cons a w))
  | memSucc : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {a b : Tm Γ σ} → {w : Tm Γ (.list σ)} →
      Prf Ξ (.mem a w) → Prf Ξ (.mem a (.cons b w))
  -- Intuitionistic logical rules
  | botElim : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A : Fml Γ} → Prf Ξ Fml.bot → Prf Ξ A
  | andIntro : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} →
      Prf Ξ A → Prf Ξ B → Prf Ξ (.and A B)
  | andElim1 : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} → Prf Ξ (.and A B) → Prf Ξ A
  | andElim2 : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} → Prf Ξ (.and A B) → Prf Ξ B
  | orInl : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} → Prf Ξ A → Prf Ξ (.or A B)
  | orInr : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} → Prf Ξ B → Prf Ξ (.or A B)
  | orElim : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B C : Fml Γ} →
      Prf Ξ (.imp A C) → Prf Ξ (.imp B C) → Prf Ξ (.or A B) → Prf Ξ C
  | impIntro : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} →
      Prf (.snoc Ξ A) B → Prf Ξ (.imp A B)
  | impElim : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A B : Fml Γ} →
      Prf Ξ (.imp A B) → Prf Ξ A → Prf Ξ B
  | allIntro : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf (wknAsmpt Ξ) A → Prf Ξ (.allH A)
  | allElim : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf Ξ (.allH A) → (u : Tm Γ σ) → Prf Ξ (A.substF u)
  | exIntro : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      (u : Tm Γ σ) → Prf Ξ (A.substF u) → Prf Ξ (.exH A)
  | exElim : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} → {B : Fml Γ} →
      Prf Ξ (.allH (.imp A B.wknF)) → Prf Ξ (.imp (.exH A) B)
  -- Standardness predicate `st` and external quantifiers `∀ˢᵗ`, `∃ˢᵗ`
  | stEq : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {a b : Tm Γ σ} →
      Prf Ξ (.st a) → Prf Ξ (.eq a b) → Prf Ξ (.st b)
  | stCl : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → (t : Tm .nil σ) → Prf Ξ (.st t.wkNil)
  | stAp : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ τ : Ty} → {f : Tm Γ (.arr σ τ)} → {a : Tm Γ σ} →
      Prf Ξ (.st f) → Prf Ξ (.st a) → Prf Ξ (.st (f ⬝ a))
  | allStI : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf Ξ (.allH (.imp (.st Tm.v0) A)) → Prf Ξ (.allSt A)
  | allStE : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf Ξ (.allSt A) → Prf Ξ (.allH (.imp (.st Tm.v0) A))
  | exStI : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf Ξ (.exH (.and (.st Tm.v0) A)) → Prf Ξ (.exSt A)
  | exStE : {Γ : Cxt} → {Ξ : Asmpt Γ} → {σ : Ty} → {A : Fml (.snoc Γ σ)} →
      Prf Ξ (.exSt A) → Prf Ξ (.exH (.and (.st Tm.v0) A))
  -- Internal (`IR`) and external (`IRˢᵗ`) induction
  | ir : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A : Fml (.snoc Γ .nat)} → Fml.Internal A →
      Prf Ξ (A.substF .zero) → Prf Ξ (.allH (.imp A A.shiftSuccF)) → Prf Ξ (.allH A)
  | irSt : {Γ : Cxt} → {Ξ : Asmpt Γ} → {A : Fml (.snoc Γ .nat)} →
      Prf Ξ (A.substF .zero) → Prf Ξ (.allSt (.imp A A.shiftSuccF)) → Prf Ξ (.allSt A)
  -- Flagship Nonstandard Principles of System H
  | idealisation : {Γ : Cxt} → {σ τ : Ty} → {φ : Fml (.snoc (.snoc Γ τ) σ)} → Fml.Internal φ →
      Prf .nil (.imp
        (@Fml.allSt Γ (.list σ)
          (@Fml.exH (.snoc Γ (.list σ)) τ
            (@Fml.allH (.snoc (.snoc Γ (.list σ)) τ) σ
              (.imp (.mem Tm.v0 Tm.v2) φ.wkn2F))))
        (@Fml.exH Γ τ (@Fml.allSt (.snoc Γ τ) σ φ)))
  | ncr : {Γ : Cxt} → {σ τ : Ty} → {Φ : Fml (.snoc (.snoc Γ τ) σ)} →
      Prf .nil (.imp
        (@Fml.allH Γ τ (@Fml.exSt (.snoc Γ τ) σ Φ))
        (@Fml.exSt Γ (.list σ)
          (@Fml.allH (.snoc Γ (.list σ)) τ
            (@Fml.exH (.snoc (.snoc Γ (.list σ)) τ) σ
              (.and (.mem Tm.v0 Tm.v2) Φ.wkn2F)))))
  | hac : {Γ : Cxt} → {σ τ : Ty} → {Φ : Fml (.snoc (.snoc Γ σ) τ)} →
      Prf .nil (.imp
        (@Fml.allSt Γ σ (@Fml.exSt (.snoc Γ σ) τ Φ))
        (@Fml.exSt Γ (.arr σ (.list τ))
          (@Fml.allSt (.snoc Γ (.arr σ (.list τ))) σ
            (@Fml.exH (.snoc (.snoc Γ (.arr σ (.list τ))) σ) τ
              (.and (.mem Tm.v0 (Tm.v2 ⬝ Tm.v1)) Φ.wkn2F)))))
  | hgmpSt : {Γ : Cxt} → {σ : Ty} → {φ : Fml (.snoc Γ σ)} → {ψ : Fml Γ} →
      Fml.Internal φ → Fml.Internal ψ →
      Prf .nil (.imp
        (.imp (@Fml.allSt Γ σ φ) ψ)
        (@Fml.exSt Γ (.list σ)
          (.imp
            (@Fml.allH (.snoc Γ (.list σ)) σ (.imp (.mem Tm.v0 Tm.v1) φ.wkn1F))
            ψ.wknF)))
  | hipAllSt : {Γ : Cxt} → {σ τ : Ty} → {φ : Fml (.snoc Γ σ)} → {Ψ : Fml (.snoc Γ τ)} →
      Fml.Internal φ →
      Prf .nil (.imp
        (.imp (@Fml.allSt Γ σ φ) (@Fml.exSt Γ τ Ψ))
        (@Fml.exSt Γ (.list τ)
          (.imp
            (@Fml.allSt (.snoc Γ (.list τ)) σ φ.wkn1F)
            (@Fml.exH (.snoc Γ (.list τ)) τ (.and (.mem Tm.v0 Tm.v1) Ψ.wkn1F)))))
  -- Arithmetic & parity axioms matching upstream `H.agda`
  | stSucc : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n : Tm Γ .nat} →
      Prf Ξ (.st n) → Prf Ξ (.st (.succ n))
  | leZeroEq : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n : Tm Γ .nat} →
      Prf Ξ (.le n .zero) → Prf Ξ (.eq n .zero)
  | leSuccOr : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n m : Tm Γ .nat} →
      Prf Ξ (.le n (.succ m)) → Prf Ξ (.or (.eq n (.succ m)) (.le n m))
  | evenZ : {Γ : Cxt} → {Ξ : Asmpt Γ} → Prf Ξ (.even .zero)
  | evenS : {Γ : Cxt} → {Ξ : Asmpt Γ} → {n : Tm Γ .nat} →
      Prf Ξ (.even n) → Prf Ξ (.even (.succ (.succ n)))

namespace Prf

/-- Project the topmost assumption `A` from `Ξ ₊ A` (`κ₀` in `H.agda`). -/
def k0 {Γ : Cxt} {A : Fml Γ} : {Ξ : Asmpt Γ} → Prf (.snoc Ξ A) A
  | .nil => .id
  | .snoc _ _ => .swap .nil (.wkn k0)

/-- Project assumption `κ₁` (`Ξ ₊ A ₊ B ⊢ A`). -/
def k1 {Γ : Cxt} {Ξ : Asmpt Γ} {A B : Fml Γ} : Prf (.snoc (.snoc Ξ A) B) A := .wkn k0

/-- Project assumption `κ₂` (`Ξ ₊ A ₊ B ₊ C ⊢ A`). -/
def k2 {Γ : Cxt} {Ξ : Asmpt Γ} {A B C : Fml Γ} : Prf (.snoc (.snoc (.snoc Ξ A) B) C) A := .wkn k1

/-- Project assumption `κ₃` (`Ξ ₊ A ₊ B ₊ C ₊ D ⊢ A`). -/
def k3 {Γ : Cxt} {Ξ : Asmpt Γ} {A B C D : Fml Γ} :
    Prf (.snoc (.snoc (.snoc (.snoc Ξ A) B) C) D) A := .wkn k2

end Prf

end SystemH
end SandersNSA
