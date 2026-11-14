/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.AbstractInterpretation

/-!
# Computable Meshing of Sets, Types & Hyperfinite NSA (`SetTypeBridge`)

Addresses Alok Singh's design note on **meshing sets, types, and nonstandard analysis**
without `Prop`-erasure or `Classical.choice` (`noncomputable` contamination):

In classical Lean libraries, sets are predicates `Set α := α → Prop` and bounded nonstandard
existence `∃ x ∈ H, P x` lives in `Prop`. Recovering a witness `x : α` from `Prop` forces
`Classical.choose`, poisoning every downstream algorithm with `noncomputable`.

Here we represent internal hyperfinite collections via `HyperfiniteSet α` (backed by an
explicit computable enumeration `elements : List α`) and provide:
1. **Set-algebraic operations** (`empty`, `singleton`, `union`, `sep`, `image`, `product`,
   `natRange`, `gridRange`) with verified membership equivalences.
2. **Decision procedures** (`memB`, `forallB`, `existsB`) reflecting directly into `Prop`.
3. **Witness Reification (`reifyWitness`)**: computably promotes a *propositional* (`Prop`)
   existence proof `∃ x ∈ H, P x = true` into a first-class **`Type`-valued** witness
   `BoundedSigma H P := { x : α // x ∈ H.elements ∧ P x = true }` with **zero `Classical.choice`**.
4. **Hyperfinite Choice Reification (`reifyHyperfiniteChoice`)**: computably turns a
   `Prop`-valued `∀ x ∈ A, ∃ y ∈ B, R x y = true` into a `Type`-valued choice function
   `(x : α) → x ∈ A.elements → BoundedSigma B (R x)`.
-/

namespace SandersNSA
namespace Tactic

/-- Computable hyperfinite set backed by an explicit finite list of elements. -/
structure HyperfiniteSet (α : Type) : Type where
  elements : List α
  deriving DecidableEq, Repr

namespace HyperfiniteSet

/-- Propositional membership `x ∈ H`. -/
def Mem {α : Type} (x : α) (H : HyperfiniteSet α) : Prop :=
  x ∈ H.elements

/-- Computable boolean membership check when `α` has `DecidableEq`. -/
def memB {α : Type} [DecidableEq α] (x : α) (H : HyperfiniteSet α) : Bool :=
  decide (x ∈ H.elements)

/-- Internal cardinality (counting with multiplicity of the hyperfinite presentation). -/
@[inline] def card {α : Type} (H : HyperfiniteSet α) : Nat :=
  H.elements.length

/-- Empty hyperfinite set `∅`. -/
def empty {α : Type} : HyperfiniteSet α := ⟨[]⟩

/-- Singleton hyperfinite set `{a}`. -/
def singleton {α : Type} (a : α) : HyperfiniteSet α := ⟨[a]⟩

/-- Binary union `H₁ ∪ H₂`. -/
def union {α : Type} (H₁ H₂ : HyperfiniteSet α) : HyperfiniteSet α :=
  ⟨H₁.elements ++ H₂.elements⟩

/-- Internal Δ₀ separation `{ x ∈ H | P x }`. -/
def sep {α : Type} (P : α → Bool) (H : HyperfiniteSet α) : HyperfiniteSet α :=
  ⟨H.elements.filter P⟩

/-- Internal image `{ f x | x ∈ H }`. -/
def image {α β : Type} (f : α → β) (H : HyperfiniteSet α) : HyperfiniteSet β :=
  ⟨H.elements.map f⟩

/-- Internal Cartesian product `H₁ × H₂`. -/
def product {α β : Type} (H₁ : HyperfiniteSet α) (H₂ : HyperfiniteSet β) :
    HyperfiniteSet (α × β) :=
  ⟨H₁.elements.flatMap (fun a => H₂.elements.map (fun b => (a, b)))⟩

/-- Hyperfinite natural initial segment `{0, 1, …, N}`. -/
def natRange (N : Nat) : HyperfiniteSet Nat :=
  ⟨(List.range (N + 1))⟩

/-- Hyperfinite rational grid `{0/(N+1), 1/(N+1), …, (N+1)/(N+1)}` on `[0, 1]`. -/
def gridRange (N : Nat) : HyperfiniteSet Antipodes.QVal :=
  ⟨(List.range (N + 2)).map (Antipodes.QVal.gridPt N)⟩

/-- Convert a `HyperfiniteSet α` into Chuangjie Xu's `WitnessApprox α` abstract domain. -/
@[inline] def toWitnessApprox {α : Type} (H : HyperfiniteSet α) : Antipodes.WitnessApprox α :=
  ⟨H.elements⟩

/-! ### Membership & Quantifier Reflection Theorems -/

theorem mem_union_iff {α : Type} (x : α) (H₁ H₂ : HyperfiniteSet α) :
    Mem x (union H₁ H₂) ↔ Mem x H₁ ∨ Mem x H₂ :=
  List.mem_append

theorem mem_sep_iff {α : Type} (P : α → Bool) (H : HyperfiniteSet α) (x : α) :
    Mem x (sep P H) ↔ Mem x H ∧ P x = true :=
  List.mem_filter

theorem mem_image_iff {α β : Type} (f : α → β) (H : HyperfiniteSet α) (y : β) :
    Mem y (image f H) ↔ ∃ x, Mem x H ∧ f x = y :=
  List.mem_map

theorem mem_product_iff {α β : Type} (H₁ : HyperfiniteSet α) (H₂ : HyperfiniteSet β) (p : α × β) :
    Mem p (product H₁ H₂) ↔ Mem p.1 H₁ ∧ Mem p.2 H₂ := by
  rcases p with ⟨a, b⟩
  unfold Mem product
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a', ha', b', hb', hEq⟩
    cases hEq
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- Computable bounded universal quantifier `∀ x ∈ H, P x`. -/
def forallB {α : Type} (P : α → Bool) (H : HyperfiniteSet α) : Bool :=
  H.elements.all P

/-- Computable bounded existential quantifier `∃ x ∈ H, P x`. -/
def existsB {α : Type} (P : α → Bool) (H : HyperfiniteSet α) : Bool :=
  H.elements.any P

theorem forallB_eq_true_iff {α : Type} (P : α → Bool) (H : HyperfiniteSet α) :
    forallB P H = true ↔ ∀ x, Mem x H → P x = true :=
  List.all_eq_true

theorem existsB_eq_true_iff {α : Type} (P : α → Bool) (H : HyperfiniteSet α) :
    existsB P H = true ↔ ∃ x, Mem x H ∧ P x = true :=
  List.any_eq_true

/-! ### Set ↔ Type Witness Reification (Zero `Classical.choice`) -/

/-- `Type`-valued carrier of elements belonging to `H`. -/
abbrev Elem {α : Type} (H : HyperfiniteSet α) : Type :=
  { x : α // Mem x H }

/-- `Type`-valued Sigma/Subtype witness of a set-bounded property `∃ x ∈ H, P x`. -/
abbrev BoundedSigma {α : Type} (H : HyperfiniteSet α) (P : α → Bool) : Type :=
  { x : α // Mem x H ∧ P x = true }

/-- Erase a `Type`-valued `BoundedSigma` witness into a `Prop`-valued set existence statement. -/
theorem eraseWitness {α : Type} {H : HyperfiniteSet α} {P : α → Bool}
    (w : BoundedSigma H P) : ∃ x, Mem x H ∧ P x = true :=
  ⟨w.val, w.property⟩

/-- Auxiliary bounded linear search promoting `Prop` existence on `xs : List α` into `Type`. -/
def reifyListWitness {α : Type} (P : α → Bool) :
    (xs : List α) → (∃ x, x ∈ xs ∧ P x = true) → { x : α // x ∈ xs ∧ P x = true }
  | [], h => False.elim (by rcases h with ⟨_, hMem, _⟩; nomatch hMem)
  | x :: xs, h =>
      if hPx : P x = true then
        ⟨x, .head xs, hPx⟩
      else
        let recRes := reifyListWitness P xs (by
          rcases h with ⟨z, hMem, hPz⟩
          cases hMem with
          | head => exact False.elim (hPx hPz)
          | tail _ hTail => exact ⟨z, hTail, hPz⟩)
        ⟨recRes.val, .tail x recRes.property.1, recRes.property.2⟩

/-- **Set-to-Type Witness Reification (`reifyWitness`)**:
    Computably promotes a `Prop`-erased set-theoretic existence proof `∃ x ∈ H, P x = true`
    into a concrete `Type`-valued `BoundedSigma H P` witness without `Classical.choice`! -/
def reifyWitness {α : Type} (H : HyperfiniteSet α) (P : α → Bool)
    (h : ∃ x, Mem x H ∧ P x = true) : BoundedSigma H P :=
  reifyListWitness P H.elements h

/-- Boolean-decided variant: when `existsB P H = true` (e.g., by `decide` or runtime check),
    extracts a `BoundedSigma H P` witness directly. -/
def reifyFromBool {α : Type} (H : HyperfiniteSet α) (P : α → Bool)
    (h : existsB P H = true) : BoundedSigma H P :=
  reifyWitness H P ((existsB_eq_true_iff P H).mp h)

/-- **Computable Hyperfinite Axiom of Choice (`reifyHyperfiniteChoice`)**:
    Given hyperfinite sets `A` and `B`, decidable relation `R : α → β → Bool`, and a
    *propositional* (`Prop`) proof `∀ x ∈ A, ∃ y ∈ B, R x y = true`, computably constructs
    an explicit `Type`-valued choice function `(x : Elem A) → BoundedSigma B (R x.val)`. -/
def reifyHyperfiniteChoice {α β : Type}
    (A : HyperfiniteSet α) (B : HyperfiniteSet β) (R : α → β → Bool)
    (h : ∀ x : α, Mem x A → ∃ y : β, Mem y B ∧ R x y = true) :
    (x : Elem A) → BoundedSigma B (R x.val) :=
  fun x => reifyWitness B (R x.val) (h x.val x.property)

/-- Reify the choice function as an explicit lookup table `List (α × β)` over `A`. -/
def reifyChoiceGraph {α β : Type}
    (A : HyperfiniteSet α) (B : HyperfiniteSet β) (R : α → β → Bool)
    (h : ∀ x : α, Mem x A → ∃ y : β, Mem y B ∧ R x y = true) :
    List (α × β) :=
  A.elements.attach.map fun x =>
    (x.val, (reifyHyperfiniteChoice A B R h x).val)

end HyperfiniteSet

end Tactic
end SandersNSA
