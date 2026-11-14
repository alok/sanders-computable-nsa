/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Kleene S1–S9 Dialogue Trees & Constructive Continuity (`KleeneDialogue`)

From Alok Singh's Jan 31, 2024 interview and email correspondence with Sam Sanders on
Kleene's S1–S9 higher-order computability (Normann & Sanders, `arXiv:2102.04787`):
how do total type-2 functionals `F : (Nat → α) → β` acquire continuity and uniform-continuity
moduli **computably**, without Cohen forcing or classical Weak König's Lemma?

Following Escardó's Brouwer–Kleene dialogue-tree presentation of S1–S9 oracle computations:
1. `Dialogue α β`: well-founded sequential oracle interaction trees querying `f : Nat → α`.
2. **Substitution Scheme S4 (`Dialogue.bind` / `eval_bind`)**: Kleene composition of dialogue
   trees is monadic tree grafting.
3. **Baire Space Continuity (`eval_eq_of_agree_on_trace`, `eval_eq_of_agree_below_pointwiseModulus`)**:
   Every `d : Dialogue α β` queries only finitely many indices along `f`, yielding an explicit
   computable pointwise modulus `pointwiseModulus d f : Nat`.
4. **Cantor Space Uniform Continuity (`fanModulus`, `eval_eq_of_agree_below_fanModulus`)**:
   Every `d : Dialogue Bool β` has a **uniform** computable fan modulus `fanModulus d : Nat`
   independent of the oracle `f : Nat → Bool`.
5. **Baire vs. Cantor Separation (`adaptiveLookupDialogue`)**: a total `Dialogue Nat Nat` whose
   first query `f 0` determines how deep (`f (f 0 + 1)`) to probe next — pointwise continuous
   everywhere on `Nat → Nat`, yet provably possessing **no** uniform modulus (`adaptive_not_uniform`)!
-/

namespace SandersNSA
namespace ReverseMath

/-- Sequential Brouwer–Kleene dialogue tree representing a total S1–S9 computation
    relative to an oracle `f : Nat → α` returning a value in `β`. -/
inductive Dialogue (α β : Type) : Type where
  | answer : β → Dialogue α β
  | query  : Nat → (α → Dialogue α β) → Dialogue α β

namespace Dialogue

/-- Evaluate a dialogue tree `d` against an oracle `f : Nat → α`. -/
def eval {α β : Type} : Dialogue α β → (Nat → α) → β
  | .answer b, _ => b
  | .query idx k, f => eval (k (f idx)) f

/-- Kleene substitution scheme **S4**: sequence two oracle computations by grafting `next`
    onto every answer leaf of `d`. -/
def bind {α β γ : Type} : Dialogue α β → (β → Dialogue α γ) → Dialogue α γ
  | .answer b, next => next b
  | .query idx k, next => .query idx (fun a => bind (k a) next)

/-- Functorial post-composition on answers. -/
def map {α β γ : Type} (g : β → γ) (d : Dialogue α β) : Dialogue α γ :=
  d.bind (fun b => .answer (g b))

/-- Single oracle query `f idx` (Kleene's oracle application scheme **S8** at type 1). -/
def askOracle (α : Type) (idx : Nat) : Dialogue α α :=
  .query idx .answer

/-- Soundness of Kleene substitution **S4**: `eval (d.bind next) f = eval (next (eval d f)) f`. -/
theorem eval_bind {α β γ : Type} (d : Dialogue α β) (next : β → Dialogue α γ) (f : Nat → α) :
    (d.bind next).eval f = (next (d.eval f)).eval f := by
  induction d with
  | answer b => rfl
  | query idx k ih => exact ih (f idx)

theorem eval_map {α β γ : Type} (g : β → γ) (d : Dialogue α β) (f : Nat → α) :
    (d.map g).eval f = g (d.eval f) :=
  eval_bind d (fun b => .answer (g b)) f

/-! ## 1. Exact Query Traces & Pointwise Continuity on Baire Space `Nat → α` -/

/-- Exact ordered list of oracle indices queried during `d.eval f`. -/
def queryTrace {α β : Type} : Dialogue α β → (Nat → α) → List Nat
  | .answer _, _ => []
  | .query idx k, f => idx :: queryTrace (k (f idx)) f

/-- Computable strict upper bound on all oracle indices queried by `d` on input `f`:
    every queried index `i` satisfies `i < d.pointwiseModulus f`. -/
def pointwiseModulus {α β : Type} : Dialogue α β → (Nat → α) → Nat
  | .answer _, _ => 0
  | .query idx k, f => Nat.max (idx + 1) (pointwiseModulus (k (f idx)) f)

/-- Every index recorded in `d.queryTrace f` is strictly bounded by `d.pointwiseModulus f`. -/
theorem mem_queryTrace_lt_modulus {α β : Type} (d : Dialogue α β) (f : Nat → α) :
    ∀ {i : Nat}, i ∈ d.queryTrace f → i < d.pointwiseModulus f := by
  induction d with
  | answer _ =>
      intro i hMem
      nomatch hMem
  | query idx k ih =>
      intro i hMem
      simp only [queryTrace, pointwiseModulus, List.mem_cons] at hMem ⊢
      rcases hMem with rfl | hTail
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih (f idx) hTail) (Nat.le_max_right _ _)

/-- **Dialogue Trace Continuity Theorem**:
    If `f` and `g` agree on every index in `d.queryTrace f`, then `d` takes the exact same
    execution path on `f` and `g` (`d.eval f = d.eval g` and `d.queryTrace f = d.queryTrace g`). -/
theorem eval_and_trace_eq_of_agree_on_trace {α β : Type} (d : Dialogue α β) (f g : Nat → α)
    (hAgree : ∀ i : Nat, i ∈ d.queryTrace f → f i = g i) :
    d.eval f = d.eval g ∧ d.queryTrace f = d.queryTrace g := by
  induction d with
  | answer b => exact ⟨rfl, rfl⟩
  | query idx k ih =>
      have hHead : f idx = g idx := hAgree idx (.head _)
      simp only [eval, queryTrace]
      rw [← hHead]
      have hSub := ih (f idx) (fun i hi => hAgree i (.tail idx hi))
      exact ⟨hSub.1, congrArg (idx :: ·) hSub.2⟩

theorem eval_eq_of_agree_on_trace {α β : Type} (d : Dialogue α β) (f g : Nat → α)
    (hAgree : ∀ i : Nat, i ∈ d.queryTrace f → f i = g i) :
    d.eval f = d.eval g :=
  (eval_and_trace_eq_of_agree_on_trace d f g hAgree).1

/-- **Pointwise Continuity on Baire Space `Nat → α`**:
    `pointwiseModulus d f` is a verified computable modulus of pointwise continuity at `f`. -/
theorem eval_eq_of_agree_below_pointwiseModulus {α β : Type}
    (d : Dialogue α β) (f g : Nat → α)
    (hAgree : ∀ i : Nat, i < d.pointwiseModulus f → f i = g i) :
    d.eval f = d.eval g :=
  eval_eq_of_agree_on_trace d f g (fun i hi => hAgree i (mem_queryTrace_lt_modulus d f hi))

/-! ## 2. Constructive Fan Functional & Uniform Continuity on Cantor Space `Nat → Bool` -/

/-- **Computable Fan Modulus (`fanModulus`)**:
    Inspects both `false` and `true` branches of a finite-branching `Dialogue Bool β` tree
    to compute a **uniform** lookahead horizon `N` valid across all `2^N` Cantor prefixes! -/
def fanModulus {β : Type} : Dialogue Bool β → Nat
  | .answer _ => 0
  | .query idx k => Nat.max (idx + 1) (Nat.max (fanModulus (k false)) (fanModulus (k true)))

/-- `pointwiseModulus d f` never exceeds the uniform Cantor `fanModulus d`. -/
theorem pointwiseModulus_le_fanModulus {β : Type} (d : Dialogue Bool β) (f : Nat → Bool) :
    d.pointwiseModulus f ≤ d.fanModulus := by
  induction d with
  | answer _ => exact Nat.le_refl 0
  | query idx k ih =>
      simp only [pointwiseModulus, fanModulus]
      cases hBit : f idx
      · have hSub : (k false).pointwiseModulus f ≤ Nat.max (k false).fanModulus (k true).fanModulus :=
          Nat.le_trans (ih false) (Nat.le_max_left _ _)
        exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hSub (Nat.le_max_right _ _)⟩
      · have hSub : (k true).pointwiseModulus f ≤ Nat.max (k false).fanModulus (k true).fanModulus :=
          Nat.le_trans (ih true) (Nat.le_max_right _ _)
        exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hSub (Nat.le_max_right _ _)⟩

/-- **Cantor Uniform Continuity Theorem (Constructive Fan Theorem for Dialogue Trees)**:
    Any two Boolean streams `f, g : Nat → Bool` agreeing on `{0, …, d.fanModulus - 1}`
    yield the exact same output `d.eval f = d.eval g`. -/
theorem eval_eq_of_agree_below_fanModulus {β : Type}
    (d : Dialogue Bool β) (f g : Nat → Bool)
    (hAgree : ∀ i : Nat, i < d.fanModulus → f i = g i) :
    d.eval f = d.eval g :=
  eval_eq_of_agree_below_pointwiseModulus d f g (fun i hi =>
    hAgree i (Nat.lt_of_lt_of_le hi (pointwiseModulus_le_fanModulus d f)))

/-! ## 3. Baire vs. Cantor Separation: Pointwise Without Uniform Continuity on `Nat → Nat` -/

/-- Boolean XOR parity dialogue on indices `0, 1, …, n - 1`. -/
def parityPrefixDialogue : Nat → Dialogue Bool Bool
  | 0 => .answer false
  | n + 1 =>
      .query n (fun bit =>
        (parityPrefixDialogue n).map (fun acc => xor bit acc))

/-- Adaptive Baire-space dialogue `F(f) := f(f(0) + 1)`:
    First queries `f 0`, then uses the returned natural number `n = f 0` to decide which
    far-out index `n + 1` to query next! -/
def adaptiveLookupDialogue : Dialogue Nat Nat :=
  .query 0 (fun n => .query (n + 1) (fun v => .answer v))

theorem adaptiveLookupDialogue_eval (f : Nat → Nat) :
    adaptiveLookupDialogue.eval f = f (f 0 + 1) := rfl

theorem adaptiveLookupDialogue_modulus (f : Nat → Nat) :
    adaptiveLookupDialogue.pointwiseModulus f = f 0 + 2 := by
  simp only [adaptiveLookupDialogue, pointwiseModulus]
  have h1 : (f 0 + 1 + 1).max 0 = f 0 + 2 := Nat.max_eq_left (Nat.zero_le _)
  rw [h1]
  exact Nat.max_eq_right (by omega)

/-- **Baire-Space Non-Uniformity Theorem**:
    Even though `adaptiveLookupDialogue` is a 2-query total S1–S9 dialogue tree (hence
    pointwise continuous everywhere by `eval_eq_of_agree_below_pointwiseModulus`), NO single
    uniform lookahead `M : Nat` suffices on Baire space `Nat → Nat`! -/
theorem adaptive_not_uniform :
    ¬ ∃ M : Nat, ∀ f g : Nat → Nat,
        (∀ i : Nat, i < M → f i = g i) →
        adaptiveLookupDialogue.eval f = adaptiveLookupDialogue.eval g := by
  rintro ⟨M, hUnif⟩
  let f : Nat → Nat := fun i => if i = 0 then M else 0
  let g : Nat → Nat := fun i => if i = 0 then M else if i = M + 1 then 1 else 0
  have hAgree : ∀ i : Nat, i < M → f i = g i := by
    intro i hi
    dsimp [f, g]
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]
    · have hNe : i ≠ M + 1 := by omega
      simp only [h0, hNe, ↓reduceIte]
  have hEq := hUnif f g hAgree
  rw [adaptiveLookupDialogue_eval, adaptiveLookupDialogue_eval] at hEq
  have hf0 : f 0 = M := rfl
  have hg0 : g 0 = M := rfl
  rw [hf0, hg0] at hEq
  have hfVal : f (M + 1) = 0 := rfl
  have hgVal : g (M + 1) = 1 := by
    dsimp [g]
    simp only [↓reduceIte]
  rw [hfVal, hgVal] at hEq
  omega

end Dialogue
end ReverseMath
end SandersNSA
