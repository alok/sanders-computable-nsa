/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.ConstructiveAnalysis
import SandersNSA.SystemH.Dialectica

/-!
# Nonstandardization as Sound Abstract Interpretation

Formalizes Chuangjie Xu's observation (email to Alok Singh & Sam Sanders, Jan 14, 2026):

> *"I began viewing nonstandardization as a kind of abstract interpretation—abstracting
> away details in proofs while remaining sound and still allowing the extraction of
> witnesses such as bounds."*

We formalize two coupled abstract domains:

1. **Finite Candidate-Set Domain (`WitnessApprox α`)**:
   - Models the semantic target of System H's Dialectica interpretation (`(d⁺ Φ)*`), where
     standardness predicates relax unique witnesses `x` into finite candidate lists `[x₁, …, xₖ]`.
   - Proves the Galois adjunction `galois_singleton_subsumes` between singleton embedding
     `embedExact` and candidate inclusion `Subsumes`, monotonicity of soundness under widening
     (`subsumes_sound`), Kleisli composition soundness (`bindApprox_sound`, modeling `impElim`
     and `HAC`), and computable concretization (`concretizeApprox`) refining any sound
     nonstandard candidate set back to an exact certified witness.
   - Proves `boundApprox_sound_of_bounded`, explaining mathematically why `lmStLe` (`m ≤ᴴ n ⇒ᴴ st m`)
     widens an exact witness `m ≤ n` to the countdown range `[n, n - 1, …, 0]` (`r3'' 2 = [2, 1, 0]`)
     while remaining Herbrand-sound.

2. **Rational Interval Domain (`QValInterval`)**:
   - Models nonstandard halo/bound approximations `[lo, hi]` over `QVal`, with point abstraction,
     interval hull (`hullInterval`, sound join), and explicit width bounds.
-/

namespace SandersNSA
namespace Antipodes

/-! ## 1. Finite Candidate-Set Abstract Domain (`WitnessApprox`) -/

/-- Abstract nonstandard witness state: a finite list of candidate witnesses. -/
structure WitnessApprox (α : Type) : Type where
  candidates : List α
  deriving DecidableEq, Repr

namespace WitnessApprox

/-- Precision preorder: `u` is at least as precise as `v` (`v` widens / over-approximates `u`)
    when every candidate in `u` belongs to `v`. -/
def Subsumes {α : Type} (u v : WitnessApprox α) : Prop :=
  ∀ x : α, x ∈ u.candidates → x ∈ v.candidates

/-- Exact constructive point witness embedded as a singleton candidate list (`α`). -/
def embedExact {α : Type} (x : α) : WitnessApprox α :=
  ⟨[x]⟩

/-- Abstract join (`⊔`): union of candidate lists (corresponding to `orElim` in `Dialectica`). -/
def joinApprox {α : Type} (u v : WitnessApprox α) : WitnessApprox α :=
  ⟨u.candidates ++ v.candidates⟩

/-- Kleisli extension (`>>=`): apply a witness-list transformer across all candidates
    (corresponding to `collect1Tm` / `impElim` / `HAC` in `Dialectica`). -/
def bindApprox {α β : Type} (u : WitnessApprox α) (k : α → WitnessApprox β) : WitnessApprox β :=
  ⟨u.candidates.flatMap (fun x => (k x).candidates)⟩

/-- Soundness invariant: at least one candidate in `u` satisfies the concrete specification `P`. -/
def SoundApprox {α : Type} (P : α → Bool) (u : WitnessApprox α) : Prop :=
  ∃ x ∈ u.candidates, P x = true

theorem subsumes_refl {α : Type} (u : WitnessApprox α) : Subsumes u u :=
  fun _ hx => hx

theorem subsumes_trans {α : Type} {u v w : WitnessApprox α}
    (huv : Subsumes u v) (hvw : Subsumes v w) : Subsumes u w :=
  fun x hx => hvw x (huv x hx)

/-- **Galois Characterization**: embedding an exact point `x` is subsumed by `u`
    iff `x` belongs to the concretized candidate set `u.candidates`. -/
theorem galois_singleton_subsumes {α : Type} (x : α) (u : WitnessApprox α) :
    Subsumes (embedExact x) u ↔ x ∈ u.candidates := by
  constructor
  · intro h
    exact h x (.head _)
  · intro hx y hy
    cases hy with
    | head => exact hx
    | tail _ hTail => nomatch hTail

theorem embedExact_sound {α : Type} {P : α → Bool} {x : α} (hP : P x = true) :
    SoundApprox P (embedExact x) :=
  ⟨x, .head _, hP⟩

/-- **Widening Soundness**: over-approximating a witness set preserves soundness. -/
theorem subsumes_sound {α : Type} {P : α → Bool} {u v : WitnessApprox α}
    (hSub : Subsumes u v) (hSound : SoundApprox P u) : SoundApprox P v := by
  rcases hSound with ⟨x, hx, hPx⟩
  exact ⟨x, hSub x hx, hPx⟩

theorem joinApprox_subsumes_left {α : Type} (u v : WitnessApprox α) :
    Subsumes u (joinApprox u v) :=
  fun _ hx => List.mem_append_left v.candidates hx

theorem joinApprox_subsumes_right {α : Type} (u v : WitnessApprox α) :
    Subsumes v (joinApprox u v) :=
  fun _ hx => List.mem_append_right u.candidates hx

theorem joinApprox_sound_left {α : Type} {P : α → Bool} {u : WitnessApprox α}
    (v : WitnessApprox α) (h : SoundApprox P u) : SoundApprox P (joinApprox u v) :=
  subsumes_sound (joinApprox_subsumes_left u v) h

theorem joinApprox_sound_right {α : Type} {P : α → Bool} (u : WitnessApprox α)
    {v : WitnessApprox α} (h : SoundApprox P v) : SoundApprox P (joinApprox u v) :=
  subsumes_sound (joinApprox_subsumes_right u v) h

/-- **Kleisli / `HAC` Composition Soundness**: chaining sound nonstandard witness extractors
    preserves `SoundApprox`. -/
theorem bindApprox_sound {α β : Type} {P : α → Bool} {Q : β → Bool}
    {u : WitnessApprox α} {k : α → WitnessApprox β}
    (hu : SoundApprox P u)
    (hk : ∀ x : α, P x = true → SoundApprox Q (k x)) :
    SoundApprox Q (bindApprox u k) := by
  rcases hu with ⟨x, hx, hPx⟩
  rcases hk x hPx with ⟨y, hy, hQy⟩
  refine ⟨y, ?_, hQy⟩
  exact List.mem_flatMap.mpr ⟨x, hx, hy⟩

/-- Computably refine a sound nonstandard approximation `u` back to an exact certified witness
    `{ x : α // x ∈ u.candidates ∧ P x = true }`, with zero classical choice. -/
def concretizeApproxAux {α : Type} (P : α → Bool) :
    (xs : List α) → (∃ x ∈ xs, P x = true) → { x : α // x ∈ xs ∧ P x = true }
  | [], h => False.elim (by rcases h with ⟨_, hMem, _⟩; nomatch hMem)
  | x :: xs, h =>
      if hPx : P x = true then
        ⟨x, ⟨.head _, hPx⟩⟩
      else
        let sub := concretizeApproxAux P xs (by
          rcases h with ⟨z, hMem, hz⟩
          cases hMem with
          | head => exact False.elim (hPx hz)
          | tail _ hTail => exact ⟨z, hTail, hz⟩)
        ⟨sub.1, ⟨.tail _ sub.2.1, sub.2.2⟩⟩

def concretizeApprox {α : Type} (P : α → Bool) (u : WitnessApprox α)
    (h : SoundApprox P u) : { x : α // x ∈ u.candidates ∧ P x = true } :=
  concretizeApproxAux P u.candidates h

/-- Direct bridge to `SystemH.HerbrandValid`: pointwise `SoundApprox` is identical to `HerbrandValid`. -/
theorem herbrandValid_iff_pointwise_sound {α β : Type} (P : α → β → Bool) (F : α → List β) :
    SystemH.HerbrandValid P F ↔ ∀ x : α, SoundApprox (P x) ⟨F x⟩ :=
  Iff.rfl

end WitnessApprox

/-! ## 2. Countdown Upper-Bound Widening (`lmStLe` Semantic Image) -/

/-- Countdown candidate range `[B, B - 1, …, 0]`, matching the semantic action of
    System H's bounded-standardness lemma `lmStLe` (`∀ˢᵗ n, ∀ᴴ m, m ≤ᴴ n ⇒ᴴ st m`). -/
def countdownRange : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdownRange n

/-- Widening operator mapping an upper bound `B : Nat` to all natural candidates `≤ B`. -/
def boundApprox (B : Nat) : WitnessApprox Nat :=
  ⟨countdownRange B⟩

theorem mem_countdownRange_iff (B m : Nat) : m ∈ countdownRange B ↔ m ≤ B := by
  induction B with
  | zero =>
      simp only [countdownRange, List.mem_singleton]
      omega
  | succ n ih =>
      simp only [countdownRange, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | hMem
        · omega
        · have := ih.mp hMem
          omega
      · intro hle
        by_cases hEq : m = n + 1
        · exact Or.inl hEq
        · exact Or.inr (ih.mpr (by omega))

/-- **Soundness of Upper-Bound Widening**: forgetting the exact identity of a witness `m`
    and retaining only its upper bound `m ≤ B` produces a sound `WitnessApprox Nat` from which
    `concretizeApprox` recovers a certified witness for any decidable predicate `P`. -/
theorem boundApprox_sound_of_bounded {P : Nat → Bool} {B m : Nat}
    (hm : m ≤ B) (hP : P m = true) : WitnessApprox.SoundApprox P (boundApprox B) :=
  ⟨m, (mem_countdownRange_iff B m).mpr hm, hP⟩

/-! ## 3. Quantitative Rational Interval Domain (`QValInterval`) -/

/-- Closed rational interval `[lo, hi]` over `QVal` modeling nonstandard halo/bound approximations. -/
structure QValInterval : Type where
  lo : QVal
  hi : QVal
  deriving DecidableEq, Repr

namespace QValInterval

/-- Concrete membership `lo ≤ x ≤ hi`. -/
def contains (I : QValInterval) (x : QVal) : Prop :=
  QVal.le I.lo x ∧ QVal.le x I.hi

/-- Interval inclusion `I ⊆ J` (`J` widens `I`). -/
def Subinterval (I J : QValInterval) : Prop :=
  QVal.le J.lo I.lo ∧ QVal.le I.hi J.hi

/-- Exact point interval `[x, x]`. -/
def point (x : QVal) : QValInterval := ⟨x, x⟩

/-- Symmetric `ε`-halo `[x - ε, x + ε]` around `x`. -/
def halo (x eps : QVal) : QValInterval := ⟨x - eps, x + eps⟩

/-- Interval join (convex hull `[min lo₁ lo₂, max hi₁ hi₂]`). -/
def hull (I J : QValInterval) : QValInterval :=
  ⟨QVal.min I.lo J.lo, QVal.max I.hi J.hi⟩

/-- Interval width `hi - lo`. -/
def width (I : QValInterval) : QVal := I.hi - I.lo

theorem point_contains (x : QVal) : (point x).contains x :=
  ⟨QVal.le_refl x, QVal.le_refl x⟩

theorem subinterval_contains {I J : QValInterval} {x : QVal}
    (hSub : Subinterval I J) (hx : I.contains x) : J.contains x :=
  ⟨QVal.le_trans hSub.1 hx.1, QVal.le_trans hx.2 hSub.2⟩

theorem subinterval_hull_left (I J : QValInterval) : Subinterval I (hull I J) := by
  constructor
  · unfold hull QVal.min
    by_cases h : QVal.leB I.lo J.lo = true
    · simp [h, QVal.le_refl]
    · simp [h]
      unfold QVal.leB at h
      have hNot : ¬ (I.lo.num * J.lo.denInt ≤ J.lo.num * I.lo.denInt) := by
        simpa [decide_eq_true_eq] using h
      unfold QVal.le
      omega
  · unfold hull QVal.max
    by_cases h : QVal.leB I.hi J.hi = true
    · simp [h]
      simpa [QVal.leB, QVal.le, decide_eq_true_eq] using h
    · simp [h, QVal.le_refl]

theorem subinterval_hull_right (I J : QValInterval) : Subinterval J (hull I J) := by
  constructor
  · unfold hull QVal.min
    by_cases h : QVal.leB I.lo J.lo = true
    · simp [h]
      simpa [QVal.leB, QVal.le, decide_eq_true_eq] using h
    · simp [h, QVal.le_refl]
  · unfold hull QVal.max
    by_cases h : QVal.leB I.hi J.hi = true
    · simp [h, QVal.le_refl]
    · simp [h]
      unfold QVal.leB at h
      have hNot : ¬ (I.hi.num * J.hi.denInt ≤ J.hi.num * I.hi.denInt) := by
        simpa [decide_eq_true_eq] using h
      unfold QVal.le
      omega

end QValInterval

end Antipodes
end SandersNSA
