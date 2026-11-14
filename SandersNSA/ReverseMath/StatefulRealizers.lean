/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.AbstractInterpretation

/-!
# Imperative / Stateful Nonstandard Realizers (`StatefulRealizers`, `arXiv:2210.05346`)

From Alok Singh's email correspondence with Sam Sanders on Bruno Dinis & Étienne Miquey,
*"A stateful calculus of nonstandard realizers"* (`arXiv:2210.05346`):
instead of threading exponentially growing Herbrand candidate lists purely functionally through
System $\mathcal{T}$ higher-order terms, nonstandard realizers can execute **imperatively** by
mutating a monotonically growing **witness store** (`WitnessApprox τ`), accumulating candidate
witnesses across `do`-notation blocks and extracting an exact certified witness at the end.

This module provides:
1. `StatefulRealizer σ α`: state-passing realizer monad with verified `Monad` and `LawfulMonad`
   instances enabling native Lean 4 `do`-notation.
2. `WitnessM τ α := StatefulRealizer (WitnessApprox τ) α`: imperative witness-store calculus
   with `emitWitness`, `emitBatch`, and `emitCountdown`.
3. `MonotoneStore`: store-monotonicity invariant (`Subsumes s (m.run s).2`) closed under `pure`,
   `>>=` (`bind_monotone`), `emitWitness`, `emitBatch`, and `emitCountdown`.
4. **Stateful Realizer Soundness Theorem (`monotone_preserves_sound`, `seq_after_valid_emit_sound`,
   `runAndConcretize`)**: once an imperative `do`-step emits a valid witness (or bound widening),
   every subsequent store-monotone computation preserves `WitnessApprox.SoundApprox`, allowing
   exact witness extraction via `concretizeApprox`.
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Stateful Realizer Monad & `LawfulMonad` Proof -/

/-- Imperative realizer computation mutating store state `σ` and producing value `α`. -/
structure StatefulRealizer (σ α : Type) : Type where
  run : σ → α × σ

namespace StatefulRealizer

instance (σ : Type) : Monad (StatefulRealizer σ) where
  pure a := ⟨fun s => (a, s)⟩
  bind m k := ⟨fun s =>
    let (a, s') := m.run s
    (k a).run s'⟩
  map f m := ⟨fun s =>
    let (a, s') := m.run s
    (f a, s')⟩
  seq mf mx := ⟨fun s =>
    let (f, s') := mf.run s
    let (x, s'') := (mx ()).run s'
    (f x, s'')⟩

instance (σ : Type) : LawfulMonad (StatefulRealizer σ) where
  map_const := rfl
  id_map x := by cases x; rfl
  seqLeft_eq x y := by cases x; cases y; rfl
  seqRight_eq x y := by cases x; cases y; rfl
  pure_seq g x := by cases x; rfl
  bind_pure_comp f x := by cases x; rfl
  bind_map f x := by cases f; cases x; rfl
  pure_bind x f := rfl
  bind_assoc x f g := by cases x; rfl

/-- Read the current store state. -/
def getStore {σ : Type} : StatefulRealizer σ σ :=
  ⟨fun s => (s, s)⟩

/-- Overwrite the store state. -/
def putStore {σ : Type} (s' : σ) : StatefulRealizer σ Unit :=
  ⟨fun _ => ((), s')⟩

/-- Modify the store state in place. -/
def modifyStore {σ : Type} (f : σ → σ) : StatefulRealizer σ Unit :=
  ⟨fun s => ((), f s)⟩

end StatefulRealizer

/-! ## 2. Witness-Store Calculus (`WitnessM`) & Monotonicity Invariant -/

/-- Imperative realizer mutating a finite nonstandard candidate store `WitnessApprox τ`. -/
abbrev WitnessM (τ α : Type) : Type :=
  StatefulRealizer (WitnessApprox τ) α

/-- Append a single candidate witness `w : τ` to the imperative witness store. -/
def emitWitness {τ : Type} (w : τ) : WitnessM τ Unit :=
  StatefulRealizer.modifyStore (fun s => WitnessApprox.joinApprox s (WitnessApprox.embedExact w))

/-- Widen the imperative witness store with a batch `u : WitnessApprox τ` of candidates. -/
def emitBatch {τ : Type} (u : WitnessApprox τ) : WitnessM τ Unit :=
  StatefulRealizer.modifyStore (fun s => WitnessApprox.joinApprox s u)

/-- Imperative `lmStLe` bound widening: record all `0 .. B` into a `Nat` witness store. -/
def emitCountdown (B : Nat) : WitnessM Nat Unit :=
  emitBatch (boundApprox B)

/-- Execute a `WitnessM τ α` computation starting from an initially empty witness store `⟨[]⟩`. -/
def execFromEmpty {τ α : Type} (m : WitnessM τ α) : α × WitnessApprox τ :=
  m.run ⟨[]⟩

/-- Store-monotonicity invariant: running `m` never discards previously recorded candidates. -/
def MonotoneStore {τ α : Type} (m : WitnessM τ α) : Prop :=
  ∀ s : WitnessApprox τ, WitnessApprox.Subsumes s (m.run s).2

theorem pure_monotone {τ α : Type} (a : α) :
    MonotoneStore (pure a : WitnessM τ α) :=
  fun s => WitnessApprox.subsumes_refl s

theorem getStore_monotone {τ : Type} :
    MonotoneStore (StatefulRealizer.getStore : WitnessM τ (WitnessApprox τ)) :=
  fun s => WitnessApprox.subsumes_refl s

theorem bind_monotone {τ α β : Type} {m : WitnessM τ α} {k : α → WitnessM τ β}
    (hm : MonotoneStore m) (hk : ∀ a : α, MonotoneStore (k a)) :
    MonotoneStore (m >>= k) := by
  intro s
  have h1 := hm s
  have h2 := hk (m.run s).1 (m.run s).2
  exact WitnessApprox.subsumes_trans h1 h2

theorem emitBatch_monotone {τ : Type} (u : WitnessApprox τ) :
    MonotoneStore (emitBatch u) :=
  fun s => WitnessApprox.joinApprox_subsumes_left s u

theorem emitWitness_monotone {τ : Type} (w : τ) :
    MonotoneStore (emitWitness w) :=
  emitBatch_monotone (WitnessApprox.embedExact w)

theorem emitCountdown_monotone (B : Nat) :
    MonotoneStore (emitCountdown B) :=
  emitBatch_monotone (boundApprox B)

/-! ## 3. Stateful Soundness & Certified Witness Extraction -/

/-- Store-monotone computations preserve `WitnessApprox.SoundApprox P`. -/
theorem monotone_preserves_sound {τ α : Type} {P : τ → Bool}
    {m : WitnessM τ α} (hm : MonotoneStore m)
    {s : WitnessApprox τ} (hSound : WitnessApprox.SoundApprox P s) :
    WitnessApprox.SoundApprox P (m.run s).2 :=
  WitnessApprox.subsumes_sound (hm s) hSound

/-- Emitting a witness `w` satisfying `P w = true` establishes `SoundApprox P` from any initial store. -/
theorem emitWitness_sound {τ : Type} {P : τ → Bool} {w : τ} (hw : P w = true)
    (s : WitnessApprox τ) :
    WitnessApprox.SoundApprox P ((emitWitness w).run s).2 :=
  WitnessApprox.joinApprox_sound_right s (WitnessApprox.embedExact_sound hw)

/-- Emitting a countdown bound `B` when some `w ≤ B` satisfies `P w = true` establishes `SoundApprox P`. -/
theorem emitCountdown_sound {P : Nat → Bool} {w B : Nat}
    (hle : w ≤ B) (hw : P w = true) (s : WitnessApprox Nat) :
    WitnessApprox.SoundApprox P ((emitCountdown B).run s).2 :=
  WitnessApprox.joinApprox_sound_right s (boundApprox_sound_of_bounded hle hw)

/-- **Imperative `do`-Sequence Soundness Theorem**:
    If `step₁` establishes `SoundApprox P` from `s` and `step₂` is store-monotone, then
    `step₁ >>= step₂` finishes in a `SoundApprox P` store! -/
theorem seq_sound_of_monotone {τ α β : Type} {P : τ → Bool}
    {step₁ : WitnessM τ α} {step₂ : α → WitnessM τ β}
    {s : WitnessApprox τ}
    (h1 : WitnessApprox.SoundApprox P (step₁.run s).2)
    (h2 : ∀ a : α, MonotoneStore (step₂ a)) :
    WitnessApprox.SoundApprox P ((step₁ >>= step₂).run s).2 :=
  monotone_preserves_sound (h2 (step₁.run s).1) h1

/-- Run an imperative `WitnessM τ α` program from empty store and refine its accumulated store
    into an exact certified witness `{ w : τ // w ∈ store ∧ P w = true }`! -/
def runAndConcretize {τ α : Type} (P : τ → Bool) (m : WitnessM τ α)
    (hSound : WitnessApprox.SoundApprox P (execFromEmpty m).2) :
    α × { w : τ // w ∈ (execFromEmpty m).2.candidates ∧ P w = true } :=
  let res := execFromEmpty m
  (res.1, WitnessApprox.concretizeApprox P res.2 hSound)

/-! ## 4. Live Imperative `do`-Notation Demo -/

/-- Imperative `do`-block realizer searching for a nontrivial solution to `n² - 5n + 6 == 0`
    by combining speculative guesses (`emitWitness 0`, `emitWitness 99`) with nonstandard
    bounded countdown widening (`emitCountdown 4`) and inspecting store size mid-flight! -/
def quadraticSearchRealizer : WitnessM Nat Nat := do
  emitWitness 0
  emitCountdown 4
  emitWitness 99
  let st ← StatefulRealizer.getStore
  pure st.candidates.length

def isQuadraticRoot (n : Nat) : Bool :=
  decide (n * n + 6 = 5 * n)

theorem quadraticSearchRealizer_sound :
    WitnessApprox.SoundApprox isQuadraticRoot (execFromEmpty quadraticSearchRealizer).2 := by
  unfold execFromEmpty quadraticSearchRealizer
  change WitnessApprox.SoundApprox isQuadraticRoot
    ((emitCountdown 4 >>= fun _ =>
      emitWitness 99 >>= fun _ =>
      StatefulRealizer.getStore >>= fun st =>
      pure st.candidates.length).run ((emitWitness 0).run ⟨[]⟩).2).2
  refine seq_sound_of_monotone
    (emitCountdown_sound (w := 2) (by omega) (by decide) ((emitWitness 0).run ⟨[]⟩).2) ?_
  intro _
  exact bind_monotone (emitWitness_monotone 99) (fun _ =>
    bind_monotone getStore_monotone (fun st => pure_monotone st.candidates.length))

/-- Extracted store size (`7` candidates: `[0, 4, 3, 2, 1, 0, 99]`) and certified root (`3` or `2`). -/
def extractedQuadraticRoot :
    Nat × { w : Nat // w ∈ (execFromEmpty quadraticSearchRealizer).2.candidates ∧ isQuadraticRoot w = true } :=
  runAndConcretize isQuadraticRoot quadraticSearchRealizer quadraticSearchRealizer_sound

end ReverseMath
end SandersNSA
