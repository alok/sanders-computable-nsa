/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.SystemH.Dialectica

/-!
# Worked Nonstandard Proof-Mining Examples in System H

Ports all examples from `Examples.agda` in Chuangjie Xu & Sam Sanders's
`nonstandard_dialectica` and extends them with `HAC` choice-functional extraction
and verified constructive witness refinement:

- `ex0`: `∀ˢᵗ n, st(n + 1)` → extracts `n ↦ [n + 1]` (`r0_spec` proved by `rfl` for all `x`).
- `lmStLe` / `ex1`: `∀ˢᵗ n, ∀ᴴ m, (m ≤ᴴ n ⇒ᴴ st m)` via external induction `IRˢᵗ`
  → extracts candidate range `n ↦ [[n, n - 1, …, 0]]` (`sr1 0 = [[0]]` by `rfl`; evaluated at
  `n = 7, 12` in `Main.lean` and `Tests/Main.lean`).
- `ex2` vs `ex2'`: two internal proofs of `∀ᴴ n, ∃ᴴ m, m ≤ᴴ n ∧ᴴ Even m` (direct vs internal
  induction `IR`), both extracting trivial unit content `[((), ())]` (`rfl`).
- `ex3`, `ex3'`, `ex3''`: three proofs of `∀ˢᵗ n, ∃ˢᵗ m, m ≤ᴴ n ∧ᴴ Even m`:
  - `ex3` (direct witness `0`) → `r3 n = [0]`.
  - `ex3'` (external induction `IRˢᵗ`) → `r3' n = [0]`.
  - `ex3''` (internal proof `ex2` + standardness bound `lmStLe`) → `r3'' 2 = [2, 1, 0]`
    (containing odd `1`!), illustrating nonstandard over-approximation.
- `ex4Hac`: applies `HAC` (`Prf.hac`) to `ex3''` to extract a choice-list functional `r4Choice`.
- `countdownRealiser_herbrandValid` & `refineCountdownEven`: proves Herbrand validity of the
  countdown candidate range `[n, n - 1, …, 0]` across all `n : Nat` and applies
  `extractExactWitness` to recover an exact certified constructive witness `{ m // m ≤ n ∧ Even m }`.
-/

namespace SandersNSA
namespace SystemH
namespace Examples

/-! ## Example 0: `∀ˢᵗ n, st(n + 1)` -/

/-- Formula `Φ₀ := ∀ˢᵗ n : Ⓝ, st(Succ n)`. -/
def phi0 {Γ : Cxt} : Fml Γ :=
  .allSt (σ := .nat) (.st (.succ Tm.v0))

/-- Formal proof of `∀ˢᵗ n, st(n + 1)` in System H. -/
def lmStSucc {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi0 :=
  .allStI (.allIntro (.impIntro (.stSucc Prf.k0)))

/-- Closed proof `Ex₀ : Prf ε Φ₀`. -/
def ex0 : Prf (Γ := .nil) .nil phi0 := lmStSucc

/-- Extracted list of realisers `t₀ : List (Nat → List Nat)`. -/
def t0 : List (Nat → List Nat) := extract ex0

theorem t0_length : t0.length = 1 := rfl

/-- Unique extracted realiser `r₀ : Nat → List Nat`. -/
def r0 : Nat → List Nat :=
  match t0 with
  | f :: _ => f
  | [] => fun _ => []

theorem r0_spec (x : Nat) : r0 x = [x + 1] := rfl

/-! ## Example 1: Boundedness Implies Standardness (`∀ˢᵗ n, ∀ᴴ m, m ≤ᴴ n ⇒ᴴ st m`) -/

/-- Inner formula `A(n) := ∀ᴴ m, m ≤ᴴ n ⇒ᴴ st m` in context `Γ ₊ Ⓝ`. -/
def stLeBody {Γ : Cxt} : Fml (.snoc Γ .nat) :=
  .allH (σ := .nat) (.imp (.le Tm.v0 Tm.v1) (.st Tm.v0))

/-- Formula `Φ₁ := ∀ˢᵗ n, ∀ᴴ m, m ≤ᴴ n ⇒ᴴ st m`. -/
def phi1 {Γ : Cxt} : Fml Γ :=
  .allSt (σ := .nat) stLeBody

/-- External-induction proof `Lmᴴ[st-≤]` that every natural bounded by a standard natural is standard. -/
def lmStLe {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi1 :=
  let base : Prf Ξ (stLeBody.substF .zero) :=
    .allIntro (.impIntro (.stEq (.stCl .zero) (.sym (.leZeroEq Prf.k0))))
  let step : Prf Ξ (.allSt (σ := .nat) (.imp stLeBody stLeBody.shiftSuccF)) :=
    .allStI (.allIntro (.impIntro (.impIntro (.allIntro (.impIntro
      (.orElim
        (.impIntro (.stEq (.stSucc Prf.k3) (.sym Prf.k0)))
        (.impIntro (.impElim (.allElim Prf.k2 Tm.v0) Prf.k0))
        (.leSuccOr Prf.k0)))))))
  .irSt base step

/-- Closed proof `Ex₁ : Prf ε Φ₁`. -/
def ex1 : Prf (Γ := .nil) .nil phi1 := lmStLe

/-- Raw extracted realiser list `t₁` (carrying unit-typed counterexample components). -/
def t1 : (dPosStar (phi1 (Γ := .nil))).denote := extract ex1

theorem t1_length : t1.length = 1 := rfl

/-- Simplified realiser `sr₁ : Nat → List (List Nat)` obtained via `simpExtract`. -/
def sr1 : Nat → List (List Nat) :=
  match simpExtract ex1 with
  | f :: _ => f
  | [] => fun _ => []

theorem sr1_at_0 : sr1 0 = [[0]] := rfl

/-! ## Example 2: Internal Proofs Carry Zero Computational Content -/

/-- Internal formula `∀ᴴ n, ∃ᴴ m, m ≤ᴴ n ∧ᴴ Even m`. -/
def phi2 {Γ : Cxt} : Fml Γ :=
  .allH (σ := .nat) (.exH (σ := .nat) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0)))

/-- Direct internal proof choosing `m = 0`. -/
def ex2 {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi2 :=
  .allIntro (.exIntro .zero (.andIntro .leZero .evenZ))

/-- Internal-induction proof using `IR` (note `Fml.Internal` discharged automatically by `rfl`!). -/
def ex2' {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi2 :=
  .ir rfl
    (.exIntro .zero (.andIntro .leZero .evenZ))
    (.allIntro (.impIntro (.exIntro .zero (.andIntro .leZero .evenZ))))

theorem extract_ex2_eq : extract (ex2 (Γ := .nil) (Ξ := .nil)) = [((), ())] := rfl

theorem extract_ex2'_eq : extract (ex2' (Γ := .nil) (Ξ := .nil)) = [((), ())] := rfl

/-! ## Example 3: Comparing Direct External Proofs vs. Nonstandard Proof via `lmStLe` -/

/-- External `Δ_ns` formula `Φ₃ := ∀ˢᵗ n, ∃ˢᵗ m, m ≤ᴴ n ∧ᴴ Even m`. -/
def phi3 {Γ : Cxt} : Fml Γ :=
  .allSt (σ := .nat) (.exSt (σ := .nat) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0)))

theorem phi3_isDeltaNS : (phi3 (Γ := .nil)).isDeltaNS = true := rfl

/-- Proof 3a (`Ex₃`): direct external witness `m = 0`. -/
def ex3 {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi3 :=
  .allStI (.allIntro (.impIntro
    (.exStI (.exIntro .zero (.andIntro (.stCl .zero) (.andIntro .leZero .evenZ))))))

/-- Proof 3b (`Ex₃'`): external induction `IRˢᵗ` choosing `m = 0` at base and step. -/
def ex3' {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi3 :=
  .irSt
    (.exStI (.exIntro .zero (.andIntro (.stCl .zero) (.andIntro .leZero .evenZ))))
    (.allStI (.allIntro (.impIntro (.impIntro
      (.exStI (.exIntro .zero (.andIntro (.stCl .zero) (.andIntro .leZero .evenZ))))))))

/-- Proof 3c (`Ex₃''`): nonstandard proof combining internal existence `ex2` with `lmStLe`. -/
def ex3'' {Γ : Cxt} {Ξ : Asmpt Γ} : Prf Ξ phi3 :=
  let Ξ₁ := wknAsmpt (σ := .nat) Ξ
  let Ξ₂ := wknAsmpt (σ := .nat) Ξ₁
  let Ξ₀ : Asmpt (.snoc (.snoc Γ .nat) .nat) :=
    .snoc (.snoc Ξ₂ (.st Tm.v1)) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0))
  let pStLe : Prf Ξ₀ phi1 := lmStLe
  let pStep1 := Prf.allElim (Prf.allStE pStLe) Tm.v1
  let pStep2 := Prf.impElim pStep1 Prf.k1
  let pStep3 := Prf.allElim pStep2 Tm.v0
  let claim0 : Prf Ξ₀ (.st Tm.v0) := Prf.impElim pStep3 (Prf.andElim1 Prf.k0)
  let claim1 :
      Prf (.snoc Ξ₁ (.st Tm.v0))
        (.allH (σ := .nat)
          (.imp (.and (.le Tm.v0 Tm.v1) (.even Tm.v0))
                (.exSt (σ := .nat) (.and (.le Tm.v0 Tm.v2) (.even Tm.v0))))) :=
    .allIntro (.impIntro (.exStI (.exIntro Tm.v0 (.andIntro claim0 Prf.k0))))
  let claim2 :
      Prf (.snoc Ξ₁ (.st Tm.v0))
        (.imp (.exH (σ := .nat) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0)))
              (.exSt (σ := .nat) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0)))) :=
    .exElim claim1
  let claim3 :
      Prf (.snoc Ξ₁ (.st Tm.v0))
        (.exH (σ := .nat) (.and (.le Tm.v0 Tm.v1) (.even Tm.v0))) :=
    .allElim ex2 Tm.v0
  .allStI (.allIntro (.impIntro (.impElim claim2 claim3)))

/-- Simplified realisers `r₃, r₃', r₃'' : Nat → List Nat` extracted from the three proofs.
    Executed and regression-tested at `n = 0, 2, 5, 7, 12` in `Main.lean` and `Tests/Main.lean`. -/
def r3 : Nat → List Nat :=
  match simpExtract (ex3 (Γ := .nil) (Ξ := .nil)) with
  | f :: _ => f
  | [] => fun _ => []

def r3' : Nat → List Nat :=
  match simpExtract (ex3' (Γ := .nil) (Ξ := .nil)) with
  | f :: _ => f
  | [] => fun _ => []

def r3'' : Nat → List Nat :=
  match simpExtract (ex3'' (Γ := .nil) (Ξ := .nil)) with
  | f :: _ => f
  | [] => fun _ => []

/-! ## Example 4: Choice-Functional Extraction via `HAC` & Constructive Refinement -/

/-- Apply System H's Herbrandized Axiom of Choice (`HAC`) to `ex3''` to obtain a finite-set
    choice functional `∃ˢᵗ F : Ⓝ ⇾ Ⓝ*, ∀ˢᵗ n, ∃ᴴ m ∈ F(n), m ≤ᴴ n ∧ᴴ Even m`. -/
def ex4Hac :
    Prf (Γ := .nil) .nil
      (@Fml.exSt .nil (.arr .nat (.list .nat))
        (@Fml.allSt (.snoc .nil (.arr .nat (.list .nat))) .nat
          (@Fml.exH (.snoc (.snoc .nil (.arr .nat (.list .nat))) .nat) .nat
            (.and (.mem Tm.v0 (Tm.v2 ⬝ Tm.v1))
              ((@Fml.and (.snoc (.snoc .nil .nat) .nat) (.le Tm.v0 Tm.v1) (.even Tm.v0)).wkn2F))))) :=
  .impElim .hac (ex3'' (Γ := .nil) (Ξ := .nil))

/-- Extracted choice functional from `ex4Hac`. -/
def r4Choice : Nat → List Nat :=
  match simpExtract ex4Hac with
  | f :: _ => f
  | [] => fun _ => []

/-- Closed-form countdown candidate realiser `[n, n - 1, …, 0]` matching `r₃''` (`r3'' 2 = [2, 1, 0]`). -/
def countdownCandidates : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdownCandidates n

/-- Decidable standard matrix `P(n, m) := (m ≤ n ∧ m % 2 = 0)` for `Φ₃`. -/
def leAndEvenPred (n m : Nat) : Bool :=
  decide (m ≤ n ∧ m % 2 = 0)

theorem zero_mem_countdownCandidates : (n : Nat) → 0 ∈ countdownCandidates n
  | 0 => .head _
  | _ + 1 => .tail _ (zero_mem_countdownCandidates _)

/-- `countdownCandidates` is Herbrand-valid for `leAndEvenPred` across all `n : Nat`. -/
theorem countdownCandidates_herbrandValid : HerbrandValid leAndEvenPred countdownCandidates := by
  intro n
  refine ⟨0, zero_mem_countdownCandidates n, ?_⟩
  simp [leAndEvenPred]

/-- Constructive refinement collapses the over-approximating candidate list `[n, n - 1, …, 0]`
    back to an exact certified even witness `m ≤ n` (selecting the largest even `m ≤ n`!). -/
def refineCountdownEven (n : Nat) : { m : Nat // leAndEvenPred n m = true } :=
  extractExactWitness leAndEvenPred countdownCandidates countdownCandidates_herbrandValid n

theorem refineCountdownEven_at_2 : (refineCountdownEven 2).val = 2 := rfl

theorem refineCountdownEven_at_5 : (refineCountdownEven 5).val = 4 := rfl

end Examples
end SystemH
end SandersNSA
