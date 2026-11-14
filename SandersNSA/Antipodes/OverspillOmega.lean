/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.ConstructiveAnalysis

/-!
# Effective Hyper-Sequences, Computable Overspill/Underspill & Ω-Invariance

Implements the constructive core of Sam Sanders's *"Reuniting the antipodes"* and
*"To be or not to be constructive"* alongside Alok Singh's note on the practical
computational meaning of overflow (overspill) and underflow (underspill):

1. **Effective Hyper-Sequences (`HyperSeq α := Nat → α`)**:
   - Standard embedding `starConst`, canonical unbounded sequence `omegaNat`, canonical
     infinitesimal `invOmega` (`n ↦ 1 / (n + 1)`), infinite `Reindexing` maps, and
     quantitative `InfinitelyClose` (`x ≈ y`) carrying explicit convergence moduli.
2. **Computable Overspill & Underspill**:
   - **Overspill (`overspillPrecisionIndex`)**: Given an internal decidable relation
     `approx k N` that holds at every standard precision `k` for sufficiently large `N`,
     computably extracts the maximal precision schedule `Ω(N)` achieved at stage `N`,
     proving both internal validity (`approx (Ω N) N = true`) and growth past every
     standard bound `K`.
   - **Underspill (`underspillMinThreshold`)**: Given an internal decidable property `P`
     holding at a large horizon `N` (`P N = true`), computably extracts the **exact minimal
     standard threshold** `m ≤ N` with `P m = true` and `∀ j < m, P j = false`.
3. **Sam Sanders's Ω-Invariance Theorem**:
   - Formalizes `OmegaInvariantSeq` (invariance of `s(M)` across all infinite reindexings `M`)
     and constructs explicit computable equivalence maps `omegaInvariant_to_cauchy` and
     `cauchy_to_omegaInvariant`, plus `OmegaInvariantGridFn → UniformContOn`.
-/

namespace SandersNSA
namespace Antipodes

/-! ## 1. Effective Hyper-Sequences & Quantitative Infinitesimals -/

/-- Effective sequential presentation of a nonstandard object `*α` without ultrafilters. -/
abbrev HyperSeq (α : Type) : Type := Nat → α

/-- Standard copy `*x` of a standard value `x : α`. -/
@[inline] def starConst {α : Type} (x : α) : HyperSeq α := fun _ => x

/-- Canonical unbounded hypernatural `Ω = (0, 1, 2, …)`. -/
@[inline] def omegaNat : HyperSeq Nat := fun n => n

/-- Canonical positive infinitesimal `ε = (1, 1/2, 1/3, …)`. -/
@[inline] def invOmega : HyperSeq QVal := fun n => QVal.unitFrac n

/-- Lift a unary standard operation internally to `HyperSeq`. -/
@[inline] def liftSeq1 {α β : Type} (f : α → β) (x : HyperSeq α) : HyperSeq β :=
  fun n => f (x n)

/-- Lift a binary standard operation internally to `HyperSeq`. -/
@[inline] def liftSeq2 {α β γ : Type} (f : α → β → γ) (x : HyperSeq α) (y : HyperSeq β) :
    HyperSeq γ :=
  fun n => f (x n) (y n)

/-- Co-final / unbounded hypernatural index map (`M : *ℕ \ ℕ` represented constructively
    as a dominating sequence `∀ n, n ≤ idx n`). -/
structure Reindexing : Type where
  idx : Nat → Nat
  dominates : ∀ n : Nat, n ≤ idx n

/-- Identity unbounded index `Ω(n) = n`. -/
def Reindexing.id : Reindexing where
  idx n := n
  dominates _ := Nat.le_refl _

/-- Shifted unbounded index `Ω + c`. -/
def Reindexing.shift (c : Nat) : Reindexing where
  idx n := n + c
  dominates _ := by omega

/-- Quantitative infinite closeness `x ≈ y` equipped with an explicit modulus. -/
structure InfinitelyClose (x y : HyperSeq QVal) : Type where
  modulus : Modulus
  spec : ∀ (k n : Nat),
    modulus k ≤ n →
    QVal.le (QVal.dist (x n) (y n)) (QVal.unitFrac k)

/-- Quantitative infinitesimal `x ≈ 0`. -/
abbrev Infinitesimal (x : HyperSeq QVal) : Type :=
  InfinitelyClose x (starConst 0)

/-- `invOmega` (`1 / (n + 1)`) is canonically infinitesimal with identity modulus `ω(k) = k`. -/
def invOmega_infinitesimal : Infinitesimal invOmega where
  modulus k := k
  spec k n hkn := by
    have hDist : QVal.eqv (QVal.dist (QVal.unitFrac n) 0) (QVal.unitFrac n) := by
      change ((QVal.unitFrac n - 0).num.natAbs : Int) * ((n + 1 : Nat) : Int) =
        1 * (QVal.dist (QVal.unitFrac n) 0).denInt
      rw [QVal.sub_num, QVal.dist_denInt]
      change ((1 * 1 - 0 * ((n + 1 : Nat) : Int)).natAbs : Int) * ((n + 1 : Nat) : Int) =
        1 * (((n + 1 : Nat) : Int) * 1)
      simp
    exact QVal.le_of_eqv_left hDist (QVal.unitFrac_anti hkn)

/-- Reflexivity of `InfinitelyClose` with constant zero modulus. -/
def InfinitelyClose.refl (x : HyperSeq QVal) : InfinitelyClose x x where
  modulus _ := 0
  spec k n _ := by
    have hPos : QVal.le 0 (QVal.unitFrac k) := by
      change (0 : Int) * ((k + 1 : Nat) : Int) ≤ 1 * 1
      omega
    exact QVal.le_of_eqv_left (QVal.dist_self (x n)) hPos

/-! ## 2. Computable Overspill & Underspill Extractors -/

/-- Scan precisions `0, 1, …, H` at stage `N` to find the highest contiguous precision prefix
    where `approx k N = true` holds for all `0 ≤ k ≤ m`. -/
def maxContiguousPrecisionAux (approx : Nat → Nat → Bool) (N : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if approx (acc + 1) N then
        maxContiguousPrecisionAux approx N fuel (acc + 1)
      else
        acc

/-- **Computable Overspill Schedule (`overspillPrecisionIndex`)**:
    Given an internal decidable predicate `approx k N` with `approx 0 N = true`, returns the
    largest precision index `m ≤ H` such that `approx j N = true` for every `j ≤ m`. -/
def overspillPrecisionIndex (approx : Nat → Nat → Bool) (H N : Nat) : Nat :=
  if approx 0 N then maxContiguousPrecisionAux approx N H 0 else 0

theorem maxContiguousPrecisionAux_ge (approx : Nat → Nat → Bool) (N : Nat) :
    ∀ (fuel acc : Nat), acc ≤ maxContiguousPrecisionAux approx N fuel acc
  | 0, _ => Nat.le_refl _
  | fuel + 1, acc => by
      unfold maxContiguousPrecisionAux
      split
      · have h := maxContiguousPrecisionAux_ge approx N fuel (acc + 1)
        omega
      · exact Nat.le_refl _

theorem maxContiguousPrecisionAux_valid (approx : Nat → Nat → Bool) (N : Nat) :
    ∀ (fuel acc : Nat), approx acc N = true →
      approx (maxContiguousPrecisionAux approx N fuel acc) N = true
  | 0, _, hAcc => hAcc
  | fuel + 1, acc, hAcc => by
      unfold maxContiguousPrecisionAux
      split
      · next hNext => exact maxContiguousPrecisionAux_valid approx N fuel (acc + 1) hNext
      · exact hAcc

theorem maxContiguousPrecisionAux_complete (approx : Nat → Nat → Bool) (N : Nat) :
    ∀ (fuel acc K : Nat),
      K ≤ acc + fuel →
      (∀ k : Nat, k ≤ K → approx k N = true) →
      K ≤ maxContiguousPrecisionAux approx N fuel acc
  | 0, acc, K, hBound, _ => by
      unfold maxContiguousPrecisionAux
      omega
  | fuel + 1, acc, K, hBound, hAll => by
      unfold maxContiguousPrecisionAux
      by_cases hK : K ≤ acc
      · split
        · have hGe := maxContiguousPrecisionAux_ge approx N fuel (acc + 1)
          omega
        · exact hK
      · have hNextLe : acc + 1 ≤ K := by omega
        have hNextTrue : approx (acc + 1) N = true := hAll (acc + 1) hNextLe
        simp only [hNextTrue, ↓reduceIte]
        exact maxContiguousPrecisionAux_complete approx N fuel (acc + 1) K (by omega) hAll

/-- **Overspill Validity Theorem**: whenever `approx 0 N = true`, the overspill index
    `Ω(N) := overspillPrecisionIndex approx H N` satisfies `approx (Ω N) N = true`. -/
theorem overspillPrecisionIndex_valid {approx : Nat → Nat → Bool} {H N : Nat}
    (h0 : approx 0 N = true) :
    approx (overspillPrecisionIndex approx H N) N = true := by
  unfold overspillPrecisionIndex
  simp only [h0, ↓reduceIte]
  exact maxContiguousPrecisionAux_valid approx N H 0 h0

/-- Maximum of a `Nat → Nat` witness modulus over `0, …, K`. -/
def maxModulusUpTo (w : Nat → Nat) : Nat → Nat
  | 0 => w 0
  | K + 1 => Nat.max (maxModulusUpTo w K) (w (K + 1))

theorem le_maxModulusUpTo (w : Nat → Nat) : ∀ {K k : Nat}, k ≤ K → w k ≤ maxModulusUpTo w K
  | 0, k, hk => by
      have hk0 : k = 0 := by omega
      subst hk0
      exact Nat.le_refl _
  | K + 1, k, hk => by
      by_cases hEq : k = K + 1
      · subst hEq
        unfold maxModulusUpTo
        exact Nat.le_max_right _ _
      · have hkLe : k ≤ K := by omega
        have ih := le_maxModulusUpTo w hkLe
        unfold maxModulusUpTo
        exact Nat.le_trans ih (Nat.le_max_left _ _)

/-- **Quantitative Overspill Growth Theorem**:
    If for every standard precision `k`, `approx k N = true` holds for all `N ≥ w(k)`,
    then for every standard target `K ≤ H` and every `N ≥ max_{k ≤ K} w(k)`,
    the overspill precision schedule exceeds `K`: `K ≤ overspillPrecisionIndex approx H N`. -/
theorem overspillPrecisionIndex_diverges {approx : Nat → Nat → Bool}
    (w : Nat → Nat)
    (hw : ∀ (k N : Nat), w k ≤ N → approx k N = true)
    {K H N : Nat} (hKH : K ≤ H) (hN : maxModulusUpTo w K ≤ N) :
    K ≤ overspillPrecisionIndex approx H N := by
  have hAll : ∀ k : Nat, k ≤ K → approx k N = true := by
    intro k hk
    exact hw k N (Nat.le_trans (le_maxModulusUpTo w hk) hN)
  have h0 : approx 0 N = true := hAll 0 (Nat.zero_le K)
  unfold overspillPrecisionIndex
  simp only [h0, ↓reduceIte]
  exact maxContiguousPrecisionAux_complete approx N H 0 K (by omega) hAll

/-- Auxiliary upward search for the least `m ≤ N` satisfying `P m = true`. -/
def findLeastTrueUpTo (P : Nat → Bool) (N : Nat) : Nat → Nat
  | 0 => N
  | fuel + 1 =>
      if P (N - (fuel + 1)) then N - (fuel + 1) else findLeastTrueUpTo P N fuel

/-- **Computable Underspill Extractor (`underspillMinThreshold`)**:
    Given an internal decidable property `P : Nat → Bool` witnessed at some large
    (e.g., hyperfinite) horizon `N`, computably extracts the **minimal** standard
    threshold `m ≤ N` with `P m = true`. -/
def underspillMinThreshold (P : Nat → Bool) (N : Nat) : Nat :=
  findLeastTrueUpTo P N N

theorem findLeastTrueUpTo_le (P : Nat → Bool) (N : Nat) :
    ∀ fuel : Nat, findLeastTrueUpTo P N fuel ≤ N
  | 0 => Nat.le_refl N
  | fuel + 1 => by
      unfold findLeastTrueUpTo
      split
      · omega
      · exact findLeastTrueUpTo_le P N fuel

theorem findLeastTrueUpTo_true (P : Nat → Bool) (N : Nat) (hN : P N = true) :
    ∀ fuel : Nat, P (findLeastTrueUpTo P N fuel) = true
  | 0 => hN
  | fuel + 1 => by
      unfold findLeastTrueUpTo
      split
      · next h => exact h
      · exact findLeastTrueUpTo_true P N hN fuel

theorem findLeastTrueUpTo_minimal (P : Nat → Bool) (N : Nat) :
    ∀ (fuel j : Nat), fuel ≤ N → N - fuel ≤ j → j < findLeastTrueUpTo P N fuel → P j = false
  | 0, j, _, hLo, hHi => by
      unfold findLeastTrueUpTo at hHi
      omega
  | fuel + 1, j, hFuel, hLo, hHi => by
      unfold findLeastTrueUpTo at hHi
      split at hHi
      · omega
      · next hIdxFalse =>
          by_cases hEq : j = N - (fuel + 1)
          · subst hEq
            cases hBool : P (N - (fuel + 1))
            · rfl
            · exact False.elim (hIdxFalse hBool)
          · exact findLeastTrueUpTo_minimal P N fuel j (by omega) (by omega) hHi

/-- **Underspill Correctness Theorem**: If `P N = true` at horizon `N`, then
    `m := underspillMinThreshold P N` satisfies `m ≤ N`, `P m = true`, and
    `∀ j < m, P j = false` (minimality). -/
theorem underspillMinThreshold_spec {P : Nat → Bool} {N : Nat} (hN : P N = true) :
    underspillMinThreshold P N ≤ N ∧
    P (underspillMinThreshold P N) = true ∧
    ∀ j : Nat, j < underspillMinThreshold P N → P j = false := by
  refine ⟨findLeastTrueUpTo_le P N N, findLeastTrueUpTo_true P N hN N, ?_⟩
  intro j hj
  exact findLeastTrueUpTo_minimal P N N j (Nat.le_refl N) (by omega) hj

/-! ## 3. Sam Sanders's Ω-Invariance Principle -/

/-- Constructive presentation of **Ω-Invariance** for a hyperfinite sequence `s : HyperSeq QVal`:
    across every pair of unbounded reindexings `M₁, M₂ : Reindexing`, `s ∘ M₁` and `s ∘ M₂`
    are `InfinitelyClose` with a uniform comparison modulus `invarianceMod`. -/
structure OmegaInvariantSeq (s : HyperSeq QVal) : Type where
  invarianceMod : Modulus
  invariant : ∀ (M₁ M₂ : Reindexing) (k n : Nat),
    invarianceMod k ≤ n →
    QVal.le (QVal.dist (s (M₁.idx n)) (s (M₂.idx n))) (QVal.unitFrac k)

/-- **Sanders's Ω-Invariance Theorem (Seq → Cauchy)**:
    Every Ω-invariant hyper-sequence `s` computably yields a Bishop `CauchySeqWithModulus`
    by instantiating `M₁, M₂` at shifted unbounded reindexings! -/
def omegaInvariant_to_cauchy {s : HyperSeq QVal}
    (hOmega : OmegaInvariantSeq s) : CauchySeqWithModulus s where
  modulus := hOmega.invarianceMod
  spec k m n hm hn := by
    -- Construct unbounded reindexings `M₁(t) = max t m` and `M₂(t) = max t n`
    let M₁ : Reindexing :=
      { idx := fun t => if t ≤ m then m else t
        dominates := fun t => by split <;> omega }
    let M₂ : Reindexing :=
      { idx := fun t => if t ≤ n then n else t
        dominates := fun t => by split <;> omega }
    -- Evaluate both at `t₀ = invarianceMod k`, wait: if `t₀ ≤ m` and `t₀ ≤ n`,
    -- `M₁.idx t₀ = m` and `M₂.idx t₀ = n`!
    let t₀ := hOmega.invarianceMod k
    have hStep := hOmega.invariant M₁ M₂ k t₀ (Nat.le_refl t₀)
    have hM1 : M₁.idx t₀ = m := by dsimp [M₁, t₀]; split <;> omega
    have hM2 : M₂.idx t₀ = n := by dsimp [M₂, t₀]; split <;> omega
    rw [hM1, hM2] at hStep
    exact hStep

/-- **Converse Ω-Invariance Theorem (Cauchy → Ω-Invariant)**:
    Every `CauchySeqWithModulus` is uniformly Ω-invariant across all unbounded reindexings `M₁, M₂`. -/
def cauchy_to_omegaInvariant {s : HyperSeq QVal}
    (hCauchy : CauchySeqWithModulus s) : OmegaInvariantSeq s where
  invarianceMod := hCauchy.modulus
  invariant M₁ M₂ k n hn := by
    have hm1 : hCauchy.modulus k ≤ M₁.idx n := Nat.le_trans hn (M₁.dominates n)
    have hm2 : hCauchy.modulus k ≤ M₂.idx n := Nat.le_trans hn (M₂.dominates n)
    exact hCauchy.spec k (M₁.idx n) (M₂.idx n) hm1 hm2

/-- **Ω-Invariance for Functions (`OmegaInvariantFn`)**:
    Whenever two sequences `x, y` in `[a, b]` are `1 / (δ(k) + 1)`-close from stage `N` onward,
    `f(x(M n))` and `f(y(M n))` agree within `1 / (k + 1)` along every unbounded reindexing `M`. -/
structure OmegaInvariantFn (f : QVal → QVal) (a b : QVal) : Type where
  scaleMod : Modulus
  spec : ∀ (M : Reindexing) (x y : HyperSeq QVal) (k n : Nat),
    QVal.le a (x (M.idx n)) → QVal.le (x (M.idx n)) b →
    QVal.le a (y (M.idx n)) → QVal.le (y (M.idx n)) b →
    QVal.le (QVal.dist (x (M.idx n)) (y (M.idx n))) (QVal.unitFrac (scaleMod k)) →
    QVal.le (QVal.dist (f (x (M.idx n))) (f (y (M.idx n)))) (QVal.unitFrac k)

/-- Every `OmegaInvariantFn` computably yields Bishop `UniformContOn f a b`, and vice versa. -/
def omegaInvariantFn_to_uniformCont {f : QVal → QVal} {a b : QVal}
    (h : OmegaInvariantFn f a b) : UniformContOn f a b where
  modulus := h.scaleMod
  spec k x y hax hxb hay hyb hdist :=
    h.spec Reindexing.id (starConst x) (starConst y) k 0 hax hxb hay hyb hdist

def uniformCont_to_omegaInvariantFn {f : QVal → QVal} {a b : QVal}
    (h : UniformContOn f a b) : OmegaInvariantFn f a b where
  scaleMod := h.modulus
  spec M x y k n hax hxb hay hyb hdist :=
    h.spec k (x (M.idx n)) (y (M.idx n)) hax hxb hay hyb hdist

end Antipodes
end SandersNSA
