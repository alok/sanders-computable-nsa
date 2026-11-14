/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.IVTAndDini

/-!
# Cousin's Lemma (`HBU`), Pincherle's Theorem & Gauge Partitions (`CousinPincherle`)

Formalizes the Higher-Order Reverse Mathematics (`HORM`) gauge-partition cluster discussed
in Alok Singh & Sam Sanders's January 31, 2024 interview:

1. **Tagged Partitions & Uniform Cousin Solver (`solveUniformCousin`)**:
   - Computably builds a `k + 1`-cell tagged partition of `[0, 1]` whose cells `[x_i, x_{i+1}]`
     are certified `1 / (k + 1)`-fine (`solveUniformCousin_deltaFine`) and cover every point of
     `[0, 1]` (`solveUniformCousin_covers`).
2. **Adaptive Dyadic Cousin Solver (`solveDyadicCousin`)**:
   - Recursively bisects `[a, b]` around rational midpoints until each cell satisfies an
     arbitrary pointwise gauge `gauge : QVal → Nat` (or hits fuel `maxDepth`).
3. **Constructive Pincherle's Theorem (`pincherleGlobalBound` / `pincherleGlobalBound_spec`)**:
   - Salvatore Pincherle (1880): if `f` is locally bounded on `[0, 1]` with modulus `locScale`,
     computably extracts an explicit global bound `M` on `[0, 1]` with `∀ x ∈ [0, 1], |f(x)| ≤ M`.
4. **Non-Uniform Gauge Unboundedness (`puncturedDenomGauge` / `nonuniform_gauge_unbounded`)**:
   - Exhibits an explicit everywhere-positive rational gauge `x ↦ x.den` (`1 / (n + 1)`-balls)
     whose required fineness grows past every standard natural `K` on `[0, 1]`, illustrating why
     uncountable Cousin (`HBU`) without uniform moduli jumps in proof-theoretic strength.
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Tagged Partitions & Uniform Cousin Solver -/

/-- A tagged rational subinterval `[left, right]` with sample tag `tag`. -/
structure TaggedCell : Type where
  left : QVal
  right : QVal
  tag : QVal
  deriving DecidableEq, Repr

/-- Finite tagged partition represented as an explicit list of cells. -/
abbrev TaggedPartition : Type := List TaggedCell

/-- A tagged cell `c` is `δ`-fine at scale `k` (`1 / (k + 1)`) when `left ≤ tag ≤ right`
    and `|left - right| ≤ 1 / (k + 1)`. -/
def CellDeltaFine (k : Nat) (c : TaggedCell) : Prop :=
  QVal.le c.left c.tag ∧
  QVal.le c.tag c.right ∧
  QVal.le (QVal.dist c.left c.right) (QVal.unitFrac k)

/-- Build uniform cells `i = 0, …, count - 1` on grid `N`. -/
def uniformCellsAux (N : Nat) : Nat → TaggedPartition
  | 0 => []
  | i + 1 =>
      uniformCellsAux N i ++
        [{ left := QVal.gridPt N i, right := QVal.gridPt N (i + 1), tag := QVal.gridPt N i }]

/-- **Computable Uniform Cousin Solver**:
    Constructs a `(k + 1)`-cell tagged partition of `[0, 1]` certified at scale `1 / (k + 1)`. -/
def solveUniformCousin (k : Nat) : TaggedPartition :=
  uniformCellsAux k (k + 1)

theorem uniformCellsAux_length (N : Nat) : ∀ m : Nat, (uniformCellsAux N m).length = m
  | 0 => rfl
  | m + 1 => by
      simp [uniformCellsAux, uniformCellsAux_length N m]

theorem solveUniformCousin_length (k : Nat) : (solveUniformCousin k).length = k + 1 :=
  uniformCellsAux_length k (k + 1)

theorem mem_uniformCellsAux_iff (N : Nat) :
    ∀ (m : Nat) (c : TaggedCell),
      c ∈ uniformCellsAux N m ↔
      ∃ i : Nat, i < m ∧
        c = { left := QVal.gridPt N i, right := QVal.gridPt N (i + 1), tag := QVal.gridPt N i }
  | 0, c => by
      simp [uniformCellsAux]
  | m + 1, c => by
      simp only [uniformCellsAux, List.mem_append, List.mem_singleton, mem_uniformCellsAux_iff N m]
      constructor
      · intro h
        rcases h with ⟨i, hi, hEq⟩ | hEq
        · exact ⟨i, by omega, hEq⟩
        · exact ⟨m, by omega, hEq⟩
      · rintro ⟨i, hi, hEq⟩
        by_cases hLt : i < m
        · exact Or.inl ⟨i, hLt, hEq⟩
        · have hiEq : i = m := by omega
          subst hiEq
          exact Or.inr hEq

/-- **Uniform Cousin Fineness Theorem**:
    Every cell of `solveUniformCousin k` is `1 / (k + 1)`-fine. -/
theorem solveUniformCousin_deltaFine (k : Nat) :
    ∀ c ∈ solveUniformCousin k, CellDeltaFine k c := by
  intro c hc
  rcases (mem_uniformCellsAux_iff k (k + 1) c).mp hc with ⟨i, _, rfl⟩
  refine ⟨QVal.le_refl _, QVal.gridPt_mono (by omega), ?_⟩
  exact QVal.le_of_eqv_left (QVal.gridPt_step_dist k i) (QVal.le_refl _)

/-- **Uniform Cousin Coverage Theorem**:
    Every `x ∈ [0, 1]` is covered by a cell of `solveUniformCousin k`. -/
theorem solveUniformCousin_covers (k : Nat) {x : QVal}
    (hx0 : QVal.le 0 x) (hx1 : QVal.le x 1) :
    ∃ c ∈ solveUniformCousin k, QVal.le c.left x ∧ QVal.le x c.right := by
  have hg0 : QVal.le (QVal.gridPt k 0) x :=
    QVal.le_of_eqv_left (QVal.gridPt_zero_eqv k) hx0
  have hg1 : QVal.le x (QVal.gridPt k (k + 1)) :=
    QVal.le_of_eqv_right hx1 (QVal.eqv_symm (QVal.gridPt_end_eqv k))
  rcases bracketGridIdxAux_spec k x hg1 k 0 (by omega) hg0 with ⟨hiK, hLo, hHi⟩
  let i := bracketGridIdx k x
  have hiLe : i ≤ k := hiK
  let cell : TaggedCell :=
    { left := QVal.gridPt k i, right := QVal.gridPt k (i + 1), tag := QVal.gridPt k i }
  refine ⟨cell, ?_, hLo, hHi⟩
  exact (mem_uniformCellsAux_iff k (k + 1) cell).mpr ⟨i, by omega, rfl⟩

/-! ## 2. Adaptive Dyadic Cousin Bisection Solver -/

/-- Recursively bisect `[a, b]` around midpoint `m = (a + b) / 2` until `|a - b| ≤ 1 / (gauge m + 1)`
    or `fuel = 0`. -/
def solveDyadicCousinAux (gauge : QVal → Nat) : Nat → QVal → QVal → TaggedPartition
  | 0, a, b => [{ left := a, right := b, tag := QVal.midpoint a b }]
  | fuel + 1, a, b =>
      let m := QVal.midpoint a b
      if QVal.leB (QVal.dist a b) (QVal.unitFrac (gauge m)) then
        [{ left := a, right := b, tag := m }]
      else
        solveDyadicCousinAux gauge fuel a m ++ solveDyadicCousinAux gauge fuel m b

/-- Adaptive dyadic Cousin solver on `[0, 1]`. -/
def solveDyadicCousin (gauge : QVal → Nat) (maxDepth : Nat) : TaggedPartition :=
  solveDyadicCousinAux gauge maxDepth 0 1

theorem solveDyadicCousinAux_nonempty (gauge : QVal → Nat) :
    ∀ (fuel : Nat) (a b : QVal), (solveDyadicCousinAux gauge fuel a b).length ≥ 1
  | 0, _, _ => by simp [solveDyadicCousinAux]
  | fuel + 1, a, b => by
      unfold solveDyadicCousinAux
      dsimp
      split
      · simp
      · rw [List.length_append]
        have h1 := solveDyadicCousinAux_nonempty gauge fuel a (QVal.midpoint a b)
        omega

/-! ## 3. Constructive Pincherle's Theorem (1880) -/

theorem qval_le_max_left (a b : QVal) : QVal.le a (QVal.max a b) := by
  unfold QVal.max
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact QVal.le_refl a
  · simp only [↓reduceIte]
    exact (QVal.leB_true_iff a b).mp h

theorem qval_le_max_right (a b : QVal) : QVal.le b (QVal.max a b) := by
  unfold QVal.max
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact QVal.leB_false_imp_le h
  · simp only [↓reduceIte]
    exact QVal.le_refl b

/-- Maximum of `localBound c.tag` across all cells of a tagged partition. -/
def maxTagBound (localBound : QVal → QVal) : TaggedPartition → QVal
  | [] => 0
  | c :: cs => QVal.max (localBound c.tag) (maxTagBound localBound cs)

theorem le_maxTagBound (localBound : QVal → QVal) {c : TaggedCell} :
    ∀ {cs : TaggedPartition}, c ∈ cs → QVal.le (localBound c.tag) (maxTagBound localBound cs)
  | _ :: _, .head _ => qval_le_max_left _ _
  | _ :: _, .tail _ hTail =>
      QVal.le_trans (le_maxTagBound localBound hTail) (qval_le_max_right _ _)

/-- **Computable Pincherle Global Bound Extractor**:
    Evaluates `maxTagBound` over `solveUniformCousin locScale`. -/
def pincherleGlobalBound (localBound : QVal → QVal) (locScale : Nat) : QVal :=
  maxTagBound localBound (solveUniformCousin locScale)

/-- **Constructive Pincherle's Theorem**:
    If `f : QVal → QVal` is locally bounded around every point `t ∈ [0, 1]` within radius
    `1 / (locScale + 1)` by `localBound t`, then `pincherleGlobalBound localBound locScale`
    uniformly bounds `|f(x)|` across the entire interval `[0, 1]`! -/
theorem pincherleGlobalBound_spec {f : QVal → QVal}
    (localBound : QVal → QVal) (locScale : Nat)
    (hLocal : ∀ (t x : QVal),
      QVal.le 0 t → QVal.le t 1 →
      QVal.le 0 x → QVal.le x 1 →
      QVal.le (QVal.dist x t) (QVal.unitFrac locScale) →
      QVal.le (f x).abs (localBound t)) :
    ∀ x : QVal, QVal.le 0 x → QVal.le x 1 →
      QVal.le (f x).abs (pincherleGlobalBound localBound locScale) := by
  intro x hx0 hx1
  rcases solveUniformCousin_covers locScale hx0 hx1 with ⟨c, hcMem, hLo, hHi⟩
  rcases (mem_uniformCellsAux_iff locScale (locScale + 1) c).mp hcMem with ⟨i, hiLt, hCellEq⟩
  have hTag0 : QVal.le 0 c.tag := by rw [hCellEq]; exact QVal.gridPt_nonneg locScale i
  have hTag1 : QVal.le c.tag 1 := by rw [hCellEq]; exact QVal.gridPt_le_one (by omega)
  have hDistXT : QVal.le (QVal.dist x c.tag) (QVal.unitFrac locScale) := by
    rw [hCellEq] at hLo hHi ⊢
    have hBet := QVal.dist_le_of_between hLo hHi
    exact QVal.le_of_eqv_right hBet (QVal.gridPt_step_dist locScale i)
  have hFxLe := hLocal c.tag x hTag0 hTag1 hx0 hx1 hDistXT
  have hTagLeGlobal := le_maxTagBound localBound hcMem
  exact QVal.le_trans hFxLe hTagLeGlobal

/-! ## 4. Non-Uniform Gauge Unboundedness (`HBU` Barrier) -/

/-- Everywhere-defined rational denominator gauge `x ↦ x.den` (demanding radius `1 / (x.den + 1)`). -/
@[inline] def puncturedDenomGauge (x : QVal) : Nat :=
  x.den

/-- Unlike uniform moduli, `puncturedDenomGauge` is unbounded on `[0, 1]`: for every `K : Nat`,
    there is an explicit rational `x ∈ [0, 1]` where `puncturedDenomGauge x > K`. -/
theorem nonuniform_gauge_unbounded (K : Nat) :
    ∃ x : QVal, QVal.le 0 x ∧ QVal.le x 1 ∧ K < puncturedDenomGauge x := by
  refine ⟨QVal.unitFrac K, ?_, ?_, ?_⟩
  · change (0 : Int) * ((K + 1 : Nat) : Int) ≤ 1 * 1
    omega
  · change 1 * 1 ≤ 1 * ((K + 1 : Nat) : Int)
    omega
  · dsimp [puncturedDenomGauge, QVal.unitFrac, QVal.den]
    omega

end ReverseMath
end SandersNSA
