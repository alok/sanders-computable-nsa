/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.OverspillOmega

/-!
# Constructive vs. Nonstandard IVT, the `LLPO` Barrier & Dini's Theorem

Implements the core case studies from Sam Sanders's *"To be or not to be constructive"* /
*"Reuniting the antipodes"*, Chuangjie Xu & Sam Sanders's Dini theorem proof-mining work,
and Alok Singh's April 6, 2026 blog post (*Nonstandard Definitions*):

1. **Hyperfinite Grid Sign-Crossing Search (`findGridCrossing`)**:
   - Scans the uniform hyperfinite grid `0, 1/(N+1), …, 1` and constructively locates an
     adjacent sign-change bracket `[i/(N+1), (i+1)/(N+1)]` with `f(x_i) ≤ 0 ≤ f(x_{i+1})`.
2. **Constructive Approximate IVT (`approxIVTPoint` / `approxIVT_spec`)**:
   - Combines `findGridCrossing` at scale `N := ω(k)` with uniform continuity `UniformContOn f 0 1`
     to compute an explicit rational `x_k ∈ [0, 1]` satisfying `|f(x_k)| ≤ 1 / (k + 1)`.
3. **Exact Constructive IVT under Separation Modulus (`exactIVT_cauchy`)**:
   - Upgrades `approxIVTPoint` into a certified `CauchySeqWithModulus` root sequence whenever `f`
     carries a quantitative separation/non-constancy modulus `SeparationModulus`.
4. **The `LLPO` Hovering-Tent Discontinuity Barrier (`hoveringTent` / `llpo_hovering_jump`)**:
   - Formalizes the piecewise-linear hovering family `hoveringTent (±1/(M+1))` (`M ≥ 4`), proving
     that arbitrarily small `±` perturbations force every exact root to jump across `[1/4, 3/4]`
     by at least `1/2`, witnessing why full `IVT` without non-constancy cannot have a continuous
     computable realiser.
5. **Computable Dini Uniform-Convergence Modulus (`dini_equicontinuous` & `dini_from_cover`)**:
   - Extracts an explicit uniform convergence modulus `UniformConvWithModulus g 0 0 1` for
     monotone decreasing sequences `g_n ↓ 0` by maximizing the pointwise convergence modulus
     across a finite `δ`-cover of `[0, 1]`.
-/

namespace SandersNSA
namespace Antipodes

/-! ## 1. Rational Order, Sign & Grid Geometry Helpers -/

/-- Extensional congruence for functions `QVal → QVal`. -/
def RespectsEqv (f : QVal → QVal) : Prop :=
  ∀ x y : QVal, QVal.eqv x y → QVal.eqv (f x) (f y)

namespace QVal

theorem leB_true_iff (p q : QVal) : leB p q = true ↔ le p q := by
  unfold leB le
  exact decide_eq_true_iff

theorem leB_false_imp_le {p q : QVal} (h : leB p q = false) : le q p := by
  have hNot : ¬ le p q := of_decide_eq_false h
  rcases le_total p q with hpq | hqp
  · exact False.elim (hNot hpq)
  · exact hqp

theorem dist_eqv_sub_of_le {a x : QVal} (hax : le a x) : eqv (dist x a) (x - a) := by
  unfold eqv at *
  unfold le at hax
  have hNonneg : 0 ≤ (x - a).num := by
    rw [sub_num]
    omega
  have hAbs : ((x - a).num.natAbs : Int) = (x - a).num := Int.natAbs_of_nonneg hNonneg
  change ((x - a).num.natAbs : Int) * (x - a).denInt = (x - a).num * (dist x a).denInt
  rw [hAbs]
  rfl

theorem sub_le_sub_right {x b : QVal} (hxb : le x b) (a : QVal) : le (x - a) (b - a) :=
  add_le_add hxb (le_refl (-a))

theorem dist_le_of_between {a x b : QVal} (hax : le a x) (hxb : le x b) :
    le (dist x a) (dist a b) := by
  have h1 : le (dist x a) (x - a) := le_of_eqv_left (dist_eqv_sub_of_le hax) (le_refl _)
  have h2 : le (x - a) (b - a) := sub_le_sub_right hxb a
  have h3 : le (b - a) (dist b a) :=
    le_of_eqv_right (le_refl _) (eqv_symm (dist_eqv_sub_of_le (le_trans hax hxb)))
  have h4 : le (dist b a) (dist a b) := le_of_eqv_right (le_refl _) (dist_symm b a)
  exact le_trans (le_trans h1 h2) (le_trans h3 h4)

/-- If `a ≤ 0` and `0 ≤ b`, then `|a| ≤ |a - b|`. -/
theorem abs_le_dist_of_opposite_signs {a b : QVal} (ha : le a 0) (hb : le 0 b) :
    le a.abs (dist a b) := by
  have haNum : a.num ≤ 0 := by
    change a.num * 1 ≤ 0 * a.denInt at ha
    omega
  have hbNum : 0 ≤ b.num := by
    change 0 * b.denInt ≤ b.num * 1 at hb
    omega
  have haDen : 0 < a.denInt := a.denInt_pos
  have hbDen : 0 < b.denInt := b.denInt_pos
  have hProdA : a.num * b.denInt ≤ 0 := by
    have h := Int.mul_le_mul_of_nonneg_right haNum (by omega : 0 ≤ b.denInt)
    omega
  have hProdB : 0 ≤ b.num * a.denInt :=
    Int.mul_nonneg hbNum (by omega)
  have hSubNeg : (a - b).num ≤ 0 := by
    rw [sub_num]
    omega
  have hAbsSub : ((a - b).num.natAbs : Int) = -(a - b).num := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hAbsA : (a.num.natAbs : Int) = -a.num := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hCore : (a.num.natAbs : Int) * b.denInt ≤ ((a - b).num.natAbs : Int) := by
    rw [hAbsA, hAbsSub, sub_num, Int.neg_mul]
    omega
  unfold le
  rw [dist_denInt]
  change (a.num.natAbs : Int) * (a.denInt * b.denInt) ≤ ((a - b).num.natAbs : Int) * a.denInt
  have hScaled := Int.mul_le_mul_of_nonneg_right hCore (by omega : 0 ≤ a.denInt)
  have hAssoc : (a.num.natAbs : Int) * b.denInt * a.denInt =
      (a.num.natAbs : Int) * (a.denInt * b.denInt) := by
    rw [Int.mul_assoc, Int.mul_comm b.denInt a.denInt]
  omega

theorem gridPt_zero_eqv (N : Nat) : eqv (gridPt N 0) 0 := by
  change (0 : Int) * 1 = 0 * ((N + 1 : Nat) : Int)
  omega

theorem gridPt_end_eqv (N : Nat) : eqv (gridPt N (N + 1)) 1 := by
  change ((N + 1 : Nat) : Int) * 1 = 1 * ((N + 1 : Nat) : Int)
  omega

theorem gridPt_nonneg (N i : Nat) : le 0 (gridPt N i) := by
  change (0 : Int) * ((N + 1 : Nat) : Int) ≤ (i : Int) * 1
  omega

theorem gridPt_le_one {N i : Nat} (hi : i ≤ N + 1) : le (gridPt N i) 1 := by
  change (i : Int) * 1 ≤ 1 * ((N + 1 : Nat) : Int)
  omega

theorem gridPt_mono {N i j : Nat} (hij : i ≤ j) : le (gridPt N i) (gridPt N j) := by
  change (i : Int) * ((N + 1 : Nat) : Int) ≤ (j : Int) * ((N + 1 : Nat) : Int)
  exact Int.mul_le_mul_of_nonneg_right (by omega) (by omega)

theorem gridPt_step_dist (N i : Nat) :
    eqv (dist (gridPt N i) (gridPt N (i + 1))) (unitFrac N) := by
  have hLe : le (gridPt N i) (gridPt N (i + 1)) := gridPt_mono (by omega)
  have hSymm := dist_symm (gridPt N i) (gridPt N (i + 1))
  have hSub := dist_eqv_sub_of_le hLe
  have hStep : eqv (gridPt N (i + 1) - gridPt N i) (unitFrac N) := by
    unfold eqv
    rw [sub_num, sub_denInt]
    change (((i + 1 : Nat) : Int) * ((N + 1 : Nat) : Int) -
            (i : Int) * ((N + 1 : Nat) : Int)) * ((N + 1 : Nat) : Int) =
           1 * (((N + 1 : Nat) : Int) * ((N + 1 : Nat) : Int))
    have hDiff : ((i + 1 : Nat) : Int) * ((N + 1 : Nat) : Int) -
        (i : Int) * ((N + 1 : Nat) : Int) = ((N + 1 : Nat) : Int) := by
      have hSucc : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
      rw [hSucc, Int.add_mul, Int.one_mul]
      omega
    rw [hDiff, Int.one_mul]
  exact eqv_trans hSymm (eqv_trans hSub hStep)

end QVal

/-! ## 2. Hyperfinite Grid Sign-Crossing Search & Approximate IVT -/

/-- Auxiliary upward scan for an adjacent sign-crossing index on `0, …, N + 1`. -/
def findGridCrossingAux (f : QVal → QVal) (N : Nat) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
      if QVal.leB 0 (f (QVal.gridPt N (i + 1))) then i
      else findGridCrossingAux f N fuel (i + 1)

/-- **Hyperfinite Grid Sign-Crossing Finder**:
    Finds `i ≤ N` such that `f(i/(N+1)) ≤ 0 ≤ f((i+1)/(N+1))`. -/
def findGridCrossing (f : QVal → QVal) (N : Nat) : Nat :=
  findGridCrossingAux f N N 0

theorem findGridCrossingAux_spec (f : QVal → QVal) (N : Nat)
    (hEnd : QVal.le 0 (f (QVal.gridPt N (N + 1)))) :
    ∀ (fuel i : Nat),
      i + fuel = N →
      QVal.le (f (QVal.gridPt N i)) 0 →
      let idx := findGridCrossingAux f N fuel i
      idx ≤ N ∧
      QVal.le (f (QVal.gridPt N idx)) 0 ∧
      QVal.le 0 (f (QVal.gridPt N (idx + 1)))
  | 0, i, hSum, hi => by
      unfold findGridCrossingAux
      have hiEq : i = N := by omega
      rw [hiEq] at hi ⊢
      exact ⟨Nat.le_refl N, hi, hEnd⟩
  | fuel + 1, i, hSum, hi => by
      unfold findGridCrossingAux
      cases hBool : QVal.leB 0 (f (QVal.gridPt N (i + 1)))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hNextNeg : QVal.le (f (QVal.gridPt N (i + 1))) 0 :=
          QVal.leB_false_imp_le hBool
        exact findGridCrossingAux_spec f N hEnd fuel (i + 1) (by omega) hNextNeg
      · simp only [↓reduceIte]
        have hNextPos : QVal.le 0 (f (QVal.gridPt N (i + 1))) :=
          (QVal.leB_true_iff _ _).mp hBool
        exact ⟨by omega, hi, hNextPos⟩

/-- **Sign-Crossing Correctness Theorem**: If `f(0_grid) ≤ 0` and `0 ≤ f(1_grid)`,
    `i := findGridCrossing f N` satisfies `i ≤ N`, `f(x_i) ≤ 0`, and `0 ≤ f(x_{i+1})`. -/
theorem findGridCrossing_spec {f : QVal → QVal} {N : Nat}
    (h0 : QVal.le (f (QVal.gridPt N 0)) 0)
    (h1 : QVal.le 0 (f (QVal.gridPt N (N + 1)))) :
    let i := findGridCrossing f N
    i ≤ N ∧
    QVal.le (f (QVal.gridPt N i)) 0 ∧
    QVal.le 0 (f (QVal.gridPt N (i + 1))) :=
  findGridCrossingAux_spec f N h1 N 0 (by omega) h0

/-- **Computable Approximate IVT Realiser**:
    Evaluates the hyperfinite grid sign-crossing finder at `N := hCont.modulus k`. -/
def approxIVTPoint (f : QVal → QVal) (hCont : UniformContOn f 0 1) (k : Nat) : QVal :=
  let N := hCont.modulus k
  QVal.gridPt N (findGridCrossing f N)

/-- **Constructive Approximate IVT Theorem**:
    For every uniformly continuous `f : [0, 1] → QVal` with `f(0) ≤ 0 ≤ f(1)`,
    `x_k := approxIVTPoint f hCont k` lies in `[0, 1]` and satisfies `|f(x_k)| ≤ 1 / (k + 1)`. -/
theorem approxIVT_spec {f : QVal → QVal}
    (hCont : UniformContOn f 0 1)
    (hResp : RespectsEqv f)
    (hf0 : QVal.le (f 0) 0)
    (hf1 : QVal.le 0 (f 1))
    (k : Nat) :
    let x := approxIVTPoint f hCont k
    QVal.le 0 x ∧ QVal.le x 1 ∧ QVal.le (f x).abs (QVal.unitFrac k) := by
  let N := hCont.modulus k
  have hg0 : QVal.le (f (QVal.gridPt N 0)) 0 :=
    QVal.le_of_eqv_left (hResp _ _ (QVal.gridPt_zero_eqv N)) hf0
  have hg1 : QVal.le 0 (f (QVal.gridPt N (N + 1))) :=
    QVal.le_of_eqv_right hf1 (hResp _ _ (QVal.eqv_symm (QVal.gridPt_end_eqv N)))
  rcases findGridCrossing_spec (N := N) hg0 hg1 with ⟨hiN, hLeft, hRight⟩
  let i := findGridCrossing f N
  have hx0 : QVal.le 0 (QVal.gridPt N i) := QVal.gridPt_nonneg N i
  have hx1 : QVal.le (QVal.gridPt N i) 1 := QVal.gridPt_le_one (by omega)
  have hy0 : QVal.le 0 (QVal.gridPt N (i + 1)) := QVal.gridPt_nonneg N (i + 1)
  have hy1 : QVal.le (QVal.gridPt N (i + 1)) 1 := QVal.gridPt_le_one (by omega)
  have hStepDist : QVal.le (QVal.dist (QVal.gridPt N i) (QVal.gridPt N (i + 1))) (QVal.unitFrac N) :=
    QVal.le_of_eqv_left (QVal.gridPt_step_dist N i) (QVal.le_refl _)
  have hFDist : QVal.le (QVal.dist (f (QVal.gridPt N i)) (f (QVal.gridPt N (i + 1)))) (QVal.unitFrac k) :=
    hCont.spec k (QVal.gridPt N i) (QVal.gridPt N (i + 1)) hx0 hx1 hy0 hy1 hStepDist
  have hAbsLe : QVal.le (f (QVal.gridPt N i)).abs
      (QVal.dist (f (QVal.gridPt N i)) (f (QVal.gridPt N (i + 1)))) :=
    QVal.abs_le_dist_of_opposite_signs hLeft hRight
  exact ⟨hx0, hx1, QVal.le_trans hAbsLe hFDist⟩

/-! ## 3. Exact Root Extraction under Quantitative Separation Modulus -/

/-- Quantitative separation / local non-constancy modulus on `[a, b]` (constructive
    counterpart of strict monotonicity or bounded inverse derivative). -/
structure SeparationModulus (f : QVal → QVal) (a b : QVal) : Type where
  sepMod : Modulus
  spec : ∀ (k : Nat) (x y : QVal),
    QVal.le a x → QVal.le x b →
    QVal.le a y → QVal.le y b →
    QVal.le (QVal.dist (f x) (f y)) (QVal.unitFrac (sepMod k)) →
    QVal.le (QVal.dist x y) (QVal.unitFrac k)

theorem abs_eqv_dist_zero (q : QVal) : QVal.eqv (QVal.dist q 0) q.abs := by
  unfold QVal.eqv
  rw [QVal.dist_denInt]
  have hSub : (q - 0).num = q.num := by
    rw [QVal.sub_num]
    change q.num * 1 - 0 * q.denInt = q.num
    omega
  change ((q - 0).num.natAbs : Int) * q.denInt = (q.num.natAbs : Int) * (q.denInt * 1)
  rw [hSub, Int.mul_one]

/-- **Exact Constructive IVT Theorem**:
    Under a `SeparationModulus`, the hyperfinite grid sign-crossing sequence
    `n ↦ approxIVTPoint f hCont n` is a certified `CauchySeqWithModulus` root sequence
    with modulus `ω(k) = 2 * sepMod(k) + 1`. -/
def exactIVT_cauchy {f : QVal → QVal}
    (hCont : UniformContOn f 0 1)
    (hSep : SeparationModulus f 0 1)
    (hResp : RespectsEqv f)
    (hf0 : QVal.le (f 0) 0)
    (hf1 : QVal.le 0 (f 1)) :
    CauchySeqWithModulus (approxIVTPoint f hCont) where
  modulus k := 2 * hSep.sepMod k + 1
  spec k m n hm hn := by
    let s := hSep.sepMod k
    rcases approxIVT_spec hCont hResp hf0 hf1 m with ⟨hxm0, hxm1, hfm⟩
    rcases approxIVT_spec hCont hResp hf0 hf1 n with ⟨hxn0, hxn1, hfn⟩
    have hfmS : QVal.le (f (approxIVTPoint f hCont m)).abs (QVal.unitFrac (2 * s + 1)) :=
      QVal.le_trans hfm (QVal.unitFrac_anti hm)
    have hfnS : QVal.le (f (approxIVTPoint f hCont n)).abs (QVal.unitFrac (2 * s + 1)) :=
      QVal.le_trans hfn (QVal.unitFrac_anti hn)
    have hd1 : QVal.le (QVal.dist (f (approxIVTPoint f hCont m)) 0) (QVal.unitFrac (2 * s + 1)) :=
      QVal.le_of_eqv_left (abs_eqv_dist_zero _) hfmS
    have hd2 : QVal.le (QVal.dist 0 (f (approxIVTPoint f hCont n))) (QVal.unitFrac (2 * s + 1)) :=
      QVal.le_of_eqv_left
        (QVal.eqv_trans (QVal.dist_symm 0 _) (abs_eqv_dist_zero _))
        hfnS
    have hTri := QVal.dist_triangle (f (approxIVTPoint f hCont m)) 0 (f (approxIVTPoint f hCont n))
    have hSum := QVal.le_trans (QVal.add_le_add hd1 hd2) (QVal.unitFrac_half_sum s)
    have hFDist : QVal.le
        (QVal.dist (f (approxIVTPoint f hCont m)) (f (approxIVTPoint f hCont n)))
        (QVal.unitFrac s) :=
      QVal.le_trans hTri hSum
    exact hSep.spec k (approxIVTPoint f hCont m) (approxIVTPoint f hCont n)
      hxm0 hxm1 hxn0 hxn1 hFDist

/-! ## 4. The `LLPO` Hovering-Tent Discontinuity Barrier -/

/-- Piecewise-linear tent function on `[0, 1]` that hovers identically at `0` across `[1/4, 3/4]`:
    - `x - 1/4` on `(-∞, 1/4]`
    - `0` on `(1/4, 3/4)`
    - `x - 3/4` on `[3/4, ∞)`. -/
def baseTent (x : QVal) : QVal :=
  if QVal.leB x ⟨1, 3⟩ then x - ⟨1, 3⟩
  else if QVal.leB ⟨3, 3⟩ x then x - ⟨3, 3⟩
  else 0

/-- Perturbed hovering tent `hoveringTent c x = baseTent x + c`. -/
def hoveringTent (c x : QVal) : QVal :=
  baseTent x + c

/-- Under positive perturbation `+1/(M+1)`, **every** root of `hoveringTent` lies in `(-∞, 1/4]`. -/
theorem hoveringTent_pos_root_le_quarter {M : Nat} {x : QVal}
    (hRoot : QVal.eqv (hoveringTent (QVal.unitFrac M) x) 0) :
    QVal.le x ⟨1, 3⟩ := by
  unfold hoveringTent baseTent at hRoot
  cases h1 : QVal.leB x ⟨1, 3⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hRoot
    cases h2 : QVal.leB ⟨3, 3⟩ x
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hRoot
      change (0 * ((M + 1 : Nat) : Int) + 1 * 1) * 1 = 0 * _ at hRoot
      omega
    · simp only [h2, ↓reduceIte] at hRoot
      have hGe : QVal.le ⟨3, 3⟩ x := (QVal.leB_true_iff _ _).mp h2
      unfold QVal.le at hGe
      have hSubNonneg : 0 ≤ (x - ⟨3, 3⟩).num := by
        rw [QVal.sub_num]
        change 0 ≤ x.num * 4 - 3 * x.denInt
        change 3 * x.denInt ≤ x.num * 4 at hGe
        omega
      have hSubDen : 0 < (x - ⟨3, 3⟩).denInt := QVal.denInt_pos _
      unfold QVal.eqv at hRoot
      change ((x - ⟨3, 3⟩).num * ((M + 1 : Nat) : Int) + 1 * (x - ⟨3, 3⟩).denInt) * 1 =
        0 * ((x - ⟨3, 3⟩) + QVal.unitFrac M).denInt at hRoot
      have hProdNonneg : 0 ≤ (x - ⟨3, 3⟩).num * ((M + 1 : Nat) : Int) :=
        Int.mul_nonneg hSubNonneg (by omega)
      omega
  · exact (QVal.leB_true_iff _ _).mp h1

/-- Under negative perturbation `-1/(M+1)`, **every** root of `hoveringTent` lies in `[3/4, ∞)`. -/
theorem hoveringTent_neg_root_ge_threeQuarter {M : Nat} {y : QVal}
    (hRoot : QVal.eqv (hoveringTent (-QVal.unitFrac M) y) 0) :
    QVal.le ⟨3, 3⟩ y := by
  unfold hoveringTent baseTent at hRoot
  cases h1 : QVal.leB y ⟨1, 3⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hRoot
    cases h2 : QVal.leB ⟨3, 3⟩ y
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hRoot
      change (0 * ((M + 1 : Nat) : Int) + (-1) * 1) * 1 = 0 * _ at hRoot
      omega
    · exact (QVal.leB_true_iff _ _).mp h2
  · simp only [h1, ↓reduceIte] at hRoot
    have hLe : QVal.le y ⟨1, 3⟩ := (QVal.leB_true_iff _ _).mp h1
    unfold QVal.le at hLe
    have hSubNonpos : (y - ⟨1, 3⟩).num ≤ 0 := by
      rw [QVal.sub_num]
      change y.num * 4 - 1 * y.denInt ≤ 0
      change y.num * 4 ≤ 1 * y.denInt at hLe
      omega
    have hSubDen : 0 < (y - ⟨1, 3⟩).denInt := QVal.denInt_pos _
    unfold QVal.eqv at hRoot
    change ((y - ⟨1, 3⟩).num * ((M + 1 : Nat) : Int) + (-1) * (y - ⟨1, 3⟩).denInt) * 1 =
      0 * ((y - ⟨1, 3⟩) + (-QVal.unitFrac M)).denInt at hRoot
    have hProdNonpos : (y - ⟨1, 3⟩).num * ((M + 1 : Nat) : Int) ≤ 0 := by
      have h := Int.mul_le_mul_of_nonneg_right hSubNonpos (by omega : 0 ≤ ((M + 1 : Nat) : Int))
      omega
    omega

/-- **The `LLPO` Discontinuity Jump Theorem**:
    For every arbitrarily fine scale `M : Nat`, any root `x₊` of `hoveringTent (+1/(M+1))`
    and any root `x₋` of `hoveringTent (-1/(M+1))` satisfy `|x₋ - x₊| ≥ 1/2`! -/
theorem llpo_hovering_jump {M : Nat} {xPos xNeg : QVal}
    (hPos : QVal.eqv (hoveringTent (QVal.unitFrac M) xPos) 0)
    (hNeg : QVal.eqv (hoveringTent (-QVal.unitFrac M) xNeg) 0) :
    QVal.le ⟨1, 1⟩ (QVal.dist xNeg xPos) := by
  have hx : QVal.le xPos ⟨1, 3⟩ := hoveringTent_pos_root_le_quarter hPos
  have hy : QVal.le ⟨3, 3⟩ xNeg := hoveringTent_neg_root_ge_threeQuarter hNeg
  have hxy : QVal.le xPos xNeg := QVal.le_trans hx (QVal.le_trans (by decide) hy)
  have hHalfLe : QVal.le ⟨1, 1⟩ (xNeg - xPos) := by
    unfold QVal.le at hx hy ⊢
    rw [QVal.sub_num, QVal.sub_denInt]
    change 1 * (xNeg.denInt * xPos.denInt) ≤ (xNeg.num * xPos.denInt - xPos.num * xNeg.denInt) * 2
    have hxPosDen : 0 < xPos.denInt := xPos.denInt_pos
    have hxNegDen : 0 < xNeg.denInt := xNeg.denInt_pos
    change xPos.num * 4 ≤ 1 * xPos.denInt at hx
    change 3 * xNeg.denInt ≤ xNeg.num * 4 at hy
    have hs1 : (xPos.num * 4) * xNeg.denInt ≤ (1 * xPos.denInt) * xNeg.denInt :=
      Int.mul_le_mul_of_nonneg_right hx (by omega)
    have hs2 : (3 * xNeg.denInt) * xPos.denInt ≤ (xNeg.num * 4) * xPos.denInt :=
      Int.mul_le_mul_of_nonneg_right hy (by omega)
    have e1 : (xPos.num * 4) * xNeg.denInt = (xPos.num * xNeg.denInt) * 4 := by
      rw [Int.mul_assoc, Int.mul_comm 4 xNeg.denInt, ← Int.mul_assoc]
    have e2 : (xNeg.num * 4) * xPos.denInt = (xNeg.num * xPos.denInt) * 4 := by
      rw [Int.mul_assoc, Int.mul_comm 4 xPos.denInt, ← Int.mul_assoc]
    have e3 : (3 * xNeg.denInt) * xPos.denInt = 3 * (xNeg.denInt * xPos.denInt) := by
      rw [Int.mul_assoc]
    have e4 : (1 * xPos.denInt) * xNeg.denInt = xNeg.denInt * xPos.denInt := by
      rw [Int.one_mul, Int.mul_comm]
    omega
  exact QVal.le_of_eqv_right hHalfLe (QVal.eqv_symm (QVal.dist_eqv_sub_of_le hxy))

/-! ## 5. Computable Dini Uniform-Convergence Modulus -/

/-- Scan `[0, 1]` to find the uniform grid subinterval `[i/(N+1), (i+1)/(N+1)]` containing `x`. -/
def bracketGridIdxAux (N : Nat) (x : QVal) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
      if QVal.leB x (QVal.gridPt N (i + 1)) then i
      else bracketGridIdxAux N x fuel (i + 1)

def bracketGridIdx (N : Nat) (x : QVal) : Nat :=
  bracketGridIdxAux N x N 0

theorem bracketGridIdxAux_spec (N : Nat) (x : QVal)
    (hx1 : QVal.le x (QVal.gridPt N (N + 1))) :
    ∀ (fuel i : Nat),
      i + fuel = N →
      QVal.le (QVal.gridPt N i) x →
      let idx := bracketGridIdxAux N x fuel i
      idx ≤ N ∧
      QVal.le (QVal.gridPt N idx) x ∧
      QVal.le x (QVal.gridPt N (idx + 1))
  | 0, i, hSum, hLo => by
      unfold bracketGridIdxAux
      have hi : i = N := by omega
      rw [hi] at hLo ⊢
      exact ⟨Nat.le_refl N, hLo, hx1⟩
  | fuel + 1, i, hSum, hLo => by
      unfold bracketGridIdxAux
      cases hB : QVal.leB x (QVal.gridPt N (i + 1))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hNextLo : QVal.le (QVal.gridPt N (i + 1)) x := QVal.leB_false_imp_le hB
        exact bracketGridIdxAux_spec N x hx1 fuel (i + 1) (by omega) hNextLo
      · simp only [↓reduceIte]
        exact ⟨by omega, hLo, (QVal.leB_true_iff _ _).mp hB⟩

theorem bracketGridIdx_dist {N : Nat} {x : QVal}
    (hx0 : QVal.le 0 x) (hx1 : QVal.le x 1) :
    let i := bracketGridIdx N x
    i ≤ N ∧ QVal.le (QVal.dist x (QVal.gridPt N i)) (QVal.unitFrac N) := by
  have hg0 : QVal.le (QVal.gridPt N 0) x :=
    QVal.le_of_eqv_left (QVal.gridPt_zero_eqv N) hx0
  have hg1 : QVal.le x (QVal.gridPt N (N + 1)) :=
    QVal.le_of_eqv_right hx1 (QVal.eqv_symm (QVal.gridPt_end_eqv N))
  rcases bracketGridIdxAux_spec N x hg1 N 0 (by omega) hg0 with ⟨hiN, hLo, hHi⟩
  refine ⟨hiN, ?_⟩
  have hBetween := QVal.dist_le_of_between hLo hHi
  exact QVal.le_of_eqv_right hBetween (QVal.gridPt_step_dist N _)

/-- Maximum of `pwMod (gridPt N i) target` across `i = 0, …, count`. -/
def maxGridPointwiseMod (pwMod : QVal → Modulus) (N target : Nat) : Nat → Nat
  | 0 => pwMod (QVal.gridPt N 0) target
  | i + 1 => Nat.max (maxGridPointwiseMod pwMod N target i) (pwMod (QVal.gridPt N (i + 1)) target)

theorem le_maxGridPointwiseMod (pwMod : QVal → Modulus) (N target : Nat) :
    ∀ {M i : Nat}, i ≤ M →
      pwMod (QVal.gridPt N i) target ≤ maxGridPointwiseMod pwMod N target M
  | 0, i, hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      exact Nat.le_refl _
  | M + 1, i, hi => by
      by_cases hEq : i = M + 1
      · subst hEq
        unfold maxGridPointwiseMod
        exact Nat.le_max_right _ _
      · have ih := le_maxGridPointwiseMod pwMod N target (M := M) (i := i) (by omega)
        unfold maxGridPointwiseMod
        exact Nat.le_trans ih (Nat.le_max_left _ _)

/-- **Computable Dini Uniform-Convergence Modulus**:
    Given an equicontinuous scale `eqMod` and a pointwise convergence modulus `pwMod`,
    evaluates the maximum pointwise threshold across the finite grid `0, …, N`
    where `N := eqMod (2 * k + 1)`. -/
def extractDiniModulus (eqMod : Modulus) (pwMod : QVal → Modulus) (k : Nat) : Nat :=
  let N := eqMod (2 * k + 1)
  maxGridPointwiseMod pwMod N (2 * k + 1) N

/-- **Constructive / Proof-Mined Dini Theorem**:
    For a sequence `g : Nat → QVal → QVal` converging pointwise to `0` on `[0, 1]` with
    pointwise modulus `pwMod` and spatial modulus `eqMod` (or monotone decreasing under a
    cover at stage `extractDiniModulus`), `extractDiniModulus eqMod pwMod` certifies
    uniform convergence `g_n ⇒ 0` on `[0, 1]`. -/
def dini_uniform_conv {g : Nat → QVal → QVal}
    (eqMod : Modulus)
    (hEqui : ∀ (n k : Nat) (x y : QVal),
      QVal.le 0 x → QVal.le x 1 →
      QVal.le 0 y → QVal.le y 1 →
      QVal.le (QVal.dist x y) (QVal.unitFrac (eqMod k)) →
      QVal.le (QVal.dist (g n x) (g n y)) (QVal.unitFrac k))
    (pwMod : QVal → Modulus)
    (hPw : ∀ (x : QVal) (k n : Nat),
      QVal.le 0 x → QVal.le x 1 →
      pwMod x k ≤ n →
      QVal.le (QVal.dist (g n x) 0) (QVal.unitFrac k)) :
    UniformConvWithModulus g (fun _ => 0) 0 1 where
  modulus := extractDiniModulus eqMod pwMod
  spec k n x hn hx0 hx1 := by
    let N := eqMod (2 * k + 1)
    rcases bracketGridIdx_dist (N := N) hx0 hx1 with ⟨hiN, hDistGrid⟩
    let xi := QVal.gridPt N (bracketGridIdx N x)
    have hxi0 : QVal.le 0 xi := QVal.gridPt_nonneg N _
    have hxi1 : QVal.le xi 1 := QVal.gridPt_le_one (by omega)
    have hStep1 : QVal.le (QVal.dist (g n x) (g n xi)) (QVal.unitFrac (2 * k + 1)) :=
      hEqui n (2 * k + 1) x xi hx0 hx1 hxi0 hxi1 hDistGrid
    have hPwLe : pwMod xi (2 * k + 1) ≤ n :=
      Nat.le_trans (le_maxGridPointwiseMod pwMod N (2 * k + 1) hiN) hn
    have hStep2 : QVal.le (QVal.dist (g n xi) 0) (QVal.unitFrac (2 * k + 1)) :=
      hPw xi (2 * k + 1) n hxi0 hxi1 hPwLe
    have hTri := QVal.dist_triangle (g n x) (g n xi) 0
    have hSum := QVal.le_trans (QVal.add_le_add hStep1 hStep2) (QVal.unitFrac_half_sum k)
    exact QVal.le_trans hTri hSum

/-- **Monotone Dini Theorem from Finite Subcover (Zero Equicontinuity)**:
    Given ANY non-negative monotone-decreasing sequence `g : Nat → QVal → QVal` (`0 ≤ g_{n+1} ≤ g_n`)
    where each individual `g_m` has its own continuity modulus, any finite subcover
    `cover : List (QVal × Nat)` of `[0, 1]` whose balls satisfy `g_{m_j}(c_j) ≤ 1/(2k+2)`
    yields an explicit uniform threshold `M := cover.foldr (fun p acc => Nat.max p.2 acc) 0`
    such that `∀ n ≥ M, ∀ x ∈ [0, 1], |g_n(x) - 0| ≤ 1/(k+1)`. -/
def maxCoverStage : List (QVal × Nat) → Nat
  | [] => 0
  | (_, m) :: rest => Nat.max m (maxCoverStage rest)

theorem mem_le_maxCoverStage {c : QVal} {m : Nat} :
    ∀ {cover : List (QVal × Nat)}, (c, m) ∈ cover → m ≤ maxCoverStage cover
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ hTail => Nat.le_trans (mem_le_maxCoverStage hTail) (Nat.le_max_right _ _)

theorem dini_monotone_from_subcover {g : Nat → QVal → QVal}
    (hNonneg : ∀ (n : Nat) (x : QVal), QVal.le 0 (g n x))
    (hMono : ∀ {m n : Nat} (x : QVal), m ≤ n → QVal.le (g n x) (g m x))
    (cont : (m : Nat) → UniformContOn (g m) 0 1)
    {k : Nat} (cover : List (QVal × Nat))
    (hCoverSmall : ∀ (c : QVal) (m : Nat), (c, m) ∈ cover →
      QVal.le 0 c ∧ QVal.le c 1 ∧ QVal.le (QVal.dist (g m c) 0) (QVal.unitFrac (2 * k + 1)))
    (hCovers : ∀ x : QVal, QVal.le 0 x → QVal.le x 1 →
      ∃ p ∈ cover, QVal.le (QVal.dist x p.1) (QVal.unitFrac ((cont p.2).modulus (2 * k + 1)))) :
    ∀ (n : Nat) (x : QVal),
      maxCoverStage cover ≤ n →
      QVal.le 0 x → QVal.le x 1 →
      QVal.le (QVal.dist (g n x) 0) (QVal.unitFrac k) := by
  intro n x hn hx0 hx1
  rcases hCovers x hx0 hx1 with ⟨⟨c, m⟩, hMem, hDistXC⟩
  rcases hCoverSmall c m hMem with ⟨hc0, hc1, hCenterSmall⟩
  have hmLeN : m ≤ n := Nat.le_trans (mem_le_maxCoverStage hMem) hn
  have hContStep : QVal.le (QVal.dist (g m x) (g m c)) (QVal.unitFrac (2 * k + 1)) :=
    (cont m).spec (2 * k + 1) x c hx0 hx1 hc0 hc1 hDistXC
  have hTri := QVal.dist_triangle (g m x) (g m c) 0
  have hSum := QVal.le_trans (QVal.add_le_add hContStep hCenterSmall) (QVal.unitFrac_half_sum k)
  have hGmBound : QVal.le (QVal.dist (g m x) 0) (QVal.unitFrac k) := QVal.le_trans hTri hSum
  have hGnLeGm : QVal.le (QVal.dist (g n x) 0) (QVal.dist (g m x) 0) :=
    QVal.le_of_eqv_right
      (QVal.dist_le_of_between (hNonneg n x) (hMono x hmLeN))
      (QVal.dist_symm 0 (g m x))
  exact QVal.le_trans hGnLeGm hGmBound

end Antipodes
end SandersNSA
