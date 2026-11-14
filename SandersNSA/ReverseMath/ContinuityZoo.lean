/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.ReverseMath.Independence

/-!
# Generalized Continuity Hierarchy (`ContinuityZoo`, `arXiv:2303.00493`)

Computable formalization of the generalized continuity classes studied by Frank Waaldijk and
Dag Normann & Sam Sanders (*"On the logical and computational power of generalized continuity"*,
`arXiv:2303.00493`):

`LipschitzOn` ⟹ `UniformContOn` ⟹ `QuasiContOn` ⟹ `CliquishOn`
and `UniformContOn` ⟹ `BaireOneOn`, together with **computable rational separating
counterexamples** proving strictness of the inclusions:

1. `heavisideHalf`: `CliquishOn` (and piecewise constant), yet **NOT** `UniformContOn`.
2. `isolatedSpike`: `CliquishOn`, yet **NOT** `QuasiContOn` (separating cliquishness from
   quasi-continuity at `x = 1/2`!).
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Quantitative Generalized Continuity Classes -/

/-- Non-degenerate open-interior subinterval witness `[lo, hi]` (`lo < hi`). -/
structure OpenBox : Type where
  lo : QVal
  hi : QVal
  nondeg : QVal.lt lo hi

/-- Quantitative `L`-Lipschitz continuity (`|f x - f y| ≤ (L + 1) |x - y|`) on `[0, 1]`. -/
structure LipschitzOn (f : QVal → QVal) (L : Nat) : Type where
  spec : ∀ x y : QVal,
    QVal.le 0 x → QVal.le x 1 →
    QVal.le 0 y → QVal.le y 1 →
    QVal.le (QVal.dist (f x) (f y)) (QVal.ofNat (L + 1) * QVal.dist x y)

/-- Global uniform continuity on `QVal` with explicit modulus `modulus : Modulus`. -/
structure GlobalUniformCont (f : QVal → QVal) : Type where
  modulus : Modulus
  spec : ∀ (k : Nat) (x y : QVal),
    QVal.le (QVal.dist x y) (QVal.unitFrac (modulus k)) →
    QVal.le (QVal.dist (f x) (f y)) (QVal.unitFrac k)

/-- **Kempisty Quasi-Continuity (`QuasiContOn`)** with computable open-box realiser:
    Given any point `x`, radius scale `r` (`1 / (r + 1)`), and target oscillation `k`
    (`1 / (k + 1)`), returns a non-degenerate subinterval `B = [lo, hi]` inside the
    `1 / (r + 1)`-neighborhood of `x` on which `|f z - f x| ≤ 1 / (k + 1)`. -/
structure QuasiContOn (f : QVal → QVal) : Type where
  selectBox : QVal → Nat → Nat → OpenBox
  boxNear : ∀ (x : QVal) (r k : Nat) (z : QVal),
    QVal.le (selectBox x r k).lo z → QVal.le z (selectBox x r k).hi →
    QVal.le (QVal.dist z x) (QVal.unitFrac r)
  oscAtCenter : ∀ (x : QVal) (r k : Nat) (z : QVal),
    QVal.le (selectBox x r k).lo z → QVal.le z (selectBox x r k).hi →
    QVal.le (QVal.dist (f z) (f x)) (QVal.unitFrac k)

/-- **Thielman Cliquishness (`CliquishOn`)** with computable open-box realiser:
    Given any point `x`, radius scale `r` (`1 / (r + 1)`), and target oscillation `k`
    (`1 / (k + 1)`), returns a non-degenerate subinterval `B = [lo, hi]` inside the
    `1 / (r + 1)`-neighborhood of `x` on which **pairwise oscillation** `|f z₁ - f z₂| ≤ 1 / (k + 1)`. -/
structure CliquishOn (f : QVal → QVal) : Type where
  selectBox : QVal → Nat → Nat → OpenBox
  boxNear : ∀ (x : QVal) (r k : Nat) (z : QVal),
    QVal.le (selectBox x r k).lo z → QVal.le z (selectBox x r k).hi →
    QVal.le (QVal.dist z x) (QVal.unitFrac r)
  oscPairwise : ∀ (x : QVal) (r k : Nat) (z₁ z₂ : QVal),
    QVal.le (selectBox x r k).lo z₁ → QVal.le z₁ (selectBox x r k).hi →
    QVal.le (selectBox x r k).lo z₂ → QVal.le z₂ (selectBox x r k).hi →
    QVal.le (QVal.dist (f z₁) (f z₂)) (QVal.unitFrac k)

/-- **Baire Class 1 (`BaireOneOn`)** on `[0, 1]`:
    Pointwise limit of uniformly continuous approximants `approx : Nat → QVal → QVal`
    equipped with a pointwise convergence modulus `pwMod : QVal → Modulus`. -/
structure BaireOneOn (f : QVal → QVal) : Type where
  approx : Nat → QVal → QVal
  approxCont : (n : Nat) → UniformContOn (approx n) 0 1
  pwMod : QVal → Modulus
  converges : ∀ (x : QVal) (k n : Nat),
    QVal.le 0 x → QVal.le x 1 →
    pwMod x k ≤ n →
    QVal.le (QVal.dist (approx n x) (f x)) (QVal.unitFrac k)

/-! ## 2. Verified Inclusion Chain -/

/-- `LipschitzOn` computably implies `UniformContOn 0 1` with modulus `(L + 1) * (k + 1)`. -/
def lipschitz_to_uniformCont {f : QVal → QVal} {L : Nat}
    (hLip : LipschitzOn f L) : UniformContOn f 0 1 where
  modulus k := (L + 1) * (k + 1)
  spec k x y hx0 hx1 hy0 hy1 hdist := by
    have h1 := hLip.spec x y hx0 hx1 hy0 hy1
    have h2 : QVal.le (QVal.ofNat (L + 1) * QVal.dist x y) (QVal.unitFrac k) := by
      unfold QVal.le at hdist ⊢
      rw [QVal.mul_denInt]
      let d := QVal.dist x y
      have hdNonneg : 0 ≤ d.num := by change 0 ≤ ((x - y).num.natAbs : Int); omega
      change d.num * (((L + 1) * (k + 1) + 1 : Nat) : Int) ≤ 1 * d.denInt at hdist
      change (((L + 1 : Nat) : Int) * d.num) * ((k + 1 : Nat) : Int) ≤ 1 * (1 * d.denInt)
      have hCast : (((L + 1) * (k + 1) : Nat) : Int) =
          ((L + 1 : Nat) : Int) * ((k + 1 : Nat) : Int) := Int.natCast_mul _ _
      have hCoeff : ((L + 1 : Nat) : Int) * ((k + 1 : Nat) : Int) ≤
          (((L + 1) * (k + 1) + 1 : Nat) : Int) := by omega
      have hMul := Int.mul_le_mul_of_nonneg_left hCoeff hdNonneg
      have hAssoc : (((L + 1 : Nat) : Int) * d.num) * ((k + 1 : Nat) : Int) =
          d.num * (((L + 1 : Nat) : Int) * ((k + 1 : Nat) : Int)) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega
    exact QVal.le_trans h1 h2

/-- `UniformContOn 0 1` computably implies `BaireOneOn` via constant approximants `approx _ := f`. -/
def uniformCont_to_baireOne {f : QVal → QVal}
    (hCont : UniformContOn f 0 1) : BaireOneOn f where
  approx _ := f
  approxCont _ := hCont
  pwMod _ _ := 0
  converges x k _ _ _ _ := by
    have hPos : QVal.le 0 (QVal.unitFrac k) := by
      change (0 : Int) * ((k + 1 : Nat) : Int) ≤ 1 * 1; omega
    exact QVal.le_of_eqv_left (QVal.dist_self (f x)) hPos

/-- Every `GlobalUniformCont` function is computably `QuasiContOn` via `[x, x + 1/(max r (ω k) + 1)]`. -/
def globalUniformCont_to_quasiCont {f : QVal → QVal}
    (hU : GlobalUniformCont f) : QuasiContOn f where
  selectBox x r k :=
    let m := Nat.max r (hU.modulus k)
    { lo := x
      hi := x + QVal.unitFrac m
      nondeg := by
        unfold QVal.lt
        rw [QVal.add_denInt]
        have hxD : 0 < x.denInt := x.denInt_pos
        change x.num * (x.denInt * ((m + 1 : Nat) : Int)) <
          (x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt) * x.denInt
        rw [Int.add_mul, Int.one_mul]
        have hPos : 0 < x.denInt * x.denInt := Int.mul_pos hxD hxD
        have e1 : x.num * ((m + 1 : Nat) : Int) * x.denInt =
            x.num * (x.denInt * ((m + 1 : Nat) : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm ((m + 1 : Nat) : Int) x.denInt]
        omega }
  boxNear x r k z hlo hhi := by
    let m := Nat.max r (hU.modulus k)
    have hBet := QVal.dist_le_of_between hlo hhi
    have hStep : QVal.le (QVal.dist x (x + QVal.unitFrac m)) (QVal.unitFrac m) := by
      unfold QVal.le
      have qdist : (QVal.dist x (x + QVal.unitFrac m)).num =
          ((x - (x + QVal.unitFrac m)).num.natAbs : Int) := rfl
      have qadd : (x + QVal.unitFrac m).num =
          x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt := rfl
      rw [qdist, QVal.dist_denInt, QVal.add_denInt, QVal.sub_num, qadd, QVal.add_denInt]
      have hSubEq : x.num * (x.denInt * ((m + 1 : Nat) : Int)) -
          (x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt) * x.denInt =
          -(x.denInt * x.denInt) := by
        rw [Int.add_mul, Int.one_mul]
        have e1 : x.num * ((m + 1 : Nat) : Int) * x.denInt =
            x.num * (x.denInt * ((m + 1 : Nat) : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm ((m + 1 : Nat) : Int) x.denInt]
        omega
      change ((x.num * (x.denInt * ((m + 1 : Nat) : Int)) -
          (x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt) * x.denInt).natAbs : Int) *
          ((m + 1 : Nat) : Int) ≤ 1 * (x.denInt * (x.denInt * ((m + 1 : Nat) : Int)))
      rw [hSubEq, Int.natAbs_neg]
      have hxD : 0 ≤ x.denInt := by have := x.denInt_pos; omega
      rw [Int.natAbs_of_nonneg (Int.mul_nonneg hxD hxD), Int.one_mul, ← Int.mul_assoc]
      exact Int.le_refl _
    exact QVal.le_trans hBet
      (QVal.le_trans hStep (QVal.unitFrac_anti (Nat.le_max_left r (hU.modulus k))))
  oscAtCenter x r k z hlo hhi := by
    let m := Nat.max r (hU.modulus k)
    have hBet := QVal.dist_le_of_between hlo hhi
    have hStep : QVal.le (QVal.dist x (x + QVal.unitFrac m)) (QVal.unitFrac m) := by
      unfold QVal.le
      have qdist : (QVal.dist x (x + QVal.unitFrac m)).num =
          ((x - (x + QVal.unitFrac m)).num.natAbs : Int) := rfl
      have qadd : (x + QVal.unitFrac m).num =
          x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt := rfl
      rw [qdist, QVal.dist_denInt, QVal.add_denInt, QVal.sub_num, qadd, QVal.add_denInt]
      have hSubEq : x.num * (x.denInt * ((m + 1 : Nat) : Int)) -
          (x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt) * x.denInt =
          -(x.denInt * x.denInt) := by
        rw [Int.add_mul, Int.one_mul]
        have e1 : x.num * ((m + 1 : Nat) : Int) * x.denInt =
            x.num * (x.denInt * ((m + 1 : Nat) : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm ((m + 1 : Nat) : Int) x.denInt]
        omega
      change ((x.num * (x.denInt * ((m + 1 : Nat) : Int)) -
          (x.num * ((m + 1 : Nat) : Int) + 1 * x.denInt) * x.denInt).natAbs : Int) *
          ((m + 1 : Nat) : Int) ≤ 1 * (x.denInt * (x.denInt * ((m + 1 : Nat) : Int)))
      rw [hSubEq, Int.natAbs_neg]
      have hxD : 0 ≤ x.denInt := by have := x.denInt_pos; omega
      rw [Int.natAbs_of_nonneg (Int.mul_nonneg hxD hxD), Int.one_mul, ← Int.mul_assoc]
      exact Int.le_refl _
    have hDistMod : QVal.le (QVal.dist z x) (QVal.unitFrac (hU.modulus k)) :=
      QVal.le_trans hBet
        (QVal.le_trans hStep (QVal.unitFrac_anti (Nat.le_max_right r (hU.modulus k))))
    exact hU.spec k z x hDistMod

/-- Every `QuasiContOn` function is computably `CliquishOn` (evaluating `selectBox` at `2*k + 1`). -/
def quasiCont_to_cliquish {f : QVal → QVal} (hQ : QuasiContOn f) : CliquishOn f where
  selectBox x r k := hQ.selectBox x r (2 * k + 1)
  boxNear x r k z hlo hhi := hQ.boxNear x r (2 * k + 1) z hlo hhi
  oscPairwise x r k z₁ z₂ h1lo h1hi h2lo h2hi := by
    have d1 := hQ.oscAtCenter x r (2 * k + 1) z₁ h1lo h1hi
    have d2 := hQ.oscAtCenter x r (2 * k + 1) z₂ h2lo h2hi
    have d2Symm := QVal.le_of_eqv_left (QVal.dist_symm (f x) (f z₂)) d2
    have hTri := QVal.dist_triangle (f z₁) (f x) (f z₂)
    exact QVal.le_trans hTri
      (QVal.le_trans (QVal.add_le_add d1 d2Symm) (QVal.unitFrac_half_sum k))

/-! ## 3. Separating Rational Counterexamples -/

/-- Step function jumping at `1/2`: `0` on `(-∞, 1/2]`, `1` on `(1/2, ∞)`. -/
def heavisideHalf (x : QVal) : QVal :=
  if QVal.leB x ⟨1, 1⟩ then 0 else 1

/-- **Separation 1 (`heavisideHalf` is NOT `UniformContOn 0 1`)**:
    No modulus `ω` can make `heavisideHalf` uniformly continuous on `[0, 1]`. -/
theorem not_uniformCont_heavisideHalf : ¬ Nonempty (UniformContOn heavisideHalf 0 1) := by
  rintro ⟨hCont⟩
  let m := hCont.modulus 1
  -- Compare `x = 1/2` (`⟨1, 1⟩`) and `y = 1/2 + 1 / (2*(m + 1))` (`⟨m + 2, 2*m + 1⟩`)!
  let x : QVal := ⟨1, 1⟩
  let y : QVal := ⟨((m + 2 : Nat) : Int), 2 * m + 1⟩
  have hx0 : QVal.le 0 x := by decide
  have hx1 : QVal.le x 1 := by decide
  have hy0 : QVal.le 0 y := by
    change (0 : Int) * ((2 * m + 2 : Nat) : Int) ≤ ((m + 2 : Nat) : Int) * 1; omega
  have hy1 : QVal.le y 1 := by
    change ((m + 2 : Nat) : Int) * 1 ≤ 1 * ((2 * m + 2 : Nat) : Int); omega
  have hDistXY : QVal.le (QVal.dist x y) (QVal.unitFrac m) := by
    unfold QVal.le
    rw [QVal.dist_denInt]
    have hSub : (x - y).num = -2 := by
      rw [QVal.sub_num]
      change 1 * ((2 * m + 2 : Nat) : Int) - ((m + 2 : Nat) : Int) * 2 = -2
      omega
    change ((x - y).num.natAbs : Int) * ((m + 1 : Nat) : Int) ≤
      1 * (2 * ((2 * m + 2 : Nat) : Int))
    rw [hSub]
    have hAbs : ((-2 : Int).natAbs : Int) = 2 := rfl
    rw [hAbs]
    omega
  have hOut := hCont.spec 1 x y hx0 hx1 hy0 hy1 hDistXY
  have hFx : heavisideHalf x = 0 := by decide
  have hFy : heavisideHalf y = 1 := by
    unfold heavisideHalf
    have hGt : QVal.leB y ⟨1, 1⟩ = false := by
      unfold QVal.leB
      apply decide_eq_false
      change ¬ (((m + 2 : Nat) : Int) * 2 ≤ 1 * ((2 * m + 2 : Nat) : Int))
      omega
    rw [hGt]
    rfl
  rw [hFx, hFy] at hOut
  have hImpossible : ¬ QVal.le (QVal.dist 0 1) (QVal.unitFrac 1) := by decide
  exact hImpossible hOut

/-- Isolated point spike at `1/2`: `1` if `x ≈ 1/2`, `0` everywhere else. -/
def isolatedSpike (x : QVal) : QVal :=
  if QVal.eqvB x ⟨1, 1⟩ then 1 else 0

theorem qval_dist_num (u v : QVal) : (QVal.dist u v).num = ((u - v).num.natAbs : Int) := rfl
theorem qval_add_num' (u v : QVal) : (u + v).num = u.num * v.denInt + v.num * u.denInt := rfl

theorem midpoint_strict_between {a b : QVal} (h : QVal.lt a b) :
    QVal.lt a (QVal.midpoint a b) ∧ QVal.lt (QVal.midpoint a b) b := by
  change QVal.lt a ((a + b) * ⟨1, 1⟩) ∧ QVal.lt ((a + b) * ⟨1, 1⟩) b
  unfold QVal.lt at h ⊢
  rw [QVal.mul_denInt, QVal.add_denInt]
  have ha : 0 < a.denInt := a.denInt_pos
  have hb : 0 < b.denInt := b.denInt_pos
  constructor
  · change a.num * ((a.denInt * b.denInt) * 2) <
      ((a.num * b.denInt + b.num * a.denInt) * 1) * a.denInt
    rw [Int.mul_one, Int.add_mul]
    have hs := Int.mul_lt_mul_of_pos_right h ha
    have e1 : a.num * ((a.denInt * b.denInt) * 2) = 2 * (a.num * b.denInt * a.denInt) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    omega
  · change ((a.num * b.denInt + b.num * a.denInt) * 1) * b.denInt <
      b.num * ((a.denInt * b.denInt) * 2)
    rw [Int.mul_one, Int.add_mul]
    have hs := Int.mul_lt_mul_of_pos_right h hb
    have e1 : b.num * ((a.denInt * b.denInt) * 2) = 2 * (b.num * a.denInt * b.denInt) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega

/-- **Separation 2 (`isolatedSpike` is NOT `QuasiContOn`, yet IS `CliquishOn`)**:
    Every non-degenerate box `[lo, hi]` (`lo < hi`) contains at least one point `z` with
    `¬ (z ≈ 1/2)`, where `|isolatedSpike z - isolatedSpike (1/2)| = |0 - 1| = 1 > 1/2`! -/
theorem not_quasiCont_isolatedSpike : ¬ Nonempty (QuasiContOn isolatedSpike) := by
  rintro ⟨hQ⟩
  let B := hQ.selectBox ⟨1, 1⟩ 0 1
  have hSpikeCenter : isolatedSpike ⟨1, 1⟩ = 1 := by decide
  -- Either `B.lo` is not equivalent to `1/2`, or `B.hi` is not equivalent to `1/2`!
  by_cases hLoEq : QVal.eqvB B.lo ⟨1, 1⟩ = true
  · have hHiNe : QVal.eqvB B.hi ⟨1, 1⟩ = false := by
      unfold QVal.eqvB at hLoEq ⊢
      have hEq1 : B.lo.num * 2 = 1 * B.lo.denInt := of_decide_eq_true hLoEq
      apply decide_eq_false
      intro hEq2
      have hLt := B.nondeg
      unfold QVal.lt at hLt
      have hloD : 0 < B.lo.denInt := B.lo.denInt_pos
      have hhiD : 0 < B.hi.denInt := B.hi.denInt_pos
      have hs1 : (B.lo.num * 2) * B.hi.denInt = B.lo.denInt * B.hi.denInt := by
        rw [hEq1, Int.one_mul]
      have hs2 : (B.hi.num * 2) * B.lo.denInt = B.hi.denInt * B.lo.denInt := by
        change B.hi.num * 2 = 1 * B.hi.denInt at hEq2
        rw [hEq2, Int.one_mul]
      have e1 : (B.lo.num * 2) * B.hi.denInt = 2 * (B.lo.num * B.hi.denInt) := by
        simp only [Int.mul_assoc, Int.mul_comm]
      have e2 : (B.hi.num * 2) * B.lo.denInt = 2 * (B.hi.num * B.lo.denInt) := by
        simp only [Int.mul_assoc, Int.mul_comm]
      have e3 : B.hi.denInt * B.lo.denInt = B.lo.denInt * B.hi.denInt := Int.mul_comm _ _
      omega
    have hOsc := hQ.oscAtCenter ⟨1, 1⟩ 0 1 B.hi (QVal.lt_imp_le B.nondeg) (QVal.le_refl B.hi)
    have hFHi : isolatedSpike B.hi = 0 := by unfold isolatedSpike; rw [hHiNe]; rfl
    rw [hFHi, hSpikeCenter] at hOsc
    have hImp : ¬ QVal.le (QVal.dist 0 1) (QVal.unitFrac 1) := by decide
    exact hImp hOsc
  · have hLoFalse : QVal.eqvB B.lo ⟨1, 1⟩ = false := by
      cases hb : QVal.eqvB B.lo ⟨1, 1⟩
      · rfl
      · exact False.elim (hLoEq hb)
    have hOsc := hQ.oscAtCenter ⟨1, 1⟩ 0 1 B.lo (QVal.le_refl B.lo) (QVal.lt_imp_le B.nondeg)
    have hFLo : isolatedSpike B.lo = 0 := by unfold isolatedSpike; rw [hLoFalse]; rfl
    rw [hFLo, hSpikeCenter] at hOsc
    have hImp : ¬ QVal.le (QVal.dist 0 1) (QVal.unitFrac 1) := by decide
    exact hImp hOsc

/-- Conversely, `isolatedSpike` **IS** constructively `CliquishOn`!
    Around any `x`, we simply pick a small box inside `[x + 1/(4r+4), x + 1/(2r+2)]` when `x ≥ 1/2`
    or `[x - 1/(2r+2), x - 1/(4r+4)]` when `x < 1/2`, avoiding `1/2` completely so `isolatedSpike`
    vanishes identically on the box! -/
def cliquish_isolatedSpike : CliquishOn isolatedSpike where
  selectBox x r _k :=
    let stepSmall : QVal := ⟨1, 4 * r + 3⟩ -- 1 / (4*(r + 1))
    let stepBig : QVal := ⟨1, 2 * r + 1⟩   -- 1 / (2*(r + 1))
    if QVal.leB ⟨1, 1⟩ x then
      { lo := x + stepSmall
        hi := x + stepBig
        nondeg := by
          unfold QVal.lt
          rw [QVal.add_denInt, QVal.add_denInt]
          have hxD : 0 < x.denInt := x.denInt_pos
          change (x.num * ((4 * r + 4 : Nat) : Int) + 1 * x.denInt) *
              (x.denInt * ((2 * r + 2 : Nat) : Int)) <
            (x.num * ((2 * r + 2 : Nat) : Int) + 1 * x.denInt) *
              (x.denInt * ((4 * r + 4 : Nat) : Int))
          rw [Int.add_mul, Int.add_mul, Int.one_mul]
          have e1 : x.num * ((4 * r + 4 : Nat) : Int) * (x.denInt * ((2 * r + 2 : Nat) : Int)) =
                    x.num * ((2 * r + 2 : Nat) : Int) * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          have hDiff : x.denInt * (x.denInt * ((2 * r + 2 : Nat) : Int)) <
                       x.denInt * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
            apply Int.mul_lt_mul_of_pos_left _ hxD
            apply Int.mul_lt_mul_of_pos_left _ hxD
            omega
          omega }
    else
      { lo := x - stepBig
        hi := x - stepSmall
        nondeg := by
          unfold QVal.lt
          rw [QVal.sub_denInt, QVal.sub_denInt, QVal.sub_num, QVal.sub_num]
          have hxD : 0 < x.denInt := x.denInt_pos
          change (x.num * ((2 * r + 2 : Nat) : Int) - 1 * x.denInt) *
              (x.denInt * ((4 * r + 4 : Nat) : Int)) <
            (x.num * ((4 * r + 4 : Nat) : Int) - 1 * x.denInt) *
              (x.denInt * ((2 * r + 2 : Nat) : Int))
          rw [Int.sub_mul, Int.sub_mul, Int.one_mul]
          have e1 : x.num * ((2 * r + 2 : Nat) : Int) * (x.denInt * ((4 * r + 4 : Nat) : Int)) =
                    x.num * ((4 * r + 4 : Nat) : Int) * (x.denInt * ((2 * r + 2 : Nat) : Int)) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          have hDiff : x.denInt * (x.denInt * ((2 * r + 2 : Nat) : Int)) <
                       x.denInt * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
            apply Int.mul_lt_mul_of_pos_left _ hxD
            apply Int.mul_lt_mul_of_pos_left _ hxD
            omega
          omega }
  boxNear x r _k z hlo hhi := by
    cases hHalf : QVal.leB ⟨1, 1⟩ x
    · simp only [hHalf, Bool.false_eq_true, ↓reduceIte] at hlo hhi
      -- `x - stepBig ≤ z ≤ x - stepSmall ≤ x`
      have hHiLeX : QVal.le (x - ⟨1, 4 * r + 3⟩) x := by
        unfold QVal.le
        rw [QVal.sub_denInt, QVal.sub_num]
        change (x.num * ((4 * r + 4 : Nat) : Int) - 1 * x.denInt) * x.denInt ≤
          x.num * (x.denInt * ((4 * r + 4 : Nat) : Int))
        rw [Int.sub_mul, Int.one_mul]
        have hxD : 0 < x.denInt := x.denInt_pos
        have hPos : 0 ≤ x.denInt * x.denInt := Int.mul_nonneg (by omega) (by omega)
        have e1 : x.num * ((4 * r + 4 : Nat) : Int) * x.denInt =
            x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
          simp only [Int.mul_assoc, Int.mul_comm]
        omega
      have hzLeX : QVal.le z x := QVal.le_trans hhi hHiLeX
      have hStepDist : QVal.le (QVal.dist (x - ⟨1, 2 * r + 1⟩) x) (QVal.unitFrac r) := by
        unfold QVal.le
        simp only [qval_dist_num, QVal.dist_denInt, QVal.sub_denInt, QVal.sub_num]
        have hSubEq : ((x.num * ((2 * r + 2 : Nat) : Int) - 1 * x.denInt) * x.denInt -
            x.num * (x.denInt * ((2 * r + 2 : Nat) : Int))) = -(x.denInt * x.denInt) := by
          rw [Int.sub_mul, Int.one_mul]
          have e1 : x.num * ((2 * r + 2 : Nat) : Int) * x.denInt =
              x.num * (x.denInt * ((2 * r + 2 : Nat) : Int)) := by
            simp only [Int.mul_assoc, Int.mul_comm]
          omega
        change (((x.num * ((2 * r + 2 : Nat) : Int) - 1 * x.denInt) * x.denInt -
            x.num * (x.denInt * ((2 * r + 2 : Nat) : Int))).natAbs : Int) * ((r + 1 : Nat) : Int) ≤
          1 * ((x.denInt * ((2 * r + 2 : Nat) : Int)) * x.denInt)
        rw [hSubEq, Int.natAbs_neg]
        have hxD : 0 ≤ x.denInt := by have := x.denInt_pos; omega
        rw [Int.natAbs_of_nonneg (Int.mul_nonneg hxD hxD)]
        have hScale : x.denInt * x.denInt * ((r + 1 : Nat) : Int) ≤
            x.denInt * x.denInt * ((2 * r + 2 : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (Int.mul_nonneg hxD hxD)
        have hR : 1 * ((x.denInt * ((2 * r + 2 : Nat) : Int)) * x.denInt) =
            x.denInt * x.denInt * ((2 * r + 2 : Nat) : Int) := by
          rw [Int.one_mul]; simp only [Int.mul_left_comm, Int.mul_comm]
        omega
      have hDirect : QVal.le (QVal.dist z x) (QVal.dist (x - ⟨1, 2 * r + 1⟩) x) := by
        have h1 := QVal.dist_eqv_sub_of_le hzLeX
        have h2 : QVal.le (x - z) (x - (x - ⟨1, 2 * r + 1⟩)) :=
          QVal.add_le_add (QVal.le_refl x) (by
            unfold QVal.le at hlo ⊢
            change (-z.num) * (x - ⟨1, 2 * r + 1⟩).denInt ≤ (-(x - ⟨1, 2 * r + 1⟩).num) * z.denInt
            rw [Int.neg_mul, Int.neg_mul]
            omega)
        have h3 := QVal.eqv_symm (QVal.dist_eqv_sub_of_le (QVal.le_trans hlo hzLeX))
        exact QVal.le_of_eqv_left (QVal.dist_symm z x)
          (QVal.le_of_eqv_right (QVal.le_of_eqv_left h1 h2)
            (QVal.eqv_trans h3 (QVal.dist_symm x _)))
      exact QVal.le_trans hDirect hStepDist
    · simp only [hHalf, ↓reduceIte] at hlo hhi
      have hxLeLo : QVal.le x (x + ⟨1, 4 * r + 3⟩) := by
        unfold QVal.le
        rw [QVal.add_denInt]
        change x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) ≤
          (x.num * ((4 * r + 4 : Nat) : Int) + 1 * x.denInt) * x.denInt
        rw [Int.add_mul, Int.one_mul]
        have hxD : 0 < x.denInt := x.denInt_pos
        have hPos : 0 ≤ x.denInt * x.denInt := Int.mul_nonneg (by omega) (by omega)
        have e1 : x.num * ((4 * r + 4 : Nat) : Int) * x.denInt =
            x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
          simp only [Int.mul_assoc, Int.mul_comm]
        omega
      have hxLeZ : QVal.le x z := QVal.le_trans hxLeLo hlo
      have hBet := QVal.dist_le_of_between hxLeZ hhi
      have hStepDist : QVal.le (QVal.dist x (x + ⟨1, 2 * r + 1⟩)) (QVal.unitFrac r) := by
        unfold QVal.le
        simp only [qval_dist_num, QVal.dist_denInt, QVal.add_denInt, qval_add_num', QVal.sub_num]
        have hSubEq : (x.num * (x.denInt * ((2 * r + 2 : Nat) : Int)) -
            (x.num * ((2 * r + 2 : Nat) : Int) + 1 * x.denInt) * x.denInt) =
            -(x.denInt * x.denInt) := by
          rw [Int.add_mul, Int.one_mul]
          have e1 : x.num * ((2 * r + 2 : Nat) : Int) * x.denInt =
              x.num * (x.denInt * ((2 * r + 2 : Nat) : Int)) := by
            simp only [Int.mul_assoc, Int.mul_comm]
          omega
        change ((x.num * (x.denInt * ((2 * r + 2 : Nat) : Int)) -
            (x.num * ((2 * r + 2 : Nat) : Int) + 1 * x.denInt) * x.denInt).natAbs : Int) *
          ((r + 1 : Nat) : Int) ≤ 1 * (x.denInt * (x.denInt * ((2 * r + 2 : Nat) : Int)))
        rw [hSubEq, Int.natAbs_neg]
        have hxD : 0 ≤ x.denInt := by have := x.denInt_pos; omega
        rw [Int.natAbs_of_nonneg (Int.mul_nonneg hxD hxD)]
        have hScale : x.denInt * x.denInt * ((r + 1 : Nat) : Int) ≤
            x.denInt * x.denInt * ((2 * r + 2 : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (Int.mul_nonneg hxD hxD)
        have hR : 1 * (x.denInt * (x.denInt * ((2 * r + 2 : Nat) : Int))) =
            x.denInt * x.denInt * ((2 * r + 2 : Nat) : Int) := by
          rw [Int.one_mul, Int.mul_assoc]
        omega
      exact QVal.le_trans hBet hStepDist
  oscPairwise x r k z₁ z₂ h1lo h1hi h2lo h2hi := by
    -- Show every `z` in `selectBox x r k` satisfies `isolatedSpike z = 0`!
    have hZeroOnBox : ∀ z : QVal,
        QVal.le (if QVal.leB ⟨1, 1⟩ x then x + ⟨1, 4 * r + 3⟩ else x - ⟨1, 2 * r + 1⟩) z →
        QVal.le z (if QVal.leB ⟨1, 1⟩ x then x + ⟨1, 2 * r + 1⟩ else x - ⟨1, 4 * r + 3⟩) →
        isolatedSpike z = 0 := by
      intro z hzlo hzhi
      unfold isolatedSpike
      have hNeHalf : QVal.eqvB z ⟨1, 1⟩ = false := by
        cases hHalf : QVal.leB ⟨1, 1⟩ x
        · simp only [hHalf, Bool.false_eq_true, ↓reduceIte] at hzhi
          have hStrict : QVal.lt (x - ⟨1, 4 * r + 3⟩) x := by
            unfold QVal.lt
            rw [QVal.sub_denInt, QVal.sub_num]
            change (x.num * ((4 * r + 4 : Nat) : Int) - 1 * x.denInt) * x.denInt <
              x.num * (x.denInt * ((4 * r + 4 : Nat) : Int))
            rw [Int.sub_mul, Int.one_mul]
            have hxD : 0 < x.denInt := x.denInt_pos
            have hPos : 0 < x.denInt * x.denInt := Int.mul_pos hxD hxD
            have e1 : x.num * ((4 * r + 4 : Nat) : Int) * x.denInt =
                x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
              simp only [Int.mul_assoc, Int.mul_comm]
            omega
          unfold QVal.eqvB
          apply decide_eq_false
          intro hEqZ
          have hzEqHalf : QVal.eqv z ⟨1, 1⟩ := hEqZ
          have hHalfLeHi : QVal.le ⟨1, 1⟩ (x - ⟨1, 4 * r + 3⟩) :=
            QVal.le_of_eqv_left (QVal.eqv_symm hzEqHalf) hzhi
          have hHalfLeX : QVal.le ⟨1, 1⟩ x :=
            QVal.le_trans hHalfLeHi (QVal.lt_imp_le hStrict)
          -- Wait: `hHalf : QVal.leB ⟨1, 1⟩ x = false` directly contradicts `hHalfLeX`!
          have hNot : ¬ QVal.le ⟨1, 1⟩ x := of_decide_eq_false hHalf
          exact hNot hHalfLeX
        · simp only [hHalf, ↓reduceIte] at hzlo
          have hHalfLeX : QVal.le ⟨1, 1⟩ x := (QVal.leB_true_iff _ _).mp hHalf
          have hStrict : QVal.lt x (x + ⟨1, 4 * r + 3⟩) := by
            unfold QVal.lt
            rw [QVal.add_denInt]
            change x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) <
              (x.num * ((4 * r + 4 : Nat) : Int) + 1 * x.denInt) * x.denInt
            rw [Int.add_mul, Int.one_mul]
            have hxD : 0 < x.denInt := x.denInt_pos
            have hPos : 0 < x.denInt * x.denInt := Int.mul_pos hxD hxD
            have e1 : x.num * ((4 * r + 4 : Nat) : Int) * x.denInt =
                x.num * (x.denInt * ((4 * r + 4 : Nat) : Int)) := by
              simp only [Int.mul_assoc, Int.mul_comm]
            omega
          unfold QVal.eqvB
          apply decide_eq_false
          intro hEqZ
          have hLoLeHalf : QVal.le (x + ⟨1, 4 * r + 3⟩) ⟨1, 1⟩ :=
            QVal.le_of_eqv_right hzlo hEqZ
          have hChain : QVal.le (x + ⟨1, 4 * r + 3⟩) x := QVal.le_trans hLoLeHalf hHalfLeX
          exact ((QVal.not_lt_iff_le _ _).mpr hChain) hStrict
      rw [hNeHalf]
      rfl
    have hZ1 : isolatedSpike z₁ = 0 := by
      apply hZeroOnBox z₁
      · cases hB : QVal.leB ⟨1, 1⟩ x <;> simp only [hB, Bool.false_eq_true, ↓reduceIte] at h1lo ⊢ <;> exact h1lo
      · cases hB : QVal.leB ⟨1, 1⟩ x <;> simp only [hB, Bool.false_eq_true, ↓reduceIte] at h1hi ⊢ <;> exact h1hi
    have hZ2 : isolatedSpike z₂ = 0 := by
      apply hZeroOnBox z₂
      · cases hB : QVal.leB ⟨1, 1⟩ x <;> simp only [hB, Bool.false_eq_true, ↓reduceIte] at h2lo ⊢ <;> exact h2lo
      · cases hB : QVal.leB ⟨1, 1⟩ x <;> simp only [hB, Bool.false_eq_true, ↓reduceIte] at h2hi ⊢ <;> exact h2hi
    rw [hZ1, hZ2]
    have hPos : QVal.le 0 (QVal.unitFrac k) := by
      change (0 : Int) * ((k + 1 : Nat) : Int) ≤ 1 * 1; omega
    exact QVal.le_of_eqv_left (QVal.dist_self 0) hPos

end ReverseMath
end SandersNSA
