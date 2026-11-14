/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Computable Exact Rationals & Bishop-Style Modulus-Bearing Analysis

Provides the dependency-free computable foundation for `SandersNSA.Antipodes`,
`SandersNSA.Tactic`, and `SandersNSA.ReverseMath`:

1. **`QVal`**: Exact computable rational numbers `num / (denPos + 1)` with zero `Nat.sub`
   truncation (`(a * b + a + b) + 1 = (a + 1) * (b + 1)`), decidable equality/order,
   normalized formatting, unit fractions `1 / (k + 1)`, dyadic scales `1 / 2^k`, and
   verified metric laws (`dist_self`, `dist_symm`, `dist_triangle`).
2. **Bishop Modulus-Bearing Structures (`Type`-valued, never erased into `Prop`)**:
   - `UniformContOn`: uniform continuity on `[a, b]` with explicit modulus `ω : Nat → Nat`.
   - `PointwiseContAt`: pointwise continuity at `x₀` with local modulus.
   - `CauchySeqWithModulus` & `LimitWithModulus`: quantitative convergence.
   - `DiffOnWithModulus`: uniform differentiability `|f(x + h) - f(x) - f'(x)h| ≤ |h|/(k+1)`.
   - `RiemannIntegrableWithModulus`: computable uniform-grid Riemann sums & convergence modulus.
   - `UniformConvWithModulus`: uniform convergence of function sequences on `[a, b]`.
-/

namespace SandersNSA
namespace Antipodes

/-! ## 1. Computable Exact Rationals (`QVal`) -/

/-- Exact rational number representing `num / (denPos + 1)`.
    Storing `denPos : Nat` guarantees positivity of the denominator by construction
    without carrying propositional side-conditions inside data computations. -/
structure QVal where
  num : Int
  denPos : Nat
  deriving DecidableEq, Repr

namespace QVal

/-- Positive natural denominator `denPos + 1 ≥ 1`. -/
@[inline] def den (q : QVal) : Nat := q.denPos + 1

/-- Positive integer denominator `((denPos + 1 : Nat) : Int) > 0`. -/
@[inline] def denInt (q : QVal) : Int := ((q.denPos + 1 : Nat) : Int)

theorem den_pos (q : QVal) : 0 < q.den := by
  unfold den
  omega

theorem denInt_pos (q : QVal) : 0 < q.denInt := by
  unfold denInt
  omega

/-- Subtraction-free product of shifted denominators:
    `(a * b + a + b) + 1 = (a + 1) * (b + 1)`. -/
@[inline] def mulDenPos (a b : Nat) : Nat := a * b + a + b

theorem mulDenPos_succ (a b : Nat) : mulDenPos a b + 1 = (a + 1) * (b + 1) := by
  unfold mulDenPos
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega

/-- Embed an integer `z` as `z / 1`. -/
@[inline] def ofInt (z : Int) : QVal := ⟨z, 0⟩

/-- Embed a natural `n` as `n / 1`. -/
@[inline] def ofNat (n : Nat) : QVal := ⟨(n : Int), 0⟩

instance (n : Nat) : OfNat QVal n where
  ofNat := ofNat n

/-- Unit fraction `1 / (k + 1)`. -/
@[inline] def unitFrac (k : Nat) : QVal := ⟨1, k⟩

/-- Dyadic scale `1 / 2^k`. -/
def dyadic : Nat → QVal
  | 0 => ⟨1, 0⟩
  | k + 1 =>
      let prev := dyadic k
      ⟨1, mulDenPos prev.denPos 1⟩

/-- Uniform grid point `i / (N + 1)` on `[0, 1]` (for `0 ≤ i ≤ N + 1`). -/
@[inline] def gridPt (N i : Nat) : QVal := ⟨(i : Int), N⟩

/-- Exact rational addition. -/
def add (p q : QVal) : QVal :=
  ⟨p.num * q.denInt + q.num * p.denInt, mulDenPos p.denPos q.denPos⟩

/-- Exact rational negation. -/
@[inline] def neg (p : QVal) : QVal := ⟨-p.num, p.denPos⟩

/-- Exact rational subtraction. -/
@[inline] def sub (p q : QVal) : QVal := add p (neg q)

/-- Exact rational multiplication. -/
def mul (p q : QVal) : QVal :=
  ⟨p.num * q.num, mulDenPos p.denPos q.denPos⟩

/-- Exact rational absolute value `|p|`. -/
@[inline] def abs (p : QVal) : QVal := ⟨(p.num.natAbs : Int), p.denPos⟩

/-- Metric distance `|p - q|`. -/
@[inline] def dist (p q : QVal) : QVal := abs (sub p q)

/-- Midpoint `(p + q) / 2`. -/
def midpoint (p q : QVal) : QVal :=
  mul (add p q) ⟨1, 1⟩

instance : Add QVal := ⟨add⟩
instance : Sub QVal := ⟨sub⟩
instance : Neg QVal := ⟨neg⟩
instance : Mul QVal := ⟨mul⟩

/-- Reduce numerator and denominator by `gcd` for canonical display. -/
def normalize (q : QVal) : QVal :=
  let g := Nat.gcd q.num.natAbs q.den
  if g ≤ 1 then q
  else
    let d' := q.den / g
    let n' := if q.num < 0 then -((q.num.natAbs / g : Nat) : Int) else ((q.num.natAbs / g : Nat) : Int)
    ⟨n', d' - 1⟩

instance : ToString QVal where
  toString q :=
    let r := q.normalize
    if r.den == 1 then s!"{r.num}" else s!"{r.num}/{r.den}"

/-! ## 2. Extensional Equivalence, Order & Metric Laws -/

/-- Extensional rational equality `p.num * q.den = q.num * p.den`. -/
def eqv (p q : QVal) : Prop := p.num * q.denInt = q.num * p.denInt

/-- Boolean decision procedure for rational equivalence. -/
def eqvB (p q : QVal) : Bool := decide (p.num * q.denInt = q.num * p.denInt)

/-- Rational `≤` via cross-multiplication against positive denominators. -/
def le (p q : QVal) : Prop := p.num * q.denInt ≤ q.num * p.denInt

/-- Boolean decision procedure for `≤`. -/
def leB (p q : QVal) : Bool := decide (p.num * q.denInt ≤ q.num * p.denInt)

/-- Rational `<` via cross-multiplication against positive denominators. -/
def lt (p q : QVal) : Prop := p.num * q.denInt < q.num * p.denInt

/-- Boolean decision procedure for `<`. -/
def ltB (p q : QVal) : Bool := decide (p.num * q.denInt < q.num * p.denInt)

instance (p q : QVal) : Decidable (eqv p q) :=
  inferInstanceAs (Decidable (p.num * q.denInt = q.num * p.denInt))

instance (p q : QVal) : Decidable (le p q) :=
  inferInstanceAs (Decidable (p.num * q.denInt ≤ q.num * p.denInt))

instance (p q : QVal) : Decidable (lt p q) :=
  inferInstanceAs (Decidable (p.num * q.denInt < q.num * p.denInt))

/-- Computable minimum and maximum. -/
def min (p q : QVal) : QVal := if leB p q then p else q
def max (p q : QVal) : QVal := if leB p q then q else p

theorem add_denInt (p q : QVal) : (p + q).denInt = p.denInt * q.denInt := by
  change ((mulDenPos p.denPos q.denPos + 1 : Nat) : Int) = p.denInt * q.denInt
  rw [mulDenPos_succ, Int.natCast_mul]
  rfl

theorem mul_denInt (p q : QVal) : (p * q).denInt = p.denInt * q.denInt := by
  change ((mulDenPos p.denPos q.denPos + 1 : Nat) : Int) = p.denInt * q.denInt
  rw [mulDenPos_succ, Int.natCast_mul]
  rfl

theorem sub_denInt (p q : QVal) : (p - q).denInt = p.denInt * q.denInt :=
  add_denInt p (-q)

theorem dist_denInt (p q : QVal) : (dist p q).denInt = p.denInt * q.denInt :=
  sub_denInt p q

theorem eqv_refl (p : QVal) : eqv p p := rfl

theorem eqv_symm {p q : QVal} (h : eqv p q) : eqv q p := h.symm

theorem le_refl (p : QVal) : le p p := Int.le_refl _

theorem le_total (p q : QVal) : le p q ∨ le q p := by
  unfold le
  omega

theorem not_lt_iff_le (p q : QVal) : ¬ lt p q ↔ le q p := by
  unfold lt le
  omega

theorem lt_imp_le {p q : QVal} (h : lt p q) : le p q := by
  unfold lt le at *
  omega

theorem Int_mul_le_mul_of_pos_right {a b c : Int} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  if hlt : b < a then
    have hmul : b * c < a * c := Int.mul_lt_mul_of_pos_right hlt hc
    omega
  else
    omega

theorem Int_mul_eq_mul_of_pos_right {a b c : Int} (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have h1 : a ≤ b := Int_mul_le_mul_of_pos_right hc (by omega)
  have h2 : b ≤ a := Int_mul_le_mul_of_pos_right hc (by omega)
  omega

theorem le_trans {p q r : QVal} (hpq : le p q) (hqr : le q r) : le p r := by
  unfold le at *
  have hqd : 0 < q.denInt := q.denInt_pos
  have hrd : 0 < r.denInt := r.denInt_pos
  have hpd : 0 < p.denInt := p.denInt_pos
  have h1 : p.num * q.denInt * r.denInt ≤ q.num * p.denInt * r.denInt :=
    Int.mul_le_mul_of_nonneg_right hpq (by omega)
  have h2 : q.num * r.denInt * p.denInt ≤ r.num * q.denInt * p.denInt :=
    Int.mul_le_mul_of_nonneg_right hqr (by omega)
  have hEq1 : p.num * q.denInt * r.denInt = (p.num * r.denInt) * q.denInt := by
    rw [Int.mul_assoc, Int.mul_comm q.denInt r.denInt, ← Int.mul_assoc]
  have hEq2 : q.num * p.denInt * r.denInt = (q.num * r.denInt) * p.denInt := by
    rw [Int.mul_assoc, Int.mul_comm p.denInt r.denInt, ← Int.mul_assoc]
  have hEq3 : r.num * q.denInt * p.denInt = (r.num * p.denInt) * q.denInt := by
    rw [Int.mul_assoc, Int.mul_comm q.denInt p.denInt, ← Int.mul_assoc]
  have hChain : (p.num * r.denInt) * q.denInt ≤ (r.num * p.denInt) * q.denInt := by
    omega
  exact Int_mul_le_mul_of_pos_right hqd hChain

theorem eqv_trans {p q r : QVal} (hpq : eqv p q) (hqr : eqv q r) : eqv p r := by
  have h1 : le p r := @le_trans p q r (by unfold le eqv at *; omega) (by unfold le eqv at *; omega)
  have h2 : le r p := @le_trans r q p (by unfold le eqv at *; omega) (by unfold le eqv at *; omega)
  unfold eqv le at *
  omega

theorem le_of_eqv_left {p p' q : QVal} (hpp : eqv p p') (h : le p' q) : le p q :=
  @le_trans p p' q (by unfold le eqv at *; omega) h

theorem le_of_eqv_right {p q q' : QVal} (h : le p q') (hqq : eqv q' q) : le p q :=
  @le_trans p q' q h (by unfold le eqv at *; omega)

theorem abs_nonneg (p : QVal) : le 0 p.abs := by
  change (0 : Int) * p.denInt ≤ (p.num.natAbs : Int) * 1
  omega

theorem dist_nonneg (p q : QVal) : le 0 (dist p q) :=
  abs_nonneg (p - q)

theorem sub_num (p q : QVal) : (p - q).num = p.num * q.denInt - q.num * p.denInt := by
  change p.num * q.denInt + (-q.num) * p.denInt = p.num * q.denInt - q.num * p.denInt
  rw [Int.neg_mul]
  omega

theorem dist_self (p : QVal) : eqv (dist p p) 0 := by
  change ((p - p).num.natAbs : Int) * 1 = 0 * (dist p p).denInt
  have hSub : (p - p).num = 0 := by
    rw [sub_num]
    omega
  rw [hSub]
  simp

theorem dist_symm (p q : QVal) : eqv (dist p q) (dist q p) := by
  change ((p - q).num.natAbs : Int) * (dist q p).denInt =
         ((q - p).num.natAbs : Int) * (dist p q).denInt
  have hNum : (q - p).num = -(p - q).num := by
    rw [sub_num, sub_num]
    omega
  have hAbs : (q - p).num.natAbs = (p - q).num.natAbs := by
    rw [hNum, Int.natAbs_neg]
  rw [dist_denInt, dist_denInt, hAbs]
  exact congrArg (fun x => ((p - q).num.natAbs : Int) * x) (Int.mul_comm q.denInt p.denInt)

theorem natAbs_add_le_int (a b : Int) :
    ((a + b).natAbs : Int) ≤ (a.natAbs : Int) + (b.natAbs : Int) := by
  have h := Int.natAbs_add_le a b
  omega

theorem dist_triangle (p q r : QVal) : le (dist p r) (dist p q + dist q r) := by
  unfold le
  have hp : 0 < p.denInt := p.denInt_pos
  have hq : 0 < q.denInt := q.denInt_pos
  have hr : 0 < r.denInt := r.denInt_pos
  let A : Int := (p.num * q.denInt - q.num * p.denInt) * r.denInt
  let B : Int := (q.num * r.denInt - r.num * q.denInt) * p.denInt
  have hSum : A + B = (p.num * r.denInt - r.num * p.denInt) * q.denInt := by
    dsimp [A, B]
    rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
    have h1 : p.num * q.denInt * r.denInt = p.num * r.denInt * q.denInt := by
      rw [Int.mul_assoc, Int.mul_comm q.denInt r.denInt, ← Int.mul_assoc]
    have h2 : q.num * p.denInt * r.denInt = q.num * r.denInt * p.denInt := by
      rw [Int.mul_assoc, Int.mul_comm p.denInt r.denInt, ← Int.mul_assoc]
    have h3 : r.num * q.denInt * p.denInt = r.num * p.denInt * q.denInt := by
      rw [Int.mul_assoc, Int.mul_comm q.denInt p.denInt, ← Int.mul_assoc]
    omega
  have hSubPR : (p - r).num = p.num * r.denInt - r.num * p.denInt := sub_num p r
  have hSubPQ : (p - q).num = p.num * q.denInt - q.num * p.denInt := sub_num p q
  have hSubQR : (q - r).num = q.num * r.denInt - r.num * q.denInt := sub_num q r
  have hTri : ((A + B).natAbs : Int) ≤ (A.natAbs : Int) + (B.natAbs : Int) :=
    natAbs_add_le_int A B
  have hAbsDen (z : Int) (n : Nat) :
      ((z * ((n + 1 : Nat) : Int)).natAbs : Int) = (z.natAbs : Int) * ((n + 1 : Nat) : Int) := by
    rw [Int.natAbs_mul, Int.natCast_mul]
    rfl
  have hAbsA : (A.natAbs : Int) = ((p - q).num.natAbs : Int) * r.denInt := by
    dsimp [A]
    rw [← hSubPQ]
    exact hAbsDen (p - q).num r.denPos
  have hAbsB : (B.natAbs : Int) = ((q - r).num.natAbs : Int) * p.denInt := by
    dsimp [B]
    rw [← hSubQR]
    exact hAbsDen (q - r).num p.denPos
  have hAbsAB : ((A + B).natAbs : Int) = ((p - r).num.natAbs : Int) * q.denInt := by
    rw [hSum, ← hSubPR]
    exact hAbsDen (p - r).num q.denPos
  have hCore :
      ((p - r).num.natAbs : Int) * q.denInt ≤
      ((p - q).num.natAbs : Int) * r.denInt + ((q - r).num.natAbs : Int) * p.denInt := by
    omega
  have hDenAdd : (dist p q + dist q r).denInt = (p.denInt * q.denInt) * (q.denInt * r.denInt) := by
    rw [add_denInt, dist_denInt, dist_denInt]
  have hDenPR : (dist p r).denInt = p.denInt * r.denInt := dist_denInt p r
  have hNumAdd :
      (dist p q + dist q r).num =
        ((p - q).num.natAbs : Int) * (q.denInt * r.denInt) +
        ((q - r).num.natAbs : Int) * (p.denInt * q.denInt) := by
    change (dist p q).num * (dist q r).denInt + (dist q r).num * (dist p q).denInt = _
    rw [dist_denInt, dist_denInt]
    rfl
  rw [hDenAdd, hDenPR, hNumAdd]
  change ((p - r).num.natAbs : Int) * ((p.denInt * q.denInt) * (q.denInt * r.denInt)) ≤
    (((p - q).num.natAbs : Int) * (q.denInt * r.denInt) +
     ((q - r).num.natAbs : Int) * (p.denInt * q.denInt)) * (p.denInt * r.denInt)
  have hPosScale : 0 ≤ p.denInt * q.denInt * r.denInt :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hScaled := Int.mul_le_mul_of_nonneg_right hCore hPosScale
  have hLHS :
      ((p - r).num.natAbs : Int) * q.denInt * (p.denInt * q.denInt * r.denInt) =
      ((p - r).num.natAbs : Int) * ((p.denInt * q.denInt) * (q.denInt * r.denInt)) := by
    simp only [Int.mul_assoc, Int.mul_left_comm]
  have hRHS :
      (((p - q).num.natAbs : Int) * r.denInt + ((q - r).num.natAbs : Int) * p.denInt) *
        (p.denInt * q.denInt * r.denInt) =
      (((p - q).num.natAbs : Int) * (q.denInt * r.denInt) +
       ((q - r).num.natAbs : Int) * (p.denInt * q.denInt)) * (p.denInt * r.denInt) := by
    rw [Int.add_mul, Int.add_mul]
    congr 1 <;> simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

theorem add_le_add {a b c d : QVal} (hab : le a b) (hcd : le c d) : le (a + c) (b + d) := by
  unfold le at *
  rw [add_denInt, add_denInt]
  change (a.num * c.denInt + c.num * a.denInt) * (b.denInt * d.denInt) ≤
         (b.num * d.denInt + d.num * b.denInt) * (a.denInt * c.denInt)
  have ha : 0 < a.denInt := a.denInt_pos
  have hb : 0 < b.denInt := b.denInt_pos
  have hc : 0 < c.denInt := c.denInt_pos
  have hd : 0 < d.denInt := d.denInt_pos
  have hs1 : (a.num * b.denInt) * (c.denInt * d.denInt) ≤ (b.num * a.denInt) * (c.denInt * d.denInt) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.mul_nonneg (by omega) (by omega))
  have hs2 : (c.num * d.denInt) * (a.denInt * b.denInt) ≤ (d.num * c.denInt) * (a.denInt * b.denInt) :=
    Int.mul_le_mul_of_nonneg_right hcd (Int.mul_nonneg (by omega) (by omega))
  have e1 : (a.num * c.denInt) * (b.denInt * d.denInt) = (a.num * b.denInt) * (c.denInt * d.denInt) := by
    simp only [Int.mul_assoc, Int.mul_left_comm]
  have e2 : (b.num * d.denInt) * (a.denInt * c.denInt) = (b.num * a.denInt) * (c.denInt * d.denInt) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have e3 : (c.num * a.denInt) * (b.denInt * d.denInt) = (c.num * d.denInt) * (a.denInt * b.denInt) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have e4 : (d.num * b.denInt) * (a.denInt * c.denInt) = (d.num * c.denInt) * (a.denInt * b.denInt) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  rw [Int.add_mul, Int.add_mul]
  omega

theorem unitFrac_anti {k m : Nat} (h : k ≤ m) : le (unitFrac m) (unitFrac k) := by
  change 1 * ((k + 1 : Nat) : Int) ≤ 1 * ((m + 1 : Nat) : Int)
  omega

theorem unitFrac_half_sum (k : Nat) :
    le (unitFrac (2 * k + 1) + unitFrac (2 * k + 1)) (unitFrac k) := by
  change (1 * ((2 * k + 2 : Nat) : Int) + 1 * ((2 * k + 2 : Nat) : Int)) * ((k + 1 : Nat) : Int) ≤
    1 * ((mulDenPos (2 * k + 1) (2 * k + 1) + 1 : Nat) : Int)
  rw [mulDenPos_succ, Int.natCast_mul]
  let m : Int := ((k + 1 : Nat) : Int)
  have h1 : ((2 * k + 2 : Nat) : Int) = 2 * m := by
    dsimp [m]
    omega
  change (1 * ((2 * k + 2 : Nat) : Int) + 1 * ((2 * k + 2 : Nat) : Int)) * m ≤
    1 * (((2 * k + 2 : Nat) : Int) * ((2 * k + 2 : Nat) : Int))
  rw [h1]
  have hLHS : (1 * (2 * m) + 1 * (2 * m)) * m = 4 * (m * m) := by
    have hk : 1 * (2 * m) + 1 * (2 * m) = 4 * m := by omega
    rw [hk, Int.mul_assoc]
  have hRHS : 1 * ((2 * m) * (2 * m)) = 4 * (m * m) := by
    rw [Int.one_mul, ← Int.mul_assoc, Int.mul_comm (2 * m) 2, ← Int.mul_assoc]
    have h4 : (2 : Int) * 2 = 4 := rfl
    rw [h4, Int.mul_assoc]
  rw [hLHS, hRHS]
  exact Int.le_refl _

end QVal

/-! ## 3. Bishop-Style Modulus-Bearing Analysis (`Type`-Valued Witnesses) -/

/-- Quantitative modulus mapping target precision `k` (`1 / (k + 1)`) to required input resolution. -/
abbrev Modulus : Type := Nat → Nat

/-- Constructive uniform continuity of `f` on `[a, b]` with explicit modulus `ω : Nat → Nat`. -/
structure UniformContOn (f : QVal → QVal) (a b : QVal) : Type where
  modulus : Modulus
  spec : ∀ (k : Nat) (x y : QVal),
    QVal.le a x → QVal.le x b →
    QVal.le a y → QVal.le y b →
    QVal.le (QVal.dist x y) (QVal.unitFrac (modulus k)) →
    QVal.le (QVal.dist (f x) (f y)) (QVal.unitFrac k)

/-- Constructive pointwise continuity of `f` at `x₀` with local modulus `ω : Nat → Nat`. -/
structure PointwiseContAt (f : QVal → QVal) (x₀ : QVal) : Type where
  modulus : Modulus
  spec : ∀ (k : Nat) (y : QVal),
    QVal.le (QVal.dist x₀ y) (QVal.unitFrac (modulus k)) →
    QVal.le (QVal.dist (f x₀) (f y)) (QVal.unitFrac k)

/-- Cauchy sequence equipped with an explicit modulus `ω : Nat → Nat`. -/
structure CauchySeqWithModulus (s : Nat → QVal) : Type where
  modulus : Modulus
  spec : ∀ (k m n : Nat),
    modulus k ≤ m → modulus k ≤ n →
    QVal.le (QVal.dist (s m) (s n)) (QVal.unitFrac k)

/-- Quantitative convergence `s n → L` with explicit rate `modulus : Nat → Nat`. -/
structure LimitWithModulus (s : Nat → QVal) (L : QVal) : Type where
  modulus : Modulus
  spec : ∀ (k n : Nat),
    modulus k ≤ n →
    QVal.le (QVal.dist (s n) L) (QVal.unitFrac k)

/-- Every sequence with an explicit limit & rate is constructively Cauchy with modulus `ω(2k + 1)`. -/
def LimitWithModulus.toCauchy {s : Nat → QVal} {L : QVal}
    (h : LimitWithModulus s L) : CauchySeqWithModulus s where
  modulus k := h.modulus (2 * k + 1)
  spec k m n hm hn := by
    have hmL := h.spec (2 * k + 1) m hm
    have hnL := h.spec (2 * k + 1) n hn
    have hSymm : QVal.le (QVal.dist L (s n)) (QVal.unitFrac (2 * k + 1)) :=
      QVal.le_of_eqv_left (QVal.dist_symm L (s n)) hnL
    have hTri := QVal.dist_triangle (s m) L (s n)
    have hSum := QVal.le_trans (QVal.add_le_add hmL hSymm) (QVal.unitFrac_half_sum k)
    exact QVal.le_trans hTri hSum

/-- Constructive uniform differentiability of `f` with derivative `f'` on `[a, b]`:
    `|f(x + h) - f(x) - f'(x) * h| ≤ |h| / (k + 1)` whenever `0 < |h| ≤ 1 / (ω(k) + 1)`. -/
structure DiffOnWithModulus (f f' : QVal → QVal) (a b : QVal) : Type where
  modulus : Modulus
  spec : ∀ (k : Nat) (x h : QVal),
    QVal.le a x → QVal.le x b →
    QVal.le a (x + h) → QVal.le (x + h) b →
    QVal.lt 0 h.abs →
    QVal.le h.abs (QVal.unitFrac (modulus k)) →
    QVal.le (QVal.dist (f (x + h) - f x) (f' x * h)) (QVal.unitFrac k * h.abs)

/-- Computable uniform left-endpoint Riemann sum `(1 / (N + 1)) * ∑_{i=0}^{N} f(i / (N + 1))` on `[0, 1]`. -/
def uniformGridSumAux (f : QVal → QVal) (N : Nat) : Nat → QVal
  | 0 => 0
  | count + 1 => uniformGridSumAux f N count + f (QVal.gridPt N count)

def uniformGridSum (f : QVal → QVal) (N : Nat) : QVal :=
  QVal.unitFrac N * uniformGridSumAux f N (N + 1)

/-- Constructive Riemann integrability of `f` on `[0, 1]` with integral value `integral`
    and explicit convergence modulus `modulus`. -/
structure RiemannIntegrableWithModulus (f : QVal → QVal) : Type where
  integral : QVal
  modulus : Modulus
  spec : ∀ (k N : Nat),
    modulus k ≤ N →
    QVal.le (QVal.dist (uniformGridSum f N) integral) (QVal.unitFrac k)

/-- Constructive uniform convergence `fn n → f` on `[a, b]` with explicit modulus `ω : Nat → Nat`. -/
structure UniformConvWithModulus (fn : Nat → QVal → QVal) (f : QVal → QVal) (a b : QVal) : Type where
  modulus : Modulus
  spec : ∀ (k n : Nat) (x : QVal),
    modulus k ≤ n →
    QVal.le a x → QVal.le x b →
    QVal.le (QVal.dist (fn n x) (f x)) (QVal.unitFrac k)

end Antipodes
end SandersNSA
