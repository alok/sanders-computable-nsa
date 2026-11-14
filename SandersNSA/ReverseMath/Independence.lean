/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.IVTAndDini

/-!
# Mutual Independence of `StandardPart` (`st`) and `Transfer` (`Independence`)

Formalizes the foundational question discussed in Alok Singh & Sam Sanders's January 31, 2024
interview: **Are `StandardPart` (`st`) and `Transfer` mutually independent (including for
concrete low-complexity fragments)?**

We construct two 100% computable algebraic/sequential models over `QVal` proving both
directions of independence constructively:

1. **`DualQ` (`st` holds, Π₁-`Transfer` FAILS)**:
   - Dual rationals `a + b ε` (`ε² = 0`).
   - Admits a total, computable ring homomorphism `DualQ.st : DualQ → QVal` (`a + b ε ↦ a`)
     with `x ≈_halo embed(st x)` for every element.
   - Standard `QVal` satisfies the universal Horn/Π₁ law `∀ q : QVal, q * q = 0 → q = 0`
     (`qval_sq_eqv_zero_imp_zero`), yet its transfer to `DualQ` fails at `ε = ⟨0, 1⟩`
     (`dualQ_transfer_fails`: `ε * ε = 0` while `ε ≠ 0`).

2. **`HyperSeq QVal` (`Transfer` holds pointwise, `StandardPart` over `QVal` FAILS)**:
   - Every universal Horn formula `∀ q : QVal, P q → Q q` valid on `QVal` transfers
     immediately to `HyperSeq QVal` (`hyperSeq_horn_transfer`, including `x * x = 0 → x = 0`).
   - Yet we construct a bounded computable sequence `invSqrt2Seq : HyperSeq QVal` (`0 ≤ s_n ≤ 1`,
     `s_n² → 1/2`) and prove constructively via infinite descent (`sq_ne_two_mul_sq` /
     `no_qval_sq_eqv_half`) that **no rational `q : QVal`** can serve as its standard part
     (`invSqrt2Seq_has_no_qval_standard_part`).
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Standard Base Truths on `QVal` -/

/-- Standard `QVal` has no non-zero nilpotents (`∀ q : QVal, q * q ≈ 0 → q ≈ 0`). -/
theorem qval_sq_eqv_zero_imp_zero {q : QVal} (h : QVal.eqv (q * q) 0) : QVal.eqv q 0 := by
  unfold QVal.eqv at h ⊢
  change (q.num * q.num) * 1 = 0 * (q * q).denInt at h
  change q.num * 1 = 0 * q.denInt
  have hSq : q.num * q.num = 0 := by omega
  rcases Int.mul_eq_zero.mp hSq with h0 | h0 <;> omega

/-- Constructive infinite-descent proof that `n² ≠ 2 m²` for all `m > 0` in `Nat`. -/
theorem sq_ne_two_mul_sq : ∀ (m : Nat), 0 < m → ∀ (n : Nat), n * n ≠ 2 * (m * m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hmPos n hEq
    have hnEven : n % 2 = 0 := by
      have hMod : (n * n) % 2 = (2 * (m * m)) % 2 := congrArg (· % 2) hEq
      rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h0 | h1
      · exact h0
      · have hOddSq : (n * n) % 2 = 1 := by rw [Nat.mul_mod, h1]
        omega
    let k := n / 2
    have hn : n = 2 * k := by omega
    have hFour : (2 * k) * (2 * k) = 4 * (k * k) := by
      calc
        (2 * k) * (2 * k) = 2 * (k * (2 * k)) := by rw [Nat.mul_assoc]
        _ = 2 * ((2 * k) * k) := by rw [Nat.mul_comm k (2 * k)]
        _ = 2 * (2 * (k * k)) := by rw [Nat.mul_assoc]
        _ = 4 * (k * k) := by omega
    have hmSq : m * m = 2 * (k * k) := by
      rw [hn, hFour] at hEq
      omega
    have hkPos : 0 < k := by
      by_cases hk0 : k = 0
      · rw [hk0] at hmSq
        have hm0 : m * m = 0 := by omega
        rcases Nat.mul_eq_zero.mp hm0 with rfl | rfl <;> omega
      · omega
    have hkLt : k < m := by
      by_cases hGe : m ≤ k
      · have hMono : m * m ≤ k * k := Nat.mul_le_mul hGe hGe
        have hkSqPos : 0 < k * k := Nat.mul_pos hkPos hkPos
        omega
      · omega
    exact ih k hkLt hkPos m hmSq

/-- **Constructive Irrationality of `1 / √2` in `QVal`**:
    no rational `q : QVal` satisfies `q² ≈ 1/2` (`⟨1, 1⟩`). -/
theorem no_qval_sq_eqv_half (q : QVal) : ¬ QVal.eqv (q * q) ⟨1, 1⟩ := by
  intro hEqv
  unfold QVal.eqv at hEqv
  rw [QVal.mul_denInt] at hEqv
  change (q.num * q.num) * 2 = 1 * (q.denInt * q.denInt) at hEqv
  have hNumNonZero : 0 < q.num.natAbs := by
    by_cases hZ : q.num = 0
    · rw [hZ] at hEqv
      have hd : 0 < q.denInt := q.denInt_pos
      have hd2 : 0 < q.denInt * q.denInt := Int.mul_pos hd hd
      omega
    · exact Int.natAbs_pos.mpr hZ
  have hNatEq : q.den * q.den = 2 * (q.num.natAbs * q.num.natAbs) := by
    have hInt1 : ((q.num.natAbs * q.num.natAbs : Nat) : Int) = q.num * q.num := by
      rw [Int.natCast_mul]
      cases q.num with
      | ofNat _ => rfl
      | negSucc a =>
          have hNeg : Int.negSucc a = -((a + 1 : Nat) : Int) := rfl
          change ((a + 1 : Nat) : Int) * ((a + 1 : Nat) : Int) = Int.negSucc a * Int.negSucc a
          rw [hNeg, Int.neg_mul_neg]
    have hInt2 : ((q.den * q.den : Nat) : Int) = q.denInt * q.denInt := Int.natCast_mul _ _
    have hInt3 : ((2 * (q.num.natAbs * q.num.natAbs) : Nat) : Int) =
        (q.num * q.num) * 2 := by
      rw [Int.natCast_mul, hInt1, Int.mul_comm]
      rfl
    omega
  exact sq_ne_two_mul_sq q.num.natAbs hNumNonZero q.den hNatEq

/-! ## 2. Model 1 (`DualQ`): `StandardPart` Holds, Π₁-`Transfer` Fails -/

/-- Computable dual-rational halo ring `a + b ε` (`ε² = 0`). -/
structure DualQ : Type where
  std : QVal
  inf : QVal
  deriving DecidableEq, Repr

namespace DualQ

@[inline] def embed (q : QVal) : DualQ := ⟨q, 0⟩
@[inline] def eps : DualQ := ⟨0, 1⟩
@[inline] def zero : DualQ := ⟨0, 0⟩
@[inline] def one : DualQ := ⟨1, 0⟩

def add (x y : DualQ) : DualQ :=
  ⟨x.std + y.std, x.inf + y.inf⟩

def mul (x y : DualQ) : DualQ :=
  ⟨x.std * y.std, x.std * y.inf + x.inf * y.std⟩

def eqv (x y : DualQ) : Prop :=
  QVal.eqv x.std y.std ∧ QVal.eqv x.inf y.inf

def haloClose (x y : DualQ) : Prop :=
  QVal.eqv x.std y.std

/-- **Computable Standard-Part Map** (`st : DualQ → QVal`). -/
@[inline] def st (x : DualQ) : QVal := x.std

theorem st_haloClose (x : DualQ) : haloClose x (embed (st x)) :=
  QVal.eqv_refl x.std

theorem st_embed (q : QVal) : QVal.eqv (st (embed q)) q :=
  QVal.eqv_refl q

theorem st_add (x y : DualQ) : QVal.eqv (st (add x y)) (st x + st y) :=
  QVal.eqv_refl _

theorem st_mul (x y : DualQ) : QVal.eqv (st (mul x y)) (st x * st y) :=
  QVal.eqv_refl _

/-- **First Independence Theorem (`st ⊬ Transfer`)**:
    `DualQ` possesses a total computable homomorphism `st` (`st_haloClose`, `st_add`, `st_mul`),
    `eps` is infinitesimal (`haloClose eps zero`), yet the standard `QVal` law
    `∀ q, q * q = 0 → q = 0` (`qval_sq_eqv_zero_imp_zero`) FAILS on `DualQ` at `eps`! -/
theorem dualQ_transfer_fails :
    haloClose eps zero ∧ eqv (mul eps eps) zero ∧ ¬ eqv eps zero := by
  refine ⟨QVal.eqv_refl 0, ?_, ?_⟩
  · constructor
    · change (0 * 0 : Int) * 1 = 0 * _
      omega
    · change ((0 * 1 : Int) * 1 + (1 * 0 : Int) * 1) * 1 = 0 * _
      omega
  · intro h
    rcases h with ⟨_, hInf⟩
    change (1 : Int) * 1 = 0 * 1 at hInf
    omega

end DualQ

/-! ## 3. Model 2 (`HyperSeq QVal`): Pointwise `Transfer` Holds, `StandardPart` over `QVal` Fails -/

def HyperSeqEqv (x y : HyperSeq QVal) : Prop :=
  ∀ n : Nat, QVal.eqv (x n) (y n)

/-- **Pointwise Universal Horn Transfer**:
    Every universal Horn implication valid on `QVal` transfers verbatim to `HyperSeq QVal`. -/
theorem hyperSeq_horn_transfer
    {P R : QVal → QVal → Prop}
    (hStd : ∀ a b : QVal, P a b → R a b)
    (x y : HyperSeq QVal)
    (hPrem : ∀ n : Nat, P (x n) (y n)) :
    ∀ n : Nat, R (x n) (y n) :=
  fun n => hStd (x n) (y n) (hPrem n)

/-- Nilpotent-freeness (`x * x = 0 → x = 0`) transfers cleanly to `HyperSeq QVal`. -/
theorem hyperSeq_sq_zero_transfer {x : HyperSeq QVal}
    (hSq : HyperSeqEqv (liftSeq2 QVal.mul x x) (starConst 0)) :
    HyperSeqEqv x (starConst 0) :=
  fun n => qval_sq_eqv_zero_imp_zero (hSq n)

/-- Polynomial `f(x) = x² - 1/2` on `[0, 1]`. -/
def halfSqFn (x : QVal) : QVal :=
  x * x - ⟨1, 1⟩

theorem qval_mul_congr {a a' b b' : QVal} (ha : QVal.eqv a a') (hb : QVal.eqv b b') :
    QVal.eqv (a * b) (a' * b') := by
  unfold QVal.eqv at *
  rw [QVal.mul_denInt, QVal.mul_denInt]
  change (a.num * b.num) * (a'.denInt * b'.denInt) = (a'.num * b'.num) * (a.denInt * b.denInt)
  calc
    (a.num * b.num) * (a'.denInt * b'.denInt)
        = (a.num * a'.denInt) * (b.num * b'.denInt) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]
    _ = (a'.num * a.denInt) * (b'.num * b.denInt) := by rw [ha, hb]
    _ = (a'.num * b'.num) * (a.denInt * b.denInt) := by
          simp only [Int.mul_assoc, Int.mul_left_comm]

theorem qval_add_congr {a a' b b' : QVal} (ha : QVal.eqv a a') (hb : QVal.eqv b b') :
    QVal.eqv (a + b) (a' + b') := by
  unfold QVal.eqv at *
  rw [QVal.add_denInt, QVal.add_denInt]
  change (a.num * b.denInt + b.num * a.denInt) * (a'.denInt * b'.denInt) =
         (a'.num * b'.denInt + b'.num * a'.denInt) * (a.denInt * b.denInt)
  rw [Int.add_mul, Int.add_mul]
  have h1 : (a.num * b.denInt) * (a'.denInt * b'.denInt) =
            (a'.num * b'.denInt) * (a.denInt * b.denInt) := by
    calc
      (a.num * b.denInt) * (a'.denInt * b'.denInt)
          = (a.num * a'.denInt) * (b.denInt * b'.denInt) := by
              simp only [Int.mul_assoc, Int.mul_left_comm]
      _ = (a'.num * a.denInt) * (b.denInt * b'.denInt) := by rw [ha]
      _ = (a'.num * b'.denInt) * (a.denInt * b.denInt) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have h2 : (b.num * a.denInt) * (a'.denInt * b'.denInt) =
            (b'.num * a'.denInt) * (a.denInt * b.denInt) := by
    calc
      (b.num * a.denInt) * (a'.denInt * b'.denInt)
          = (b.num * b'.denInt) * (a.denInt * a'.denInt) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (b'.num * b.denInt) * (a.denInt * a'.denInt) := by rw [hb]
      _ = (b'.num * a'.denInt) * (a.denInt * b.denInt) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- Lipschitz modulus `ω(k) = 2 * (k + 1)` for `halfSqFn (x) = x² - 1/2` on `[0, 1]`. -/
def halfSqFn_uniformCont : UniformContOn halfSqFn 0 1 where
  modulus k := 2 * (k + 1)
  spec k x y hx0 hx1 hy0 hy1 hdist := by
    have hxNonneg : 0 ≤ x.num := by change 0 * x.denInt ≤ x.num * 1 at hx0; omega
    have hyNonneg : 0 ≤ y.num := by change 0 * y.denInt ≤ y.num * 1 at hy0; omega
    have hxLe : x.num ≤ x.denInt := by change x.num * 1 ≤ 1 * x.denInt at hx1; omega
    have hyLe : y.num ≤ y.denInt := by change y.num * 1 ≤ 1 * y.denInt at hy1; omega
    have hSumNonneg : 0 ≤ x.num * y.denInt + y.num * x.denInt := by
      have h1 : 0 ≤ x.num * y.denInt := Int.mul_nonneg hxNonneg (by have := y.denInt_pos; omega)
      have h2 : 0 ≤ y.num * x.denInt := Int.mul_nonneg hyNonneg (by have := x.denInt_pos; omega)
      omega
    have hSumLe : x.num * y.denInt + y.num * x.denInt ≤ 2 * (x.denInt * y.denInt) := by
      have h1 : x.num * y.denInt ≤ x.denInt * y.denInt :=
        Int.mul_le_mul_of_nonneg_right hxLe (by have := y.denInt_pos; omega)
      have h2 : y.num * x.denInt ≤ y.denInt * x.denInt :=
        Int.mul_le_mul_of_nonneg_right hyLe (by have := x.denInt_pos; omega)
      have hComm : y.denInt * x.denInt = x.denInt * y.denInt := Int.mul_comm _ _
      omega
    -- Note `halfSqFn x - halfSqFn y` has numerator `2 * ((x² - y²).num) * 2`? Check directly:
    have hDiffEqv : QVal.eqv (QVal.dist (halfSqFn x) (halfSqFn y)) (QVal.dist (x * x) (y * y)) := by
      unfold halfSqFn QVal.eqv
      rw [QVal.dist_denInt, QVal.dist_denInt, QVal.sub_denInt, QVal.sub_denInt]
      have hSubNum : ((x * x - ⟨1, 1⟩) - (y * y - ⟨1, 1⟩)).num = 4 * (x * x - y * y).num := by
        rw [QVal.sub_num, QVal.sub_num, QVal.sub_num, QVal.sub_num,
            QVal.sub_denInt, QVal.sub_denInt]
        change ((x * x).num * 2 - 1 * (x * x).denInt) * ((y * y).denInt * 2) -
               ((y * y).num * 2 - 1 * (y * y).denInt) * ((x * x).denInt * 2) =
               4 * ((x * x).num * (y * y).denInt - (y * y).num * (x * x).denInt)
        rw [Int.sub_mul, Int.sub_mul]
        have t1 : ((x * x).num * 2) * ((y * y).denInt * 2) =
            4 * ((x * x).num * (y * y).denInt) := by
          have h22 : (2 : Int) * 2 = 4 := rfl
          calc
            ((x * x).num * 2) * ((y * y).denInt * 2)
                = ((x * x).num * (y * y).denInt) * (2 * 2) := by
                    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            _ = 4 * ((x * x).num * (y * y).denInt) := by rw [h22, Int.mul_comm]
        have t2 : ((y * y).num * 2) * ((x * x).denInt * 2) =
            4 * ((y * y).num * (x * x).denInt) := by
          have h22 : (2 : Int) * 2 = 4 := rfl
          calc
            ((y * y).num * 2) * ((x * x).denInt * 2)
                = ((y * y).num * (x * x).denInt) * (2 * 2) := by
                    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            _ = 4 * ((y * y).num * (x * x).denInt) := by rw [h22, Int.mul_comm]
        have t3 : (1 * (x * x).denInt) * ((y * y).denInt * 2) =
                  (1 * (y * y).denInt) * ((x * x).denInt * 2) := by
          simp only [Int.one_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        rw [t1, t2, t3, Int.mul_sub]
        omega
      change (((x * x - ⟨1, 1⟩) - (y * y - ⟨1, 1⟩)).num.natAbs : Int) *
        ((x * x).denInt * (y * y).denInt) =
        ((x * x - y * y).num.natAbs : Int) *
        (((x * x).denInt * 2) * ((y * y).denInt * 2))
      rw [hSubNum, Int.natAbs_mul, Int.natCast_mul]
      have hDen4 : ((x * x).denInt * 2) * ((y * y).denInt * 2) =
          4 * ((x * x).denInt * (y * y).denInt) := by
        have h22 : (2 : Int) * 2 = 4 := rfl
        calc
          ((x * x).denInt * 2) * ((y * y).denInt * 2)
              = ((x * x).denInt * (y * y).denInt) * (2 * 2) := by
                  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = 4 * ((x * x).denInt * (y * y).denInt) := by rw [h22, Int.mul_comm]
      rw [hDen4]
      change (4 * ((x * x - y * y).num.natAbs : Int)) * ((x * x).denInt * (y * y).denInt) =
        ((x * x - y * y).num.natAbs : Int) * (4 * ((x * x).denInt * (y * y).denInt))
      simp only [Int.mul_assoc, Int.mul_comm]
    have hFact : (x * x - y * y).num = (x - y).num * (x.num * y.denInt + y.num * x.denInt) := by
      rw [QVal.sub_num, QVal.sub_num, QVal.mul_denInt, QVal.mul_denInt]
      let A := x.num * y.denInt
      let B := y.num * x.denInt
      have hLHS : (x * x).num * (y.denInt * y.denInt) - (y * y).num * (x.denInt * x.denInt) =
          A * A - B * B := by
        change (x.num * x.num) * (y.denInt * y.denInt) - (y.num * y.num) * (x.denInt * x.denInt) =
          A * A - B * B
        have eA : (x.num * x.num) * (y.denInt * y.denInt) = A * A := by
          dsimp [A]; simp only [Int.mul_assoc, Int.mul_left_comm]
        have eB : (y.num * y.num) * (x.denInt * x.denInt) = B * B := by
          dsimp [B]; simp only [Int.mul_assoc, Int.mul_left_comm]
        rw [eA, eB]
      rw [hLHS]
      change A * A - B * B = (A - B) * (A + B)
      rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm B A]
      omega
    have hAbsSq : ((x * x - y * y).num.natAbs : Int) ≤
        ((x - y).num.natAbs : Int) * (2 * (x.denInt * y.denInt)) := by
      rw [hFact, Int.natAbs_mul, Int.natCast_mul, Int.natAbs_of_nonneg hSumNonneg]
      exact Int.mul_le_mul_of_nonneg_left hSumLe (by omega)
    have hDistSq : QVal.le (QVal.dist (x * x) (y * y)) (QVal.unitFrac k) := by
      unfold QVal.le at hdist ⊢
      rw [QVal.dist_denInt, QVal.mul_denInt, QVal.mul_denInt]
      rw [QVal.dist_denInt] at hdist
      change ((x - y).num.natAbs : Int) * ((2 * (k + 1) + 1 : Nat) : Int) ≤
        1 * (x.denInt * y.denInt) at hdist
      change ((x * x - y * y).num.natAbs : Int) * ((k + 1 : Nat) : Int) ≤
        1 * ((x.denInt * x.denInt) * (y.denInt * y.denInt))
      have hMul1 := Int.mul_le_mul_of_nonneg_right hAbsSq (by omega : 0 ≤ ((k + 1 : Nat) : Int))
      have hCoeff : 2 * ((k + 1 : Nat) : Int) ≤ ((2 * (k + 1) + 1 : Nat) : Int) := by omega
      have hMul2 := Int.mul_le_mul_of_nonneg_left hCoeff (by omega : 0 ≤ ((x - y).num.natAbs : Int))
      have hBound2 : ((x - y).num.natAbs : Int) * (2 * ((k + 1 : Nat) : Int)) ≤ x.denInt * y.denInt := by
        omega
      have hScaleXY : 0 ≤ x.denInt * y.denInt :=
        Int.mul_nonneg (by have := x.denInt_pos; omega) (by have := y.denInt_pos; omega)
      have hMul3 := Int.mul_le_mul_of_nonneg_right hBound2 hScaleXY
      have hRearrL :
          (((x - y).num.natAbs : Int) * (2 * (x.denInt * y.denInt))) * ((k + 1 : Nat) : Int) =
          (((x - y).num.natAbs : Int) * (2 * ((k + 1 : Nat) : Int))) * (x.denInt * y.denInt) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      have hRearrR :
          (x.denInt * y.denInt) * (x.denInt * y.denInt) =
          1 * ((x.denInt * x.denInt) * (y.denInt * y.denInt)) := by
        rw [Int.one_mul]
        simp only [Int.mul_assoc, Int.mul_left_comm]
      omega
    exact QVal.le_of_eqv_left hDiffEqv hDistSq

/-- Computable bounded sequence `s_k := approxIVTPoint halfSqFn halfSqFn_uniformCont k` in `[0, 1]`
    whose squares converge to `1/2` (`|(s_k)² - 1/2| ≤ 1 / (k + 1)`). -/
def invSqrt2Seq : HyperSeq QVal :=
  approxIVTPoint halfSqFn halfSqFn_uniformCont

theorem halfSqFn_respectsEqv : RespectsEqv halfSqFn := by
  intro x y hxy
  exact qval_add_congr (qval_mul_congr hxy hxy) (QVal.eqv_refl _)

theorem invSqrt2Seq_spec (k : Nat) :
    QVal.le 0 (invSqrt2Seq k) ∧
    QVal.le (invSqrt2Seq k) 1 ∧
    QVal.le (QVal.dist (invSqrt2Seq k * invSqrt2Seq k) ⟨1, 1⟩) (QVal.unitFrac k) := by
  have hf0 : QVal.le (halfSqFn 0) 0 := by decide
  have hf1 : QVal.le 0 (halfSqFn 1) := by decide
  exact approxIVT_spec halfSqFn_uniformCont halfSqFn_respectsEqv hf0 hf1 k

/-- Every rational `q : QVal` has a strictly positive distance away from `1/2` in square:
    `∃ K : Nat, 1 / (K + 1) < |q² - 1/2|`. -/
theorem qval_sq_dist_half_lower_bound (q : QVal) :
    ∃ K : Nat, QVal.lt (QVal.unitFrac K) (QVal.dist (q * q) ⟨1, 1⟩) := by
  have hNe : ¬ QVal.eqv (q * q) ⟨1, 1⟩ := no_qval_sq_eqv_half q
  let diff := (q * q) - ⟨1, 1⟩
  have hPosNum : 1 ≤ (diff.num.natAbs : Int) := by
    by_cases hZ : diff.num = 0
    · exfalso
      apply hNe
      unfold QVal.eqv
      dsimp [diff] at hZ
      rw [QVal.sub_num] at hZ
      change (q * q).num * 2 - 1 * (q * q).denInt = 0 at hZ
      change (q * q).num * 2 = 1 * (q * q).denInt
      omega
    · have hp := Int.natAbs_pos.mpr hZ
      omega
  refine ⟨diff.den, ?_⟩
  unfold QVal.lt
  change 1 * (diff.den : Int) < (diff.num.natAbs : Int) * ((diff.den + 1 : Nat) : Int)
  have hDenPos : 0 < (diff.den : Int) := diff.denInt_pos
  have hScale := Int.mul_le_mul_of_nonneg_right hPosNum (by omega : 0 ≤ ((diff.den + 1 : Nat) : Int))
  omega

/-- General algebraic bound for any `s ∈ [0, 1]` and arbitrary `q : QVal` (no sign assumption on `q`!):
    `|s² - q²| ≤ (1 + |q|) · |s - q|`, bounded cleanly by `(q.den + q.num.natAbs) / q.den` — or
    even simpler, `(1 + q.num.natAbs) · |s - q|` since `|q| ≤ q.num.natAbs`! -/
theorem sq_diff_le_for_unit_and_any_q {s q : QVal}
    (hs0 : QVal.le 0 s) (hs1 : QVal.le s 1) :
    QVal.le (QVal.dist (s * s) (q * q))
      (QVal.ofNat (q.num.natAbs + 1) * QVal.dist s q) := by
  let M : Nat := q.num.natAbs + 1
  have hsNonneg : 0 ≤ s.num := by change 0 * s.denInt ≤ s.num * 1 at hs0; omega
  have hsLe : s.num ≤ s.denInt := by change s.num * 1 ≤ 1 * s.denInt at hs1; omega
  have hFact : (s * s - q * q).num = (s - q).num * (s.num * q.denInt + q.num * s.denInt) := by
    rw [QVal.sub_num, QVal.sub_num, QVal.mul_denInt, QVal.mul_denInt]
    let A := s.num * q.denInt
    let B := q.num * s.denInt
    change (s.num * s.num) * (q.denInt * q.denInt) - (q.num * q.num) * (s.denInt * s.denInt) =
      (A - B) * (A + B)
    have eA : (s.num * s.num) * (q.denInt * q.denInt) = A * A := by
      dsimp [A]; simp only [Int.mul_assoc, Int.mul_left_comm]
    have eB : (q.num * q.num) * (s.denInt * s.denInt) = B * B := by
      dsimp [B]; simp only [Int.mul_assoc, Int.mul_left_comm]
    rw [eA, eB, Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm B A]
    omega
  have hSumAbs : ((s.num * q.denInt + q.num * s.denInt).natAbs : Int) ≤
      (M : Int) * (s.denInt * q.denInt) := by
    have hTri := QVal.natAbs_add_le_int (s.num * q.denInt) (q.num * s.denInt)
    have hsPos : 0 ≤ s.denInt := by have := s.denInt_pos; omega
    have hqPos : 0 ≤ q.denInt := by have := q.denInt_pos; omega
    have hA : ((s.num * q.denInt).natAbs : Int) ≤ s.denInt * q.denInt := by
      rw [Int.natAbs_of_nonneg (Int.mul_nonneg hsNonneg hqPos)]
      exact Int.mul_le_mul_of_nonneg_right hsLe hqPos
    have hB : ((q.num * s.denInt).natAbs : Int) ≤ (q.num.natAbs : Int) * (s.denInt * q.denInt) := by
      rw [Int.natAbs_mul, Int.natCast_mul, Int.natAbs_of_nonneg hsPos]
      have hGe1 : 1 ≤ q.denInt := by have := q.denInt_pos; omega
      have hMul := Int.mul_le_mul_of_nonneg_left hGe1
        (Int.mul_nonneg (by omega : 0 ≤ (q.num.natAbs : Int)) hsPos)
      rw [Int.mul_one, Int.mul_assoc] at hMul
      exact hMul
    have hM : (M : Int) * (s.denInt * q.denInt) =
        s.denInt * q.denInt + (q.num.natAbs : Int) * (s.denInt * q.denInt) := by
      have hmEq : (M : Int) = 1 + (q.num.natAbs : Int) := by dsimp [M]; omega
      rw [hmEq, Int.add_mul, Int.one_mul]
    omega
  have hProdAbs : ((s * s - q * q).num.natAbs : Int) ≤
      ((s - q).num.natAbs : Int) * ((M : Int) * (s.denInt * q.denInt)) := by
    rw [hFact, Int.natAbs_mul, Int.natCast_mul]
    exact Int.mul_le_mul_of_nonneg_left hSumAbs (by omega)
  unfold QVal.le
  rw [QVal.dist_denInt, QVal.mul_denInt, QVal.mul_denInt, QVal.mul_denInt, QVal.dist_denInt]
  change ((s * s - q * q).num.natAbs : Int) * (1 * (s.denInt * q.denInt)) ≤
    ((M : Int) * ((s - q).num.natAbs : Int)) * ((s.denInt * s.denInt) * (q.denInt * q.denInt))
  have hScaleXY : 0 ≤ s.denInt * q.denInt :=
    Int.mul_nonneg (by have := s.denInt_pos; omega) (by have := q.denInt_pos; omega)
  have hMul := Int.mul_le_mul_of_nonneg_right hProdAbs hScaleXY
  have hL : ((s * s - q * q).num.natAbs : Int) * (1 * (s.denInt * q.denInt)) =
      ((s * s - q * q).num.natAbs : Int) * (s.denInt * q.denInt) := by rw [Int.one_mul]
  have hR : (((s - q).num.natAbs : Int) * ((M : Int) * (s.denInt * q.denInt))) * (s.denInt * q.denInt) =
      ((M : Int) * ((s - q).num.natAbs : Int)) * ((s.denInt * s.denInt) * (q.denInt * q.denInt)) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- **Second Independence Theorem (`Transfer ⊬ st` over `QVal`)**:
    `invSqrt2Seq` is bounded in `[0, 1]` inside `HyperSeq QVal` (which satisfies Horn `Transfer`
    over `QVal`), yet **no rational `q : QVal`** is infinitely close to `invSqrt2Seq`! -/
theorem invSqrt2Seq_has_no_qval_standard_part (q : QVal) :
    ¬ Nonempty (InfinitelyClose invSqrt2Seq (starConst q)) := by
  rintro ⟨hClose⟩
  rcases qval_sq_dist_half_lower_bound q with ⟨K, hLower⟩
  let k1 : Nat := 2 * K + 1
  let M : Nat := q.num.natAbs + 1
  let kSq : Nat := M * (k1 + 1)
  let n : Nat := Nat.max (hClose.modulus kSq) k1
  have hn1 : hClose.modulus kSq ≤ n := Nat.le_max_left _ _
  have hn2 : k1 ≤ n := Nat.le_max_right _ _
  rcases invSqrt2Seq_spec n with ⟨hs0, hs1, hSqHalfN⟩
  have hSqHalf : QVal.le (QVal.dist (invSqrt2Seq n * invSqrt2Seq n) ⟨1, 1⟩) (QVal.unitFrac k1) :=
    QVal.le_trans hSqHalfN (QVal.unitFrac_anti hn2)
  have hDistSQ : QVal.le (QVal.dist (invSqrt2Seq n) q) (QVal.unitFrac kSq) :=
    hClose.spec kSq n hn1
  have hDiffBound := sq_diff_le_for_unit_and_any_q (q := q) hs0 hs1
  have hScaledSmall :
      QVal.le (QVal.ofNat M * QVal.dist (invSqrt2Seq n) q) (QVal.unitFrac k1) := by
    unfold QVal.le at hDistSQ ⊢
    rw [QVal.mul_denInt]
    let d := QVal.dist (invSqrt2Seq n) q
    have hdNonneg : 0 ≤ d.num := by change 0 ≤ ((invSqrt2Seq n - q).num.natAbs : Int); omega
    change d.num * ((M * (k1 + 1) + 1 : Nat) : Int) ≤ 1 * d.denInt at hDistSQ
    change ((M : Int) * d.num) * ((k1 + 1 : Nat) : Int) ≤ 1 * (1 * d.denInt)
    have hCoeff : (M : Int) * ((k1 + 1 : Nat) : Int) ≤ ((M * (k1 + 1) + 1 : Nat) : Int) := by
      have hCast : ((M * (k1 + 1) : Nat) : Int) = (M : Int) * ((k1 + 1 : Nat) : Int) :=
        Int.natCast_mul _ _
      omega
    have hMul := Int.mul_le_mul_of_nonneg_left hCoeff hdNonneg
    have hAssoc : ((M : Int) * d.num) * ((k1 + 1 : Nat) : Int) =
        d.num * ((M : Int) * ((k1 + 1 : Nat) : Int)) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  have hSqQ : QVal.le (QVal.dist (invSqrt2Seq n * invSqrt2Seq n) (q * q)) (QVal.unitFrac k1) :=
    QVal.le_trans hDiffBound hScaledSmall
  have hSymm := QVal.le_of_eqv_left
    (QVal.dist_symm (q * q) (invSqrt2Seq n * invSqrt2Seq n)) hSqQ
  have hTri := QVal.dist_triangle (q * q) (invSqrt2Seq n * invSqrt2Seq n) ⟨1, 1⟩
  have hUpper : QVal.le (QVal.dist (q * q) ⟨1, 1⟩) (QVal.unitFrac K) :=
    QVal.le_trans hTri (QVal.le_trans (QVal.add_le_add hSymm hSqHalf) (QVal.unitFrac_half_sum K))
  exact ((QVal.not_lt_iff_le _ _).mpr hUpper) hLower

end ReverseMath
end SandersNSA
