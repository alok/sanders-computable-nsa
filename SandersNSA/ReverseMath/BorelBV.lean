/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.ReverseMath.Independence

/-!
# Borel's Height Countability & Jordan Bounded Variation (`BorelBV`)

Formalizes two closely intertwined threads from Dag Normann & Sam Sanders (`arXiv:2208.03027`,
*"On the uncountability of ℝ"*) discussed in the January 31, 2024 interview:

1. **Three Inequivalent Constructive/HORM Notions of Countability**:
   - `EnumerationCountable`: surjective/covering sequence `Nat → α`.
   - `InjectionCountable`: injection `{ x // S x } → Nat`.
   - `HeightCountable` (**Émile Borel's height-function countability**): a height map
     `height : α → Nat` accompanied by finite sublevel enumerations `sublevel : Nat → List α`
     certifying `{ x ∈ S | height x ≤ H } ⊆ sublevel H`.
2. **Computable Jordan Bounded Variation (`BV`) & Decomposition**:
   - `posVariation`, `negVariation`, `totalVariation` over rational sequences `Nat → QVal`.
   - Monotonicity (`posVariation_mono`, `negVariation_mono`), exact total-variation splitting
     (`totalVariation_eqv_sum`), and **Jordan's Decomposition Theorem**
     (`jordan_decomposition`: `f(0) + P(n) - N(n) ≈ f(n)`).
3. **Borel Height Bound on `BV` Jumps (`borel_jump_height_bound`)**:
   - Proves that if `totalVariation f n ≤ V`, the number of `1 / (k + 1)`-jumps in `0 .. n`
     is bounded by `(k + 1) * V`, exhibiting how `BV` jump sets carry canonical Borel heights.
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Enumeration, Injection & Borel Height Countability -/

/-- Classical/sequential countability via an enumerating map `enum : Nat → α`. -/
structure EnumerationCountable (α : Type) (S : α → Prop) : Type where
  enum : Nat → α
  covers : ∀ x : α, S x → ∃ n : Nat, enum n = x

/-- Set-theoretic countability via an injection into `Nat` (`NIN` dual). -/
structure InjectionCountable (α : Type) (S : α → Prop) : Type where
  code : α → Nat
  injectiveOn : ∀ x y : α, S x → S y → code x = code y → x = y

/-- **Émile Borel's Height Countability** (`arXiv:2208.03027`):
    `S` is decomposing into finite sublevels `{ x ∈ S | height x ≤ H }` witnessed by an
    explicit computable list realiser `sublevel : Nat → List α`. -/
structure HeightCountable (α : Type) (S : α → Prop) : Type where
  height : α → Nat
  sublevel : Nat → List α
  finiteSublevel : ∀ (H : Nat) (x : α), S x → height x ≤ H → x ∈ sublevel H

/-- Every `HeightCountable` witness with inhabited default `d : α` computably flattens into
    a prefix-indexed enumeration sequence, whereas the converse (`InjectionCountable → HeightCountable`)
    requires non-constructive comprehension in Higher-Order Reverse Mathematics! -/
def flattenSublevels {α : Type} (sublevel : Nat → List α) : Nat → List α
  | 0 => sublevel 0
  | H + 1 => flattenSublevels sublevel H ++ sublevel (H + 1)

theorem subset_flattenSublevels {α : Type} (sublevel : Nat → List α) :
    ∀ {H : Nat} {x : α}, x ∈ sublevel H → x ∈ flattenSublevels sublevel H
  | 0, _, hx => hx
  | _ + 1, _, hx => List.mem_append_right _ hx

/-- Any finite list `xs : List α` carries a canonical `HeightCountable` structure with height `0`. -/
def heightCountableOfList {α : Type} (xs : List α) :
    HeightCountable α (fun x => x ∈ xs) where
  height _ := 0
  sublevel _ := xs
  finiteSublevel _ _ hx _ := hx

/-! ## 2. Computable Jordan Bounded Variation (`BV`) -/

/-- Positive increment `max(b - a, 0)` computed branchlessly via `QVal.leB`. -/
def posStep (a b : QVal) : QVal :=
  if QVal.leB a b then b - a else 0

/-- Negative increment `max(a - b, 0)` computed branchlessly via `QVal.leB`. -/
def negStep (a b : QVal) : QVal :=
  if QVal.leB a b then 0 else a - b

/-- Cumulative positive variation `P(n) = ∑_{i < n} (f(i+1) - f(i))⁺`. -/
def posVariation (f : Nat → QVal) : Nat → QVal
  | 0 => 0
  | n + 1 => posVariation f n + posStep (f n) (f (n + 1))

/-- Cumulative negative variation `N(n) = ∑_{i < n} (f(i+1) - f(i))⁻`. -/
def negVariation (f : Nat → QVal) : Nat → QVal
  | 0 => 0
  | n + 1 => negVariation f n + negStep (f n) (f (n + 1))

/-- Cumulative total variation `TV(n) = ∑_{i < n} |f(i+1) - f(i)|`. -/
def totalVariation (f : Nat → QVal) : Nat → QVal
  | 0 => 0
  | n + 1 => totalVariation f n + QVal.dist (f (n + 1)) (f n)

theorem qval_add_num (p q : QVal) : (p + q).num = p.num * q.denInt + q.num * p.denInt := rfl

theorem qval_add_zero_eqv (a : QVal) : QVal.eqv (a + 0) a := by
  unfold QVal.eqv
  rw [qval_add_num, QVal.add_denInt]
  change (a.num * 1 + 0 * a.denInt) * a.denInt = a.num * (a.denInt * 1)
  rw [Int.mul_one, Int.zero_mul, Int.add_zero, Int.mul_one]

theorem qval_zero_add_eqv (a : QVal) : QVal.eqv (0 + a) a := by
  unfold QVal.eqv
  rw [qval_add_num, QVal.add_denInt]
  change (0 * a.denInt + a.num * 1) * a.denInt = a.num * (1 * a.denInt)
  rw [Int.zero_mul, Int.mul_one, Int.zero_add, Int.one_mul]

theorem qval_neg_congr {a a' : QVal} (h : QVal.eqv a a') : QVal.eqv (-a) (-a') := by
  unfold QVal.eqv at *
  change (-a.num) * a'.denInt = (-a'.num) * a.denInt
  rw [Int.neg_mul, Int.neg_mul, h]

theorem qval_sub_congr {a a' b b' : QVal} (ha : QVal.eqv a a') (hb : QVal.eqv b b') :
    QVal.eqv (a - b) (a' - b') :=
  qval_add_congr ha (qval_neg_congr hb)

theorem qval_add_comm (a b : QVal) : QVal.eqv (a + b) (b + a) := by
  unfold QVal.eqv
  rw [qval_add_num, qval_add_num, QVal.add_denInt, QVal.add_denInt,
      Int.add_comm (a.num * b.denInt), Int.mul_comm a.denInt b.denInt]

theorem qval_add_assoc (a b c : QVal) : QVal.eqv ((a + b) + c) (a + (b + c)) := by
  unfold QVal.eqv
  simp only [qval_add_num, QVal.add_denInt, Int.add_mul]
  have hd : a.denInt * (b.denInt * c.denInt) = a.denInt * b.denInt * c.denInt := by
    rw [Int.mul_assoc]
  rw [hd]
  have m1 : a.num * (b.denInt * c.denInt) = a.num * b.denInt * c.denInt := by
    rw [Int.mul_assoc]
  have m2 : b.num * c.denInt * a.denInt = b.num * a.denInt * c.denInt := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have m3 : c.num * b.denInt * a.denInt = c.num * (a.denInt * b.denInt) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  rw [m1, m2, m3, Int.add_assoc]

theorem qval_sub_self_eqv_zero (a : QVal) : QVal.eqv (a - a) 0 := by
  unfold QVal.eqv
  rw [QVal.sub_num, QVal.sub_denInt]
  change (a.num * a.denInt - a.num * a.denInt) * 1 = 0 * (a.denInt * a.denInt)
  rw [Int.sub_self, Int.zero_mul, Int.zero_mul]

theorem posStep_nonneg (a b : QVal) : QVal.le 0 (posStep a b) := by
  unfold posStep
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact QVal.le_refl 0
  · simp only [↓reduceIte]
    have hab : QVal.le a b := (QVal.leB_true_iff a b).mp h
    unfold QVal.le at hab ⊢
    rw [QVal.sub_num]
    change 0 * (b - a).denInt ≤ (b.num * a.denInt - a.num * b.denInt) * 1
    omega

theorem negStep_nonneg (a b : QVal) : QVal.le 0 (negStep a b) := by
  unfold negStep
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hba : QVal.le b a := QVal.leB_false_imp_le h
    unfold QVal.le at hba ⊢
    rw [QVal.sub_num]
    change 0 * (a - b).denInt ≤ (a.num * b.denInt - b.num * a.denInt) * 1
    omega
  · simp only [↓reduceIte]
    exact QVal.le_refl 0

theorem step_diff_eqv (a b : QVal) : QVal.eqv (posStep a b - negStep a b) (b - a) := by
  unfold posStep negStep
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold QVal.eqv
    simp only [QVal.sub_num, QVal.sub_denInt]
    have hzNum : (0 : QVal).num = 0 := rfl
    have hzDen : (0 : QVal).denInt = 1 := rfl
    rw [hzNum, hzDen, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_sub, Int.neg_sub]
    exact congrArg (fun z => (b.num * a.denInt - a.num * b.denInt) * z) (Int.mul_comm _ _)
  · simp only [↓reduceIte]
    exact qval_add_zero_eqv (b - a)

theorem step_sum_eqv_dist (a b : QVal) :
    QVal.eqv (posStep a b + negStep a b) (QVal.dist b a) := by
  unfold posStep negStep
  cases h : QVal.leB a b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hba : QVal.le b a := QVal.leB_false_imp_le h
    have h1 := qval_zero_add_eqv (a - b)
    have h2 := QVal.eqv_symm (QVal.dist_eqv_sub_of_le hba)
    have h3 := QVal.dist_symm a b
    exact QVal.eqv_trans h1 (QVal.eqv_trans h2 h3)
  · simp only [↓reduceIte]
    have hab : QVal.le a b := (QVal.leB_true_iff a b).mp h
    exact QVal.eqv_trans (qval_add_zero_eqv (b - a))
      (QVal.eqv_symm (QVal.dist_eqv_sub_of_le hab))

theorem posVariation_step_le (f : Nat → QVal) (n : Nat) :
    QVal.le (posVariation f n) (posVariation f (n + 1)) := by
  change QVal.le (posVariation f n) (posVariation f n + posStep (f n) (f (n + 1)))
  have h0 := QVal.add_le_add (QVal.le_refl (posVariation f n)) (posStep_nonneg (f n) (f (n + 1)))
  exact QVal.le_of_eqv_left (QVal.eqv_symm (qval_add_zero_eqv (posVariation f n))) h0

theorem negVariation_step_le (f : Nat → QVal) (n : Nat) :
    QVal.le (negVariation f n) (negVariation f (n + 1)) := by
  change QVal.le (negVariation f n) (negVariation f n + negStep (f n) (f (n + 1)))
  have h0 := QVal.add_le_add (QVal.le_refl (negVariation f n)) (negStep_nonneg (f n) (f (n + 1)))
  exact QVal.le_of_eqv_left (QVal.eqv_symm (qval_add_zero_eqv (negVariation f n))) h0

/-- `posVariation f` is monotone non-decreasing (`i ≤ j → P(i) ≤ P(j)`). -/
theorem posVariation_mono (f : Nat → QVal) {i j : Nat} (hij : i ≤ j) :
    QVal.le (posVariation f i) (posVariation f j) := by
  induction j with
  | zero =>
      have hi0 : i = 0 := by omega
      subst hi0
      exact QVal.le_refl _
  | succ m ih =>
      by_cases hEq : i = m + 1
      · subst hEq
        exact QVal.le_refl _
      · exact QVal.le_trans (ih (by omega)) (posVariation_step_le f m)

/-- `negVariation f` is monotone non-decreasing (`i ≤ j → N(i) ≤ N(j)`). -/
theorem negVariation_mono (f : Nat → QVal) {i j : Nat} (hij : i ≤ j) :
    QVal.le (negVariation f i) (negVariation f j) := by
  induction j with
  | zero =>
      have hi0 : i = 0 := by omega
      subst hi0
      exact QVal.le_refl _
  | succ m ih =>
      by_cases hEq : i = m + 1
      · subst hEq
        exact QVal.le_refl _
      · exact QVal.le_trans (ih (by omega)) (negVariation_step_le f m)

theorem qval_add_four_swap (a b c d : QVal) :
    QVal.eqv ((a + b) + (c + d)) ((a + c) + (b + d)) := by
  have h1 := qval_add_assoc a b (c + d)
  have h2 : QVal.eqv (b + (c + d)) (c + (b + d)) :=
    QVal.eqv_trans (QVal.eqv_symm (qval_add_assoc b c d))
      (QVal.eqv_trans (qval_add_congr (qval_add_comm b c) (QVal.eqv_refl d))
        (qval_add_assoc c b d))
  have h3 := qval_add_congr (QVal.eqv_refl a) h2
  have h4 := QVal.eqv_symm (qval_add_assoc a c (b + d))
  exact QVal.eqv_trans h1 (QVal.eqv_trans h3 h4)

theorem qval_neg_add (a b : QVal) : QVal.eqv (-(a + b)) ((-a) + (-b)) := by
  unfold QVal.eqv
  have hNegNum : ∀ p : QVal, (-p).num = -p.num := fun _ => rfl
  have hNegDen : ∀ p : QVal, (-p).denInt = p.denInt := fun _ => rfl
  rw [hNegNum, hNegDen, qval_add_num, qval_add_num, QVal.add_denInt, QVal.add_denInt,
      hNegNum, hNegNum, hNegDen, hNegDen]
  rw [Int.neg_add, Int.neg_mul, Int.neg_mul]

theorem qval_rearrange_step (A P dp N dn x y : QVal)
    (hBase : QVal.eqv (A + P - N) x)
    (hStep : QVal.eqv (dp - dn) (y - x)) :
    QVal.eqv (A + (P + dp) - (N + dn)) y := by
  -- Note `u - v` is definitionally `u + (-v)`!
  have hSubDef : ∀ u v : QVal, u - v = u + (-v) := fun _ _ => rfl
  rw [hSubDef] at hBase hStep ⊢
  rw [hSubDef y x] at hStep
  have hAssocL : QVal.eqv (A + (P + dp) + -(N + dn)) (((A + P) + dp) + ((-N) + (-dn))) :=
    qval_add_congr (QVal.eqv_symm (qval_add_assoc A P dp)) (qval_neg_add N dn)
  have hSwap := qval_add_four_swap (A + P) dp (-N) (-dn)
  have hPlug := qval_add_congr hBase hStep
  have hCancel : QVal.eqv (x + (y + (-x))) y := by
    have c1 := QVal.eqv_trans (qval_add_comm x (y + (-x)))
      (qval_add_assoc y (-x) x)
    have c2 : QVal.eqv ((-x) + x) 0 :=
      QVal.eqv_trans (qval_add_comm (-x) x) (qval_sub_self_eqv_zero x)
    exact QVal.eqv_trans c1
      (QVal.eqv_trans (qval_add_congr (QVal.eqv_refl y) c2) (qval_add_zero_eqv y))
  exact QVal.eqv_trans hAssocL
    (QVal.eqv_trans hSwap (QVal.eqv_trans hPlug hCancel))

/-- **Jordan Decomposition Theorem**:
    Every discrete rational function `f : Nat → QVal` decomposes identically into the
    difference of two monotone non-decreasing functions (`posVariation` and `negVariation`):
    `f(0) + P(n) - N(n) ≈ f(n)`. -/
theorem jordan_decomposition (f : Nat → QVal) :
    ∀ n : Nat, QVal.eqv (f 0 + posVariation f n - negVariation f n) (f n)
  | 0 => by
      change QVal.eqv (f 0 + 0 - 0) (f 0)
      exact QVal.eqv_trans
        (qval_sub_congr (qval_add_zero_eqv (f 0)) (QVal.eqv_refl 0))
        (qval_add_zero_eqv (f 0))
  | n + 1 => by
      change QVal.eqv
        (f 0 + (posVariation f n + posStep (f n) (f (n + 1))) -
          (negVariation f n + negStep (f n) (f (n + 1))))
        (f (n + 1))
      exact qval_rearrange_step (f 0) (posVariation f n) (posStep (f n) (f (n + 1)))
        (negVariation f n) (negStep (f n) (f (n + 1))) (f n) (f (n + 1))
        (jordan_decomposition f n) (step_diff_eqv (f n) (f (n + 1)))

/-- Total variation splits additively as `P(n) + N(n) ≈ TV(n)`. -/
theorem totalVariation_eqv_sum (f : Nat → QVal) :
    ∀ n : Nat, QVal.eqv (posVariation f n + negVariation f n) (totalVariation f n)
  | 0 => by
      change QVal.eqv (0 + 0) 0
      exact qval_add_zero_eqv 0
  | n + 1 => by
      change QVal.eqv
        ((posVariation f n + posStep (f n) (f (n + 1))) +
         (negVariation f n + negStep (f n) (f (n + 1))))
        (totalVariation f n + QVal.dist (f (n + 1)) (f n))
      have ih := totalVariation_eqv_sum f n
      have hStep := step_sum_eqv_dist (f n) (f (n + 1))
      have hComm := qval_add_four_swap
        (posVariation f n) (posStep (f n) (f (n + 1)))
        (negVariation f n) (negStep (f n) (f (n + 1)))
      exact QVal.eqv_trans hComm (qval_add_congr ih hStep)

/-! ## 3. Borel Jump-Height Bound for Bounded Variation Functions -/

/-- Count how many steps `i < n` exhibit a jump `|f(i+1) - f(i)| ≥ 1 / (k + 1)`. -/
def countLargeJumps (f : Nat → QVal) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let prev := countLargeJumps f k n
      if QVal.leB (QVal.unitFrac k) (QVal.dist (f (n + 1)) (f n)) then prev + 1 else prev

theorem countLargeJumps_mul_le_tv (f : Nat → QVal) (k : Nat) :
    ∀ n : Nat,
      QVal.le ⟨(countLargeJumps f k n : Int), k⟩ (totalVariation f n)
  | 0 => by
      unfold countLargeJumps totalVariation
      change (0 : Int) * 1 ≤ 0 * ((k + 1 : Nat) : Int)
      omega
  | n + 1 => by
      unfold countLargeJumps totalVariation
      dsimp
      have ih := countLargeJumps_mul_le_tv f k n
      cases hJump : QVal.leB (QVal.unitFrac k) (QVal.dist (f (n + 1)) (f n))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hDistNonneg : QVal.le 0 (QVal.dist (f (n + 1)) (f n)) := QVal.dist_nonneg _ _
        have hSum := QVal.add_le_add ih hDistNonneg
        exact QVal.le_of_eqv_left (QVal.eqv_symm (qval_add_zero_eqv _)) hSum
      · simp only [↓reduceIte]
        have hStepGe : QVal.le (QVal.unitFrac k) (QVal.dist (f (n + 1)) (f n)) :=
          (QVal.leB_true_iff _ _).mp hJump
        have hSum := QVal.add_le_add ih hStepGe
        have hEqv : QVal.eqv ⟨((countLargeJumps f k n + 1 : Nat) : Int), k⟩
            (⟨(countLargeJumps f k n : Int), k⟩ + QVal.unitFrac k) := by
          unfold QVal.eqv
          rw [qval_add_num, QVal.add_denInt]
          change ((countLargeJumps f k n + 1 : Nat) : Int) *
              (((k + 1 : Nat) : Int) * ((k + 1 : Nat) : Int)) =
            ((countLargeJumps f k n : Int) * ((k + 1 : Nat) : Int) +
              1 * ((k + 1 : Nat) : Int)) * ((k + 1 : Nat) : Int)
          have hSucc : ((countLargeJumps f k n + 1 : Nat) : Int) =
              (countLargeJumps f k n : Int) + 1 := by omega
          rw [hSucc, Int.add_mul, Int.add_mul, Int.one_mul, Int.one_mul, Int.mul_assoc]
        exact QVal.le_of_eqv_left hEqv hSum

/-- **Borel Height Bound on `BV` Jumps**:
    If `totalVariation f n ≤ V` (`V : Nat`), then at most `(k + 1) * V` steps in `0 .. n`
    have oscillation `≥ 1 / (k + 1)`. -/
theorem borel_jump_height_bound {f : Nat → QVal} {k n V : Nat}
    (hTV : QVal.le (totalVariation f n) (QVal.ofNat V)) :
    countLargeJumps f k n ≤ (k + 1) * V := by
  have hChain := QVal.le_trans (countLargeJumps_mul_le_tv f k n) hTV
  unfold QVal.le at hChain
  change (countLargeJumps f k n : Int) * 1 ≤ (V : Int) * ((k + 1 : Nat) : Int) at hChain
  have hCast : ((V * (k + 1) : Nat) : Int) = (V : Int) * ((k + 1 : Nat) : Int) :=
    Int.natCast_mul _ _
  have hComm : (k + 1) * V = V * (k + 1) := Nat.mul_comm _ _
  omega

end ReverseMath
end SandersNSA
