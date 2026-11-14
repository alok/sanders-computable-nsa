/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SandersNSA.Antipodes.ConstructiveAnalysis

/-!
# Constructive Hyperfinite Counting & Loeb Measure (`LoebMeasure`)

From Alok Singh's blog & NSA research notes (`2026-04-06` / `2026-04-09`) and Sam Sanders's
reverse-mathematics study of nonstandard measure and integration:
Peter Loeb's 1975 insight was that a **finitely additive** internal counting probability on a
hyperfinite grid `{0, 1, …, N}` induces a genuine $\sigma$-additive external measure via standard
parts and inner/outer internal approximations — **without** constructing ultrafilters when we
replace $\mathrm{st}(\mu_N(A))$ by quantitative modulus-equipped approximations!

This module provides:
1. `hyperfiniteCount` and `hyperfiniteProb` ($\mu_N(P) = |\{i \le N \mid P(i)\}| / (N + 1)$).
2. Exact Kolmogorov–Boolean algebra laws:
   - `hyperfiniteProb_bounds` ($0 \le \mu_N(P) \le 1$)
   - `hyperfiniteProb_false` ($\mu_N(\bot) \approx 0$) and `hyperfiniteProb_true` ($\mu_N(\top) \approx 1$)
   - `hyperfiniteCount_inclusion_exclusion` ($|P \lor R| + |P \land R| = |P| + |R|$)
   - `hyperfiniteProb_disjoint_or` (finite additivity on disjoint events)
   - `hyperfiniteProb_complement` ($\mu_N(P) + \mu_N(\neg P) \approx 1$)
   - `hyperfiniteProb_mono` (monotonicity)
3. `LoebApproximable`: inner/outer internal Boolean event sandwiches squeezing the measure gap
   below $1 / (k + 1)$, with computable extraction of the Loeb measure Cauchy sequence
   (`extractLoebMeasureSeq`).
4. **Hyperfinite Expectation ↔ Constructive Riemann Integral Bridge**:
   `hyperfiniteExpect_grid_eq_riemannSum` (`hyperfiniteExpect N (fun i => f (gridPt N i)) = uniformGridSum f N`)
   and `loebGridExpect_converges_to_integral`.
-/

namespace SandersNSA
namespace ReverseMath

open SandersNSA.Antipodes

/-! ## 1. Hyperfinite Counting Measure on `{0, 1, …, N}` -/

/-- Count how many indices `i < m` satisfy decidable internal predicate `P`. -/
def hyperfiniteCount (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => hyperfiniteCount P m + (if P m then 1 else 0)

/-- Uniform hyperfinite counting probability on `{0, 1, …, N}` (`N + 1` grid points):
    `μ_N(P) := |{i ≤ N | P i = true}| / (N + 1)`. -/
def hyperfiniteProb (N : Nat) (P : Nat → Bool) : QVal :=
  ⟨(hyperfiniteCount P (N + 1) : Int), N⟩

theorem hyperfiniteCount_le : ∀ (P : Nat → Bool) (m : Nat), hyperfiniteCount P m ≤ m
  | _, 0 => Nat.le_refl 0
  | P, m + 1 => by
      simp only [hyperfiniteCount]
      have ih := hyperfiniteCount_le P m
      cases hP : P m <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem hyperfiniteCount_true : ∀ m : Nat, hyperfiniteCount (fun _ => true) m = m
  | 0 => rfl
  | m + 1 => by
      simp only [hyperfiniteCount, ↓reduceIte]
      rw [hyperfiniteCount_true m]

theorem hyperfiniteCount_false : ∀ m : Nat, hyperfiniteCount (fun _ => false) m = 0
  | 0 => rfl
  | m + 1 => by
      simp only [hyperfiniteCount, Bool.false_eq_true, ↓reduceIte]
      rw [hyperfiniteCount_false m]

theorem hyperfiniteCount_mono {P R : Nat → Bool} :
    ∀ (m : Nat), (∀ i : Nat, i < m → P i = true → R i = true) →
      hyperfiniteCount P m ≤ hyperfiniteCount R m
  | 0, _ => Nat.le_refl 0
  | m + 1, hImp => by
      simp only [hyperfiniteCount]
      have ih := hyperfiniteCount_mono m (fun i hi => hImp i (by omega))
      have hTop := hImp m (Nat.lt_succ_self m)
      cases hP : P m
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases R m <;> omega
      · have hR : R m = true := hTop hP
        simp only [hR, ↓reduceIte]
        omega

/-- **Exact Hyperfinite Inclusion-Exclusion**:
    `|P ∨ R| + |P ∧ R| = |P| + |R|` on `{0, …, m - 1}`. -/
theorem hyperfiniteCount_inclusion_exclusion (P R : Nat → Bool) :
    ∀ m : Nat,
      hyperfiniteCount (fun i => P i || R i) m +
      hyperfiniteCount (fun i => P i && R i) m =
      hyperfiniteCount P m + hyperfiniteCount R m
  | 0 => rfl
  | m + 1 => by
      simp only [hyperfiniteCount]
      have ih := hyperfiniteCount_inclusion_exclusion P R m
      have hPB : P m = false ∨ P m = true := by cases P m <;> simp
      have hRB : R m = false ∨ R m = true := by cases R m <;> simp
      rcases hPB with hP | hP <;> rcases hRB with hR | hR <;>
        simp only [hP, hR, Bool.or_true, Bool.or_false,
          Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem hyperfiniteCount_disjoint_or {P R : Nat → Bool} :
    ∀ (m : Nat),
      (∀ i : Nat, i < m → ¬ (P i = true ∧ R i = true)) →
      hyperfiniteCount (fun i => P i || R i) m =
      hyperfiniteCount P m + hyperfiniteCount R m
  | 0, _ => rfl
  | m + 1, hDisj => by
      have hIE := hyperfiniteCount_inclusion_exclusion P R (m + 1)
      have hAndZero : hyperfiniteCount (fun i => P i && R i) (m + 1) = 0 := by
        have hLe : hyperfiniteCount (fun i => P i && R i) (m + 1) ≤
            hyperfiniteCount (fun _ => false) (m + 1) := by
          apply hyperfiniteCount_mono
          intro i hi hBoth
          simp only [Bool.and_eq_true] at hBoth
          exact False.elim (hDisj i hi hBoth)
        rw [hyperfiniteCount_false] at hLe
        omega
      omega

theorem hyperfiniteCount_complement (P : Nat → Bool) :
    ∀ m : Nat, hyperfiniteCount P m + hyperfiniteCount (fun i => !P i) m = m
  | 0 => rfl
  | m + 1 => by
      simp only [hyperfiniteCount]
      have ih := hyperfiniteCount_complement P m
      have hPB : P m = false ∨ P m = true := by cases P m <;> simp
      rcases hPB with hP | hP <;>
        simp only [hP, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ## 2. Verified Probability Algebra Laws on `QVal` -/

/-- `0 ≤ μ_N(P) ≤ 1` for every internal Boolean event `P`. -/
theorem hyperfiniteProb_bounds (N : Nat) (P : Nat → Bool) :
    QVal.le 0 (hyperfiniteProb N P) ∧ QVal.le (hyperfiniteProb N P) 1 := by
  have hBound := hyperfiniteCount_le P (N + 1)
  constructor
  · change (0 : Int) * ((N + 1 : Nat) : Int) ≤ (hyperfiniteCount P (N + 1) : Int) * 1
    omega
  · change (hyperfiniteCount P (N + 1) : Int) * 1 ≤ 1 * ((N + 1 : Nat) : Int)
    omega

theorem hyperfiniteProb_false (N : Nat) :
    QVal.eqv (hyperfiniteProb N (fun _ => false)) 0 := by
  unfold hyperfiniteProb QVal.eqv
  rw [hyperfiniteCount_false]
  change (0 : Int) * 1 = 0 * ((N + 1 : Nat) : Int)
  omega

theorem hyperfiniteProb_true (N : Nat) :
    QVal.eqv (hyperfiniteProb N (fun _ => true)) 1 := by
  unfold hyperfiniteProb QVal.eqv
  rw [hyperfiniteCount_true]
  change ((N + 1 : Nat) : Int) * 1 = 1 * ((N + 1 : Nat) : Int)
  omega

theorem hyperfiniteProb_mono {N : Nat} {P R : Nat → Bool}
    (hImp : ∀ i : Nat, i ≤ N → P i = true → R i = true) :
    QVal.le (hyperfiniteProb N P) (hyperfiniteProb N R) := by
  have hCount := hyperfiniteCount_mono (N + 1) (fun i hi => hImp i (by omega))
  unfold hyperfiniteProb QVal.le
  change (hyperfiniteCount P (N + 1) : Int) * ((N + 1 : Nat) : Int) ≤
    (hyperfiniteCount R (N + 1) : Int) * ((N + 1 : Nat) : Int)
  exact Int.mul_le_mul_of_nonneg_right (by omega) (by omega)

theorem qval_same_den_add (a b : Int) (N : Nat) :
    QVal.eqv ⟨a + b, N⟩ (⟨a, N⟩ + ⟨b, N⟩) := by
  unfold QVal.eqv
  have hAddNum : (⟨a, N⟩ + ⟨b, N⟩ : QVal).num =
      a * ((N + 1 : Nat) : Int) + b * ((N + 1 : Nat) : Int) := rfl
  rw [hAddNum, QVal.add_denInt]
  change (a + b) * (((N + 1 : Nat) : Int) * ((N + 1 : Nat) : Int)) =
    (a * ((N + 1 : Nat) : Int) + b * ((N + 1 : Nat) : Int)) * ((N + 1 : Nat) : Int)
  rw [Int.add_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc]

/-- **Finite Additivity of Hyperfinite Counting Probability**:
    Whenever `P` and `R` are disjoint on `{0, …, N}`,
    `μ_N(P ∨ R) ≈ μ_N(P) + μ_N(R)`. -/
theorem hyperfiniteProb_disjoint_or {N : Nat} {P R : Nat → Bool}
    (hDisj : ∀ i : Nat, i ≤ N → ¬ (P i = true ∧ R i = true)) :
    QVal.eqv (hyperfiniteProb N (fun i => P i || R i))
      (hyperfiniteProb N P + hyperfiniteProb N R) := by
  unfold hyperfiniteProb
  rw [hyperfiniteCount_disjoint_or (N + 1) (fun i hi => hDisj i (by omega))]
  have hCast : ((hyperfiniteCount P (N + 1) + hyperfiniteCount R (N + 1) : Nat) : Int) =
      (hyperfiniteCount P (N + 1) : Int) + (hyperfiniteCount R (N + 1) : Int) := by omega
  rw [hCast]
  exact qval_same_den_add _ _ N

/-- **Complement Probability Law**: `μ_N(P) + μ_N(¬P) ≈ 1`. -/
theorem hyperfiniteProb_complement (N : Nat) (P : Nat → Bool) :
    QVal.eqv (hyperfiniteProb N P + hyperfiniteProb N (fun i => !P i)) 1 := by
  unfold hyperfiniteProb
  have hSymm := QVal.eqv_symm
    (qval_same_den_add (hyperfiniteCount P (N + 1) : Int)
      (hyperfiniteCount (fun i => !P i) (N + 1) : Int) N)
  have hComp := hyperfiniteCount_complement P (N + 1)
  have hCast : (hyperfiniteCount P (N + 1) : Int) +
      (hyperfiniteCount (fun i => !P i) (N + 1) : Int) = ((N + 1 : Nat) : Int) := by omega
  have hOne : QVal.eqv ⟨(hyperfiniteCount P (N + 1) : Int) +
      (hyperfiniteCount (fun i => !P i) (N + 1) : Int), N⟩ 1 := by
    unfold QVal.eqv
    rw [hCast]
    change ((N + 1 : Nat) : Int) * 1 = 1 * ((N + 1 : Nat) : Int)
    omega
  exact QVal.eqv_trans hSymm hOne

/-! ## 3. Constructive Carathéodory–Loeb Measurability -/

/-- Constructive Carathéodory–Loeb measurable event family:
    Sandwiched at every precision scale `k` by decidable internal inner and outer events
    `inner k N, outer k N : Nat → Bool` with `inner ⊆ outer`, measure gap `≤ 1 / (k + 1)`
    past grid horizon `gapMod k`, and Cauchy stabilization of the inner measures along diagonal
    resolutions! -/
structure LoebApproximable : Type where
  inner : Nat → Nat → Nat → Bool
  outer : Nat → Nat → Nat → Bool
  gapMod : Modulus
  nested : ∀ (k N i : Nat), i ≤ N → inner k N i = true → outer k N i = true
  gapSmall : ∀ (k N : Nat),
    gapMod k ≤ N →
    QVal.le (QVal.dist (hyperfiniteProb N (outer k N)) (hyperfiniteProb N (inner k N)))
      (QVal.unitFrac k)
  diagCauchy : CauchySeqWithModulus (fun k => hyperfiniteProb (gapMod k) (inner k (gapMod k)))

/-- Computably extract the **Loeb outer diagonal measure** Cauchy sequence and prove it agrees
    within `1 / (k + 1)` with the inner diagonal sequence! -/
def loebOuterSeq (L : LoebApproximable) (k : Nat) : QVal :=
  let N := L.gapMod k
  hyperfiniteProb N (L.outer k N)

def loebInnerSeq (L : LoebApproximable) (k : Nat) : QVal :=
  let N := L.gapMod k
  hyperfiniteProb N (L.inner k N)

theorem loeb_inner_outer_squeeze (L : LoebApproximable) (k : Nat) :
    QVal.le (loebInnerSeq L k) (loebOuterSeq L k) ∧
    QVal.le (QVal.dist (loebOuterSeq L k) (loebInnerSeq L k)) (QVal.unitFrac k) :=
  ⟨hyperfiniteProb_mono (L.nested k (L.gapMod k)),
   L.gapSmall k (L.gapMod k) (Nat.le_refl _)⟩

/-! ## 4. Hyperfinite Expectation ↔ Constructive Riemann Integral Bridge -/

/-- Sum `∑_{i=0}^{m-1} g(i)` of an internal `QVal`-valued random variable `g : Nat → QVal`. -/
def hyperfiniteSum (g : Nat → QVal) : Nat → QVal
  | 0 => 0
  | m + 1 => hyperfiniteSum g m + g m

/-- Uniform hyperfinite expectation `𝔼_N[g] := (1 / (N + 1)) * ∑_{i=0}^{N} g(i)`. -/
def hyperfiniteExpect (N : Nat) (g : Nat → QVal) : QVal :=
  QVal.unitFrac N * hyperfiniteSum g (N + 1)

theorem hyperfiniteSum_grid_eq_uniformGridSumAux (f : QVal → QVal) (N : Nat) :
    ∀ m : Nat, hyperfiniteSum (fun i => f (QVal.gridPt N i)) m = uniformGridSumAux f N m
  | 0 => rfl
  | m + 1 => by
      simp only [hyperfiniteSum, uniformGridSumAux]
      rw [hyperfiniteSum_grid_eq_uniformGridSumAux f N m]

/-- **Exact Loeb–Riemann Expectation Identity**:
    Evaluating the uniform hyperfinite expectation `𝔼_N` on the grid-sampled function
    `i ↦ f(i / (N + 1))` equals `uniformGridSum f N` **syntactically** (`=`, not merely `≈`)! -/
theorem hyperfiniteExpect_grid_eq_riemannSum (f : QVal → QVal) (N : Nat) :
    hyperfiniteExpect N (fun i => f (QVal.gridPt N i)) = uniformGridSum f N := by
  unfold hyperfiniteExpect uniformGridSum
  rw [hyperfiniteSum_grid_eq_uniformGridSumAux f N (N + 1)]

/-- Every constructively Riemann-integrable `f` has hyperfinite grid expectations converging
    quantitatively to `hInt.integral` with the exact same modulus `hInt.modulus`! -/
def loebGridExpect_converges_to_integral {f : QVal → QVal}
    (hInt : RiemannIntegrableWithModulus f) :
    LimitWithModulus (fun N => hyperfiniteExpect N (fun i => f (QVal.gridPt N i))) hInt.integral where
  modulus := hInt.modulus
  spec k N hN := by
    rw [hyperfiniteExpect_grid_eq_riemannSum]
    exact hInt.spec k N hN

end ReverseMath
end SandersNSA
