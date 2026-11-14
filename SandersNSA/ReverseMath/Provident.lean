/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Adrian Mathias's Provident Set Theory (`Provident`)

From Alok Singh's Jan 31, 2024 interview and follow-up correspondence with Sam Sanders:
Adrian Mathias's **Provident Set Theory (`PROV`)** (*"Provident sets and rudimentary set
functions"*, Fund. Math. 2015) is the weak, computationally tame set theory **without the
Powerset Axiom** or $\omega$-Infinity Axiom that still closes under rudimentary ($\Delta_0$)
operations, Jensen hierarchies, relative complements, Cartesian products, and ordinal arithmetic.

We give a 100% computable, structurally recursive realization of `PROV` over hereditarily finite
tree representations (`HF`) equipped with:
1. Decidable structural-fuel extensional equality `extEqB` and membership `memB`.
2. **Full Set-Theoretic Extensionality (`extEqB_iff_forall_memB`)**:
   `extEqB a b = true ↔ ∀ z : HF, memB z a = memB z b`.
3. **Powerset-Free Rudimentary / Provident Closure**:
   - `empty` ($\emptyset$), `upair` ($\{a, b\}$), `singleton` ($\{a\}$), `kpair` (Kuratowski $\langle a, b\rangle$)
   - `union2` ($a \cup b$), `sUnion` ($\bigcup a$)
   - `sep` ($\Delta_0$-Separation $\{x \in a \mid P(x)\}$), `sdiff` ($a \setminus b$)
   - `repl` ($\Delta_0$-Replacement $\{F(x) \mid x \in a\}$)
   - `cartesian` ($a \times b$ constructed purely from `sUnion` + `repl` **without Powerset**!)
   - `vonNeumann` (finite ordinals $0, 1, 2, \dots$ with linear representation size `n`,
     contrasting with the $2^{2^{\dots}}$ blowup of iterated powersets).
-/

namespace SandersNSA
namespace ReverseMath

/-- Computable tree representation of hereditarily finite sets. -/
inductive HF : Type where
  | mk : List HF → HF
  deriving Repr

namespace HF

/-- Direct list of immediate child representations of `a : HF`. -/
def elems : HF → List HF
  | .mk xs => xs

mutual
  /-- Strictly positive nesting depth (`1 + max child depth`), used as canonical structural fuel. -/
  def depth : HF → Nat
    | .mk xs => 1 + depthList xs

  def depthList : List HF → Nat
    | [] => 0
    | x :: xs => Nat.max (depth x) (depthList xs)
end

theorem depth_pos (a : HF) : 1 ≤ a.depth := by
  cases a with
  | mk xs =>
      simp only [depth]
      omega

theorem depth_mem_lt {x : HF} {xs : List HF} (hMem : x ∈ xs) :
    x.depth ≤ depthList xs := by
  induction xs with
  | nil => nomatch hMem
  | cons hd tl ih =>
      simp only [List.mem_cons] at hMem
      simp only [depthList]
      rcases hMem with rfl | hTl
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hTl) (Nat.le_max_right _ _)

theorem depth_mem_strict {x : HF} {xs : List HF} (hMem : x ∈ xs) :
    x.depth < (HF.mk xs).depth := by
  have hLe := depth_mem_lt hMem
  simp only [depth]
  omega

/-! ## 1. Structural-Fuel Extensional Equality & Membership -/

/-- Fuel-bounded mutual subcollection check (`xs ⊆_ext ys ∧ ys ⊆_ext xs`). -/
def extEqFuel : Nat → HF → HF → Bool
  | 0, _, _ => false
  | fuel + 1, .mk xs, .mk ys =>
      xs.all (fun x => ys.any (fun y => extEqFuel fuel x y)) &&
      ys.all (fun y => xs.any (fun x => extEqFuel fuel x y))

theorem list_any_congr {α : Type} {xs : List α} {p q : α → Bool}
    (h : ∀ x : α, x ∈ xs → p x = q x) :
    xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.any_cons]
      rw [h hd (.head _), ih (fun x hx => h x (.tail hd hx))]

theorem list_all_congr {α : Type} {xs : List α} {p q : α → Bool}
    (h : ∀ x : α, x ∈ xs → p x = q x) :
    xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.all_cons]
      rw [h hd (.head _), ih (fun x hx => h x (.tail hd hx))]

/-- **Fuel Invariance Theorem**: once `fuel ≥ a.depth` and `fuel ≥ b.depth`, increasing `fuel`
    never changes `extEqFuel fuel a b`. -/
theorem extEqFuel_invariant :
    ∀ (k₁ k₂ : Nat) (a b : HF),
      a.depth ≤ k₁ → b.depth ≤ k₁ →
      a.depth ≤ k₂ → b.depth ≤ k₂ →
      extEqFuel k₁ a b = extEqFuel k₂ a b
  | 0, _, a, _, ha1, _, _, _ => by
      have hp := depth_pos a
      omega
  | _ + 1, 0, a, _, _, _, ha2, _ => by
      have hp := depth_pos a
      omega
  | m₁ + 1, m₂ + 1, .mk xs, .mk ys, ha1, hb1, ha2, hb2 => by
      simp only [extEqFuel]
      have hLeft :
          (xs.all fun x => ys.any fun y => extEqFuel m₁ x y) =
          (xs.all fun x => ys.any fun y => extEqFuel m₂ x y) := by
        apply list_all_congr
        intro x hx
        apply list_any_congr
        intro y hy
        have hxlt := depth_mem_strict hx
        have hylt := depth_mem_strict hy
        exact extEqFuel_invariant m₁ m₂ x y (by omega) (by omega) (by omega) (by omega)
      have hRight :
          (ys.all fun y => xs.any fun x => extEqFuel m₁ x y) =
          (ys.all fun y => xs.any fun x => extEqFuel m₂ x y) := by
        apply list_all_congr
        intro y hy
        apply list_any_congr
        intro x hx
        have hxlt := depth_mem_strict hx
        have hylt := depth_mem_strict hy
        exact extEqFuel_invariant m₁ m₂ x y (by omega) (by omega) (by omega) (by omega)
      rw [hLeft, hRight]

/-- Computable decidable extensional equality `a ≈_ext b` on hereditarily finite sets. -/
def extEqB (a b : HF) : Bool :=
  extEqFuel (Nat.max a.depth b.depth) a b

theorem extEqB_eq_fuel {a b : HF} {k : Nat} (ha : a.depth ≤ k) (hb : b.depth ≤ k) :
    extEqB a b = extEqFuel k a b :=
  extEqFuel_invariant (Nat.max a.depth b.depth) k a b
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) ha hb

/-- Exact unfolding of `extEqB (.mk xs) (.mk ys)` in terms of `extEqB` on elements! -/
theorem extEqB_mk (xs ys : List HF) :
    extEqB (.mk xs) (.mk ys) =
      (xs.all (fun x => ys.any (fun y => extEqB x y)) &&
       ys.all (fun y => xs.any (fun x => extEqB x y))) := by
  let K := Nat.max (HF.mk xs).depth (HF.mk ys).depth
  have hPos : 1 ≤ K := Nat.le_trans (depth_pos (.mk xs)) (Nat.le_max_left _ _)
  obtain ⟨m, hm⟩ : ∃ m : Nat, K = m + 1 := ⟨K - 1, by omega⟩
  change extEqFuel K (.mk xs) (.mk ys) = _
  rw [hm]
  simp only [extEqFuel]
  have h1 :
      (xs.all fun x => ys.any fun y => extEqFuel m x y) =
      (xs.all fun x => ys.any fun y => extEqB x y) := by
    apply list_all_congr; intro x hx; apply list_any_congr; intro y hy
    have hxlt : x.depth < K := Nat.lt_of_lt_of_le (depth_mem_strict hx) (Nat.le_max_left _ _)
    have hylt : y.depth < K := Nat.lt_of_lt_of_le (depth_mem_strict hy) (Nat.le_max_right _ _)
    exact (extEqB_eq_fuel (by omega) (by omega)).symm
  have h2 :
      (ys.all fun y => xs.any fun x => extEqFuel m x y) =
      (ys.all fun y => xs.any fun x => extEqB x y) := by
    apply list_all_congr; intro y hy; apply list_any_congr; intro x hx
    have hxlt : x.depth < K := Nat.lt_of_lt_of_le (depth_mem_strict hx) (Nat.le_max_left _ _)
    have hylt : y.depth < K := Nat.lt_of_lt_of_le (depth_mem_strict hy) (Nat.le_max_right _ _)
    exact (extEqB_eq_fuel (by omega) (by omega)).symm
  rw [h1, h2]

theorem extEqFuel_refl : ∀ (k : Nat) (a : HF), a.depth ≤ k → extEqFuel k a a = true
  | 0, a, ha => by have := depth_pos a; omega
  | m + 1, .mk xs, ha => by
      simp only [extEqFuel, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxlt := depth_mem_strict hx
        exact ⟨x, hx, extEqFuel_refl m x (by omega)⟩
      · intro x hx
        have hxlt := depth_mem_strict hx
        exact ⟨x, hx, extEqFuel_refl m x (by omega)⟩

theorem extEqB_refl (a : HF) : extEqB a a = true := by
  unfold extEqB
  exact extEqFuel_refl _ a (Nat.le_max_left _ _)

theorem extEqFuel_symm : ∀ (k : Nat) (a b : HF), extEqFuel k a b = extEqFuel k b a
  | 0, _, _ => rfl
  | m + 1, .mk xs, .mk ys => by
      simp only [extEqFuel]
      have h1 :
          (xs.all fun x => ys.any fun y => extEqFuel m x y) =
          (xs.all fun x => ys.any fun y => extEqFuel m y x) := by
        apply list_all_congr; intro x _; apply list_any_congr; intro y _
        exact extEqFuel_symm m x y
      have h2 :
          (ys.all fun y => xs.any fun x => extEqFuel m x y) =
          (ys.all fun y => xs.any fun x => extEqFuel m y x) := by
        apply list_all_congr; intro y _; apply list_any_congr; intro x _
        exact extEqFuel_symm m x y
      rw [h1, h2, Bool.and_comm]

theorem extEqB_symm (a b : HF) : extEqB a b = extEqB b a := by
  unfold extEqB
  have hc : a.depth.max b.depth = b.depth.max a.depth := Nat.max_comm a.depth b.depth
  rw [hc]
  exact extEqFuel_symm _ a b

theorem extEqFuel_trans :
    ∀ (k : Nat) (a b c : HF),
      extEqFuel k a b = true → extEqFuel k b c = true → extEqFuel k a c = true
  | 0, _, _, _, hab, _ => nomatch hab
  | m + 1, .mk xs, .mk ys, .mk zs, hab, hbc => by
      simp only [extEqFuel, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hab hbc ⊢
      constructor
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := hab.1 x hx
        obtain ⟨z, hz, hyz⟩ := hbc.1 y hy
        exact ⟨z, hz, extEqFuel_trans m x y z hxy hyz⟩
      · intro z hz
        obtain ⟨y, hy, hyz⟩ := hbc.2 z hz
        obtain ⟨x, hx, hxy⟩ := hab.2 y hy
        exact ⟨x, hx, extEqFuel_trans m x y z hxy hyz⟩

theorem extEqB_trans {a b c : HF} (hab : extEqB a b = true) (hbc : extEqB b c = true) :
    extEqB a c = true := by
  let K := a.depth + b.depth + c.depth
  have habK : extEqFuel K a b = true := by
    rw [← extEqB_eq_fuel (k := K) (by omega) (by omega)]; exact hab
  have hbcK : extEqFuel K b c = true := by
    rw [← extEqB_eq_fuel (k := K) (by omega) (by omega)]; exact hbc
  rw [extEqB_eq_fuel (k := K) (by omega) (by omega)]
  exact extEqFuel_trans K a b c habK hbcK

/-- Decidable extensional set membership `x ∈_ext a`. -/
def memB (x : HF) : HF → Bool
  | .mk ys => ys.any (fun y => extEqB x y)

theorem memB_iff {x : HF} {ys : List HF} :
    memB x (.mk ys) = true ↔ ∃ y ∈ ys, extEqB x y = true := by
  simp only [memB, List.any_eq_true]

theorem memB_congr_left {x x' : HF} (hxx' : extEqB x x' = true) (a : HF) :
    memB x a = memB x' a := by
  cases a with
  | mk ys =>
      apply Bool.eq_iff_iff.mpr
      simp only [memB_iff]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hx'x : extEqB x' x = true := by rw [extEqB_symm]; exact hxx'
        exact ⟨y, hy, extEqB_trans hx'x hxy⟩
      · rintro ⟨y, hy, hx'y⟩
        exact ⟨y, hy, extEqB_trans hxx' hx'y⟩

/-- **Axiom of Extensionality Theorem (`PROV`)**:
    Two hereditarily finite sets are extensionally equal (`extEqB a b = true`) if and only if
    they have the exact same extensional members (`∀ z, memB z a = memB z b`). -/
theorem extEqB_iff_forall_memB (a b : HF) :
    extEqB a b = true ↔ ∀ z : HF, memB z a = memB z b := by
  cases a with
  | mk xs =>
      cases b with
      | mk ys =>
          rw [extEqB_mk]
          simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
          constructor
          · rintro ⟨hXY, hYX⟩ z
            apply Bool.eq_iff_iff.mpr
            simp only [memB_iff]
            constructor
            · rintro ⟨x, hx, hzx⟩
              obtain ⟨y, hy, hxy⟩ := hXY x hx
              exact ⟨y, hy, extEqB_trans hzx hxy⟩
            · rintro ⟨y, hy, hzy⟩
              obtain ⟨x, hx, hxy⟩ := hYX y hy
              have hyx : extEqB y x = true := by rw [extEqB_symm]; exact hxy
              exact ⟨x, hx, extEqB_trans hzy hyx⟩
          · intro hAll
            constructor
            · intro x hx
              have hMemX : memB x (.mk xs) = true :=
                memB_iff.mpr ⟨x, hx, extEqB_refl x⟩
              rw [hAll x] at hMemX
              exact memB_iff.mp hMemX
            · intro y hy
              have hMemY : memB y (.mk ys) = true :=
                memB_iff.mpr ⟨y, hy, extEqB_refl y⟩
              rw [← hAll y] at hMemY
              obtain ⟨x, hx, hyx⟩ := memB_iff.mp hMemY
              have hxy : extEqB x y = true := by rw [extEqB_symm]; exact hyx
              exact ⟨x, hx, hxy⟩

/-! ## 2. Powerset-Free Rudimentary / Provident Operations (`PROV`) -/

/-- Empty set `∅`. -/
def empty : HF := .mk []

/-- Unordered pair `{a, b}`. -/
def upair (a b : HF) : HF := .mk [a, b]

/-- Singleton `{a}`. -/
def singleton (a : HF) : HF := .mk [a]

/-- Kuratowski ordered pair `⟨a, b⟩ := {{a}, {a, b}}`. -/
def kpair (a b : HF) : HF := upair (singleton a) (upair a b)

/-- Binary union `a ∪ b`. -/
def union2 : HF → HF → HF
  | .mk xs, .mk ys => .mk (xs ++ ys)

/-- Generalized union `⋃ a`. -/
def sUnion : HF → HF
  | .mk xs => .mk (xs.flatMap HF.elems)

/-- $\Delta_0$-Separation `{x ∈ a | P x}`. -/
def sep (a : HF) (P : HF → Bool) : HF :=
  .mk (a.elems.filter P)

/-- Relative complement `a \ b := {x ∈ a | x ∉ b}` (rudimentary difference). -/
def sdiff (a b : HF) : HF :=
  sep a (fun x => !memB x b)

/-- $\Delta_0$-Replacement / image `{F x | x ∈ a}`. -/
def repl (a : HF) (F : HF → HF) : HF :=
  .mk (a.elems.map F)

/-- **Powerset-Free Cartesian Product `a × b`**:
    In `ZFC`, `a × b` is carved out of `𝒫(𝒫(a ∪ b))` via Separation, requiring two Powersets.
    In Mathias's `PROV`, `a × b = ⋃_{x ∈ a} {⟨x, y⟩ | y ∈ b}` uses **only** Replacement and Union! -/
def cartesian (a b : HF) : HF :=
  sUnion (repl a (fun x => repl b (fun y => kpair x y)))

/-- Successor ordinal `S(a) := a ∪ {a}`. -/
def succOrd (a : HF) : HF :=
  union2 a (singleton a)

/-- Finite von Neumann ordinals `0 = ∅, 1 = {0}, 2 = {0, 1}, …` constructed in `PROV`. -/
def vonNeumann : Nat → HF
  | 0 => empty
  | n + 1 => succOrd (vonNeumann n)

/-! ## 3. Verified Membership Characterizations of `PROV` Operations -/

/-- A Boolean predicate on `HF` is extensional if it respects `extEqB`. -/
def ExtPred (P : HF → Bool) : Prop :=
  ∀ x y : HF, extEqB x y = true → P x = P y

/-- A function `F : HF → HF` is extensional if it preserves `extEqB`. -/
def ExtFn (F : HF → HF) : Prop :=
  ∀ x y : HF, extEqB x y = true → extEqB (F x) (F y) = true

theorem memB_empty (z : HF) : memB z empty = false := rfl

theorem memB_singleton (z a : HF) : memB z (singleton a) = extEqB z a := by
  simp only [singleton, memB, List.any_cons, List.any_nil, Bool.or_false]

theorem memB_upair (z a b : HF) :
    memB z (upair a b) = (extEqB z a || extEqB z b) := by
  simp only [upair, memB, List.any_cons, List.any_nil, Bool.or_false]

theorem memB_union2 (z a b : HF) :
    memB z (union2 a b) = (memB z a || memB z b) := by
  cases a with
  | mk xs =>
      cases b with
      | mk ys =>
          simp only [union2, memB, List.any_append]

theorem memB_sUnion_iff (z a : HF) :
    memB z (sUnion a) = true ↔ ∃ b : HF, memB b a = true ∧ memB z b = true := by
  cases a with
  | mk xs =>
      rw [sUnion, memB_iff]
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨w, ⟨b, hbIn, hwIn⟩, hzw⟩
        cases b with
        | mk bs =>
            simp only [elems] at hwIn
            exact ⟨.mk bs, memB_iff.mpr ⟨.mk bs, hbIn, extEqB_refl _⟩,
              memB_iff.mpr ⟨w, hwIn, hzw⟩⟩
      · rintro ⟨b, hbInA, hzb⟩
        obtain ⟨b₀, hb0In, hbb0⟩ := memB_iff.mp hbInA
        have hzb0 : memB z b₀ = true := by
          have hAll := (extEqB_iff_forall_memB b b₀).mp hbb0
          rw [← hAll z]
          exact hzb
        cases b₀ with
        | mk bs =>
            obtain ⟨w, hwIn, hzw⟩ := memB_iff.mp hzb0
            exact ⟨w, ⟨.mk bs, hb0In, hwIn⟩, hzw⟩

theorem memB_sep {P : HF → Bool} (hExt : ExtPred P) (z a : HF) :
    memB z (sep a P) = (memB z a && P z) := by
  cases a with
  | mk xs =>
      apply Bool.eq_iff_iff.mpr
      simp only [sep, elems, Bool.and_eq_true, memB_iff, List.mem_filter]
      constructor
      · rintro ⟨y, ⟨hyIn, hPy⟩, hzy⟩
        rw [hExt z y hzy]
        exact ⟨⟨y, hyIn, hzy⟩, hPy⟩
      · rintro ⟨⟨y, hyIn, hzy⟩, hPz⟩
        have hPy : P y = true := by rw [← hExt z y hzy]; exact hPz
        exact ⟨y, ⟨hyIn, hPy⟩, hzy⟩

theorem memB_sdiff (z a b : HF) :
    memB z (sdiff a b) = (memB z a && !memB z b) := by
  apply memB_sep
  intro x y hxy
  dsimp only
  rw [memB_congr_left hxy b]

theorem memB_repl_iff {F : HF → HF} (hExt : ExtFn F) (z a : HF) :
    memB z (repl a F) = true ↔ ∃ x : HF, memB x a = true ∧ extEqB z (F x) = true := by
  cases a with
  | mk xs =>
      simp only [repl, elems, memB_iff, List.mem_map]
      constructor
      · rintro ⟨_, ⟨x, hxIn, rfl⟩, hzx⟩
        exact ⟨x, ⟨x, hxIn, extEqB_refl x⟩, hzx⟩
      · rintro ⟨x, ⟨x₀, hx0In, hxx0⟩, hzx⟩
        have hFxFx0 : extEqB (F x) (F x₀) = true := hExt x x₀ hxx0
        exact ⟨F x₀, ⟨x₀, hx0In, rfl⟩, extEqB_trans hzx hFxFx0⟩

/-- **Powerset-Free Cartesian Product Theorem**:
    `z ∈_ext cartesian a b` iff `z` is extensionally equal to `kpair x y` for some
    `x ∈_ext a` and `y ∈_ext b`. -/
theorem memB_cartesian_iff (z a b : HF) :
    memB z (cartesian a b) = true ↔
      ∃ x y : HF, memB x a = true ∧ memB y b = true ∧ extEqB z (kpair x y) = true := by
  have hKpairRight : ∀ x : HF, ExtFn (fun y => kpair x y) := by
    intro x y₁ y₂ hy
    apply (extEqB_iff_forall_memB _ _).mpr
    intro w
    simp only [kpair, memB_upair]
    have hPairEq : extEqB (upair x y₁) (upair x y₂) = true := by
      apply (extEqB_iff_forall_memB _ _).mpr
      intro u
      simp only [memB_upair]
      have hu : extEqB u y₁ = extEqB u y₂ := by
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro h1; exact extEqB_trans h1 hy
        · intro h2; rw [extEqB_symm] at hy; exact extEqB_trans h2 hy
      rw [hu]
    have hw : extEqB w (upair x y₁) = extEqB w (upair x y₂) := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h1; exact extEqB_trans h1 hPairEq
      · intro h2; rw [extEqB_symm] at hPairEq; exact extEqB_trans h2 hPairEq
    rw [hw]
  have hOuterExt : ExtFn (fun x => repl b (fun y => kpair x y)) := by
    intro x₁ x₂ hx
    apply (extEqB_iff_forall_memB _ _).mpr
    intro w
    apply Bool.eq_iff_iff.mpr
    rw [memB_repl_iff (hKpairRight x₁), memB_repl_iff (hKpairRight x₂)]
    have hKpairLeft : ∀ y : HF, extEqB (kpair x₁ y) (kpair x₂ y) = true := by
      intro y
      apply (extEqB_iff_forall_memB _ _).mpr
      intro u
      simp only [kpair, memB_upair]
      have hSing : extEqB (singleton x₁) (singleton x₂) = true := by
        apply (extEqB_iff_forall_memB _ _).mpr
        intro v; simp only [memB_singleton]
        apply Bool.eq_iff_iff.mpr
        exact ⟨fun h1 => extEqB_trans h1 hx,
               fun h2 => extEqB_trans h2 (by rw [extEqB_symm]; exact hx)⟩
      have hUp : extEqB (upair x₁ y) (upair x₂ y) = true := by
        apply (extEqB_iff_forall_memB _ _).mpr
        intro v; simp only [memB_upair]
        have hv : extEqB v x₁ = extEqB v x₂ := by
          apply Bool.eq_iff_iff.mpr
          exact ⟨fun h1 => extEqB_trans h1 hx,
                 fun h2 => extEqB_trans h2 (by rw [extEqB_symm]; exact hx)⟩
        rw [hv]
      have hsEq : extEqB u (singleton x₁) = extEqB u (singleton x₂) :=
        Bool.eq_iff_iff.mpr ⟨fun h1 => extEqB_trans h1 hSing,
          fun h2 => extEqB_trans h2 (by rw [extEqB_symm]; exact hSing)⟩
      have huEq : extEqB u (upair x₁ y) = extEqB u (upair x₂ y) :=
        Bool.eq_iff_iff.mpr ⟨fun h1 => extEqB_trans h1 hUp,
          fun h2 => extEqB_trans h2 (by rw [extEqB_symm]; exact hUp)⟩
      rw [hsEq, huEq]
    constructor
    · rintro ⟨y, hyb, hwk⟩
      exact ⟨y, hyb, extEqB_trans hwk (hKpairLeft y)⟩
    · rintro ⟨y, hyb, hwk⟩
      have hSymm : extEqB (kpair x₂ y) (kpair x₁ y) = true := by
        rw [extEqB_symm]; exact hKpairLeft y
      exact ⟨y, hyb, extEqB_trans hwk hSymm⟩
  unfold cartesian
  rw [memB_sUnion_iff]
  constructor
  · rintro ⟨row, hRowIn, hzInRow⟩
    rw [memB_repl_iff hOuterExt] at hRowIn
    obtain ⟨x, hxa, hRowEq⟩ := hRowIn
    have hzInRepl : memB z (repl b (fun y => kpair x y)) = true := by
      have hAll := (extEqB_iff_forall_memB row _).mp hRowEq
      rw [← hAll z]
      exact hzInRow
    rw [memB_repl_iff (hKpairRight x)] at hzInRepl
    obtain ⟨y, hyb, hzk⟩ := hzInRepl
    exact ⟨x, y, hxa, hyb, hzk⟩
  · rintro ⟨x, y, hxa, hyb, hzk⟩
    refine ⟨repl b (fun y' => kpair x y'), ?_, ?_⟩
    · rw [memB_repl_iff hOuterExt]
      exact ⟨x, hxa, extEqB_refl _⟩
    · rw [memB_repl_iff (hKpairRight x)]
      exact ⟨y, hyb, hzk⟩

/-- Linear representation size of `vonNeumann n`: `(vonNeumann n).elems.length = n`. -/
theorem vonNeumann_length : ∀ n : Nat, (vonNeumann n).elems.length = n
  | 0 => rfl
  | n + 1 => by
      have ih := vonNeumann_length n
      cases hV : vonNeumann n with
      | mk xs =>
          rw [hV] at ih
          simp only [elems] at ih
          simp only [vonNeumann, hV, succOrd, singleton, union2, elems,
            List.length_append, List.length_singleton, ih]

theorem memB_vonNeumann_self (n : Nat) :
    memB (vonNeumann n) (vonNeumann (n + 1)) = true := by
  simp only [vonNeumann, succOrd, memB_union2, memB_singleton, extEqB_refl, Bool.or_true]

end HF
end ReverseMath
end SandersNSA
