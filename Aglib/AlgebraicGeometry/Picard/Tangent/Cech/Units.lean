/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Generator
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sections

/-!
# The units `1 + ε b` of a split square-zero thickening

Let `i : X ⟶ Y`, `p : Y ⟶ X` with `i ≫ p = 𝟙 X` and let `G` be an `IdealGenerator` with
generator `ε`; the example is `X ⟶ X[ε] ⟶ X` for the dual numbers. For an open `W` of `X`:

* `IdealGenerator.oneAdd W b`: the unit `1 + ε p^♯ b` of `Γ(Y, p⁻¹ W)`, inverse `1 - ε p^♯ b`;
  `b ↦ 1 + ε p^♯ b` is injective and turns sums into products, commutes with restriction, and
  has reduction `1`.
* `IdealGenerator.units_reduction_eq_one_iff`: for affine `W`, the units of `Γ(Y, p⁻¹ W)` with
  reduction `1` are exactly the `1 + ε p^♯ b`.
* `IdealGenerator.exists_eq_mul_oneAdd`: for affine `W`, every unit `g` is
  `p^♯ (i^♯ g) · (1 + ε p^♯ b)`.

These are the unit computations behind the truncated exponential sequence
`0 → 𝒪_X → 𝒪_{X[ε]}^* → 𝒪_X^* → 1` (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 43),
on sections over one open.
-/

@[expose] public section

noncomputable section


open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible (sectionRestrict)

universe u

namespace AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {p : Y ⟶ X} {h : i ≫ p = 𝟙 X}
  (G : IdealGenerator i p h)

/-- Products of two multiples of the generator vanish. -/
theorem mulApp_mul_mulApp (W : X.Opens) (a b : Γ(X, W)) : G.mulApp W a * G.mulApp W b = 0 := by
  change restrictTop p G.ε W * (p.app W).hom a * (restrictTop p G.ε W * (p.app W).hom b) = 0
  have hε : restrictTop p G.ε W * restrictTop p G.ε W = 0 := by
    rw [← map_mul, G.eps_mul_self, map_zero]
  linear_combination ((p.app W).hom a * (p.app W).hom b) * hε

/-- The unit `1 + ε p^♯ b` of `Γ(Y, p⁻¹ W)`, with inverse `1 - ε p^♯ b`. -/
def oneAdd (W : X.Opens) (b : Γ(X, W)) : (Γ(Y, p ⁻¹ᵁ W))ˣ where
  val := 1 + G.mulApp W b
  inv := 1 - G.mulApp W b
  val_inv := by linear_combination -(G.mulApp_mul_mulApp W b b)
  inv_val := by linear_combination -(G.mulApp_mul_mulApp W b b)

@[simp]
theorem coe_oneAdd (W : X.Opens) (b : Γ(X, W)) :
    (G.oneAdd W b : Γ(Y, p ⁻¹ᵁ W)) = 1 + G.mulApp W b :=
  rfl

theorem oneAdd_add (W : X.Opens) (a b : Γ(X, W)) :
    G.oneAdd W (a + b) = G.oneAdd W a * G.oneAdd W b := by
  apply Units.ext
  rw [Units.val_mul, coe_oneAdd, coe_oneAdd, coe_oneAdd, map_add]
  linear_combination -(G.mulApp_mul_mulApp W a b)

@[simp]
theorem oneAdd_zero (W : X.Opens) : G.oneAdd W 0 = 1 :=
  Units.ext (by rw [coe_oneAdd, map_zero, add_zero, Units.val_one])

theorem oneAdd_neg (W : X.Opens) (b : Γ(X, W)) : G.oneAdd W (-b) = (G.oneAdd W b)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← oneAdd_add, neg_add_cancel, oneAdd_zero]

theorem oneAdd_sub (W : X.Opens) (a b : Γ(X, W)) :
    G.oneAdd W (a - b) = G.oneAdd W a * (G.oneAdd W b)⁻¹ := by
  rw [sub_eq_add_neg, oneAdd_add, oneAdd_neg]

theorem oneAdd_injective (W : X.Opens) : Function.Injective (G.oneAdd W) := by
  intro a b hab
  apply G.mulApp_injective W
  have e := congrArg (fun w : (Γ(Y, p ⁻¹ᵁ W))ˣ => (w : Γ(Y, p ⁻¹ᵁ W)) - 1) hab
  simpa only [coe_oneAdd, add_sub_cancel_left] using e

/-- Multiplication by the generator commutes with restriction, for any proof of the
inclusion of the preimages. -/
theorem sectionRestrict_mulApp {V W : X.Opens} (hVW : V ≤ W) (hp : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ W)
    (a : Γ(X, W)) :
    sectionRestrict Y hp (G.mulApp W a) = G.mulApp V (sectionRestrict X hVW a) :=
  G.mulApp_restrict hVW a

/-- The units `1 + ε p^♯ b` commute with restriction. -/
theorem units_map_oneAdd {V W : X.Opens} (hVW : V ≤ W) (hp : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ W)
    (b : Γ(X, W)) :
    Units.map (sectionRestrict Y hp).toMonoidHom (G.oneAdd W b) =
      G.oneAdd V (sectionRestrict X hVW b) := by
  apply Units.ext
  change sectionRestrict Y hp (1 + G.mulApp W b) = 1 + G.mulApp V (sectionRestrict X hVW b)
  rw [map_add, map_one, G.sectionRestrict_mulApp hVW hp]

-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The reduction of a multiple of the generator vanishes. -/
theorem reduction_mulApp (W : X.Opens) (a : Γ(X, W)) :
    ((reduction i p h).hom.app (op W)).hom (G.mulApp W a) = 0 := by
  change ((reduction i p h).hom.app (op W)).hom (restrictTop p G.ε W * (p.app W).hom a) = 0
  rw [map_mul, reduction_restrictTop i p h G.ε G.app_top_eps, zero_mul]

-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The reduction of `1 + ε p^♯ b` is `1`. -/
theorem reduction_oneAdd (W : X.Opens) (b : Γ(X, W)) :
    Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom (G.oneAdd W b) = 1 := by
  apply Units.ext
  change ((reduction i p h).hom.app (op W)).hom ((1 : Γ(Y, p ⁻¹ᵁ W)) + G.mulApp W b) = 1
  rw [map_add, map_one, G.reduction_mulApp, add_zero]

/-- The reduction of a unit pulled back by `p` is the unit itself. -/
theorem reduction_units_map_projection (W : X.Opens) (x : (Γ(X, W))ˣ) :
    Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom
      (Units.map (p.app W).hom.toMonoidHom x) = x :=
  Units.ext (reduction_projection i p h (op W) (x : Γ(X, W)))

-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, a unit with reduction `1` is `1 + ε p^♯ b`. -/
theorem exists_oneAdd_eq (W : X.Opens) (hW : IsAffineOpen W) (g : (Γ(Y, p ⁻¹ᵁ W))ˣ)
    (hg : Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom g = 1) :
    ∃ b : Γ(X, W), G.oneAdd W b = g := by
  have hg₁ : ((reduction i p h).hom.app (op W)).hom (g : Γ(Y, p ⁻¹ᵁ W)) = 1 :=
    congrArg Units.val hg
  have hg' : ((reduction i p h).hom.app (op W)).hom
      ((g : Γ(Y, p ⁻¹ᵁ W)) - (1 : Γ(Y, p ⁻¹ᵁ W))) = 0 := by
    rw [map_sub, map_one, hg₁, sub_self]
  obtain ⟨b, hb⟩ := G.exists_eq W hW _ hg'
  refine ⟨b, Units.ext ?_⟩
  change 1 + restrictTop p G.ε W * (p.app W).hom b = (g : Γ(Y, p ⁻¹ᵁ W))
  rw [hb]
  ring

/-- On an affine open, the units with reduction `1` are exactly the `1 + ε p^♯ b`. -/
theorem units_reduction_eq_one_iff (W : X.Opens) (hW : IsAffineOpen W)
    (g : (Γ(Y, p ⁻¹ᵁ W))ˣ) :
    Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom g = 1 ↔
      ∃ b : Γ(X, W), G.oneAdd W b = g := by
  refine ⟨G.exists_oneAdd_eq W hW g, ?_⟩
  rintro ⟨b, rfl⟩
  exact G.reduction_oneAdd W b

-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, every unit `g` is `p^♯ (i^♯ g) · (1 + ε p^♯ b)`. -/
theorem exists_eq_mul_oneAdd (W : X.Opens) (hW : IsAffineOpen W) (g : (Γ(Y, p ⁻¹ᵁ W))ˣ) :
    ∃ b : Γ(X, W), g = Units.map (p.app W).hom.toMonoidHom
      (Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom g) * G.oneAdd W b := by
  obtain ⟨b, hb⟩ := G.exists_oneAdd_eq W hW ((Units.map (p.app W).hom.toMonoidHom
    (Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom g))⁻¹ * g) (by
      rw [map_mul, map_inv, reduction_units_map_projection, inv_mul_cancel])
  exact ⟨b, by rw [hb, mul_inv_cancel_left]⟩

end AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator
