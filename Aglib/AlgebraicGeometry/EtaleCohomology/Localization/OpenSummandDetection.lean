/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.LowDegreeEdge
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.GeometricFunctors
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Pullback

/-! # Original open-summand classes under conditional ordinary exchange

The ordinary exchange is the specified canonical mate, not a chosen isomorphism.
Its invertibility remains an explicit intermediate hypothesis. Lower-degree
higher-image vanishing and vanishing of the original restricted class kill the
original module-unit summand. No effacement or smooth base change is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eT eU dT dU dA

attribute [local instance] hasSheafifyLarge

variable {X U T V : Scheme.{u}}
  [HasExt.{eT} (AbelianSheaf.{u, u + 1} T)]
  [HasExt.{eU} (AbelianSheaf.{u, u + 1} V)]

/-- Invertible coefficient transport detects zero without changing the class. -/
private theorem cohomology_map_eq_zero_of_isIso
    {F G : AbelianSheaf.{u, u + 1} T} (a : F ⟶ G) [IsIso a]
    (q : ℕ) (x : Sheaf.H.{eT} F q) (hx : Sheaf.H.map a q x = 0) : x = 0 := by
  have h := congrArg (Sheaf.H.map (inv a) q) hx
  simpa only [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id,
    Sheaf.H.map_id_apply, map_zero] using h

variable
  [HasDerivedCategory.{dT} (AbelianSheaf.{u, u + 1} T)]
  [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} V)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- Conditional ordinary exchange and lower higher-image vanishing detect zero
from the original restriction. The square need only commute. -/
theorem directImageClass_eq_zero_of_restriction
    (j : U ⟶ X) (j' : V ⟶ T) (b : T ⟶ X) (b' : V ⟶ U)
    (h : j' ≫ b = b' ≫ j) (A : AbelianSheaf.{u, u + 1} U)
    [IsIso ((baseChangeMap j j' b b' h).app A)]
    (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((higherDirectImage j' a).obj ((inverseImage b').obj A)))
    (x : Sheaf.H.{eT} ((inverseImage b).obj ((directImage j).obj A)) q)
    (hx : cohomologyPullback j' _ q x = 0) : x = 0 := by
  let β := (baseChangeMap j j' b b' h).app A
  have hz : Sheaf.H.map β q x = 0 := by
    apply cohomologyDirectImageEdge_injective j' ((inverseImage b').obj A) q hq hvan
    rw [map_zero, cohomologyDirectImageEdge_apply, cohomologyPullback_coefficientMap]
    dsimp only [Functor.comp_obj]
    rw [hx, map_zero, map_zero]
  exact cohomology_map_eq_zero_of_isIso β q x hz

/-- Every original coefficient arrow to the direct image has a zero summand
when the original class restricts to zero. Naturality supplies compatibility;
no extra unit or mate equation is assumed. -/
theorem directImageSummand_eq_zero_of_restriction
    (j : U ⟶ X) (j' : V ⟶ T) (b : T ⟶ X) (b' : V ⟶ U)
    (h : j' ≫ b = b' ≫ j) (A : AbelianSheaf.{u, u + 1} U)
    [IsIso ((baseChangeMap j j' b b' h).app A)]
    {F : AbelianSheaf.{u, u + 1} X} (k : F ⟶ (directImage j).obj A)
    (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((higherDirectImage j' a).obj ((inverseImage b').obj A)))
    (x : Sheaf.H.{eT} ((inverseImage b).obj F) q)
    (hx : cohomologyPullback j' _ q x = 0) :
    Sheaf.H.map ((inverseImage b).map k) q x = 0 := by
  apply directImageClass_eq_zero_of_restriction j j' b b' h A q hq hvan
  rw [cohomologyPullback_coefficientMap, hx, map_zero]

/-- The complete coefficient-transport argument is shared before inserting
native module direct images. Both the original arrow and its transport remain
specified; only the ordinary exchange component is assumed invertible. -/
theorem transportedDirectImageSummand_eq_zero_of_restriction
    (j : U ⟶ X) (j' : V ⟶ T) (b : T ⟶ X) (b' : V ⟶ U)
    (h : j' ≫ b = b' ≫ j) (A : AbelianSheaf.{u, u + 1} U)
    [IsIso ((baseChangeMap j j' b b' h).app A)]
    {F D : AbelianSheaf.{u, u + 1} X} (k : F ⟶ D) (μ : D ≅ (directImage j).obj A)
    (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((higherDirectImage j' a).obj ((inverseImage b').obj A)))
    (x : Sheaf.H.{eT} ((inverseImage b).obj F) q)
    (hx : cohomologyPullback j' _ q x = 0) :
    Sheaf.H.map ((inverseImage b).map k) q x = 0 := by
  have hz := directImageSummand_eq_zero_of_restriction j j' b b' h A
    (k ≫ μ.hom) q hq hvan x hx
  rw [Functor.map_comp, Sheaf.H.map_comp_apply] at hz
  exact cohomology_map_eq_zero_of_isIso ((inverseImage b).map μ.hom) q
    (Sheaf.H.map ((inverseImage b).map k) q x) hz

open Coefficients

/-- The literal module-unit summand used by open/closed detection vanishes.
The canonical q0 exchange hypothesis is not supplied here. This works for any
module coefficient; injectivity belongs only to the separate retract detector. -/
theorem moduleOpenSummand_eq_zero_of_restriction
    (j : U ⟶ X) (j' : V ⟶ T) (b : T ⟶ X) (b' : V ⟶ U)
    (h : j' ≫ b = b' ≫ j) (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf X Λ)
    [IsIso ((baseChangeMap j j' b b' h).app
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj
        ((moduleInverseImage j Λ).obj I)))]
    (q : ℕ) (hq : 0 < q)
    (hvan : ∀ a : ℕ, 1 ≤ a → a < q →
      IsZero ((higherDirectImage j' a).obj ((inverseImage b').obj
        ((SheafOfModules.toSheaf (constantRing U Λ)).obj
          ((moduleInverseImage j Λ).obj I)))))
    (x : Sheaf.H.{eT} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) q)
    (hx : cohomologyPullback j' _ q x = 0) :
    Sheaf.H.map ((inverseImage b).map
      ((SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageAdjunction j Λ).unit.app I))) q x = 0 := by
  have hzero := transportedDirectImageSummand_eq_zero_of_restriction j j' b b' h
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj ((moduleInverseImage j Λ).obj I))
    ((SheafOfModules.toSheaf (constantRing X Λ)).map
      ((moduleInverseImageAdjunction j Λ).unit.app I))
    ((moduleDirectImageUnderlyingIso j Λ).app ((moduleInverseImage j Λ).obj I))
    q hq hvan x hx
  exact hzero

end AlgebraicGeometry.Scheme.EtaleCohomology
