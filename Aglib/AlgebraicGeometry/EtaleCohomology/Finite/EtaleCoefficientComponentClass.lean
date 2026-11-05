/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientCompositeZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # Original classes with genuine restricted component coefficients

Restriction along an etale coefficient map preserves genuine module
injectivity by the actual exact lower-shriek adjunction. The commuting
scheme square and the original underlying comparison give an explicit
coefficient isomorphism. Its induced class is the same original class,
pulled back and transported through that isomorphism. Subsequent zero
is equivalent to zero along the original composite map.

In particular this applies to coproduct component inclusions. No new
injective envelope is chosen, and no local vanishing existence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY eZ eV

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Genuine injectivity of the original etale restriction, obtained from the
actual exact extension-by-zero adjunction, without choosing a new envelope. -/
theorem moduleInverseImage_etale_injective
    {B D : Scheme.{u}} (i : D ⟶ B) [Etale i]
    (Λ : Type (u + 1)) [Ring Λ] (J : ModuleSheaf B Λ) [Injective J] :
    Injective ((moduleInverseImage i Λ).obj J) :=
  (moduleLowerShriekAdjunction i Λ).map_injective J inferInstance

/-- The canonical coefficient comparison for the original commutative square.
It requires neither Cartesianity nor injectivity and uses the actual
underlying module inverse-image isomorphism. -/
def moduleCoefficientComponentIso
    {B D Y Z : Scheme.{u}} (i : D ⟶ B) (v : Z ⟶ Y)
    (b : Y ⟶ B) (d : Z ⟶ D) (h : v ≫ b = d ≫ i)
    (Λ : Type (u + 1)) [Ring Λ] (J : ModuleSheaf B Λ) :
    (inverseImage v).obj ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj J)) ≅
    (inverseImage d).obj ((SheafOfModules.toSheaf (constantRing D Λ)).obj
      ((moduleInverseImage i Λ).obj J)) :=
  (inverseImageSquareIso i v b d h).app
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj J) ≪≫
    (inverseImage d).mapIso ((moduleInverseImageUnderlyingIso Λ i).app J).symm

/-- The actual component class of the unchanged original class. -/
def moduleCoefficientComponentClass
    {B D Y Z : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (i : D ⟶ B) (v : Z ⟶ Y) (b : Y ⟶ B) (d : Z ⟶ D)
    (h : v ≫ b = d ≫ i)
    (Λ : Type (u + 1)) [Ring Λ] (J : ModuleSheaf B Λ)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj J)) q) :
    Sheaf.H.{eZ} ((inverseImage d).obj
      ((SheafOfModules.toSheaf (constantRing D Λ)).obj
        ((moduleInverseImage i Λ).obj J))) q :=
  Sheaf.H.map (moduleCoefficientComponentIso i v b d h Λ J).hom q
    (cohomologyPullback.{u, eY, eZ} v _ q c)

/-- Any subsequent restriction of the actual component class vanishes
exactly when the unchanged original class vanishes along the composite.
The proof is the general coefficient-isomorphism naturality theorem. -/
theorem moduleCoefficientComponentClass_restriction_zero_iff
    {B D Y Z V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    (i : D ⟶ B) (v : Z ⟶ Y) (b : Y ⟶ B) (d : Z ⟶ D)
    (h : v ≫ b = d ≫ i) (k : V ⟶ Z)
    (Λ : Type (u + 1)) [Ring Λ] (J : ModuleSheaf B Λ)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj J)) q) :
    cohomologyPullback.{u, eZ, eV} k _ q
        (moduleCoefficientComponentClass.{u, eY, eZ} i v b d h Λ J q c) = 0 ↔
      cohomologyPullback.{u, eY, eV} (k ≫ v) _ q c = 0 :=
  coefficient_iso_restriction_zero_iff_composite_zero v k _ _
    (moduleCoefficientComponentIso i v b d h Λ J) q c

end AlgebraicGeometry.Scheme.EtaleCohomology
