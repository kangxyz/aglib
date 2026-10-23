/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor

/-! # The original bounded-below étale inverse-image/direct-image adjunction -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Exact inverse image on the actual bounded-below derived categories. -/
abbrev derivedInverseImage (f : X ⟶ S) :
    DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S) ⥤
      DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) :=
  (inverseImage f).rightDerivedFunctorPlus

/-- The bounded-below exact inverse image is the restriction of its full derived descent. -/
def derivedInverseImageCompιIso (f : X ⟶ S) :
    derivedInverseImage f ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ (inverseImage f).mapDerivedCategory :=
  (inverseImage f).rightDerivedFunctorPlusCompιIso

/-- The canonical adjunction, with unit and counit induced from the original sheaf adjunction. -/
def derivedImageAdjunction (f : X ⟶ S) :
    derivedInverseImage f ⊣ derivedDirectImage f :=
  (inverseImageAdjunction f).rightDerivedFunctorPlus

/-- The original unit factorization on bounded-below complexes of sheaves. -/
@[reassoc]
theorem derivedImageAdjunction_unit_fac (f : X ⟶ S)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} S)) :
    (derivedImageAdjunction f).unit.app (DerivedCategory.Plus.Q.obj K) ≫
        (derivedDirectImage f).map
          ((inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app K) =
      DerivedCategory.Plus.Q.map
          ((inverseImageAdjunction f).mapCochainComplexPlus.unit.app K) ≫
        (directImage f).rightDerivedFunctorPlusUnit.app
          ((inverseImage f).mapCochainComplexPlus.obj K) :=
  (inverseImageAdjunction f).rightDerivedFunctorPlus_unit_fac K

/-- The original counit factorization on bounded-below complexes of sheaves. -/
@[reassoc]
theorem derivedImageAdjunction_counit_fac (f : X ⟶ S)
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (derivedInverseImage f).map ((directImage f).rightDerivedFunctorPlusUnit.app K) ≫
        (derivedImageAdjunction f).counit.app (DerivedCategory.Plus.Q.obj K) =
      (inverseImage f).rightDerivedFunctorPlusExactComparison.hom.app
          ((directImage f).mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map
          ((inverseImageAdjunction f).mapCochainComplexPlus.counit.app K) :=
  (inverseImageAdjunction f).rightDerivedFunctorPlus_counit_fac K

end AlgebraicGeometry.Scheme.EtaleCohomology
