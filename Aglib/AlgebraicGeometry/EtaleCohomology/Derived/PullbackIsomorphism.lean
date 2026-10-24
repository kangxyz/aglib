/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.CategoryTheory.Adjunction.Mates.Equivalences

/-! # Original derived inverse image along a scheme isomorphism

The native derived identity and composition comparisons give the quasi-inverse
of the original functor. Native iterated-mate conjugation proves invertibility
of the original exchange across horizontal scheme isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The actual bounded-below inverse image of a scheme isomorphism is an equivalence. -/
def derivedInverseImageEquivalenceOfIso {S X : Scheme.{u}}
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)] (e : S ≅ X) :
    DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) ≌
      DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S) :=
  CategoryTheory.Equivalence.mk (derivedInverseImage e.hom) (derivedInverseImage e.inv)
    ((derivedInverseImageIdIso X).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X => derivedInverseImage f) e.inv_hom_id).symm ≪≫
      derivedInverseImageCompIso e.hom e.inv)
    ((derivedInverseImageCompIso e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun f : S ⟶ S => derivedInverseImage f) e.hom_inv_id) ≪≫
      derivedInverseImageIdIso S)

instance derivedInverseImage_isEquivalence_of_isIso {S X : Scheme.{u}}
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    (f : S ⟶ X) [IsIso f] : (derivedInverseImage f).IsEquivalence :=
  (derivedInverseImageEquivalenceOfIso (asIso f)).isEquivalence_functor

/-- Horizontal scheme isomorphisms give invertible original derived exchange
for arbitrary vertical morphisms and arbitrary bounded-below coefficients. -/
theorem derivedBaseChangeMap_isIso_of_horizontal_isIso
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) [IsIso g] [IsIso g'] :
    IsIso (derivedBaseChangeMap f f' g g' h) :=
  mateEquiv_isIso_of_equivalences (derivedImageAdjunction f) (derivedImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)

end AlgebraicGeometry.Scheme.EtaleCohomology
