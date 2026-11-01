/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteImageClosedDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.ImageMates

/-! # Original direct images after a surjective closed source restriction

The original closed unit and original direct-image composition identify the
original coefficient image with the image of its actual source restriction.
This is valid without a finite-presentation or bounded-nilpotence assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The entire original direct image is unchanged by a surjective closed
source restriction, through the original unit and image composition. -/
def moduleDirectImageClosedSourceIso {Z Y X : Scheme.{u}}
    (f : Y ⟶ X) (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i] :
    moduleDirectImage R f ≅ moduleInverseImage R i ⋙ moduleDirectImage R (i ≫ f) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (finiteImageClosedUnitIso R i) (moduleDirectImage R f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleInverseImage R i) (moduleDirectImageCompIso R f i)

/-- Constructibility of the original image is equivalent to that of the
actual source restriction along any surjective closed immersion. -/
theorem isConstructible_directImage_iff_closedSource {Z Y X : Scheme.{u}}
    (f : Y ⟶ X) (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (F : ModuleSheaf R Y) :
    IsConstructible ((moduleDirectImage R f).obj F) ↔
      IsConstructible ((moduleDirectImage R (i ≫ f)).obj ((moduleInverseImage R i).obj F)) :=
  isConstructible_iff_of_iso ((moduleDirectImageClosedSourceIso R f i).app F)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
