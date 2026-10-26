/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward

/-! # Original tensor objects, maps and units on a ringed site

The module carrier is the coefficient-ring carrier universe `uR`, as in the
existing tensor construction. Site objects and morphisms have independent
universes. These are the actual pointwise-tensor/sheafification constructors;
no monoidal or closed structure on module sheaves is assumed here.
-/

@[expose] public noncomputable section

universe uC vC uR

open CategoryTheory MonoidalCategory

namespace SheafOfModulesOfCommRing

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR}) [HasSheafify J AddCommGrpCat.{uR}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uR}]

/-- The existing tensor object, obtained by native module sheafification. -/
abbrev tensorProduct (M N : SheafOfModulesOfCommRing R) : SheafOfModulesOfCommRing R :=
  (tensorLeftFunctor R M).obj N

/-- The original pointwise tensor map followed by module sheafification. -/
abbrev tensorMap {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    tensorProduct R M N ⟶ tensorProduct R M' N' :=
  (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ (toPresheaf R).map g)

/-- The actual module-sheafification counit, retaining the original arrow. -/
abbrev sheafifyForgetIso (M : SheafOfModulesOfCommRing R) :
    (associatedSheaf R).obj ((toPresheaf R).obj M) ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
    (𝟙 _)).counit).app M

/-- The original sheafification unit on the pointwise tensor. -/
abbrev tensorUnitMap (M N : SheafOfModulesOfCommRing R) :
    (toPresheaf R).obj M ⊗ (toPresheaf R).obj N ⟶
      (toPresheaf R).obj (tensorProduct R M N) :=
  (associatedSheafUnit R).app ((toPresheaf R).obj M ⊗ (toPresheaf R).obj N)

/-- The chosen tensor object is the object of the original tensor bifunctor. -/
theorem tensorProduct_eq_tensorFunctor (M N : SheafOfModulesOfCommRing R) :
    tensorProduct R M N = ((tensorFunctor R).obj M).obj N := rfl

/-- The chosen two-variable map retains its literal original sheafification factor. -/
theorem tensorMap_eq {M M' N N' : SheafOfModulesOfCommRing R} (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap R f g =
      (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ (toPresheaf R).map g) := rfl

/-- The chosen counit isomorphism has the actual counit as its forward arrow. -/
theorem sheafifyForgetIso_hom (M : SheafOfModulesOfCommRing R) :
    (sheafifyForgetIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction
        (R := (sheafCompose J (forget₂ CommRingCat.{uR} RingCat.{uR})).obj R)
        (𝟙 _)).counit.app M := rfl

/-- The tensor unit map is the original sheafification-unit component. -/
theorem tensorUnitMap_eq (M N : SheafOfModulesOfCommRing R) :
    tensorUnitMap R M N =
      (associatedSheafUnit R).app ((toPresheaf R).obj M ⊗ (toPresheaf R).obj N) := rfl

end SheafOfModulesOfCommRing
