/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageMates
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgetting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images

/-! # Native module image mates and scalar forgetting

The actual module inverse-image underlying comparison has precisely the
actual direct-image comparison as its mate. The comparison aliases are supplied
explicitly before geometric specialization; scalar forgetting need not be full.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Original direct-image composition from actual base change of etale tests. -/
def moduleDirectImageCompIso {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    moduleDirectImage R g ⋙ moduleDirectImage R f ≅ moduleDirectImage R (g ≫ f) :=
  Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    (ModuleCat.{u + 1} R) X.smallEtaleTopology S.smallEtaleTopology T.smallEtaleTopology

/-- The original scalar-forgetting inverse comparison, as a square of left adjoints. -/
def moduleUnderlyingImageSquare {X S : Scheme.{u}} (f : S ⟶ X) :
    TwoSquare (moduleUnderlying R X) (moduleInverseImage R f)
      (inverseImage f) (moduleUnderlying R S) :=
  TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso R f).inv

/-- Its native mate is precisely the original direct-image scalar comparison. -/
theorem moduleUnderlyingImageSquare_mate {X S : Scheme.{u}} (f : S ⟶ X) :
    mateEquiv (moduleImageAdjunction R f) (inverseImageAdjunction f)
        (moduleUnderlyingImageSquare R f) =
      TwoSquare.mk _ _ _ _ (moduleDirectImageUnderlyingIso R f).hom := by
  exact mateEquiv_inv_eq_of_unit
    (moduleImageAdjunction R f) (inverseImageAdjunction f)
    (moduleInverseImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f) (fun F => by
      change (moduleUnderlying R X).map ((moduleImageAdjunction R f).unit.app F) ≫
          (𝟙 _ ≫ (directImage f).map ((moduleInverseImageUnderlyingIso R f).hom.app F)) = _
      exact (congrArg
        (fun t => (moduleUnderlying R X).map ((moduleImageAdjunction R f).unit.app F) ≫ t)
        (Category.id_comp
          ((directImage f).map ((moduleInverseImageUnderlyingIso R f).hom.app F)))).trans
            (ModuleCat.Sheaf.pullbackUnderlyingIso_unit R (siteBaseChange f)
              X.smallEtaleTopology S.smallEtaleTopology F))

/-- The actual inverse-image comparison is conjugate to the actual direct-image comparison. -/
theorem conjugateEquiv_moduleInverseImageComp_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv ((moduleImageAdjunction R f).comp (moduleImageAdjunction R g))
        (moduleImageAdjunction R (g ≫ f)) (moduleInverseImageComp R f g).hom =
      (moduleDirectImageCompIso R f g).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (moduleImageAdjunction R f) (moduleImageAdjunction R g)
    (moduleImageAdjunction R (g ≫ f)) (moduleDirectImageCompIso R f g)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
