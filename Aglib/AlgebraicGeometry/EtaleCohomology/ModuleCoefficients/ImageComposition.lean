/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.ImageMates
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageComposition
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgettingCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Original module inverse-image composition and scalar forgetting

The original adjoint composition is compared through its native direct-image
mate. The direct-image cube is supplied at the coefficient/site level; equality
transport is normalized for abstract families before geometric specialization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

private theorem scalarComparisonFamily_eqToHom
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {I : Sort*} (U : A ⥤ A') (V : B ⥤ B') (L : I → A ⥤ B) (L' : I → A' ⥤ B')
    (e : ∀ i, L i ⋙ V ≅ U ⋙ L' i) {i j : I} (h : i = j) (F : A) :
    (eqToHom (congrArg L' h)).app (U.obj F) ≫ (e j).inv.app F =
      (e i).inv.app F ≫ V.map ((eqToHom (congrArg L h)).app F) := by
  subst j
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id ((e i).inv.app F)).symm.trans
    (congrArg (fun t => (e i).inv.app F ≫ t) (V.map_id ((L i).obj F)).symm)

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Scalar forgetting respects the original inverse-image composition maps. -/
theorem moduleInverseImageUnderlying_comp {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (F : ModuleSheaf R X) :
    (inverseImageComp f g).hom.app ((moduleUnderlying R X).obj F) ≫
        (inverseImage g).map ((moduleInverseImageUnderlyingIso R f).inv.app F) ≫
        (moduleInverseImageUnderlyingIso R g).inv.app ((moduleInverseImage R f).obj F) =
      (moduleInverseImageUnderlyingIso R (g ≫ f)).inv.app F ≫
        (moduleUnderlying R T).map ((moduleInverseImageComp R f g).hom.app F) := by
  exact scalarComparison_comp
    (moduleImageAdjunction R f) (inverseImageAdjunction f)
    (moduleImageAdjunction R g) (inverseImageAdjunction g)
    (moduleImageAdjunction R (g ≫ f)) (inverseImageAdjunction (g ≫ f))
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R g)
    (moduleInverseImageUnderlyingIso R (g ≫ f))
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R g)
    (moduleDirectImageUnderlyingIso R (g ≫ f))
    (moduleInverseImageComp R f g) (inverseImageComp f g)
    (moduleDirectImageCompIso R f g).symm (directImageCompIso f g).symm
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R g)
    (moduleUnderlyingImageSquare_mate R (g ≫ f))
    (conjugateEquiv_moduleInverseImageComp_hom R f g)
    (conjugateEquiv_inverseImageComp_hom f g)
    (ModuleCat.Sheaf.pushforwardUnderlyingIso_comp R
      (siteBaseChange f) (siteBaseChange g) (siteBaseChange (g ≫ f))
      X.smallEtaleTopology S.smallEtaleTopology T.smallEtaleTopology
      (siteBaseChangeComp f g).symm) F

/-- Equality transports of the original inverse images commute with scalar forgetting. -/
theorem moduleInverseImageUnderlying_eqToHom {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) (F : ModuleSheaf R X) :
    (eqToHom (congrArg (fun k : S ⟶ X => inverseImage k) h)).app
        ((moduleUnderlying R X).obj F) ≫ (moduleInverseImageUnderlyingIso R g).inv.app F =
      (moduleInverseImageUnderlyingIso R f).inv.app F ≫
        (moduleUnderlying R S).map
          ((eqToHom (congrArg (fun k : S ⟶ X => moduleInverseImage R k) h)).app F) :=
  scalarComparisonFamily_eqToHom (moduleUnderlying R X) (moduleUnderlying R S)
    (fun k : S ⟶ X => moduleInverseImage R k) (fun k : S ⟶ X => inverseImage k)
    (fun k => moduleInverseImageUnderlyingIso R k) h F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
