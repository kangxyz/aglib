/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.ImageMates
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImageSquares
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarConjugateCube
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit

/-! # Original module exchange and scalar-forgetting comparison

The exchange for every commuting square is the mate of the original module
inverse-image square under its native adjunctions. Scalar forgetting identifies
this literal map with the original abelian exchange through the actual underlying
comparisons. No cartesianness, finite morphism or coefficient restriction is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ScalarConjugateCube


namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

variable {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The original module inverse-image square uses the native composition comparisons. -/
def moduleInverseImageSquareIso :
    moduleInverseImage R g ⋙ moduleInverseImage R f' ≅
      moduleInverseImage R f ⋙ moduleInverseImage R g' :=
  (moduleInverseImageComp R g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage R k) h) ≪≫
      moduleInverseImageComp R f g'

/-- The original module exchange is the native mate of its inverse-image square. -/
def moduleBaseChangeMap :
    moduleDirectImage R f ⋙ moduleInverseImage R g ⟶
      moduleInverseImage R g' ⋙ moduleDirectImage R f' :=
  (mateEquiv (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom)).natTrans

/-- The literal original unit, square and counit formula for module exchange. -/
@[reassoc]
theorem moduleBaseChangeMap_app (F : ModuleSheaf R X) :
    (moduleBaseChangeMap R f f' g g' h).app F =
      (moduleImageAdjunction R f').unit.app
          ((moduleInverseImage R g).obj ((moduleDirectImage R f).obj F)) ≫
        (moduleDirectImage R f').map
          ((moduleInverseImageSquareIso R f f' g g' h).hom.app
            ((moduleDirectImage R f).obj F)) ≫
        (moduleDirectImage R f').map
          ((moduleInverseImage R g').map ((moduleImageAdjunction R f).counit.app F)) :=
  mateEquiv_app_eq (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom) F

/-- The original module counit characterizes the adjoint of the native exchange. -/
@[reassoc]
theorem moduleBaseChangeMap_counit (F : ModuleSheaf R X) :
    (moduleInverseImage R f').map ((moduleBaseChangeMap R f f' g g' h).app F) ≫
        (moduleImageAdjunction R f').counit.app ((moduleInverseImage R g').obj F) =
      (moduleInverseImageSquareIso R f f' g g' h).hom.app ((moduleDirectImage R f).obj F) ≫
        (moduleInverseImage R g').map ((moduleImageAdjunction R f).counit.app F) :=
  mateEquiv_counit (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (TwoSquare.mk _ _ _ _ (moduleInverseImageSquareIso R f f' g g' h).hom) F

/-- The native original module direct-image square. -/
def moduleDirectImageSquareIso :
    moduleDirectImage R g' ⋙ moduleDirectImage R f ≅
      moduleDirectImage R f' ⋙ moduleDirectImage R g :=
  moduleDirectImageCompIso R f g' ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => moduleDirectImage R k) h.symm) ≪≫
      (moduleDirectImageCompIso R g f').symm

/-- The actual module inverse-image square has the original direct-image square as conjugate. -/
theorem conjugateEquiv_moduleInverseImageSquareIso_hom :
    conjugateEquiv ((moduleImageAdjunction R f).comp (moduleImageAdjunction R g'))
      ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
      (moduleInverseImageSquareIso R f f' g g' h).hom =
        (moduleDirectImageSquareIso R f f' g g' h).hom :=
  conjugate_iso_chain_of_eq
    ((moduleImageAdjunction R f).comp (moduleImageAdjunction R g'))
    (moduleImageAdjunction R (g' ≫ f)) (moduleImageAdjunction R (f' ≫ g))
    ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
    (moduleInverseImageComp R f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleInverseImage R k) h))
    (moduleInverseImageComp R g f') (moduleDirectImageCompIso R f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => moduleDirectImage R k) h.symm))
    (moduleDirectImageCompIso R g f').symm
    (moduleInverseImageSquareIso R f f' g g' h)
    (moduleDirectImageSquareIso R f f' g g' h) rfl rfl
    (conjugateEquiv_moduleInverseImageComp_hom R f g')
    (conjugateFamily_eqToHom (fun k : X' ⟶ S => moduleInverseImage R k)
      (fun k : X' ⟶ S => moduleDirectImage R k) (fun k => moduleImageAdjunction R k) h)
    (conjugate_inv_of_hom
      ((moduleImageAdjunction R g).comp (moduleImageAdjunction R f'))
      (moduleImageAdjunction R (f' ≫ g))
      (moduleInverseImageComp R g f') (moduleDirectImageCompIso R g f')
      (conjugateEquiv_moduleInverseImageComp_hom R g f'))

/-- Scalar compatibility of the original inverse square follows from its whole right mate. -/
private theorem moduleInverseImageSquareIso_underlying (F : ModuleSheaf R S) :
    ScalarSquareEquation (moduleUnderlying R S) (moduleUnderlying R X')
      (moduleInverseImageSquareIso R f f' g g' h).hom
      (inverseImageSquareIso f f' g g' h).hom
      (fun M => (inverseImage f').map ((moduleInverseImageUnderlyingIso R g).inv.app M) ≫
        (moduleInverseImageUnderlyingIso R f').inv.app ((moduleInverseImage R g).obj M))
      (fun M => (inverseImage g').map ((moduleInverseImageUnderlyingIso R f).inv.app M) ≫
        (moduleInverseImageUnderlyingIso R g').inv.app ((moduleInverseImage R f).obj M)) F :=
  scalarSquare_of_conjugateSquare
    (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleImageAdjunction R g) (moduleImageAdjunction R g')
    (inverseImageAdjunction g) (inverseImageAdjunction g')
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g) (moduleInverseImageUnderlyingIso R g')
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f')
    (moduleDirectImageUnderlyingIso R g) (moduleDirectImageUnderlyingIso R g')
    (moduleInverseImageSquareIso R f f' g g' h).hom
    (inverseImageSquareIso f f' g g' h).hom
    (moduleDirectImageSquareIso R f f' g g' h).hom
    (directImageSquareIso f f' g g' h).hom
    (conjugateEquiv_moduleInverseImageSquareIso_hom R f f' g g' h)
    (conjugateEquiv_inverseImageSquareIso_hom f f' g g' h)
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R f')
    (moduleUnderlyingImageSquare_mate R g) (moduleUnderlyingImageSquare_mate R g')
    (ModuleCat.Sheaf.pushforwardUnderlyingIso_square R
      (siteBaseChange f) (siteBaseChange g') (siteBaseChange g) (siteBaseChange f')
      S.smallEtaleTopology X.smallEtaleTopology S'.smallEtaleTopology X'.smallEtaleTopology
      (fun k : X' ⟶ S => siteBaseChange k) h.symm
      (siteBaseChangeComp f g').symm (siteBaseChangeComp g f').symm
      (moduleDirectImageSquareIso R f f' g g' h)
      (directImageSquareIso f f' g g' h) rfl rfl) F

/-- The actual underlying comparison at the source of module exchange. -/
def moduleBaseChangeSourceUnderlyingIso :
    (moduleDirectImage R f ⋙ moduleInverseImage R g) ⋙ moduleUnderlying R S' ≅
      moduleUnderlying R X ⋙ (directImage f ⋙ inverseImage g) :=
  scalarMateSourceIso (moduleDirectImageUnderlyingIso R f)
    (moduleInverseImageUnderlyingIso R g)

/-- The actual underlying comparison at the target of module exchange. -/
def moduleBaseChangeTargetUnderlyingIso :
    (moduleInverseImage R g' ⋙ moduleDirectImage R f') ⋙ moduleUnderlying R S' ≅
      moduleUnderlying R X ⋙ (inverseImage g' ⋙ directImage f') :=
  scalarMateTargetIso (moduleDirectImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g')

/-- The literal module mate forgets to the literal original abelian mate,
through the actual source and target underlying-sheaf isomorphisms. -/
@[reassoc]
theorem moduleBaseChangeMap_underlying_app (F : ModuleSheaf R X) :
    (moduleUnderlying R S').map ((moduleBaseChangeMap R f f' g g' h).app F) ≫
        (moduleBaseChangeTargetUnderlyingIso R f' g').hom.app F =
      (moduleBaseChangeSourceUnderlyingIso R f g).hom.app F ≫
        (baseChangeMap f f' g g' h).app ((moduleUnderlying R X).obj F) :=
  scalarComparison_mate_of_squareEquation
    (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R f')
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g) (moduleInverseImageUnderlyingIso R g')
    (moduleInverseImageSquareIso R f f' g g' h).hom
    (inverseImageSquareIso f f' g g' h).hom
    (moduleBaseChangeMap R f f' g g' h) (baseChangeMap f f' g g' h) rfl rfl
    (moduleBaseChangeSourceUnderlyingIso R f g)
    (moduleBaseChangeTargetUnderlyingIso R f' g') rfl rfl
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R f')
    (moduleInverseImageSquareIso_underlying R f f' g g' h) F

/-- The entire original natural transformation, not merely its isomorphism class,
commutes with scalar forgetting and the native underlying comparisons. -/
theorem moduleBaseChangeMap_underlying :
    Functor.whiskerRight (moduleBaseChangeMap R f f' g g' h) (moduleUnderlying R S') ≫
        (moduleBaseChangeTargetUnderlyingIso R f' g').hom =
      (moduleBaseChangeSourceUnderlyingIso R f g).hom ≫
        Functor.whiskerLeft (moduleUnderlying R X) (baseChangeMap f f' g g' h) :=
  scalarComparison_mate_whole_of_conjugateSquare
    (moduleImageAdjunction R f) (moduleImageAdjunction R f')
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (moduleImageAdjunction R g) (moduleImageAdjunction R g')
    (inverseImageAdjunction g) (inverseImageAdjunction g')
    (moduleInverseImageUnderlyingIso R f) (moduleInverseImageUnderlyingIso R f')
    (moduleInverseImageUnderlyingIso R g) (moduleInverseImageUnderlyingIso R g')
    (moduleDirectImageUnderlyingIso R f) (moduleDirectImageUnderlyingIso R f')
    (moduleDirectImageUnderlyingIso R g) (moduleDirectImageUnderlyingIso R g')
    (moduleInverseImageSquareIso R f f' g g' h).hom
    (inverseImageSquareIso f f' g g' h).hom
    (moduleDirectImageSquareIso R f f' g g' h).hom
    (directImageSquareIso f f' g g' h).hom
    (conjugateEquiv_moduleInverseImageSquareIso_hom R f f' g g' h)
    (conjugateEquiv_inverseImageSquareIso_hom f f' g g' h)
    (moduleUnderlyingImageSquare_mate R f) (moduleUnderlyingImageSquare_mate R f')
    (moduleUnderlyingImageSquare_mate R g) (moduleUnderlyingImageSquare_mate R g')
    (ModuleCat.Sheaf.pushforwardUnderlyingIso_square R
      (siteBaseChange f) (siteBaseChange g') (siteBaseChange g) (siteBaseChange f')
      S.smallEtaleTopology X.smallEtaleTopology S'.smallEtaleTopology X'.smallEtaleTopology
      (fun k : X' ⟶ S => siteBaseChange k) h.symm
      (siteBaseChangeComp f g').symm (siteBaseChangeComp g f').symm
      (moduleDirectImageSquareIso R f f' g g' h)
      (directImageSquareIso f f' g g' h) rfl rfl)
    (moduleBaseChangeMap R f f' g g' h) (baseChangeMap f f' g g' h) rfl rfl
    (moduleBaseChangeSourceUnderlyingIso R f g)
    (moduleBaseChangeTargetUnderlyingIso R f' g') rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
