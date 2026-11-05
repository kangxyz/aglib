/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryFaces
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate
public import Aglib.CategoryTheory.Adjunction.Mates.Chart

/-! # Horizontal mate of the original source-chart comparison

The explicit right-adjoint comparison uses ordinary étale chart exchange and
the original composite direct-image square. Its identification with the
product-test comparison is the separate remaining site-coherence step.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (H : IsPullback g' f' f g)

/-- Composite-chart formula for the original right-adjoint square. -/
def sourceEtaleCompositeDirectIso (U : X.Etale) :
    directImage g' ⋙ sourceEtaleImage f U ≅
      sourceEtaleImage f' ((siteBaseChange g').obj U) ⋙ directImage g :=
  let U' := (siteBaseChange g').obj U
  let v := pullback.fst U.hom g'
  SourceChartMates.rightIso (etaleBaseChangeIso g' U.hom)
    (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g v
      (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageInverseIso f U) (sourceEtaleImageInverseIso f' U')

/-- The actual étale restriction square has its original direct-image mate. -/
theorem sourceEtaleChartInverseMate (U : X.Etale) :
    (mateEquiv (inverseImageAdjunction g')
      (inverseImageAdjunction (pullback.fst U.hom g'))
      (TwoSquare.mk _ _ _ _
        (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
          (pullback.fst U.hom g') pullback.condition.symm).inv)).natTrans =
      (etaleBaseChangeIso g' U.hom).hom := by
  let U' := (siteBaseChange g').obj U
  let v := pullback.fst U.hom g'
  have he := inverseImageSquareIso_transpose U.hom U'.hom g' v pullback.condition.symm
  have hm := congrArg (fun (e : inverseImage U.hom ⋙ inverseImage v ≅
      inverseImage g' ⋙ inverseImage U'.hom) =>
    (mateEquiv (inverseImageAdjunction g') (inverseImageAdjunction v)
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans) he
  exact hm.symm.trans (etaleBaseChangeIso_hom g' U.hom).symm

/-- Horizontal mating gives the original étale-chart and composite-square path.
The native result type is inferred from the exact generic word. -/
theorem sourceEtaleOrdinaryComparison_mate (U : X.Etale)
    (F : AbelianSheaf.{u, u + 1} X') : type_of% (
  congrArg (fun z => z.app F) (SourceChartMates.mate_comparison
    (inverseImageAdjunction g') (inverseImageAdjunction (pullback.fst U.hom g'))
    (inverseImageAdjunction g)
    (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
      (pullback.fst U.hom g') pullback.condition.symm).symm
    (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageInverseIso f U)
    (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))
    (etaleBaseChangeIso g' U.hom)
    (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleChartInverseMate g' U)
    (mate_baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm))
    ) :=
  congrArg (fun z => z.app F) (SourceChartMates.mate_comparison
    (inverseImageAdjunction g') (inverseImageAdjunction (pullback.fst U.hom g'))
    (inverseImageAdjunction g)
    (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
      (pullback.fst U.hom g') pullback.condition.symm).symm
    (baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleImageInverseIso f U)
    (sourceEtaleImageInverseIso f' ((siteBaseChange g').obj U))
    (etaleBaseChangeIso g' U.hom)
    (directImageSquareIso (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm)
    (sourceEtaleChartInverseMate g' U)
    (mate_baseChangeMap (U.hom ≫ f) (pullback.snd U.hom g' ≫ f') g
      (pullback.fst U.hom g') (sourceEtaleCompositeSquare f f' g g' H U).w.symm))

end AlgebraicGeometry.Scheme.EtaleCohomology
