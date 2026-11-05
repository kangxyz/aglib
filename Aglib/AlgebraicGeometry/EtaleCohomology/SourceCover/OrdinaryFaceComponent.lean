/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SourceCover.OrdinaryProductMate
public import Aglib.CategoryTheory.Adjunction.Mates.WholeFaceComponent

/-! # Whole ordinary source-chart face naturality

The native mate is identified with the actual site product square before its
original face law is transported back. No face compatibility is assumed.
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

/-- The original source-face equation at the unchanged original coefficient. -/
theorem sourceEtaleOrdinaryComparison_face_app {U V : X.Etale} (a : U ⟶ V)
    (F : AbelianSheaf.{u, u + 1} X) : type_of% (
  mateEquiv_natTrans_face_component (inverseImageAdjunction g') (inverseImageAdjunction g)
    (sourceEtaleOrdinaryComparison f f' g g' H V)
    (sourceEtaleOrdinaryComparison f f' g g' H U)
    (sourceEtaleImageMap f a) (sourceEtaleImageMap f' ((siteBaseChange g').map a))
    (sourceEtaleDirectImageSquare f f' g g' H.w.symm V).hom
    (sourceEtaleDirectImageSquare f f' g g' H.w.symm U).hom
    (sourceEtaleOrdinaryComparison_mate_product f f' g g' H V)
    (sourceEtaleOrdinaryComparison_mate_product f f' g g' H U)
    (sourceEtaleDirectImageSquare_face f f' g g' H.w.symm a) F
    ) :=
  mateEquiv_natTrans_face_component (inverseImageAdjunction g') (inverseImageAdjunction g)
    (sourceEtaleOrdinaryComparison f f' g g' H V)
    (sourceEtaleOrdinaryComparison f f' g g' H U)
    (sourceEtaleImageMap f a) (sourceEtaleImageMap f' ((siteBaseChange g').map a))
    (sourceEtaleDirectImageSquare f f' g g' H.w.symm V).hom
    (sourceEtaleDirectImageSquare f f' g g' H.w.symm U).hom
    (sourceEtaleOrdinaryComparison_mate_product f f' g g' H V)
    (sourceEtaleOrdinaryComparison_mate_product f f' g g' H U)
    (sourceEtaleDirectImageSquare_face f f' g g' H.w.symm a) F

end AlgebraicGeometry.Scheme.EtaleCohomology
