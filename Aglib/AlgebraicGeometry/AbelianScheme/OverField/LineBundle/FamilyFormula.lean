/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.Morphism

/-!
# The actual line-bundle family classified by the original morphism

The original tensor bundle of translated pullback and dual pullback has the
class used by `lineBundleMorphism`. The whole normalization/fppf comparison
is proved before evaluating that family on a test scheme. Thus the public
formula also uses the original fppf representation, not only its normalized
view. This is the comparison needed for the original Picard base-change map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory


variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

variable [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original fppf representation classifies the original translated
family, on every locally Noetherian parameter scheme. -/
theorem fppf_homEquiv_comp_lineBundleClassMorphism
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (a : PicardGroup G.left) :
    R.homEquiv (ObjectProperty.homMk (t ≫ lineBundleClassMorphism G P R a)) =
      ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
        (translationFamilyClass G t a) := by
  let E := normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
    G.hom η[G].left (Over.w η[G])
  have h := homEquiv_comp_lineBundleClassMorphism G P R t a
  rw [lineBundleNormalizedRepresentation,
    normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv] at h
  have h' := congrArg ((E.hom.app (op T.obj)).hom) h
  have hc (z : (fppfPicardSheaf G.hom).obj.obj (op T.obj)) :
      (E.hom.app (op T.obj)).hom ((E.inv.app (op T.obj)).hom z) = z :=
    congrArg (fun θ => θ.hom z) (E.inv_hom_id_app (op T.obj))
  rw [hc, normalizedFamilyClass_fppf] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same formula names the original actual tensor line bundle, with
no choice of a representative of its Picard class. -/
theorem fppf_homEquiv_comp_lineBundleMorphism
    {T : LocallyNoetherianOver (Spec (.of k))} (t : T.obj ⟶ G)
    (L : LineBundle G.left) :
    R.homEquiv (ObjectProperty.homMk (t ≫ lineBundleMorphism G P R L)) =
      ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
        (classOf _ (translationFamilyLineBundle G t L)) := by
  exact (fppf_homEquiv_comp_lineBundleClassMorphism G P R t (classOf _ L)).trans
    (congrArg ((quotientProjection G.hom ≫ toFppfPicardSheaf G.hom).app (op T.obj)).hom
      (classOf_translationFamilyLineBundle G t L)).symm

end AlgebraicGeometry.Scheme.RelativePicard
