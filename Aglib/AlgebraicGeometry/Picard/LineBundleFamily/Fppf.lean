/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Normalized
public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy
public import Aglib.AlgebraicGeometry.Picard.GroupLaw

/-!
# Normalized line-bundle families and the original fppf Picard group law

These comparisons use the original proper flat geometrically integral morphism
with its section over a locally Noetherian base. The representation, where used,
is the supplied one on locally Noetherian tests. No field or abelian-variety
hypothesis enters the whole normalization comparison or its group-law equations.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

attribute [local instance] Over.cartesianMonoidalCategory

section NormalizedGroupLaw

variable {S X : Scheme.{u}} [IsLocallyNoetherian S]
  (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsProper p] [Flat p] [GeometricallyIntegral p]
  (P : LocallyNoetherianOver S) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The normalized representation of the same scheme sends its original
group identity to zero. -/
theorem normalizedRepresentableBy_homEquiv_one (T : LocallyNoetherianOver S) :
    letI := picardCommGrpObj p P R
    (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R).homEquiv
      (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)) =
        (0 : normalizedSubgroup p o ho (op T.obj)) := by
  let := picardCommGrpObj p P R
  rw [normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv,
    picard_homEquiv_one]
  exact map_zero ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app
    (op T.obj)).hom

/-- The normalized representation retains the original Picard group law,
before evaluation at a particular family. -/
theorem normalizedRepresentableBy_homEquiv_mul {T : LocallyNoetherianOver S}
    (f g : T.obj ⟶ P.obj) :
    letI := picardCommGrpObj p P R
    (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R).homEquiv
      (ObjectProperty.homMk (f * g)) =
      (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R).homEquiv'
        (F := (locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho)
        (ObjectProperty.homMk f) +
      (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R).homEquiv'
        (F := (locallyNoetherianOverInclusion S).op ⋙ normalizedPicardFunctor p o ho)
        (ObjectProperty.homMk g) := by
  let := picardCommGrpObj p P R
  simp only [normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral_homEquiv,
    picard_homEquiv_mul, map_add]
  rfl

end NormalizedGroupLaw

section GeneralNormalization

variable {S X : Scheme.{u}} [IsLocallyNoetherian S]
  (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- The whole normalization comparison cancels against the original
normalized/fppf isomorphism, before any family is evaluated. -/
theorem familyNormalization_comp_normalizedFppfIso :
    familyNormalization p o ho ≫
        (normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom =
      quotientProjection p ≫ toFppfPicardSheaf p := by
  let : IsSplitEpi p := IsSplitEpi.mk' ⟨o, ho⟩
  simp only [familyNormalization, normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_hom]

/-- Evaluation of the whole comparison on an original family class. -/
theorem normalizedFamilyClass_fppf (T : Over S)
    (a : PicardGroup (pullback p T.hom)) :
    ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom.app (op T)).hom
        (normalizedFamilyClass p o ho T a) =
      ((quotientProjection p ≫ toFppfPicardSheaf p).app (op T)).hom a :=
  congrArg (fun θ => (θ.app (op T)).hom a)
    (familyNormalization_comp_normalizedFppfIso p o ho)

end GeneralNormalization

end AlgebraicGeometry.Scheme.RelativePicard
