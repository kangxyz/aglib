/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.Lifting
public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy

/-! # Smoothness of a supplied relative Picard representative

The original two-affine square-zero lifting construction applies to the supplied
representative itself. Existence of a representing scheme is not used here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

/-- Smoothness of the same original fppf representative, obtained from two-affine lifting.
The displayed affine morphism is geometric data, not a smoothness hypothesis. -/
theorem smooth_representative_of_isAffineHom_projectiveP1
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] [Flat p] [GeometricallyIntegral p]
    (o : Spec (.of A) ⟶ X) (ho : o ≫ p = 𝟙 _)
    (P : LocallyNoetherianOver (Spec (.of A))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
      (fppfPicardSheaf p).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    {R₀ : Type u} [CommRing R₀] (ρ : X ⟶ ProjectiveLine.projectiveP1 R₀)
    [IsAffineHom ρ] : Smooth P.obj.hom := by
  have : IsSplitEpi p := IsSplitEpi.mk' ⟨o, ho⟩
  exact Hom.smooth_of_liftsAlongNoetherianSquareZero
    (liftsAlongNoetherianSquareZero_of_relativeRepresentableBy_of_isAffineHom_projectiveP1
      p (relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p R) ρ)

end AlgebraicGeometry.Scheme.RelativePicard
