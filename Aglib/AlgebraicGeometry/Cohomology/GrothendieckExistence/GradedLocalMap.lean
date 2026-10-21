/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPresentationMapSquare
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinateNaturality
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineMap
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCompatibility
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientNaturality

/-! # Actual coefficient morphisms between local graded quotients -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)
  (U : X.affineOpens)

/-- The original degree-zero coefficient map pulled back to the graded space. -/
def formalGradedAmbientMap : formalGradedAmbient f I F ⟶ formalGradedAmbient f I G :=
  (Scheme.Modules.pullback (formalGradedProjection f I)).map (F.gradedPieceMap φ 0)

/-- The genuine tilde morphism of the original local graded section map. -/
def formalGradedLocalMap :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
      (formalGradedLocalModule f I F U) ⟶
    tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
      (formalGradedLocalModule f I G U) := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule f I G U
  exact tilde.map (ModuleCat.ofHom (formalGradedAffineMap f I U φ))

/-- The actual ambient coordinate isomorphisms preserve coefficient morphisms. -/
theorem formalGradedAmbientSectionsIso_naturality :
    letI := formalGradedSectionAlgebra f U
    chartPullbackCoordinatesCompatible (R := Γ(X, U))
      (S := Γ(X, U) ⊗[A] I.associatedGraded)
      (formalGradedProjection f I) U.property.fromSpec (formalGradedChart f I U)
      (formalGradedChart_projection f I U) (F.gradedPieceMap φ 0)
      (affineChartΓIso U (F.gradedPiece 0)) (affineChartΓIso U (G.gradedPiece 0))
      ((F.gradedPieceMap φ 0).val.app (op U.val)) := by
  let := formalGradedSectionAlgebra f U
  exact chartPullbackCoordinatesCompatible_of_source_naturality
    (R := Γ(X, U)) (S := Γ(X, U) ⊗[A] I.associatedGraded)
    (formalGradedProjection f I) U.property.fromSpec (formalGradedChart f I U)
    (formalGradedChart_projection f I U) (F.gradedPieceMap φ 0)
    (affineChartΓIso U (F.gradedPiece 0)) (affineChartΓIso U (G.gradedPiece 0))
    ((F.gradedPieceMap φ 0).val.app (op U.val))
    (affineChartΓIso_naturality U (F.gradedPieceMap φ 0))

/-- The original scalar-extension presentations preserve every formal morphism. -/
@[reassoc]
theorem formalGradedLocalSectionQuotient_naturality :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map
      (formalGradedAmbientMap f I φ)) ≫ formalGradedLocalSectionQuotient f I G U =
      formalGradedLocalSectionQuotient f I F U ≫
        ModuleCat.ofHom (formalGradedAffineMap f I U φ) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  have hn := formalGradedAmbientSectionsIso_naturality f I φ U
  dsimp only [chartPullbackCoordinatesCompatible] at hn
  dsimp only [formalGradedLocalSectionQuotient, formalGradedAmbientSectionsIso,
    formalGradedAmbientMap]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  erw [← formalGradedAffinePresentation_map_square_categorical f I U φ]

/-- The actual local sheaf map retains the original ambient quotient square. -/
@[reassoc]
theorem formalGradedLocalQuotient_naturality :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map
      (formalGradedAmbientMap f I φ) ≫
      formalGradedLocalQuotient f I G U =
    formalGradedLocalQuotient f I F U ≫ formalGradedLocalMap f I φ U := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  exact affineQuotientFromSections_naturality _ _ _ _
    (formalGradedLocalSectionQuotient_naturality f I φ U)

end AlgebraicGeometry.Scheme.Cohomology
