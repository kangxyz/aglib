/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGeometry
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineFinite
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.BaseChangeChartSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinates
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotient
public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-! # Canonical local quotients for the actual formal graded coefficient

The ambient module is the pullback of the actual degree-zero coefficient.
Every local quotient is tilde of the literal direct sum of original sections;
its quotient map is induced by the original homogeneous degree-zero action.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The actual ambient degree-zero pullback used to glue relation kernels. -/
def formalGradedAmbient : (formalGradedSpace f I).Modules :=
  (Scheme.Modules.pullback (formalGradedProjection f I)).obj (F.gradedPiece 0)

instance formalGradedAmbient_isQuasicoherent :
    (formalGradedAmbient f I F).IsQuasicoherent :=
  inferInstanceAs (((Scheme.Modules.pullback (formalGradedProjection f I)).obj
    (F.gradedPiece 0)).IsQuasicoherent)

variable (U : X.affineOpens)
/-- The exact finite tensor-coordinate module, not an isomorphic replacement. -/
def formalGradedLocalModule :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    ModuleCat (Γ(X, U) ⊗[A] I.associatedGraded) := by
  letI := formalGradedSectionAlgebra f U
  letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact ModuleCat.of _ (⨁ n, Γ(F.gradedPiece n, U))

/-- Actual ambient sections identify canonically with the degree-zero tensor source. -/
def formalGradedAmbientSectionsIso :=
  letI := formalGradedSectionAlgebra f U
  chartPullbackCoordinatesIso (R := Γ(X, U))
    (S := Γ(X, U) ⊗[A] I.associatedGraded)
    (formalGradedProjection f I) U.property.fromSpec (formalGradedChart f I U)
    (formalGradedChart_projection f I U) (F.gradedPiece 0)
    (affineChartΓIso U (F.gradedPiece 0))

/-- The actual section presentation on the graded chart. -/
def formalGradedLocalSectionQuotient :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    moduleSpecΓFunctor.obj ((formalGradedAmbient f I F).restrict (formalGradedChart f I U)) ⟶
      formalGradedLocalModule f I F U := by
  letI := formalGradedSectionAlgebra f U
  letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact (formalGradedAmbientSectionsIso f I F U).hom ≫
    ModuleCat.ofHom (formalGradedAffinePresentation f I F U)

theorem formalGradedLocalSectionQuotient_surjective :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    Function.Surjective (formalGradedLocalSectionQuotient f I F U) := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact (formalGradedAffinePresentation_surjective f I F U U.property).comp
    (ConcreteCategory.bijective_of_isIso (formalGradedAmbientSectionsIso f I F U).hom).2

/-- The canonical quotient on the literal tensor affine chart. -/
def formalGradedLocalQuotient :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    (formalGradedAmbient f I F).restrict (formalGradedChart f I U) ⟶
      tilde (formalGradedLocalModule f I F U) := by
  letI := formalGradedSectionAlgebra f U
  letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact affineQuotientFromSections _ _ (formalGradedLocalSectionQuotient f I F U)

instance formalGradedLocalQuotient_epi :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    Epi (formalGradedLocalQuotient f I F U) := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact affineQuotientFromSections_epi _ _ _
    (formalGradedLocalSectionQuotient_surjective f I F U)

/-- Local finiteness is a theorem about the actual formal section module. -/
theorem formalGradedLocalQuotient_finite :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    affineLocallyFiniteType (Spec (CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded)))
      (tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U)) := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  let : Module.Finite (Γ(X, U) ⊗[A] I.associatedGraded)
      (formalGradedLocalModule f I F U) := formalGradedAffineModule_finite f I F U U.property
  exact affineLocallyFiniteType_tilde
    (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
    (formalGradedLocalModule f I F U)

/-- The sheaf quotient retains exactly the original homogeneous section presentation. -/
@[reassoc]
theorem formalGradedLocalQuotient_sections :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    (moduleSpecΓFunctor (R := CommRingCat.of
      (Γ(X, U) ⊗[A] I.associatedGraded))).map (formalGradedLocalQuotient f I F U) ≫
      ((tilde.toTildeΓNatIso (R := CommRingCat.of
        (Γ(X, U) ⊗[A] I.associatedGraded))).app (formalGradedLocalModule f I F U)).inv =
        formalGradedLocalSectionQuotient f I F U := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  exact affineQuotientFromSections_sections
    (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded)) _ _ _

end AlgebraicGeometry.Scheme.Cohomology
