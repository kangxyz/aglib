/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineModule
public import Aglib.RingTheory.AssociatedGraded.TensorRing
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeChart
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections

/-! # The actual associated-graded base change and its affine charts

The coordinate algebra uses the original structural map on sections. No
identification with the associated graded of a chart ideal is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- The geometric space for the external associated-graded coefficient. -/
def formalGradedSpace : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (R := A) (S := I.associatedGraded)
    (algebraMap A I.associatedGraded)))

/-- The original affine base-change projection. -/
def formalGradedProjection : formalGradedSpace f I ⟶ X :=
  pullback.fst _ _

variable (U : X.affineOpens)

/-- The chosen section algebra is the actual structural map of the affine chart. -/
theorem formalGradedChart_over :
    letI := formalGradedSectionAlgebra f U
    U.property.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, U))) := by
  let := formalGradedSectionAlgebra f U
  rw [← SpecMap_affineOpen_baseRingHom f U.property]
  congr 1

/-- The literal tensor-coordinate chart of the graded base change. -/
def formalGradedChart :
    letI := formalGradedSectionAlgebra f U
    letI : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
    Spec (CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded)) ⟶
    formalGradedSpace f I := by
  letI := formalGradedSectionAlgebra f U
  letI : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
  exact AffineBaseChange.tensorChartMap (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)

instance formalGradedChart_isOpenImmersion : IsOpenImmersion (formalGradedChart f I U) := by
  let := formalGradedSectionAlgebra f U
  let : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
  exact inferInstanceAs (IsOpenImmersion (AffineBaseChange.tensorChartMap
    (A := A) (B := Γ(X, U)) (C := I.associatedGraded)
    f U.property.fromSpec (formalGradedChart_over f U)))

@[reassoc (attr := simp)]
theorem formalGradedChart_projection :
    letI := formalGradedSectionAlgebra f U
    letI : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
    formalGradedChart f I U ≫ formalGradedProjection f I =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))) ≫ U.property.fromSpec := by
  let := formalGradedSectionAlgebra f U
  let : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
  exact AffineBaseChange.tensorChartMap_fst (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)

/-- The chart covers exactly the inverse image of the original affine open. -/
theorem formalGradedChart_range :
    Set.range (formalGradedChart f I U) =
      (formalGradedProjection f I) ⁻¹' Set.range U.property.fromSpec := by
  let := formalGradedSectionAlgebra f U
  let : CommRing (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instCommRing (R := A) (A := Γ(X, U))
      (B := I.associatedGraded)
  exact AffineBaseChange.tensorChartMap_range (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)

end AlgebraicGeometry.Scheme.Cohomology
