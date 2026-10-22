/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.Operations
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.QuotientCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineReductionCoordinates
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientChartTower
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Sections

/-! # All original affine quotient algebras of an algebraization

The original geometric quotient unit and the specified formal comparison give
linear quotient coordinates over the full affine chart ring. Their algebra
upgrade retains the original section rings, canonical quotient scalars, and the
original stage map on every unit tensor, in every order including zero.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicAlgebraizationData

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F : AdicSystem X (idealThickeningIdealSheaf f I)} [AdicAlgebraStructure F]
  (d : AdicAlgebraizationData F) (U : X.affineOpens)

local notation "J" => I.map (idealSectionRingHom X (idealThickeningBaseScalar f) U.val)

/-- Whole affine quotient coordinates with their original stage-map formula. -/
def affineQuotientLinearCoordinates (n : ℕ) :
    { e : (Γ(d.algebra.X, U.val) ⧸
        (J ^ n • (⊤ : Submodule Γ(X, U.val) Γ(d.algebra.X, U.val)))) ≃ₗ[Γ(X, U.val)]
          Γ(F.obj.obj (op n), U.val) //
      ∀ x, e (Submodule.Quotient.mk x) = (d.quotientMaps.app (op n)).app U.val x } := by
  let : d.algebra.X.IsQuasicoherent := QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (d.algebra_coherent R j).1)
  let c := Cohomology.idealPowerQuotientIdealSheafIso f I d.algebra.X n
  let b : (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj
      d.algebra.X ≅ F.obj.obj (op n) :=
    ((adicSystemToDiagram X (idealThickeningIdealSheaf f I)).mapIso d.beta).app (op n)
  refine quotientReductionCoordinates (idealSectionsFunctor X U.val) (J ^ n)
    (idealQuotientπ X (idealThickeningBaseScalar f) d.algebra.X (I ^ n))
    (idealPowerQuotientAffineChartEquiv f d.algebra.X I U n)
    (idealPowerQuotientAffineChartEquiv_mk f d.algebra.X I U n)
    (c ≪≫ b) (d.quotientMaps.app (op n)) ?_
  change (idealQuotientπ X (idealThickeningBaseScalar f) d.algebra.X (I ^ n)) ≫
    (c.hom ≫ b.hom) = _
  rw [← Category.assoc, Cohomology.idealQuotientπ_idealSheafIso_hom]
  rfl

/-- The actual affine section algebra modulo each original ideal power is the
specified formal-stage algebra. The packet includes canonical quotient scalars
and the original quotient map on unit tensors. -/
def affineQuotientAlgebraCoordinates (n : ℕ) :
    Algebra.QuotientAlgebraCoordinates (J ^ n)
      (Algebra.sectionAlgHom
        (show d.algebra.X ⟶ F.obj.obj (op n) from d.quotientMaps.app (op n)) U.val) :=
  Algebra.quotientAlgebraCoordinates (J ^ n)
    (Algebra.sectionAlgHom
      (show d.algebra.X ⟶ F.obj.obj (op n) from d.quotientMaps.app (op n)) U.val)
    (d.affineQuotientLinearCoordinates f I U n)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicAlgebraizationData
