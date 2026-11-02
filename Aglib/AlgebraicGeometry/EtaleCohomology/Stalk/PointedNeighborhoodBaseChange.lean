/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PointedNeighborhoodLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricBaseChange

/-! # Original fibre products of all pointed étale neighborhoods -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u
open Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {S X : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η) (f : X ⟶ S)

/-- Original structural maps of every pointed neighborhood. -/
def pointedNeighborhoodStructure :
    pointedNeighborhoodDiagram Ω η ⟶ (Functor.const _).obj S :=
  ((Over.forgetCocone S).whisker
    (Functor.Elements.π (pointSmallEtale η).fiber ⋙ Etale.forget S)).ι

/-- The original single fibre product at every marked étale neighborhood. -/
def pointedNeighborhoodBaseChangedDiagram :
    (pointSmallEtale η).fiber.Elements ⥤ Over X :=
  Over.lift (pointedNeighborhoodDiagram Ω η) (pointedNeighborhoodStructure Ω η) ⋙
    Over.pullback f

/-- The cone with apex the literal single fibre product over the original base. -/
def pointedNeighborhoodBaseChangedCone :
    Cone (pointedNeighborhoodBaseChangedDiagram Ω η f) :=
  (Over.pullback f).mapCone
    (Over.liftCone (pointedNeighborhoodDiagram Ω η) (pointedNeighborhoodStructure Ω η)
      (pointedNeighborhoodCone R Ω j η hη)
      (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
      (pointedNeighborhoodCone_π_structure R Ω j η hη))

/-- The full original fibre-product cone is limiting as a scheme cone. -/
def pointedNeighborhoodBaseChangedConeIsLimit :
    IsLimit ((Over.forget X).mapCone (pointedNeighborhoodBaseChangedCone R Ω j η hη f)) := by
  have : Nonempty (pointSmallEtale η).fiber.Elements := IsCofiltered.nonempty
  exact isLimitOfPreserves (Over.pullback f ⋙ Over.forget X)
    (Over.isLimitLiftCone (pointedNeighborhoodDiagram Ω η)
      (pointedNeighborhoodStructure Ω η) (pointedNeighborhoodCone R Ω j η hη)
      (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
      (pointedNeighborhoodCone_π_structure R Ω j η hη)
      (pointedNeighborhoodConeIsLimit R Ω j η hη))

/-- At chart objects the entire original over-arrow is the accepted chart-cone leg. -/
lemma pointedNeighborhoodBaseChangedCone_π_chart
    (i : (GeometricEtaleNeighborhood R Ω)ᵒᵖ) :
    (pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app
      ((chartToPointElements R Ω j η hη).obj i) =
      (chartGeometricBaseChangedCone R Ω j f).π.app i := by
  have h :
      (Over.liftCone (pointedNeighborhoodDiagram Ω η) (pointedNeighborhoodStructure Ω η)
        (pointedNeighborhoodCone R Ω j η hη)
        (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
        (pointedNeighborhoodCone_π_structure R Ω j η hη)).π.app
        ((chartToPointElements R Ω j η hη).obj i) =
      (Over.liftCone (diagram R Ω) (chartGeometricStructureMap R Ω j)
        (specCone R Ω) (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j)
        (chartGeometricStructure_fac R Ω j)).π.app i := by
    apply Over.OverMorphism.ext
    exact pointedNeighborhoodCone_π_chart R Ω j η hη i
  exact congrArg (fun a => (Over.pullback f).map a) h

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
