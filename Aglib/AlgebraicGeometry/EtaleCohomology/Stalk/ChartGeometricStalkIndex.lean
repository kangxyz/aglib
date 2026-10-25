/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtalePointOpenCofinality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodCofinal
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # The actual arbitrary-base stalk index through a marked affine chart -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u
open Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η)

/-- The original affine algebra neighborhoods, with their literal marked point in the base. -/
def chartToPointElements : (GeometricEtaleNeighborhood R Ω)ᵒᵖ ⥤
    (pointSmallEtale η).fiber.Elements :=
  toPointElements R Ω ⋙ Scheme.EtalePointOpen.toPointElements j
    (Spec.algebraMap R Ω) η hη

/-- The actual final-index candidate, retaining the original double-op reindexing. -/
def chartToStalkIndex : GeometricEtaleNeighborhood R Ω ⥤
    (pointSmallEtale η).fiber.Elementsᵒᵖ :=
  (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse ⋙
    (chartToPointElements R Ω j η hη).op

/-- The actual marked point of a postcomposed original étale neighborhood. -/
def chartStagePoint (U : GeometricEtaleNeighborhood R Ω) :
    (pointSmallEtale η).fiber.obj
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) :=
  ((chartToPointElements R Ω j η hη).obj (op U)).val

/-- The original small presheaf diagram, with right-associated indexing. -/
def chartSectionDiagram (P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    GeometricEtaleNeighborhood R Ω ⥤ AddCommGrpCat.{u + 1} :=
  chartToStalkIndex R Ω j η hη ⋙ (Functor.Elements.π (pointSmallEtale η).fiber).op ⋙ P

variable [Mono j]

instance chartToPointElements_initial : (chartToPointElements R Ω j η hη).Initial := by
  unfold chartToPointElements
  infer_instance

instance chartToStalkIndex_final : (chartToStalkIndex R Ω j η hη).Final := by
  unfold chartToStalkIndex
  infer_instance

/-- The actual native stalk is the colimit over the marked affine chart neighborhoods. -/
def chartPresheafStalkIso (P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit (chartSectionDiagram R Ω j η hη P) ≅ (pointSmallEtale η).presheafFiber.obj P :=
  Functor.Final.colimitIso (chartToStalkIndex R Ω j η hη) _

/-- The native colimit comparison sends each original stage section to its marked germ. -/
@[reassoc (attr := simp)]
theorem ι_chartPresheafStalkIso_hom (P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (U : GeometricEtaleNeighborhood R Ω) :
    colimit.ι (chartSectionDiagram R Ω j η hη P) U ≫
        (chartPresheafStalkIso R Ω j η hη P).hom =
      (pointSmallEtale η).toPresheafFiber
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))
        (chartStagePoint R Ω j η hη U) P :=
  Functor.Final.ι_colimitIso_hom (chartToStalkIndex R Ω j η hη) _ U

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
