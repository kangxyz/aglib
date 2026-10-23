/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodCofinal
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # The original geometric stalk as the small algebra-neighborhood colimit -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]

/-- The actual final functor from the algebra index to the original stalk index. -/
def toStalkIndex : GeometricEtaleNeighborhood R Ω ⥤
    (pointSmallEtale (Spec.algebraMap R Ω)).fiber.Elementsᵒᵖ :=
  (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse ⋙ (toPointElements R Ω).op

instance : (toStalkIndex R Ω).Final := by
  unfold toStalkIndex
  infer_instance

/-- The section diagram over the small algebra-presentation index. -/
def sectionDiagram (P : (Spec (.of R)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    GeometricEtaleNeighborhood R Ω ⥤ AddCommGrpCat.{u + 1} :=
  toStalkIndex R Ω ⋙
    (Functor.Elements.π (pointSmallEtale (Spec.algebraMap R Ω)).fiber).op ⋙ P

/-- The native comparison is induced by the original colimit maps on germs. -/
def stalkIso (P : (Spec (.of R)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit (sectionDiagram R Ω P) ≅
      (pointSmallEtale (Spec.algebraMap R Ω)).presheafFiber.obj P :=
  Functor.Final.colimitIso (toStalkIndex R Ω) _

/-- A section at a presentation stage maps to its literal original geometric germ. -/
@[reassoc (attr := simp)]
lemma ι_stalkIso_hom (P : (Spec (.of R)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (X : GeometricEtaleNeighborhood R Ω) :
    colimit.ι (sectionDiagram R Ω P) X ≫ (stalkIso R Ω P).hom =
      (pointSmallEtale (Spec.algebraMap R Ω)).toPresheafFiber
        (etaleObject R Ω X) (stagePoint R Ω X) P :=
  Functor.Final.ι_colimitIso_hom (toStalkIndex R Ω) _ X

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
