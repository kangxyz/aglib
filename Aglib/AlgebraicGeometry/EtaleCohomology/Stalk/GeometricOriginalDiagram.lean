/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductOriginalDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricCohomologyDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodStalk

/-! # Whole original cohomology diagrams on geometric neighborhoods -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : (Spec (.of R)).Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : (Spec (.of R)).Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((geometricCoefficientDiagram R Ω f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (etaleObject R Ω U).hom f)))

/-- Restrict the original unresized fibre-product diagram to the actual geometric index. -/
def geometricOriginalCohomologyDiagram :
    GeometricEtaleNeighborhood R Ω ⥤ AddCommGrpCat.{e} :=
  toStalkIndex R Ω ⋙
    (Functor.Elements.π (pointSmallEtale (Spec.algebraMap R Ω)).fiber).op ⋙
      originalFibreProductCohomologyPresheaf f F q

/-- The actual system and original scheme-H diagrams agree before any resizing. -/
def geometricOriginalCohomologyIso :
    diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
        (geometricPullbackCoefficientSystem R Ω f F) q ≅
      geometricOriginalCohomologyDiagram R Ω f F q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    exact (Category.comp_id _).trans
      ((geometricDiagramCohomologyMap_eq R Ω f F q a).trans (Category.id_comp _).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
